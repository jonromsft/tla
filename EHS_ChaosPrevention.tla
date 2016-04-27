------------------------ MODULE EHS_ChaosPrevention ------------------------
(***************************************************************************************************************************************************************)
(* EHS_ChaosPrevention is a spec for automatic failover protection mechanism in Ehs                                                                            *)
(* EHS (EdgeHealthService) is a monitoring service running in each of Azure Frontdoor's Edge which determines whether that Edge can serve user traffic or not. *)
(* When an Edge is determined not fit to serve traffic then it is turned off. In order to prevent global outage of all Edges, we need this protection          *)
(* mechanism to prevent all EHS instances from turning off all Edges at the same time.                                                                         *)
(***************************************************************************************************************************************************************)

EXTENDS FiniteSets, Integers, Sequences

CONSTANT 
 Edges, \* Set of Edges serving user traffic
 NumEdgesAllowedToTurnOff \* Number of Edges allowed to turn off automatically. 

ASSUME NumEdgesAllowedToTurnOff =< Cardinality(Edges)

VARIABLES
  edgeState, \* State of Edges indicating indicating whether it can serve traffic or not.
  ehsDecision, \* EHS decision for the respective edge
  messagingState, \* Messaging state of an edge indicating whether it has sent its message to other edges or not.
  msgs \* Messages sent to other Edges

-----------------------------------------------------------------------------------------------------
(*************************************************************************)
(* State Filters                                                         *)
(*************************************************************************)
EdgesInOffState == {e \in Edges : edgeState[e] = "Off"}

EdgesInTurningOffState == {e \in Edges : edgeState[e] = "TurningOff"}

EdgesInOnState == {e \in Edges : ehsDecision[e] = "On"}

EdgesInHealthyState == {e \in Edges : ehsDecision[e] = "Off"}

EdgesInUnhealthyState == {e \in Edges : ehsDecision[e] = "Unhealthy"}

-----------------------------------------------------------------------------------------------------
(*************************************************************************)
(* Model Messages                                                        *)
(*************************************************************************)
Messages == 
  [type : {"StatusRequest"}, reqSeq : Nat, sender : EdgesInTurningOffState, receiver : Edges]
    \cup
  [type : {"StatusResponse"}, reqSeq : Nat, sender : Edges, receiver : EdgesInTurningOffState, val : {"On", "TurningOff", "Off", "Timeout"}] 
    \cup
  [type : {"StatusRequestCompleted"}, sender : EdgesInTurningOffState, reason : {"BackOn" ,"TurnedOff", "Retry"}]

-----------------------------------------------------------------------------------------------------
(*************************************************************************)
(* Model Init                                                            *)
(*************************************************************************)
EhsInit ==   
  /\ edgeState = [edge \in Edges |-> "On"]
  /\ ehsDecision = [ehs \in Edges |-> "Healthy"]
  /\ messagingState = [ehs \in Edges |-> "Reset"]
  /\ msgs = {}

-----------------------------------------------------------------------------------------------------
(*************************************************************************)
(* Message Actions                                                       *)
(*************************************************************************)

SendMessage(m) == msgs' = msgs \cup {m}

SendMessages(m) == msgs' = msgs \cup m

-----------------------------------------------------------------------------------------------------
(*************************************************************************)
(* Message Filtering                                                     *)
(*************************************************************************)
HaveGotAllStatusResponseMessages(e) == 
    (* Determines whether an Edge has got responses from all the Edges to which it sent the request to. *)
    LET allSentMessages == { m \in msgs: /\ m.type = "StatusRequest"
                                         /\ m.sender = e }
        receivedMessagesForLatestSeq == { m \in msgs: /\ m.type = "StatusResponse"
                                                      /\ m.receiver = e }                          
    IN /\ Cardinality(allSentMessages) = Cardinality(receivedMessagesForLatestSeq)
                       
CompleteStatusRequestMessage(e) == 
  (* Complete status request message seq once by removing the request & response messages for a sequence *)
  LET messagesBelongingToEdge == {m \in msgs: \/ (m.type = "StatusRequest" /\ m.sender = e)
                                              \/ (m.type = "StatusResponse" /\ m.receiver = e)}
  IN /\ msgs' = msgs \ messagesBelongingToEdge

EdgesThatRespondWithGivenStateForLatestRequest(state, e) == 
 (* Returns that responded with the given state (On, Off, Turning off or Timeout) for the latest Status Request message *)
 { m1.sender : m1 \in {m \in msgs : /\ m.type = "StatusResponse" 
                                    /\ m.receiver = e 
                                    /\ m.val = state} }
                                    
StateOfTargetEdgeAsPerEdge(targetEdge, e) == 
 (* Returns what is the state of the edge 'TargetEdge' in the view of edge 'e' based on the response of 'TargetEdge' *)
 (* to the latest StatusRequest messsage from edge 'e'                                                               *)
 { m1.val : m1 \in {m \in msgs : /\ m.type = "StatusResponse" 
                                 /\ m.receiver = e
                                 /\ m.sender = targetEdge} }                                                             
EdgesNotInOnStateInTheViewOfEdge(e) == 
  (*******************************************************************************)
  (* Get the list of Edges which are not in the On state.                        *)
  (* That is any edge which responsed with Off, Turning Off or Timeout as status.*)
  (* Also, include the edge itself.                                              *)
  (*******************************************************************************)
  EdgesThatRespondWithGivenStateForLatestRequest("Off", e) 
    \cup 
  EdgesThatRespondWithGivenStateForLatestRequest("TurningOff", e)
    \cup
  EdgesThatRespondWithGivenStateForLatestRequest("Timeout", e)
    \cup 
  IF edgeState[e] /= "On" THEN {e}
  ELSE {}
  
CanTurnOff(e) ==
    (*************************************************************************)
    (* An Edge can turn off only if (total number of edges which responded   *)
    (* as Off, TurnedOff or Timeout) <= Number Edges Allowed to Turn Off     *)
    (*************************************************************************)
    /\ Cardinality(EdgesNotInOnStateInTheViewOfEdge(e)) =< NumEdgesAllowedToTurnOff
    
-----------------------------------------------------------------------------------------------------
(*************************************************************************)
(* State Changes                                                         *)
(*************************************************************************)
EhsHealthyToUnHealthy(e) == 
  (* EHS can at anytime determine that edge goes from Healthy to UnHealthy state *)
  /\ ehsDecision[e] = "Healthy"
  /\ ehsDecision' = [ehsDecision EXCEPT ![e] = "Unhealthy"]
  /\ UNCHANGED <<edgeState, msgs, messagingState>>

EhsUnHealthyToHealthy(e) == 
  (* EHS can at anytime determine that edge goes from UnHealthy to Healthy state *)
  /\ ehsDecision[e] = "Unhealthy"
  /\ ehsDecision' = [ehsDecision EXCEPT ![e] = "Healthy"]
  /\ UNCHANGED <<edgeState, msgs, messagingState>>
   
EdgeOnToTurningOff(e) == 
  (* When Ehs' decision is Unhealthy then the Edge goes to TurningOff state if it is in On state. *)
  /\ ehsDecision[e] = "Unhealthy"
  /\ edgeState[e] = "On"
  /\ edgeState' = [edgeState EXCEPT ![e] = "TurningOff"]
  /\ UNCHANGED <<ehsDecision, msgs, messagingState>>
  
EdgeTurningOffToOn(e) == 
  (* When Ehs' decision is Healthy then the Edge goes to On state from Turning Off state, provided *)
  (* it has completed it messaging process which it started when it went to Turning Off state*)
  /\ ehsDecision[e] = "Healthy"
  /\ edgeState[e] = "TurningOff"
  /\ messagingState[e] = "Completed"
  /\ edgeState' = [edgeState EXCEPT ![e] = "On"]
  /\ messagingState' = [messagingState EXCEPT ![e] = "Reset"]
  /\ CompleteStatusRequestMessage(e)
  /\ UNCHANGED <<ehsDecision>>
  
EdgeTurningOffToTurningOff(e) ==
  (****************************************************************************)
  (* This is a case where the Edge can't move away from the Turning Off state *)
  (* because there are too many edges in turning off or off state or have not *)
  (* responded to the status request message                                  *) 
  (****************************************************************************)
  /\ ehsDecision[e] = "Unhealthy"
  /\ edgeState[e] = "TurningOff"
  /\ messagingState[e] = "Completed"
  /\ ~CanTurnOff(e)
  /\ messagingState' = [messagingState EXCEPT ![e] = "Reset"]
  /\ CompleteStatusRequestMessage(e)
  /\ UNCHANGED <<edgeState, ehsDecision>>
   
EdgeTurningOffToOff(e) == 
  (* Edge has gotten responses from other Edges and it determines that the total number of edges not in On state     *)
  (* are below the allowed threshold. Hence, it can go to Off State from Turning Off state as it is still unhealthy. *)
  /\ ehsDecision[e] = "Unhealthy"
  /\ edgeState[e] = "TurningOff"
  /\ messagingState[e] = "Completed"
  /\ CanTurnOff(e)
  /\ edgeState' = [edgeState EXCEPT ![e] = "Off"]
  /\ messagingState' = [messagingState EXCEPT ![e] = "Reset"]
  /\ CompleteStatusRequestMessage(e)
  /\ UNCHANGED <<ehsDecision>>

EdgeOffToOn(e) == 
  (* When Ehs' decision is Healthy then the Edge goes to On state if it is in Off state. *)
  /\ ehsDecision[e] = "Healthy"
  /\ edgeState[e] = "Off"
  /\ edgeState' = [edgeState EXCEPT ![e] = "On"]
  /\ UNCHANGED <<ehsDecision, msgs, messagingState>>
  
-----------------------------------------------------------------------------------------------------
(*************************************************************************)
(* Messaging Actions                                                     *)
(*************************************************************************)
NotRespondedToStatusRequestMessage(e, statusRequestMessage) == 
  /\ ~(\E m \in msgs: /\ m.type="StatusResponse" 
                      /\ m.sender = e
                      /\ m.receiver = statusRequestMessage.sender)
                      
EdgeProcessResponses(e) ==
   (* Once an Edge has received all the responses for its requests then the message has completed. *)
   /\ edgeState[e] = "TurningOff"
   /\ ehsDecision[e] = "Unhealthy"
   /\ messagingState[e] = "Sent"
   /\ HaveGotAllStatusResponseMessages(e)
   /\ messagingState' = [messagingState EXCEPT ![e] = "Completed"]
   /\ UNCHANGED <<ehsDecision, edgeState, msgs>>

EdgeSendsRequest(e) == 
     (* When an edge comes to Turning Off, then it will send a request to all other edges asking their state. *)
     /\ edgeState[e] = "TurningOff"
     /\ ehsDecision[e] = "Unhealthy"
     /\ messagingState[e] = "Reset"
     /\ messagingState' = [messagingState EXCEPT ![e] = "Sent"]
     /\ SendMessages({[type |-> "StatusRequest", sender |-> e, receiver |-> e1] : e1 \in Edges \ {e}})
     /\ UNCHANGED <<ehsDecision, edgeState>>

EdgeRespondsWithStatus(e) == 
  (* Whenever there is a pending request, asking its state, for the edge then the edge responds with it state. *)
  /\ \E m \in msgs:
    /\ m.type = "StatusRequest"
    /\ m.receiver = e
    /\ NotRespondedToStatusRequestMessage(e, m)
    /\ SendMessage([type |-> "StatusResponse", sender |-> e, receiver |-> m.sender, val |-> edgeState[e]])
  /\ UNCHANGED <<ehsDecision, edgeState, messagingState>>

EdgeRespondsWithAbort(e) == 
  (* At times an edge can respond with a timeout message for pending state request to it. *)
  (* This simulates request timeouts *)
  /\ \E m \in msgs:
    /\ m.type = "StatusRequest"
    /\ m.receiver = e
    /\ NotRespondedToStatusRequestMessage(e, m)
    /\ SendMessage([type |-> "StatusResponse", sender |-> e, receiver |-> m.sender, val |-> "Timeout"])
  /\ UNCHANGED <<ehsDecision, edgeState, messagingState>>
  
-----------------------------------------------------------------------------------------------------
(*************************************************************************)
(* Model Invariants                                                      *)
(*************************************************************************)
EhsTypeOK == 
  (* Invariant ensuring that the different state don't take an invalid value. *)
  /\ edgeState \in [Edges -> {"On", "TurningOff", "Off"}]
  /\ ehsDecision \in [Edges -> {"Healthy", "Unhealthy"}]
  /\ messagingState \in [Edges -> {"Reset", "Sent", "Completed"}]

EhsStateOK ==
  (* Important Invariant which ensures that not too many Edges are in Off state thus preventing global outage. *)
  /\ Cardinality(EdgesInOffState) =< NumEdgesAllowedToTurnOff

EhsModelOk == 
  /\ EhsTypeOK
  /\ EhsStateOK

NoEdgeHasLiedAboutItsState == 
  (* Invariant which ensures that no edges gives a wrong reply to the StatusRequest Message. *)
  ~(\E m \in msgs: /\ m.type = "StateResponse"
                 /\ (m.val /= "Timeout" /\ edgeState[m.sender] /= m.val))

NoTwoTurningOffEdgesSeeEachOtherInOnState == 
  (* Invariant which ensures there are no race condition when two edges are turning off at the same time.      *)
  (* No two edges which are going to turning off state at the time should see each other in On state.          *)
  (* This ensures that the edges updates its state before requesting other edges about their respective state. *)
  ~(\E e1, e2 \in Edges : /\ e1 /= e2
                          /\ edgeState[e1] = "TurningOff"
                          /\ edgeState[e2] = "TurningOff"
                          /\ messagingState[e1] = "Completed"
                          /\ messagingState[e1] = "Completed"
                          /\ StateOfTargetEdgeAsPerEdge(e2, e1) = {"On"}
                          /\ StateOfTargetEdgeAsPerEdge(e1, e2) = {"On"})

----------------------------------------------------------------------------------------------------

EhsNext ==
  \/ \E e \in Edges : 
       EhsHealthyToUnHealthy(e) \/ EhsUnHealthyToHealthy(e) 
         \/ EdgeOnToTurningOff(e) \/ EdgeTurningOffToOn(e) \/ EdgeTurningOffToOff(e) \/ EdgeTurningOffToTurningOff(e) \/ EdgeOffToOn(e)
             \/ EdgeSendsRequest(e) \/ EdgeProcessResponses(e) \/ EdgeRespondsWithStatus(e) \/ EdgeRespondsWithAbort(e)
           
EhsSpec == EhsInit /\ [][EhsNext]_<<edgeState, ehsDecision, messagingState, msgs>> 

=============================================================================
\* Modification History
\* Last modified Wed Apr 27 10:55:09 PDT 2016 by guhanr
\* Created Wed Apr 20 10:03:01 PDT 2016 by guhanr
