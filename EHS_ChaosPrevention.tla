------------------------ MODULE EHS_ChaosPrevention ------------------------
EXTENDS FiniteSets, Integers

CONSTANT 
 Edges, \* Set of Edges
 NumEdgesAllowedToTurnOff 

ASSUME NumEdgesAllowedToTurnOff =< Cardinality(Edges)

VARIABLES
  edgeState,
  ehsDecision,
  msgs

EdgesInOffState == {e \in Edges : edgeState[e] = "Off"}

EdgesInTurningOffState == {e \in Edges : edgeState[e] = "TurningOff"}

EdgesInOnState == {e \in Edges : edgeState[e] = "On"}

Messages == 
  [type : {"StatusRequest"}, sender : EdgesInTurningOffState, receiver : Edges]
    \cup
  [type : {"StatusResponse"}, sender : Edges, receiver : Edges, val : {"On", "TurningOff", "Off", "Timeout"}] 
(*************************************************************************)
(* Model Invariants                                                      *)
(*************************************************************************)
EhsTypeOK == 
  /\ edgeState \in [Edges -> {"On", "TurningOff", "Off"}]
  /\ ehsDecision \in [Edges -> {"Healthy", "Unhealthy"}]

EhsStateOK ==
  /\ Cardinality(EdgesInOffState) =< NumEdgesAllowedToTurnOff

EhsModelOk == 
  /\ EhsTypeOK
  /\ EhsStateOK

(*************************************************************************)
(* Model Init                                                            *)
(*************************************************************************)
EhsInit ==   
  /\ edgeState = [edge \in Edges |-> "On"]
  /\ ehsDecision = [ehs \in Edges |-> "Healthy"]
  /\ msgs = {}

(*************************************************************************)
(* State Changes                                                         *)
(*************************************************************************)
EhsHealthyToUnHealthy(e) == 
  /\ ehsDecision[e] = "Healthy"
  /\ ehsDecision' = [ehsDecision EXCEPT ![e] = "Unhealthy"]
  /\ UNCHANGED <<edgeState, msgs>>

EhsUnHealthyToHealthy(e) == 
  /\ ehsDecision[e] = "Unhealthy"
  /\ ehsDecision' = [ehsDecision EXCEPT ![e] = "Healthy"]
  /\ UNCHANGED <<edgeState, msgs>>
   
EdgeOnToTurningOff(e) == 
  /\ ehsDecision[e] = "Unhealthy"
  /\ edgeState[e] = "On"
  /\ edgeState' = [edgeState EXCEPT ![e] = "TurningOff"]
  /\ UNCHANGED <<ehsDecision, msgs>>
  
EdgeTurningOffToOn(e) == 
  /\ ehsDecision[e] = "Healthy"
  /\ edgeState[e] = "TurningOff"
  /\ edgeState' = [edgeState EXCEPT ![e] = "On"]
  /\ UNCHANGED <<ehsDecision, msgs>>
  
DecideToTurnOff(e, messages) ==
    /\ Cardinality({ m \in messages : /\ m.type = "StatusResponse" /\ m.receiver = e /\ m.val = "Off"}
        \cup
       { m \in messages : /\ m.type = "StatusResponse" /\ m.receiver = e /\ m.val = "TurningOff"}
        \cup
       { m \in messages : /\ m.type = "StatusResponse" /\ m.receiver = e /\ m.val = "Abort"}) =< NumEdgesAllowedToTurnOff
    /\ Cardinality ({ m \in messages : /\ m.type = "StatusResponse" /\ m.receiver = e}) = Cardinality(Edges)
       
EdgeTurningOffToOff(e) == 
  /\ ehsDecision[e] = "Unhealthy"
  /\ edgeState[e] = "TurningOff"
  /\ edgeState' = [edgeState EXCEPT ![e] = "Off"]
  /\ DecideToTurnOff(e, msgs)
  /\ UNCHANGED <<ehsDecision, msgs>>

EdgeOffToOn(e) == 
  /\ ehsDecision[e] = "Healthy"
  /\ edgeState[e] = "Off"
  /\ edgeState' = [edgeState EXCEPT ![e] = "On"]
  /\ UNCHANGED <<ehsDecision, msgs>>

(*************************************************************************)
(* Model Action                                                          *)
(*************************************************************************)
Send(m) == msgs' = msgs \cup {m}

EdgeSendsRequest(e) == 
  /\ edgeState[e] = "TurningOff"
  /\ \A targetEdge \in Edges \ {e} :
    /\ Send([type |-> "StatusRequest", sender |-> e, receiver |-> targetEdge])
  /\ UNCHANGED <<ehsDecision, edgeState>>

EdgeRespondsWithStatus(e) == 
  /\ \E m \in msgs:
    /\ m.type = "StatusRequest"
    /\ Send([type |-> "StatusResponse", sender |-> e, receiver |-> m.sender, val |-> edgeState[e]])
  /\ UNCHANGED <<ehsDecision, edgeState>>

EdgeRespondsWithAbort(e) == 
  /\ \E m \in msgs:
    /\ m.type = "StatusRequest"
    /\ Send([type |-> "StatusResponse", sender |-> e, receiver |-> m.sender, val |-> "Timeout"])
  /\ UNCHANGED <<ehsDecision, edgeState>>
  
EhsNext ==
  \/ \E e \in Edges : 
       EhsHealthyToUnHealthy(e) \/ EhsUnHealthyToHealthy(e) 
         \/ EdgeOnToTurningOff(e) \/ EdgeTurningOffToOn(e) \/ EdgeTurningOffToOff(e) \/ EdgeOffToOn(e)
             \/ EdgeSendsRequest(e) \/ EdgeRespondsWithStatus(e) \/ EdgeRespondsWithAbort(e)
           
EhsSpec == EhsInit /\ [][EhsNext]_<<edgeState, ehsDecision, msgs>> 

=============================================================================
\* Modification History
\* Last modified Thu Apr 21 00:30:53 PDT 2016 by guhanr
\* Created Wed Apr 20 10:03:01 PDT 2016 by guhanr
