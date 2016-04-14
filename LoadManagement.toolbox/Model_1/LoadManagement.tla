--------------------------- MODULE LoadManagement ---------------------------
EXTENDS Integers, Sequences

CONSTANT Locations,      \* Where the objects are
         ClientLoad,     \* How much load is coming from one location
         ServerCapacity  \* How much capacity is available at one location

VARIABLE serverCapacityRemaining, \* Mapping from location to utilization of the server at that location
         clientLoadRemaining      \* How much of the load from any location is consumed

vars == <<serverCapacityRemaining, clientLoadRemaining>>

Init ==
    /\  serverCapacityRemaining = [ l \in Locations |-> ServerCapacity[l] ]
    /\  clientLoadRemaining = [ l \in Locations |-> ClientLoad[l] ]

TypeOK ==
    /\ \A l \in Locations : /\ serverCapacityRemaining[l] \in 0..ServerCapacity[l]
                            /\ clientLoadRemaining[l] \in 0..ClientLoad[l]

Min(m, n) == IF m < n THEN m ELSE n

ConsumeClientLoad(from, to) == /\ serverCapacityRemaining[to] > 0
                               /\ clientLoadRemaining[from] > 0
                               /\ LET consumed == Min(clientLoadRemaining[from], serverCapacityRemaining[to])
                                  IN /\ clientLoadRemaining' = [clientLoadRemaining EXCEPT ![from] = clientLoadRemaining[from] - consumed]
                                     /\ serverCapacityRemaining' = [serverCapacityRemaining EXCEPT ![to] = serverCapacityRemaining[to] - consumed]

ConsumeLocally == \E l \in Locations: 
                ConsumeClientLoad(l, l)

ConsumeFromOthers == \E l1, l2 \in Locations : 
                /\ clientLoadRemaining[l2] \leq ClientLoad[l2] 
                /\ ConsumeClientLoad(l1, l2)

Next == 
   \/ ConsumeLocally
   \/ ConsumeFromOthers

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) \* /\ WF_vars(ConsumeLocally)

\* Servers prefer to consume traffic from the local client
LivenessFairnessOnConsumption == \A l \in Locations : TRUE ~> ServerCapacity[l] = 0 \/ clientLoadRemaining[l] \leq ClientLoad[l]

\* If there's available capacity somewhere I should not have any ClientLoad remaining
LivenessNoIdleCapacityLeftIfClientLoadRemaining == TRUE ~> (~\E l \in Locations : serverCapacityRemaining[l]>0 ) \/ (~\E l \in Locations :  clientLoadRemaining[l] > 0)

=============================================================================
\* Modification History
\* Last modified Thu Apr 07 12:36:58 PDT 2016 by jonro
\* Created Thu Apr 07 10:06:57 PDT 2016 by jonro
