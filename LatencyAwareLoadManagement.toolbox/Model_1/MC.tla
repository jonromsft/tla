---- MODULE MC ----
EXTENDS LatencyAwareLoadManagement, TLC

\* CONSTANT definitions @modelParameterConstants:0Locations
const_1460067346019886000 == 
{"L1", "L2", "L3"}
----

\* CONSTANT definitions @modelParameterConstants:1ServerCapacity
const_1460067346029887000 == 
("L1" :> 11) @@ ("L2" :> 21) @@ ("L3" :> 1)
----

\* CONSTANT definitions @modelParameterConstants:2ClientLoad
const_1460067346040888000 == 
("L1" :> 0) @@ ("L2" :> 18) @@ ("L3" :> 12)
----

\* CONSTANT definitions @modelParameterConstants:3LocationDistanceMap
const_1460067346050889000 == 
(<<"L1", "L1">> :> 0)  @@ (<<"L2", "L2">> :> 0) @@ (<<"L3", "L3">> :> 0) @@
(<<"L1", "L2">> :> 5)  @@ (<<"L2", "L1">> :> 3) @@
(<<"L1", "L3">> :> 10) @@ (<<"L3", "L1">> :> 6) @@
(<<"L2", "L3">> :> 7)  @@ (<<"L3", "L2">> :> 4)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1460067346060890000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1460067346071891000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1460067346081892000 ==
\E l \in Locations : clientLoadRemaining[l] > 0
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1460067346091893000 ==
LivenessFairnessOnConsumption
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1460067346102894000 ==
LivenessNoIdleCapacityLeftIfClientLoadRemaining
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_1460067346112895000 ==
LM!LivenessFairnessOnConsumption
----
\* PROPERTY definition @modelCorrectnessProperties:3
prop_1460067346122896000 ==
LM!LivenessNoIdleCapacityLeftIfClientLoadRemaining
----
\* PROPERTY definition @modelCorrectnessProperties:4
prop_1460067346132897000 ==
LM!Spec
----
=============================================================================
\* Modification History
\* Created Thu Apr 07 15:15:46 PDT 2016 by jonro
