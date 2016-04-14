---- MODULE MC ----
EXTENDS LoadManagement, TLC

\* CONSTANT definitions @modelParameterConstants:0Locations
const_1460062796078811000 == 
{"L1", "L2", "L3"}
----

\* CONSTANT definitions @modelParameterConstants:1ServerCapacity
const_1460062796088812000 == 
("L1" :> 5) @@ ("L2" :> 10) @@ ( "L3" :> 0 )
----

\* CONSTANT definitions @modelParameterConstants:2ClientLoad
const_1460062796098813000 == 
("L1" :> 90) @@ ("L2" :> 0) @@ ( "L3" :> 9 )
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1460062796109814000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1460062796120815000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1460062796130816000 ==
LivenessFairnessOnConsumtion
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1460062796140817000 ==
LivenessNoIdleCapacityLeftIfClientLoadRemaining
----
=============================================================================
\* Modification History
\* Created Thu Apr 07 13:59:56 PDT 2016 by jonro
