---- MODULE MC ----
EXTENDS AnycastAvailability, TLC

\* CONSTANT definitions @modelParameterConstants:0MachinesPerEnvironment
const_14606599389972000 == 
("Edge-Prod-Foo" :> 3) @@ ("Edge-Prod-Bar" :> 3)
----

\* CONSTANT definitions @modelParameterConstants:1Environments
const_14606599390133000 == 
{"Edge-Prod-Foo", "Edge-Prod-Bar"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_14606599390284000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_14606599390445000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_14606599390606000 ==
VIPAvailable
----
=============================================================================
\* Modification History
\* Created Thu Apr 14 11:52:19 PDT 2016 by jonro
