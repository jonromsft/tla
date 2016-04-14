---- MODULE MC ----
EXTENDS DieHarder, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
big, small
----

\* MV CONSTANT definitions JugIds
const_1459888050410431000 == 
{big, small}
----

\* CONSTANT definitions @modelParameterConstants:1Goal
const_1459888050421432000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:2JugCapacity
const_1459888050431433000 == 
(big :> 5) @@ (small :> 3)
----

\* INIT definition @modelBehaviorInit:0
init_1459888050441434000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1459888050451435000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1459888050461436000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1459888050472437000 ==
~(\E j \in JugIds : jugContents[j] = Goal)
----
=============================================================================
\* Modification History
\* Created Tue Apr 05 13:27:30 PDT 2016 by jonro
