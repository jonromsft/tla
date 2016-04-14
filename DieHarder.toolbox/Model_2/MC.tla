---- MODULE MC ----
EXTENDS DieHarder, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
big, medium, small
----

\* MV CONSTANT definitions JugIds
const_1459887786016417000 == 
{big, medium, small}
----

\* CONSTANT definitions @modelParameterConstants:1Goal
const_1459887786027418000 == 
11
----

\* CONSTANT definitions @modelParameterConstants:2JugCapacity
const_1459887786037419000 == 
(big :> 15) @@ (medium :> 7) @@ (small :> 3)
----

\* INIT definition @modelBehaviorInit:0
init_1459887786048420000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1459887786058421000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1459887786069422000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1459887786080423000 ==
~(\E j \in JugIds : jugContents[j] = Goal)
----
=============================================================================
\* Modification History
\* Created Tue Apr 05 13:23:06 PDT 2016 by jonro
