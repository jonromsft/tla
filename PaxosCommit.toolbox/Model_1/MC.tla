---- MODULE MC ----
EXTENDS PaxosCommit, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT definitions Acceptor
const_1459898069964512000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions RM
const_1459898069989513000 == 
{r1, r2}
----

\* SYMMETRY definition
symm_1459898070004514000 == 
Permutations(const_1459898069964512000) \union Permutations(const_1459898069989513000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballot
const_1459898070020515000 == 
{0, 1}
----

\* CONSTANT definitions @modelParameterConstants:2Majority
const_1459898070036516000 == 
{{a1, a2}, {a1, a3}, {a2, a3}}
----

\* INIT definition @modelBehaviorInit:0
init_1459898070051517000 ==
PCInit
----
\* NEXT definition @modelBehaviorNext:0
next_1459898070067518000 ==
PCNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1459898070090519000 ==
PCTypeOK
----
=============================================================================
\* Modification History
\* Created Tue Apr 05 16:14:30 PDT 2016 by jonro
