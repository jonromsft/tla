----------------------------- MODULE DieHarder -----------------------------
EXTENDS Integers

CONSTANT JugIds \* The set of Jug IDs
CONSTANT JugCapacity \* Map from Jug ID to capacity of that jug
CONSTANT Goal \* The number of gallons we're shooting for

VARIABLES jugContents \* The current capacity of each jug

(*************************************************************************)
(* Every jugs starts out empty                                           *)
(*************************************************************************)
Init == jugContents = [j \in JugIds |-> 0]

(*************************************************************************)
(* We can fill, empty, or transfer from one jug to another               *)
(*************************************************************************)
FillJug(j) == jugContents' = [jugContents EXCEPT ![j] = JugCapacity[j]]
                 
EmptyJug(j) == jugContents' = [jugContents EXCEPT ![j] = 0]

Min(m, n) == IF m < n THEN m ELSE n

Pour(from, to) == /\ from # to
                  /\ LET poured == Min(jugContents[from] + jugContents[to], JugCapacity[to]) - jugContents[to] IN
                     jugContents' = [jugContents EXCEPT ![from] = jugContents[from] - poured, ![to] = jugContents[to] + poured]

Next == \E a, b \in JugIds : FillJug(a) \/ EmptyJug(a) \/ Pour(a, b)
    
TypeOK == \A j \in JugIds : jugContents[j] \in 0..JugCapacity[j]

=============================================================================

