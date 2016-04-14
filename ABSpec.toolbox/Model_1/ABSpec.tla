------------------------------ MODULE ABSpec --------------------------------
EXTENDS Integers

CONSTANT Data  \* The set of all possible data values.

VARIABLES AVar,   \* The last <<value, bit>> pair A decided to send.
          BVar    \* The last <<value, bit>> pair B received.
          
(***************************************************************************)
(* Type correctness means that AVar and BVar are tuples <<d, i>> where     *)
(* d \in Data and i \in {0, 1}.                                            *)
(***************************************************************************)
TypeOK == (AVar \in Data \X {0,1}) /\ (BVar \in Data \X {0,1})

(***************************************************************************)
(* It's useful to define vars to be the tuple of all variables, for        *)
(* example so we can write [Next]_vars instead of [Next]_<< ...  >>        *)
(***************************************************************************)
vars == << AVar, BVar >>


(***************************************************************************)
(* Initially AVar can equal <<d, 1>> for any Data value d, and BVar equals *)
(* AVar.                                                                   *)
(***************************************************************************)
Init == /\ AVar \in {<<d, 1>> : d \in Data}
        /\ BVar = AVar

(***************************************************************************)
(* When AVar = BVar, the sender can "send" an arbitrary data d item by     *)
(* setting AVar[1] to d and complementing AVar[2].  It then waits until    *)
(* the receiver "receives" the message by setting BVar to AVar before it   *)
(* can send its next message.  Sending is described by action A and        *)
(* receiving by action B.                                                  *)
(***************************************************************************)
A == /\ AVar = BVar
     /\ \E d \in Data: AVar' = <<d, 1 - AVar[2]>>
     /\ BVar' = BVar

B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* For understanding the spec, it's useful to define formulas that should  *)
(* be invariants and check that they are invariant.  The following         *)
(* invariant Inv asserts that when AVar and BVar have equal second         *)
(* components, then they are equal (which by the invariance of TypeOK      *)
(* means that they have equal first components).                           *)
(***************************************************************************)
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)
-----------------------------------------------------------------------------
(***************************************************************************)
(* FairSpec is Spec with the addition requirement that it keeps taking     *)
(* steps.                                                                  *)
(***************************************************************************)
FairSpec == Spec /\ WF_vars(Next) 
=============================================================================
\* Modification History
\* Last modified Wed Apr 06 14:39:34 PDT 2016 by jonro
\* Last modified Mon Mar 21 17:41:40 PDT 2016 by lamport
\* Created Fri Sep 04 07:08:22 PDT 2015 by lamport

