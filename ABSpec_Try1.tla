------------------------------ MODULE ABSpec_Try1 --------------------------------
(***************************************************************************)
(* The purpose of the Alternating Bit protocol is for A to choose a value  *)
(* and send it to B.  When B has received the value, A can then choose a   *)
(* new value and send it to B.  And so on.                                 *)
(*                                                                         *)
(* At this level of abstraction, the fact that messages are used to        *)
(* accomplish this is irrelevant.  All we observe are the values being     *)
(* sent by A and received by B.                                            *)
(***************************************************************************)

CONSTANT Data  \* The set of all possible data values.

VARIABLES AVar,  \* The last value that A decided to send.
          BVar   \* The last value that B received.

TypeOK == (AVar \in Data ) /\ (BVar \in Data)

Init == /\ AVar \in Data
        /\ BVar = AVar

(***************************************************************************)
(* When AVar = BVar, the sender can "sends" an arbitrary data item d by    *)
(* setting AVar to d.  It then waits until the receiver "receives" the     *)
(* message by setting BVar to AVar before it can send its next message.    *)
(* Sending is described by action A and receiving by action B.             *)
(***************************************************************************)
A == /\ AVar = BVar
     /\ AVar' \in Data  \* Can also write \E d \in Data : AVar' = d
     /\ BVar' = BVar

B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == Init /\ [][Next]_<<AVar, BVar>>

(***************************************************************************)
(* What's wrong with this spec?                                            *)
(***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Sat Mar 12 11:25:06 PST 2016 by lamport
\* Created Fri Sep 04 07:08:22 PDT 2015 by lamport

