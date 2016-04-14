---------------------------- MODULE ABJonRoSpec ----------------------------
EXTENDS Integers, Sequences

CONSTANT Data \* The input data set.  All the values that A can send to B

\* Remove the ith element from the sequence, returning a new sequence
Remove(i, seq) == [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

VARIABLES AVar, \* Current message of A
          BVar, \* Current message of B
          AtoB, \* Lossy FIFO channel from A to B
          BtoA  \* Lossy FIFO channel from B to A

\* The set of all sequence bits is 0 or 1
SequenceBits == {0, 1}

\* The set of all messages is everything from Data as the value, and everything in SequenceBits as the seqBit
Messages == [value : Data, seqBit : SequenceBits]
  
TypeOK == /\ (AVar \in Messages) \* AVar must be a message
          /\ (BVar \in Messages) \* BVar is a sequence bit
          /\ (\A i \in 1..Len(AtoB) : AtoB[i] \in Messages) \* AtoB is a sequence of messages
          /\ (\A i \in 1..Len(BtoA) : BtoA[i] \in SequenceBits) \* BtoA is a sequence of sequence bits

\* The variables in the system
vars == << AVar, BVar, AtoB, BtoA >>

Init == /\ \E d \in Data : AVar = [ value |-> d, seqBit |-> 1 ] \* A starts with random data and a seqBit of 1
        /\ BVar = AVar \* B has already received message with sequence bit 1 from A
        /\ AtoB = <<>> \* Nothing in the channel
        /\ BtoA = <<>> \* Nothing in the channel

(*********************************************************************************)
(* A to B                                                                        *)
(* A can read/write AVar, consume the BtoA channel, and produce the AtoB channel *)
(*********************************************************************************)
\* If there are messages from B and the first message is an acknowledgement
\* of the last message A sent, then we're ready to advance to the next message
\* to send.
ASendNextMessage == /\ Len(BtoA) > 0
                    /\ AVar.seqBit = Head(BtoA)
                    /\ \E d \in Data : AVar' = [ value |-> d, seqBit |-> 1 - AVar.seqBit ]
                    /\ AtoB' = AtoB
                    /\ BtoA' = Tail(BtoA) \* Consume the ack from B
                    /\ UNCHANGED <<BVar>> \* Don't touch BVar

\* If there are messages from B and the first message is not an acknowledgement
\* of the last message A sent, then ignore it.
AIgnoreBadAck == /\ Len(BtoA) > 0
                 /\ AVar.seqBit # Head(BtoA)
                 /\ AVar' = AVar
                 /\ AtoB' = AtoB
                 /\ BtoA' = Tail(BtoA) \* Consume the bad message from B
                 /\ UNCHANGED <<BVar>> \* Don't touch BVar
                                    
\* At any time, A can retransmit what it previously sent
ARetransmit == /\ AVar' = AVar
               /\ AtoB' = Append(AtoB, AVar) \* Produce the new message to the channel to B
               /\ BtoA' = BtoA
               /\ UNCHANGED <<BVar>> \* Don't touch BVar

(*********************************************************************************)
(* B to A                                                                        *)
(* B can read/write BVar, consume the AtoB channel, and produce the BtoA channel *)
(*********************************************************************************)
\* If there are messages from A and the first message has a different sequence
\* number than our current message, it's new!  Consume and acknowledge it.
BAcknowledge == /\ Len(AtoB) > 0
                /\ BVar.seqBit # Head(AtoB).seqBit
                /\ BVar' = Head(AtoB) \* Remember the new message number
                /\ AtoB' = Tail(AtoB) \* Consume the message from A
                /\ BtoA' = BtoA \* Don't need to send a message to A to receive new data from A
                /\ UNCHANGED <<AVar>> \* Don't touch 

\* If there are messages from A and the first message has the same sequence
\* number as our current message, ignore it.
BIgnoreBadMsg == /\ Len(AtoB) > 0
                 /\ BVar.seqBit = Head(AtoB).seqBit
                 /\ BVar' = BVar
                 /\ AtoB' = Tail(AtoB) \* Consume the AtoB channel
                 /\ BtoA' = BtoA
                 /\ UNCHANGED <<AVar>>

\* At any time, B can retransmit what it previously sent
BRetransmit == /\ BVar' = BVar
               /\ AtoB' = AtoB
               /\ BtoA' = Append(BtoA, BVar.seqBit) \* Produce the BtoA channel
               /\ UNCHANGED <<AVar>>

(*************************************************************************)
(* Simulate loss by removing messages from AtoB while maintaining FIFO   *) 
(*************************************************************************)
DropAtoBMessage == /\ Len(AtoB) > 0
                   /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
                   /\ UNCHANGED <<AVar, BVar, BtoA>>

(*************************************************************************)
(* Simulate loss by removing messages from BtoA while maintaining FIFO   *) 
(*************************************************************************)
DropBtoAMessage == /\ Len(BtoA) > 0
                   /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
                   /\ UNCHANGED <<AVar, BVar, AtoB>>

Next == \/ ASendNextMessage
        \/ AIgnoreBadAck
        \/ ARetransmit
        \/ BAcknowledge
        \/ BIgnoreBadMsg
        \/ BRetransmit
        \/ DropAtoBMessage
        \/ DropBtoAMessage

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK

AB == INSTANCE ABSpec 

THEOREM Spec => AB!Spec

=============================================================================
\* Modification History
\* Last modified Wed Apr 06 16:33:55 PDT 2016 by jonro
\* Created Wed Apr 06 10:20:29 PDT 2016 by jonro
