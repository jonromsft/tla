------------------------- MODULE TrafficManagement -------------------------
EXTENDS Integers, Sequences

(**************************************************************************)
(*  *)
(**************************************************************************)

CONSTANT Users,  \* The set of users in the system
         LDNS,   \* The LDNS for each user
         ADNS,   \* The authoritative DNS servers for the host
         Servers \* The set of servers capable of answering the request

=============================================================================
\* Modification History
\* Last modified Thu Apr 07 09:55:35 PDT 2016 by jonro
\* Created Thu Apr 07 08:56:33 PDT 2016 by jonro
