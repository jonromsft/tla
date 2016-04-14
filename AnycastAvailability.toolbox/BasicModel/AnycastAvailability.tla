------------------------ MODULE AnycastAvailability ------------------------
EXTENDS Integers, Sequences

(**************************************************************************)
(* Environments:  The full set of environments.  If any environment is    *)
(*                announcing the VIP, the VIP is available.               *)
(*                                                                        *)
(* MachinesPerEnvironment:  A function from environment to machine count  *)
(*                          in that environment.  If more than 50% of the *)
(*                          machines in an environment fail, the          *)
(*                          environment stops announcing the VIP.         *)
(**************************************************************************)
CONSTANT Environments,
         MachinesPerEnvironment
         
(**************************************************************************)
(* healthyMachinesPerEnvironment:  A function from environment to the     *)
(*                                 count of healthy machines in that      *)
(*                                 environment.                           *)
(**************************************************************************)
VARIABLE healthyMachinesPerEnvironment

(**************************************************************************)
(* All environments have more than 0 machines in them                     *)
(* The domain of MachinesPerEnvironment is exactly Environments           *)
(**************************************************************************)
ASSUME /\ \A e \in Environments : MachinesPerEnvironment[e] > 0
       /\ DOMAIN MachinesPerEnvironment = Environments
       
vars == <<healthyMachinesPerEnvironment>>

(**************************************************************************)
(* Everything starts out healthy                                          *)
(**************************************************************************)
Init == healthyMachinesPerEnvironment = MachinesPerEnvironment

(**************************************************************************)
(* All healthyEnvironments must be Environments                           *)
(* Exactly the set of environments are being tracked for machine health   *)
(* All environments must have a healthy machine count between 0 and the   *)
(*     machine count for that environment                                 *)
(**************************************************************************)
TypeOK == /\ DOMAIN healthyMachinesPerEnvironment = Environments
          /\ \A e \in Environments : healthyMachinesPerEnvironment[e] \in 0..MachinesPerEnvironment[e]

(**************************************************************************)
(* An environment is healthy when at least half of the machines in it are *)
(* healthy.                                                               *)
(**************************************************************************)
EnvironmentIsHealthy(e) == healthyMachinesPerEnvironment[e] > MachinesPerEnvironment[e] \div 2

(**************************************************************************)
(* The VIP is available when any environment is healthy                   *)
(**************************************************************************)
VIPAvailable == \E e \in Environments : EnvironmentIsHealthy(e)

(**************************************************************************)
(* Hardware can fail at any time, but once we lose 3 machines, we start   *)
(* repairing them.  When an environment is repaired, all machines are     *)
(* repaired.                                                              *)
(**************************************************************************)
MachineHardwareFailure == \E e \in Environments : /\ EnvironmentIsHealthy(e)
                                                  /\ healthyMachinesPerEnvironment' = [healthyMachinesPerEnvironment EXCEPT ![e] = healthyMachinesPerEnvironment[e] - 1] 

MachineHardwareRepair == \E e \in Environments : /\ healthyMachinesPerEnvironment[e] < MachinesPerEnvironment[e]
                                                 /\ healthyMachinesPerEnvironment' = [healthyMachinesPerEnvironment EXCEPT ![e] = MachinesPerEnvironment[e]]

Next == \/ MachineHardwareFailure
        \/ MachineHardwareRepair

Spec == Init /\ [][Next]_vars /\ WF_vars(MachineHardwareRepair)

=============================================================================
\* Modification History
\* Last modified Sat Apr 09 17:42:59 PDT 2016 by jonro
\* Created Sat Apr 09 14:07:29 PDT 2016 by jonro
