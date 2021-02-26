Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import MutHeader SimModSem.
Require Import Mem2 LinkedList1 Echo1 EchoMain Client.

Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Definition Σ: GRA.t := GRA.of_list [Mem1.memRA].
  Local Existing Instance Σ.

  Let memRA_inG: @GRA.inG Mem1.memRA Σ.
  Proof.
    exists 0. ss.
  Qed.
  Local Existing Instance memRA_inG.

  Definition echo: Mod.t := {|
    Mod.get_modsem := fun _ => {|
        ModSem.fnsems := List.map (fun '(fn, sb) => (fn, fun_to_src sb.(fsb_body))) (MainSbtb ++ MemSbtb ++ LinkedListSbtb ++ EchoSbtb ++ ClientSbtb);
        ModSem.initial_mrs := [("Main", (ε, tt↑)) ; ("Mem", (ε, tt↑)) ; ("LinkedList", (ε, tt↑)) ; ("Echo", (ε, ([]: list Z)↑)) ; ("Client", (ε, tt↑))];
      |};
    Mod.sk := Sk.unit;
  |}
  .

End PROOF.

Definition echo_prog := ModSem.initial_itr_no_check (Mod.enclose echo).
