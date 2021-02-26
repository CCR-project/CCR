Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import MutHeader SimModSem.
Require Import Mem2 LinkedList1 Echo2 EchoMain1 Client1.

Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.


Section PROOF.

  Definition Σ: GRA.t := GRA.of_list [Mem1.memRA; URA.auth (RA.excl (list Z))].
  Local Existing Instance Σ.

  Let memRA_inG: @GRA.inG Mem1.memRA Σ.
  Proof.
    exists 0. ss.
  Qed.
  Local Existing Instance memRA_inG.

  Let echoRA_inG: @GRA.inG (URA.auth (RA.excl (list Z))) Σ.
  Proof.
    exists 1. ss.
  Qed.
  Local Existing Instance echoRA_inG.

  Definition echo_mod: Mod.t :=
    Mod.add_list [
        md_src Mem MemSbtb ; (* Mem *)
        md_src Main MainSbtb ; (* Main *)
        md_src LinkedList LinkedListSbtb ; (* LinkedList *)
        md_src Echo EchoSbtb ; (* Echo *)
        md_src Client ClientSbtb (* Client *)
      ].

End PROOF.

Definition echo_prog := ModSem.initial_itr_no_check (Mod.enclose echo_mod).
