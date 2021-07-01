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
Require Import OpenDef.
(* Require Import Mem1 Stack1 Echo2 EchoMain1 Client1. *)
Require Import Mem0 NewStack0 NewEcho0 NewEchoMain0 NewClient0.

Require Import TODOYJ.

Set Implicit Arguments.







Section ECHOIMPL.

  Let Σ: GRA.t := GRA.of_list [].
  Local Existing Instance Σ.

  Definition echo_impl: ModL.t :=
    Mod.add_list [Mem; Main; Stack; Echo; Client].

End ECHOIMPL.

Definition echo_impl_itr := ModSemL.initial_itr (ModL.enclose echo_impl) None.





Require Import MemOpen NewStack3A NewEcho1 NewEchoMain0 NewClient0.

Section ECHOSPEC.

  Let Σ: GRA.t := GRA.of_list [Mem1.memRA; stkRA].
  Local Existing Instance Σ.

  Let memRA_inG: @GRA.inG Mem1.memRA Σ.
  Proof.
    exists 0. ss.
  Qed.
  Local Existing Instance memRA_inG.

  Let stkRA_inG: @GRA.inG stkRA Σ.
  Proof.
    exists 1. ss.
  Qed.
  Local Existing Instance stkRA_inG.

  Let frds: list string := ["Mem"; "Stack"; "Echo"].
  Definition echo_spec: ModL.t :=
    Mod.add_list [
      Mem0.Mem;
      (KMod.transl_src (fun _ => frds) KStack);
      (KMod.transl_src (fun _ => frds) KEcho);
      Main;
      Client
      ].

End ECHOSPEC.

Definition echo_spec_itr := ModSemL.initial_itr (ModL.enclose echo_spec) None.






Require Import Mem0 NewStackImp NewEchoImp NewEchoMainImp NewClientImp.

Section ECHOIMP.

  Let Σ: GRA.t := GRA.of_list [].
  Local Existing Instance Σ.

  Definition echo_imp: ModL.t :=
    Mod.add_list [Mem; EchoMain; Stack; Echo; Client].

End ECHOIMP.

Definition echo_imp_itr := ModSemL.initial_itr (ModL.enclose echo_imp) None.
