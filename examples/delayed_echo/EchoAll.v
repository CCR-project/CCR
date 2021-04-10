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
Require Import Mem1 Stack1 Echo2 EchoMain1 Client1.

Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.




Section AUX________REMOVEME_____REDUNDANT.

  Context `{Σ: GRA.t}.

  Definition refines_closed (md_tgt md_src: ModL.t): Prop :=
    Beh.of_program (ModL.compile md_tgt) <1= Beh.of_program (ModL.compile md_src)
  .

  Lemma refines_close: SimModSem.refines <2= refines_closed.
  Proof. ii. specialize (PR nil). ss. unfold Mod.add_list in *. ss. rewrite ! ModL.add_empty_l in PR. eauto. Qed.

  Definition add_list (ms: list ModL.t): ModL.t := fold_right ModL.add ModL.empty ms.

  Global Program Instance refines_closed_PreOrder: PreOrder refines_closed.
  Next Obligation. ii; ss. Qed.
  Next Obligation. ii; ss. r in H. r in H0. eauto. Qed.

End AUX________REMOVEME_____REDUNDANT.





Section ECHO.

  Definition Σ: GRA.t := GRA.of_list [Mem1.memRA; Echo1.echoRA].
  Local Existing Instance Σ.

  Let memRA_inG: @GRA.inG Mem1.memRA Σ.
  Proof.
    exists 0. ss.
  Qed.
  Local Existing Instance memRA_inG.

  Let echoRA_inG: @GRA.inG Echo1.echoRA Σ.
  Proof.
    exists 1. ss.
  Qed.
  Local Existing Instance echoRA_inG.

  Definition echo_spec: ModL.t :=
    add_list [
        md_src Mem MemSbtb ; (* Mem *)
        md_src Main MainSbtb ; (* Main *)
        md_src Stack StackSbtb ; (* Stack *)
        md_src Echo EchoSbtb ; (* Echo *)
        md_src Client ClientSbtb (* Client *)
      ].

End ECHO.

Definition echo_prog := ModSemL.initial_itr_no_check (ModL.enclose echo_spec).
