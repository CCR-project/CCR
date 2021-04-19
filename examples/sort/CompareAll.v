Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import CompareHeader SimModSemL.
Require Import CompareMain0 CompareMain1 Wrap0 Wrap1.
Require Import CompareMain01proof Wrap01proof.

Require Import HTactics.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.




Section AUX.

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

End AUX.

Section PROOF.

  Let Σ: GRA.t := fun _ => of_RA.t RA.empty.
  Local Existing Instance Σ.

  Let CmpsStb: SkEnv.t -> list (gname * fspec) :=
    fun skenv => MainCmpsStb.

  Let GlobalStb: SkEnv.t -> list (gname * fspec) :=
    fun skenv => (MainStb) ++ (WrapStb CmpsStb skenv).

  Definition CompareAll0: ModL.t := Mod.add_list [CompareMain0.Main ; Wrap0.Wrap].

  Definition CompareAll1: ModL.t := Mod.add_list [CompareMain1.Main GlobalStb ; Wrap1.Wrap CmpsStb GlobalStb].

  Lemma CompareAll01_correct:
    SimModSem.refines CompareAll0 CompareAll1.
  Proof.
    eapply SimModSem.adequacy_local_list. econs; [|econs; [|econs; ss]].
    - eapply CompareMain01proof.correct with (CmpsStb0:=CmpsStb) (GlobalStb0:=GlobalStb).
      + i. ss.
      + i. ss.
    - eapply Wrap01proof.correct.
      + i. ss. unfold sumbool_to_bool in *. des_ifs.
  Qed.

  (* TODO: Define CompareAll2 adn prove ComapreAll12_correct *)

End PROOF.
