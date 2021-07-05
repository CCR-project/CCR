Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import STB KnotHeader SimModSem.
Require Import KnotMain0 KnotMain1 Knot0 Knot1 Mem0 Mem1.
Require Import KnotMain01proof Knot01proof Mem01proof.

Require Import HTactics Invariant.

Set Implicit Arguments.




Section PROOF.

  Let Σ: GRA.t := GRA.of_list [invRA; knotRA; memRA].
  Local Existing Instance Σ.

  Let invRA_inG: @GRA.inG invRA Σ.
  Proof.
    exists 0. ss.
  Qed.
  Local Existing Instance invRA_inG.

  Let knotRA_inG: @GRA.inG knotRA Σ.
  Proof.
    exists 1. ss.
  Qed.
  Local Existing Instance knotRA_inG.

  Let memRA_inG: @GRA.inG memRA Σ.
  Proof.
    exists 2. ss.
  Qed.
  Local Existing Instance memRA_inG.

  Let RecStb: SkEnv.t -> gname -> option fspec :=
    fun skenv => to_stb KnotRecStb.
  Hint Unfold RecStb: stb.

  Let FunStb: SkEnv.t -> gname -> option fspec :=
    fun skenv => to_stb (MainFunStb RecStb skenv).
  Hint Unfold RecStb: stb.

  Let smds := [SMain RecStb; SKnot RecStb FunStb; SMem].

  Let stb

  Definition KnotAll0: list Mod.t := [KnotMain0.Main; Knot0.Knot; Mem0.Mem].

  Definition KnotAll1: list Mod.t := List.map (SMod.to_tgt GlobalStb) smds.

[SMain RecStb; SKnot RecStb FunStb; SMem].

  Definition KnotAll2: list Mod.t :=
    List.map SMod.to_src [SMain RecStb; SKnot RecStb FunStb; SMem].


  Let stb := fun skenv =>

  Let GlobalStb: SkEnv.t -> gname -> option fspec :=
    fun skenv => to_stb ((MainStb RecStb skenv) ++ (KnotStb RecStb FunStb skenv) ++ MemStb).
  Hint Unfold RecStb: stb.

  Definition KnotAll0: list Mod.t := [KnotMain0.Main; Knot0.Knot; Mem0.Mem].

  Definition KnotAll1: list Mod.t :=
    List.map (SMod.to_tgt GlobalStb) [SMain RecStb; SKnot RecStb FunStb; SMem].

  Definition KnotAll2: list Mod.t :=
    List.map SMod.to_src [SMain RecStb; SKnot RecStb FunStb; SMem].

  Ltac stb_incl_tac :=
    i; eapply incl_to_stb;
    [ autounfold with stb; autorewrite with stb; ii; ss; des; clarify; auto|
      autounfold with stb; autorewrite with stb; repeat econs; ii; ss; des; ss].

  Ltac ors_tac := repeat ((try by (ss; left; ss)); right).

  Lemma KnotAll01_correct:
    refines2 KnotAll0 KnotAll1.
  Proof.
    cbn. eapply refines2_pairwise. econs; [|econs; [|econs; ss]].
    - eapply adequacy_local2.
      eapply KnotMain01proof.correct with (RecStb0:=RecStb) (FunStb0:=FunStb) (GlobalStb0:=GlobalStb).
      + stb_incl_tac.
      + ii. econs; ss. refl.
      + ii. econs; ss. refl.
    - eapply adequacy_local2.
      eapply Knot01proof.correct with (RecStb0:=RecStb) (FunStb0:=FunStb) (GlobalStb0:=GlobalStb).
      + stb_incl_tac.
      + stb_incl_tac.
      + stb_incl_tac; ors_tac.
    - etrans.
      { eapply adequacy_local2. eapply Mem01proof.correct. }
      { eapply adequacy_local2. eapply Weakening.adequacy_weaken. ss. }
  Qed.

  Lemma KnotAll12_correct:
    refines_closed (Mod.add_list KnotAll1) (Mod.add_list KnotAll2).
  Proof.
    eapply adequacy_type.
    {


with (stb:=fun _ => GlobalStb); et.



  Lemma Knot_correct:
    refines_closed KnotAll0 KnotAll1.
  Proof.
    eapply adequacy_local_list. econs; [|econs; [|econs; ss]].
    - eapply KnotMain01proof.correct with (RecStb0:=RecStb) (FunStb0:=FunStb) (GlobalStb0:=GlobalStb).
      + stb_incl_tac.
      + ii. econs; ss. refl.
      + ii. econs; ss. refl.
    - eapply Knot01proof.correct with (RecStb0:=RecStb) (FunStb0:=FunStb) (GlobalStb0:=GlobalStb).
      + stb_incl_tac.
      + stb_incl_tac.
      + stb_incl_tac; ors_tac.
    - eapply Mem01proof.correct.
  Qed.


End PROOF.
