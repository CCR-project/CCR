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

Require Import HTactics TODOYJ Invariant.

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

  Let FunStb: SkEnv.t -> gname -> option fspec :=
    fun skenv => to_stb (MainFunStb RecStb skenv).

  Let GlobalStb: SkEnv.t -> gname -> option fspec :=
    fun skenv => to_stb ((MainStb RecStb skenv) ++ (KnotStb RecStb FunStb skenv) ++ MemStb).

  Definition KnotAll0: ModL.t := Mod.add_list [KnotMain0.Main; Knot0.Knot; Mem0.Mem].

  Definition KnotAll1: ModL.t := Mod.add_list [KnotMain1.Main RecStb GlobalStb; Knot1.Knot RecStb FunStb GlobalStb; Mem1.Mem].

  Lemma KnotAll01_correct:
    refines KnotAll0 KnotAll1.
  Proof.
    eapply adequacy_local_list. econs; [|econs; [|econs; ss]].
    - eapply KnotMain01proof.correct with (RecStb0:=RecStb) (FunStb0:=FunStb) (GlobalStb0:=GlobalStb).
      + ii. ss. unfold FunStb, RecStb, GlobalStb, to_stb in *. ss.
        rewrite ! eq_rel_dec_correct in *. des_ifs.
      + ii. econs; ss. refl.
      + ii. econs; ss. refl.
    - eapply Knot01proof.correct with (RecStb0:=RecStb) (FunStb0:=FunStb) (GlobalStb0:=GlobalStb).
      + ii. ss.
      + ii. ss. unfold FunStb, RecStb, GlobalStb, to_stb in *. ss.
        rewrite ! eq_rel_dec_correct in *. des_ifs.
      + ii. ss. unfold FunStb, RecStb, GlobalStb, to_stb in *. ss.
        rewrite ! eq_rel_dec_correct in *. des_ifs; stb_tac; ss.
    - eapply Mem01proof.correct.
  Qed.

End PROOF.
