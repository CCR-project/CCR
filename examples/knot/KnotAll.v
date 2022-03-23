Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import STB KnotHeader.
Require Import KnotMainImp KnotMain0 KnotMain1 KnotImp Knot0 Knot1 Mem0 Mem1.
Require Import KnotMainImp0proof KnotImp0proof KnotMain01proof Knot01proof Mem01proof.
Require Import ProofMode.

Require Import Invariant Weakening.

Set Implicit Arguments.




Section PROOF.

  Let Σ: GRA.t := GRA.of_list [invRA; knotRA; memRA].
  Local Existing Instance Σ.

  Let invRA_inG: @GRA.inG invRA Σ.
  Proof. exists 0. ss. Defined.
  Local Existing Instance invRA_inG.

  Let knotRA_inG: @GRA.inG knotRA Σ.
  Proof. exists 1. ss. Defined.
  Local Existing Instance knotRA_inG.

  Let memRA_inG: @GRA.inG memRA Σ.
  Proof. exists 2. ss. Defined.
  Local Existing Instance memRA_inG.

  Let RecStb: Sk.t -> gname -> option fspec :=
    fun sk => to_stb KnotRecStb.
  Hint Unfold RecStb: stb.

  Let FunStb: Sk.t -> gname -> option fspec :=
    fun sk => to_stb (MainFunStb RecStb sk).
  Hint Unfold FunStb: stb.

  Let smds := [SMain RecStb; SKnot RecStb FunStb; SMem (fun _ => true)].
  Let GlobalStb := fun sk => to_stb (SMod.get_stb smds sk).
  Hint Unfold GlobalStb: stb.

  Definition KnotAllImp: list Mod.t := [KnotMainImp.KnotMain; KnotImp.Knot; Mem0.Mem (fun _ => false)].
  Definition KnotAll0: list Mod.t := [KnotMain0.Main; Knot0.Knot; Mem0.Mem (fun _ => false)].
  Definition KnotAll1: list Mod.t := List.map (SMod.to_tgt GlobalStb) smds.
  Definition KnotAll2: list Mod.t := List.map SMod.to_src smds.

  Lemma KnotAll01_correct:
    refines2 KnotAll0 KnotAll1.
  Proof.
    eapply refines2_cons.
    { eapply KnotMain01proof.correct with (RecStb:=RecStb) (FunStb:=FunStb) (GlobalStb:=GlobalStb).
      { stb_incl_tac. }
      { ii. econs; ss. refl. }
      { ii. econs; ss. refl. }
    }
    eapply refines2_cons.
    { eapply Knot01proof.correct with (RecStb:=RecStb) (FunStb:=FunStb) (GlobalStb:=GlobalStb).
      + stb_incl_tac.
      + stb_incl_tac.
      + stb_incl_tac; ors_tac.
    }
    etrans.
    { eapply Mem01proof.correct. }
    { eapply Weakening.adequacy_weaken. ss. }
  Qed.

  Lemma KnotAll12_correct:
    refines_closed (Mod.add_list KnotAll1) (Mod.add_list KnotAll2).
  Proof.
    eapply adequacy_type.
    { instantiate (1:=GRA.embed inv_token ⋅ GRA.embed (Auth.white (Some None: Excl.t (option (nat -> nat))): knotRA)).
      g_wf_tac.
      { Local Transparent Sk.load_skenv _points_to string_dec.
        ur. unfold var_points_to, initial_mem_mr. ss. uo. split.
        2: { ur. i. ur. i. ur. des_ifs. }
        { repeat rewrite URA.unit_id. ur. eexists ε.
          repeat rewrite URA.unit_id. extensionality k. extensionality n.
          unfold sumbool_to_bool, andb. des_ifs.
          { ss. clarify. }
          { ss. clarify. exfalso. lia. }
          { repeat (destruct k; ss). }
        }
      }
      { unfold knot_full. ur. splits; auto.
        { rewrite URA.unit_id. refl. }
        { ur. ss. }
      }
      { ur. ss. }
    }
    { i. ss. clarify. ss. exists id. splits; auto.
      { iIntros "[H0 H1]". iFrame. iSplits; ss. }
      { i. iPureIntro. i. des; auto. }
    }
  Qed.

  Theorem Knot_correct:
    refines_closed (Mod.add_list KnotAllImp) (Mod.add_list KnotAll2).
  Proof.
    transitivity (Mod.add_list KnotAll0).
    { eapply refines_close. eapply refines2_pairwise. econs; simpl.
      { eapply KnotMainImp0proof.correct. }
      econs; simpl.
      { eapply KnotImp0proof.correct. }
      econs; ss.
    }
    etrans.
    { eapply refines_close. eapply KnotAll01_correct. }
    { eapply KnotAll12_correct. }
  Qed.

End PROOF.
