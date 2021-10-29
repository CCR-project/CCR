Require Import HoareDef MultHeader Mult0 Mult1 SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import STB ProofMode.
Require Import HTactics2.

Set Implicit Arguments.

Local Open Scope nat_scope.




Section PROOF.

  Context `{Σ: GRA.t}.

  Local Transparent APC.

  Lemma hAPC_both
        A mp_src0 mp_tgt0 (mr_src0 mr_tgt0: Σ)
        mn r rg
        k_src k_tgt
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        o_src0 o_src1 o_tgt0 o_tgt1
        (FUELS: o_src0 = Ord_S_n o_src1 5)
        (FUELT: o_tgt0 = Ord_S_n o_tgt1 5)
        ctx0


        rx
        (* ips Xtra *)
        (* (ACC: current_iPropL ctx0 ips) *)
        (* (ENTAIL: bi_entails (from_iPropL ips) ((OwnT mr_tgt0) ** (Xtra ∧ Exactly rx))) *)
        Xn Invtn Xtra
        (ACC: current_iPropL ctx0 [(Invtn, OwnT mr_tgt0); (Xn, (Xtra ∧ Exactly rx)%I)])
        (* (ARG: forall *)
        (*     rx *)
        (*     (ACC: current_iPropL ctx0 [(Invtn, OwnT mr_tgt0); (Xn, (Xtra ∧ Exactly rx)%I)]), *)
        (*     gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_src1 o_tgt1 a *)
        (*            (mpr_src, k_src) *)
        (*            (Any.pair mp_tgt0 mr_tgt0↑, k_tgt (ctx0 ⋅ rx, vret_src))) *)
        stb d_tgt d_src
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr o_src0 o_tgt0 a
             (Any.pair mp_src0 mr_src0↑, (interp_hCallE_tgt mn stb d_src APC ctx0) >>= k_src)
             (Any.pair mp_tgt0 mr_tgt0↑, (interp_hCallE_tgt mn stb d_tgt APC (ctx0 ⋅ rx)) >>= k_tgt)
  .
  Proof.
    subst.
    unfold APC. steps. force_l. exists x. steps. force_l; ss. steps.

    {
      rewrite unfold_APC. steps. force_l. exists x0. steps.
      destruct x0.
      - steps. admit "".
      - steps. force_l. exists x0. steps. force_l; ss. steps. force_l. eexists (_, _). steps.
        rewrite _UNWRAPN. steps. instantiate (1:=t).
        Local Transparent HoareCall. unfold HoareCall. unfold mput, mget. steps.
        force_l. exists (c0, c, c1). steps. force_l; ss.
        { eapply wf_extends; et. exists rx. r_solve. }
        steps. force_l. esplits; et. steps. force_l. esplits; et. steps. force_l. esplits; et.
        steps. force_l; et. steps. force_l; ss. { des. esplits; et. admit "ez". } steps.
        { TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT }
        (* hcall _ _ _. *)
        (* { iIntros "[A [B _]]". iFrame. } *)
        (* { iModIntro. iSplitR "P"; et. *)
        (*   admit "". *)
        (*   instantiate (1:=x_tgt). *)
        (*   instantiate (1:=o_tgt). *)
    }

    eapply current_iPropL_entail_all with (Hn:="A") in ACC; et.
    mDesAll.
    mAssert _ with "A1". { iAssumption. }
    mAssert _ with "A2". { iAssumption. }
    mAssert _ with "A3". { iAssumption. }
    mAssert _ with "A". { iAssumption. }
    eapply hpost_clo_tgt; et.
  Unshelve. all: try exact 0.
  Qed.

End PROOF.




Section SIMMODSEM.

  Context `{@GRA.inG fRA Σ}.
  Context `{@GRA.inG gRA Σ}.
  Context `{@GRA.inG hRA Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (fun _ _ st_tgt => ⌜True⌝%I)
  .

  Theorem correct: refines2 [Mult0.Mult (fun _ => to_stb GlobalStb0)] [Mult1.Mult (fun _ => to_stb GlobalStb1)].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    { esplits. econs; ss. eapply to_semantic. iIntros "H". iSplits; ss. }

    econs; [|ss].

    {
      (*** init ***)
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)



      harg. mDesAll; clarify. steps.
      harg_tgt.
      { iFrame. iSplits; et. instantiate (1:=True%I); ss. }

      steps.


      hret _; ss.
      { iDestruct "Q" as "[[A B] %]". iModIntro. iFrame. iSplits; et. }
      { iDestruct "Q" as "[_ %]". clarify. iPureIntro. r. esplits; et. }
    }

    econs; [|ss].
    {
      (*** init ***)
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)



      harg. mDesAll; clarify. steps.
      mAssert _ with "PRE" as "PRE".
      { iApply (OwnM_Upd with "PRE"). eapply f01_update. }
      mUpd "PRE".

      harg_tgt.
      { iFrame. iSplits; et. iAssumption. }

      unfold ccallU. steps. stb_tac; clarify. force_l; stb_tac; clarify. steps.


      hcall _ _ _.
      { iModIntro. iDestruct "P" as "[[A %] %]". clarify. iFrame. iSplits; ss; et. iAssumption. }
      { esplits; ss; et. }
      { i. iIntros "H". ss. iDestruct "H" as "[A %]". eauto. }
      mDesAll. clarify. steps. force_l; stb_tac; ss; clarify. steps.



      hpost_tgt.
      { iFrame. iSplits; et. iAssumption. }
      steps. rewrite _UNWRAPU. steps. stb_tac. clarify.



      hcall _ _ _.
      { iModIntro. iDestruct "P" as "[% %]". clarify. iFrame. iSplits; ss; et. instantiate (1:=True%I). ss. }
      { esplits; ss; et. }
      { i. iIntros "H". ss. iDestruct "H" as "[A %]". eauto. }
      clear_fast. mDesAll. clarify. steps.



      hpost_tgt.
      { iFrame. iSplits; et. iAssumption. } 
      steps. rewrite _UNWRAPU0. steps.


      hret _; ss.
      { iDestruct "Q" as "[[A B] %]". iPoseProof (OwnM_Upd with "A") as "A".
        { eapply f23_update. }
        iMod "A". iModIntro. iSplits; ss; et. iFrame. }
      { iDestruct "Q" as "[_ %]". iPureIntro. clarify. r. esplits; et. }
    }

    econs; [|ss].
    {
      (*** init ***)
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)




      harg. mDesAll; clarify. steps.
      harg_tgt.
      { iFrame. iSplits; et. instantiate (1:=True%I). ss. }

      unfold ccallU. steps. stb_tac; clarify. force_l; stb_tac; clarify. steps.
      harg_clo_tgt.



    }

  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
