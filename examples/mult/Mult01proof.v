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

  Definition is_possibly_pure (fsp: fspec): Prop :=
    exists x mn varg_src varg_tgt d r, fsp.(precond) x mn varg_src varg_tgt d r ∧ is_pure d
  .

  Definition stb_pure_incl (stb_tgt stb_src: string -> option fspec): Prop :=
    forall fn fsp (FIND: stb_tgt fn = Some fsp) (PURE: is_possibly_pure fsp), stb_src fn = Some fsp
  .

  Local Transparent HoareCall.

  Lemma hAPC_both
        A mp_src0 mp_tgt0 (mr_src0 mr_tgt0: Σ)
        mn r rg
        k_src k_tgt
        _a a0 (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        o_new_src o_new_tgt
        o_src0 o_src1 o_tgt0 o_tgt1
        (FUELS: o_src0 = Ord_S_n o_src1 5)
        (FUELT: o_tgt0 = Ord_S_n o_tgt1 5)
        ctx0
        `{PreOrder _ le}

        (* (WF: mk_wf R a0 ((Any.pair mp_src0 mr_src0↑), (Any.pair mp_tgt0 mr_tgt0↑))) *)

        rx0
        (* ips Xtra *)
        (* (ACC: current_iPropL ctx0 ips) *)
        (* (ENTAIL: bi_entails (from_iPropL ips) ((OwnT mr_tgt0) ** (Xtra ∧ Exactly rx))) *)
        Xn Invtn Xtra
        (ACC: current_iPropL ctx0 [(Invtn, OwnT mr_tgt0); (Xn, (Xtra ∧ Exactly rx0)%I)])
        FR
        (ENTAIL: bi_entails Xtra (R a0 mp_src0 mp_tgt0 ** FR))
        (* (WFA: forall a1 mp_src1 mp_tgt1 (mr_src1 mr_tgt1: Σ) (INV: I mr_src1), *)
        (*     mk_wf R a1 ((Any.pair mp_src1 mr_src1↑), (Any.pair mp_tgt1 mr_tgt1↑))) *)


        (ARG: forall
            (mr_src1 mr_tgt1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
            (WLE: le a0 a1)
            ctx1 rx1
            (ACC: current_iPropL ctx1 [("INVT", OwnT mr_tgt1);
                                      ("X", ((R a1 mp_src1 mp_tgt1 ** FR) ∧ Exactly rx1)%I)]),
            gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_new_src o_new_tgt _a
                   (Any.pair mp_src1 mr_src1↑, k_src (ctx1, tt))
                   (Any.pair mp_tgt1 mr_tgt1↑, k_tgt (ctx1 ⋅ rx1, tt)))
        stb_src stb_tgt d
        (STBINCL: stb_pure_incl stb_tgt stb_src)
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr o_src0 o_tgt0 _a
             (Any.pair mp_src0 mr_src0↑, (interp_hCallE_tgt mn stb_src d APC ctx0) >>= k_src)
             (Any.pair mp_tgt0 mr_tgt0↑, (interp_hCallE_tgt mn stb_tgt d APC (ctx0 ⋅ rx0)) >>= k_tgt)
  .
  Proof.
    subst.
    unfold APC. steps. force_l. exists x. steps. force_l; ss. steps.

    (* Unset Printing Notations. *)
    instantiate (1:=5%ord). instantiate (1:=5%ord).
    clear_until x. gen x d ctx0 rx0. gen mp_src0 mp_tgt0 mr_src0 mr_tgt0. gen a0. gcofix CIH. i.
    {
      rewrite unfold_APC. ired_both.
      force_r. i. force_l. exists x0.
      destruct x0.
      - steps. eapply gpaco8_mon; et.
        { eapply ARG. { refl. } admit "". }
      -
        assert(T: exists rf_src rm_src, R a0 mp_src0 mp_tgt0 rm_src /\ FR rf_src /\ rx0 = rf_src ⋅ rm_src).
        { clear - ACC ENTAIL. uipropall.
          eapply current_iPropL_pop in ACC. des.
          eapply current_iPropL_pop in TL. des.
          eapply current_iPropL_nil in TL0. ss.
          des. r in HD1. uipropall. clarify.
          exploit ENTAIL; try apply HD0.
          { eapply wf_extends; et. exists (ctx0 ⋅ hdr). r_solve. }
          i; des. clarify. esplits; et.
          r_solve.
        }
        des. subst.

        steps. force_l. exists x0. steps. force_l; ss. steps. unfold HoareCall. unfold mput, mget. steps.
        des; ss.
        assert(STB: stb_src s = Some f).
        { eapply STBINCL; et. r. esplits; et. }
        force_l. eexists (_, _). steps. rewrite STB. steps. instantiate (1:=t).
        unfold HoareCall. unfold mput, mget. steps.

        force_l. rename c into mr_tgt1. rename c0 into ro. rename c1 into rf.
        exists (ro, rf ⋅ rf_src, rm_src ⋅ mr_tgt1). steps. force_l; ss.
        { r_wf _GUARANTEE1. }
        steps. force_l. esplits; et. steps. force_l. esplits; et. steps. force_l. esplits; et.
        steps. force_l; et. steps. force_l; ss. steps.
        { econs. eapply to_semantic. iIntros "[A B]". iFrame. iStopProof.
          uipropall. i. r in H0. des; clarify. esplits; et. r. uipropall.
        }

        inv WF. rewrite Any.pair_split in *. clarify. rewrite Any.upcast_downcast. steps.
        hexploit1 RSRC.
        { eapply wf_extends; et. r. exists (c ⋅ rf ⋅ rf_src ⋅ c0). r_solve. }
        rename c into ri. rename c0 into ctx1.
        r in RSRC. autounfold with iprop in RSRC; autorewrite with iprop in RSRC. des. clarify.
        rename a into rinv.
        force_r. exists (ri, ctx1 ⋅ (rinv ⋅ rf_src)). steps. force_r; ss.
        { eapply wf_extends; et.
          Local Transparent OwnT. r in RSRC1. uipropall. r in RSRC1. des; clarify.
          r. exists (ctx). r_solve. }
        steps. force_r. esplits. steps. force_r; et. steps.

        move CIH at bottom.
        gbase. eapply (CIH w1); et.
        { i. eapply ARG; try apply ACC0. etrans; et. }
        { iIntros "H". }
        instantiate (1:=5). instantiate (1:=5).
        eapply CIH; et.
        {
        steps.
        {
        steps.
          r.
          iIntros "H". TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT }
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

      unfold ccallU. steps. eapply hAPC_both; et. stb_tac; clarify. force_l; stb_tac; clarify. steps.
      harg_clo_tgt.



    }

  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
