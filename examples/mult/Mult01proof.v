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
Require Import HTactics.

Set Implicit Arguments.

Local Open Scope nat_scope.


(* Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 '------------------------------------------------------------------' src2 tgt2" *)
(*   := *)
(*     (gpaco8 (_sim_itree wf _) _ _ _ _ _ _ _ _ n ((Any.pair src0 src1), src2) ((Any.pair tgt0 _), tgt2)) *)
(*       (at level 60, *)
(*        format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' "). *)



Section MODE.

  Context `{Σ: GRA.t}.

  Variant mk_wf (A: Type)
          (R: A -> Any.t -> Any.t -> iProp)
    : A -> Any.t * Any.t -> Prop :=
  | mk_wf_intro
      a
      mr_src mr_tgt mp_src mp_tgt
      (RSRC: URA.wf mr_src -> (R a mp_src mp_tgt ** Own mr_tgt) mr_src)
    :
      mk_wf R a ((Any.pair mp_src mr_src↑), (Any.pair mp_tgt mr_tgt↑))
  .

  Local Transparent HoareFun HoareFunArg HoareFunRet HoareCall.

  (* Lemma own_rewrite *)
  (*       r (P: iProp) *)
  (*       (HOLDS: P r) *)
  (*   : *)
  (*     bi_entails (Own r) P *)
  (* . *)
  (* Proof. *)
  (*   uipropall.  i. et. *)
  (* Qed. *)

  (* Lemma harg_clo *)
  (*       A Rn Invsn Invtn *)
  (*       mn r rg *)
  (*       X (P: option mname -> X -> Any.t -> Any.t -> ord -> Σ -> Prop) varg *)
  (*       mpr_src mp_tgt mr_tgt f_tgt k_src *)
  (*       a (le: A -> A -> Prop) *)
  (*       (R: A -> Any.t -> Any.t -> iProp) *)
  (*       (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop) *)
  (*       (WF: mk_wf R a (mpr_src, (Any.pair mp_tgt mr_tgt↑))) *)
  (*       o_src0 o_src1 o_tgt0 o_tgt1 *)
  (*       (FUEL: o_tgt0 = Ord_S_n o_tgt1 7) *)
  (*       (ARG: *)
  (*          forall x varg_src ord_cur *)
  (*                 ctx (mr_src: Σ) mp_src *)
  (*                 (ACC: current_iPropL ctx [(Rn, P mn x varg_src varg ord_cur); *)
  (*                                          (Invsn, R a mp_src mp_tgt); *)
  (*                                          (Invtn, Own mr_tgt)]), *)
  (*            gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_src1 o_tgt1 a *)
  (*                   (Any.pair mp_src mr_src↑, k_src (ctx, ((mn, x), varg_src, ord_cur))) *)
  (*                   ((Any.pair mp_tgt mr_tgt↑), f_tgt)) *)
  (*   : *)
  (*     gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr o_src0 o_tgt0 a *)
  (*            (mpr_src, (HoareFunArg P (mn, varg) >>= k_src)) *)
  (*            ((Any.pair mp_tgt mr_tgt↑), f_tgt) *)
  (* . *)
  (* Proof. *)
  (*   inv WF. *)
  (*   unfold HoareFunArg, mput, mget, assume, guarantee. *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). intro x. *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). intro varg_src. *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). intros (rarg_src, ctx). *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). intro VALID. *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). intro ord_cur. *)
  (*   repeat (ired_both; gstep; econs; eauto with ord_step2). i. *)
  (*   eapply Any.pair_inj in H2. des; clarify. eapply Any.upcast_inj in H0. des; clarify. *)
  (*   ired_both. eapply ARG; et. *)
  (*   red. econs. *)
  (*   { instantiate (1:=rarg_src ⋅ mr_src). r_wf VALID. } *)
  (*   { ss. red. rr. *)
  (*     autorewrite with iprop; ss. esplits; et. *)
  (*     assert(T: URA.wf mr_src). *)
  (*     { eapply URA.wf_mon. instantiate (1:=(ctx ⋅ rarg_src)). r_wf VALID. } *)
  (*     spc RSRC. *)
  (*     clear - RSRC T VALID. *)
  (*     uipropall. des. clarify. esplits; et. *)
  (*     { rewrite URA.unit_id; ss. } *)
  (*     { r. uipropall. } *)
  (*   } *)
  (*   Unshelve. all: try exact 0. *)
  (* Qed. *)

  Definition OwnInvT := Own.

  Lemma harg_clo
        A Rn Invsn Invtn
        mn r rg
        X (P: option mname -> X -> Any.t -> Any.t -> ord -> Σ -> Prop) varg
        mp_src mp_tgt (mr_src mr_tgt: Σ) f_tgt k_src
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (WF: mk_wf R a ((Any.pair mp_src mr_src↑), (Any.pair mp_tgt mr_tgt↑)))
        o_src0 o_src1 o_tgt0 o_tgt1
        (FUEL: o_tgt0 = Ord_S_n o_tgt1 7)
        (ARG:
           forall x varg_src ord_cur ctx
                  (ACC: current_iPropL ctx [(Rn, P mn x varg_src varg ord_cur);
                                           (Invsn, R a mp_src mp_tgt);
                                           (Invtn, OwnInvT mr_tgt)]),
             gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_src1 o_tgt1 a
                    (Any.pair mp_src mr_src↑, k_src (ctx, ((mn, x), varg_src, ord_cur)))
                    (Any.pair mp_tgt mr_tgt↑, f_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr o_src0 o_tgt0 a
             ((Any.pair mp_src mr_src↑), (HoareFunArg P (mn, varg) >>= k_src))
             ((Any.pair mp_tgt mr_tgt↑), f_tgt)
  .
  Proof.
    inv WF.
    unfold HoareFunArg, mput, mget, assume, guarantee.
    repeat (ired_both; gstep; econs; eauto with ord_step2). intro x.
    repeat (ired_both; gstep; econs; eauto with ord_step2). intro varg_src.
    repeat (ired_both; gstep; econs; eauto with ord_step2). intros (rarg_src, ctx).
    repeat (ired_both; gstep; econs; eauto with ord_step2).
    repeat (ired_both; gstep; econs; eauto with ord_step2). intro VALID.
    repeat (ired_both; gstep; econs; eauto with ord_step2). intro ord_cur.
    repeat (ired_both; gstep; econs; eauto with ord_step2). i.
    eapply Any.pair_inj in H2. des; clarify. eapply Any.upcast_inj in H0. des; clarify.
    eapply Any.pair_inj in H1. des; clarify. eapply Any.upcast_inj in H0. des; clarify.
    ired_both. eapply ARG; et.
    red. econs.
    { instantiate (1:=rarg_src ⋅ mr_src). r_wf VALID. }
    { ss. red. rr.
      autorewrite with iprop; ss. esplits; et.
      assert(T: URA.wf mr_src).
      { eapply URA.wf_mon. instantiate (1:=(ctx ⋅ rarg_src)). r_wf VALID. }
      spc RSRC.
      clear - RSRC T VALID. unfold OwnInvT.
      uipropall. des. clarify. esplits; et.
      { rewrite URA.unit_id; ss. }
      { r. uipropall. }
    }
    Unshelve. all: try exact 0.
  Qed.

  Lemma current_iPropL_pop
        ctx hd tl
        (P: current_iPropL ctx (hd :: tl))
    :
      exists hdr, <<TL: current_iPropL (ctx ⋅ hdr) tl>> ∧ <<HD: hd.2 hdr>>
  .
  Proof.
    rr in P. inv P. destruct hd. ss. unfold from_iPropL in IPROP. fold from_iPropL in IPROP.
    rr in IPROP. rewrite Seal.sealing_eq in *. des. subst. esplits; et.
    rr. econs; et. rewrite URA.add_assoc. rewrite URA.add_comm. rewrite URA.add_assoc. ss.
  Qed.

  Lemma current_iPropL_push
        ctx hdr
        (hd : string * iProp) tl
        (TL: current_iPropL (ctx ⋅ hdr) tl)
        (HD: hd.2 hdr)
    :
        <<P: current_iPropL ctx (hd :: tl)>>
  .
  Proof.
    unfold current_iPropL in *. destruct hd; ss. unfold from_iPropL; fold from_iPropL.
    inv TL.
    econs; et.
    { instantiate (1:=r ⋅ hdr). erewrite f_equal; et. rewrite <- ! URA.add_assoc. f_equal.
      rewrite URA.add_comm. ss. }
    uipropall. esplits; try eassumption. rewrite URA.add_comm. refl.
  Qed.

  Lemma current_iPropL_nil
        ctx
    :
      current_iPropL ctx [] <-> URA.wf ctx
  .
  Proof.
    split; i.
    - rr in H. inv H. rewrite URA.add_comm in GWF. eapply URA.wf_mon; et.
    - rr. unfold from_iPropL. econs; et. { rewrite URA.unit_idl; ss. } r; uipropall.
  Qed.

  Definition Exactly (r0: Σ): iProp' :=
    Seal.sealing
      "iProp"
      (fun r1 => r0 = r1).

  Hint Unfold Exactly: iprop.

  Lemma Exactly_spec
        r0 r1
    :
      Exactly r0 r1 <-> r0 = r1
  .
  Proof. unfold Exactly. uipropall. Qed.

  Lemma harg_clo_tgt
        A Xn Xtra Rn Invtn mp_tgt mr_tgt
        mn r rg
        X (P: option mname -> X -> Any.t -> Any.t -> ord -> Σ -> Prop) varg
        mpr_src f_src k_tgt
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (WF: mk_wf R a (mpr_src, Any.pair mp_tgt mr_tgt↑))
        o_src0 o_src1 o_tgt0 o_tgt1
        (FUEL: o_src0 = Ord_S_n o_src1 7)
        ctx x varg_tgt ord_cur
        (ACC: current_iPropL ctx [(Rn, P mn x varg_tgt varg ord_cur); (Invtn, OwnInvT mr_tgt); (Xn, Xtra)])
        (ARG: forall
            rx
            (ACC: current_iPropL ctx [(Rn, P mn x varg_tgt varg ord_cur);
                                     (Invtn, OwnInvT mr_tgt);
                                     (Xn, (Xtra ∧ Exactly rx)%I)]),
            gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_src1 o_tgt1 a
                   (mpr_src, f_src)
                   (Any.pair mp_tgt mr_tgt↑, k_tgt (ctx ⋅ rx, ((mn, x), varg_tgt, ord_cur))))
        (* (ARG: *)
        (*    exists x varg_tgt ord_cur *)
        (*           ctx (mr_src: Σ) mp_src mr_tgt mp_tgt *)
        (*           (ACC: current_iPropL ctx [(Rn, P mn x varg_tgt varg ord_cur); *)
        (*                                    (Invsn, R a mp_src mp_tgt); *)
        (*                                    (Invtn, Own mr_tgt)]) *)
        (*    , *)
        (*      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr o_src1 o_tgt1 a *)
        (*             (Any.pair mp_tgt mr_tgt↑, f_src) *)
        (*             (Any.pair mp_src mr_src↑, k_tgt (ctx, ((mn, x), varg_tgt, ord_cur)))) *)
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr o_src0 o_tgt0 a
             (mpr_src, f_src)
             (Any.pair mp_tgt mr_tgt↑, (HoareFunArg P (mn, varg) >>= k_tgt))
  .
  Proof.
    inv WF.
    unfold HoareFunArg, mput, mget, assume, guarantee. des.
    repeat (ired_both; gstep; econs; eauto with ord_step2). exists x.
    repeat (ired_both; gstep; econs; eauto with ord_step2). exists varg_tgt.
    eapply current_iPropL_pop in ACC. des.
    eapply current_iPropL_pop in TL. des.
    eapply current_iPropL_pop in TL0. des. ss. clear_fast.
    eapply current_iPropL_nil in TL. rename hdr into rarg_src. rename hdr0 into rinv. rename hdr1 into rx.
    apply Any.pair_inj in H2. des; clarify. apply Any.upcast_inj in H0. des; clarify.
    repeat (ired_both; gstep; econs; eauto with ord_step2). exists (rarg_src, (ctx ⋅ rx)).
    repeat (ired_both; gstep; econs; eauto with ord_step2). esplits.
    { clear - TL HD0. rr in HD0. uipropall. rr in HD0. des; clarify. rewrite URA.add_assoc in *.
      eapply URA.wf_mon with ctx0. erewrite f_equal; et.
      rewrite (URA.add_comm rarg_src). rewrite <- ! URA.add_assoc. do 2 f_equal. rewrite ! URA.add_assoc.
      rewrite (URA.add_comm rx). rewrite <- ! URA.add_assoc. f_equal. rewrite URA.add_comm. ss. }
    repeat (ired_both; gstep; econs; eauto with ord_step2). exists ord_cur.
    repeat (ired_both; gstep; econs; eauto with ord_step2). eexists; et.
    ired_both. eapply ARG.
    eapply current_iPropL_push; et.
    eapply current_iPropL_push; et.
    eapply current_iPropL_push; et.
    2: { instantiate (1:=rx). cbn. uipropall. }
    eapply current_iPropL_nil; et.
  Unshelve. all: try exact 0.
  Qed.

  Lemma wf_extends
        (x0 x1: Σ)
        (WF: URA.wf x0)
        (EXT: URA.extends x1 x0)
    :
      <<WF: URA.wf x1>>
  .
  Proof. r in EXT. des; clarify. eapply URA.wf_mon; et. Qed.

  Lemma hret_clo_both
        A (a: shelve__ A)
        mn r rg n m mp_src mp_tgt (mr_src mr_tgt: Σ) a0
        Xs (Qs: option mname -> Xs -> Any.t -> Any.t -> Σ -> Prop)
        Xt (Qt: option mname -> Xt -> Any.t -> Any.t -> Σ -> Prop)
        xs xt vret_src vret_tgt
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (R: A -> Any.t -> Any.t -> iProp) n' m'
        (FUEL: n = Ord_S_n n' 14)
        (FUEL2: m = Ord_S_n m' 14)

        ctx rx
        Invtn Xn Xtra
        (ACC: current_iPropL ctx [(Invtn, OwnInvT mr_tgt); (Xn, (Xtra ∧ Exactly rx)%I)])

        (WLE: le a0 a)

        (UPDATABLE: forall vret_tgt_tgt,
           bi_entails ((Qt mn xt vret_tgt vret_tgt_tgt: iProp) ** Xtra)
                      (bupd (R a mp_src mp_tgt ** (Qs mn xs vret_src vret_tgt: iProp))))

        (EQ: forall (mr_src1 mr_tgt1: Σ) (WLE: le a0 a) vret_tgt_tgt
                    (QT: exists rq, Qt mn xt vret_tgt vret_tgt_tgt rq)
                    (WF: mk_wf R a (Any.pair mp_src mr_src1↑, Any.pair mp_tgt mr_tgt1↑)),
            eqr (Any.pair mp_src mr_src1↑) (Any.pair mp_tgt mr_tgt1↑) vret_tgt vret_tgt_tgt)
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a0
             (Any.pair mp_src mr_src↑, (HoareFunRet Qs mn xs (ctx, vret_src)))
             (Any.pair mp_tgt mr_tgt↑, (HoareFunRet Qt mn xt (ctx ⋅ rx, vret_tgt)))
  .
  Proof.
    subst. unfold HoareFunRet, mput, mget, guarantee.
    repeat (ired_both; gstep; econs; eauto with ord_step2). exists vret_tgt.
    steps.
    repeat (ired_both; gstep; econs; eauto with ord_step2).
    rename c0 into mr_tgt1.
    assert (exists mr_src1 rret_src,
               (<<UPDATABLE: URA.wf (ctx ⋅ (mr_tgt1 ⋅ mr_src1 ⋅ rret_src))>>) /\
               (<<RSRC: R a mp_src mp_tgt mr_src1>>) /\
               (<<PRE: Qs mn xs vret_src vret_tgt rret_src>>)).
    { clear - ACC UPDATABLE x0 x1. red in ACC. inv ACC.
      rename x into vret_tgt_tgt. rename c into rt.
      specialize (UPDATABLE vret_tgt_tgt).
      unfold from_iPropL in IPROP.
      uipropall. des. clarify. rename a1 into rx.
      hexploit (UPDATABLE (rt ⋅ rx)); et.
      { eapply wf_extends; try apply x0. r. exists (ctx ⋅ mr_tgt1). r_solve. }
      { instantiate (1:=ctx ⋅ mr_tgt1). r_wf x0. }
      i; des. clarify. esplits; et.
      r_wf H.
    }
    des. exists (rret_src, mr_src1 ⋅ mr_tgt1).
    steps.
    repeat (ired_both; gstep; econs; eauto with ord_step2). unshelve esplits.
    { r_wf UPDATABLE0. }
    repeat (ired_both; gstep; econs; eauto with ord_step2). unshelve esplits; eauto.
    repeat (ired_both; gstep; econs; eauto with ord_step2).
    eapply EQ; et. econs; et.
    { ii. uipropall. esplits; et. refl. }
    Unshelve. all: ss.
  Qed.

End MODE.

Ltac harg :=
  let PRE := constr:("PRE") in
  let INVS := constr:("INVS") in
  let INVT := constr:("INVT") in
  eapply (@harg_clo _ _ PRE INVS INVT);
  [eassumption
  |refl
  |
  ]; i.



Ltac init :=
  let varg_src := fresh "varg_src" in
  let mn := fresh "mn" in
  let varg := fresh "varg" in
  let EQ := fresh "EQ" in
  let w := fresh "w" in
  let mrp_src := fresh "mrp_src" in
  let mp_tgt := fresh "mp_tgt" in
  let WF := fresh "WF" in
  split; rr; ss; intros varg_src [mn varg] EQ w mrp_src mp_tgt WF;
  (try subst varg_src); eexists _, _; cbn;
  ginit;
  try (unfold fun_to_tgt, cfunN, cfunU; rewrite ! HoareFun_parse); simpl.

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

    econs.

    (*** init ***)
    init.
    rename mp_tgt into mpr_tgt.
    assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
              mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
    { inv WF. esplits; et. } des; clarify.
    (*** init ***)



    harg. mDesAll; clarify. steps.
    (*** TODO: use entailment instead ***)
    mAssert (⌜True⌝)%I with "" as "X"; ss.
    mAssert _ with "INVT" as "INVT". { iExact "INVT". }
    mAssert (((OwnM fpre ** ⌜ord_top = ord_top⌝) ∧ ⌜varg = varg⌝))%I
      with "PRE" as "P".
    { iSplits; ss; et. }
    eapply harg_clo_tgt; et. i.

    clear ACC.
    steps.
    mClear "P".
    eapply hret_clo_both; et.
    { i. iIntros "H". iDestruct "H" as "[[A _] B]". iModIntro. iFrame. iSplits; et. }
    { i. r. esplits; et. des; clarify. uipropall. des; clarify. rr in QT0. uipropall. }
  Unshelve. all: ss. all: try exact 0.
  Qed.

End SIMMODSEM.
