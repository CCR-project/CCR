Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
Require Import SimModSem.

Require Import HTactics.
Require Import ProofMode.

From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.


Module TAC.
  Ltac steps := repeat (_steps; des_ifs_safe).
  Ltac force_l := _force_l.
  Ltac force_r := _force_r.
End TAC.
Import TAC.

Section PROOF.

  Context `{Σ: GRA.t}.

  Let W: Type := (Any.t) * (Any.t).


  Variable stb_src stb_tgt: gname -> option fspec.
  Hypothesis stb_stronger:
    forall fn fsp_tgt (FINDTGT: stb_tgt fn = Some (fsp_tgt)),
    exists fsp_src,
      (<<FINDSRC: stb_src fn = Some (fsp_src)>>) /\
      (<<WEAKER: fspec_weaker fsp_tgt fsp_src>>)
  .

  Variable mn: mname.

  Let wf: unit -> W -> Prop :=
    fun _ '(st_src, st_tgt) =>
      exists mp (mr: Σ),
        st_src = Any.pair mp mr↑ /\
        st_tgt = Any.pair mp mr↑.

  Lemma weakening_itree
    :
      forall
        R mp (mr: Σ) ord_cur_src ord_cur_tgt (ORD: ord_weaker ord_cur_tgt ord_cur_src) fr_src fr_tgt
        (UPD: URA.updatable fr_src fr_tgt)
        (WF: URA.wf (fr_src ⋅ mr)) itr,
        paco8 (_sim_itree wf top2) bot8 (Σ * R)%type (Σ * R)%type
              (fun st_src st_tgt vret_src vret_tgt =>
                 exists mp (mr: Σ) fr_src fr_tgt vret,
                   <<UPD: URA.updatable fr_src fr_tgt>> /\
                   <<WF: URA.wf (fr_src ⋅ mr)>> /\
                   st_src = Any.pair mp mr↑ /\
                   st_tgt = Any.pair mp mr↑ /\
                   vret_src = (fr_src, vret) /\
                   vret_tgt = (fr_tgt, vret))
              false false tt
              (Any.pair mp mr↑, interp_hCallE_tgt mn stb_src ord_cur_src itr fr_src)
              (Any.pair mp mr↑, interp_hCallE_tgt mn stb_tgt ord_cur_tgt itr fr_tgt).
  Proof.
    ginit. gcofix CIH. i. ides itr.
    { steps. gstep. econs. esplits; et. }
    { steps. deflag. gbase. eapply CIH; ss. }
    rewrite <- bind_trigger. steps.
    destruct e.
    { resub. destruct h. steps.
      hexploit stb_stronger; et. i. des. rewrite FINDSRC. steps.
      Local Transparent HoareCall. unfold HoareCall, mput, mget. Local Opaque HoareCall.
      steps. specialize (WEAKER x (Some mn)). des.
      assert(T: URA.updatable (fr_src ⋅ mr) (fr_tgt ⋅ mr)).
      { eapply URA.updatable_add; et. refl. }
      assert (exists rarg_src,
                 (<<PRE: precond fsp_src (Some mn) x_tgt varg_src x0 rarg_src>>) /\
                 (<<VALID: URA.updatable (fr_tgt ⋅ mr) (rarg_src ⋅ c1 ⋅ c)>>)
             ).
      { hexploit PRE. i. uipropall. hexploit (H c0); et.
        { eapply URA.wf_mon. instantiate (1:=c1 ⋅ c). rewrite URA.add_assoc. eapply URA.updatable_wf; et.
          etrans; et. }
        i. des. esplits; et. etrans; et.
        eapply URA.updatable_add; try refl.
        eapply URA.updatable_add; try refl. r. eauto.
      }
      des. force_l. exists (rarg_src, c1, c).
      steps. force_l; et. { etrans; et. }
      steps. force_l. exists x_tgt.
      steps. force_l. exists x0.
      steps. force_l; et.
      steps. force_l; et.
      { esplits; et.
        - r in MEASURE. des_ifs; ss; des_ifs. ss. eapply Ord.le_lt_lt; et. eapply Ord.lt_le_lt; et.
        - i. spc _GUARANTEE2. r in MEASURE. des_ifs; ss; des_ifs.
        - i. spc _GUARANTEE3. r in MEASURE. des_ifs; ss; des_ifs.
      }
      steps.
      { esplits; et. }
      i. destruct w1. red in WF0. des; clarify.
      rewrite Any.pair_split in _UNWRAPU. des; clarify.
      steps. rewrite Any.upcast_downcast in *. sym in _UNWRAPU0. clarify.
      rename x2 into vret_src.
      assert (exists rret_tgt,
                 (<<POSTTGT: postcond f (Some mn) x vret_src vret rret_tgt>>) /\
                 (<<VALIDTGT: URA.wf (rret_tgt ⋅ c1 ⋅ mr0)>> /\
                 (<<UPD: URA.updatable x1 rret_tgt>>))
             ).
      { hexploit POST. i. uipropall. hexploit (H x1); et.
        { eapply URA.wf_mon. instantiate (1:=c1 ⋅ mr0). rewrite URA.add_assoc. eapply URA.updatable_wf; et.
          refl. }
        i. des. esplits; et. eapply URA.updatable_add; et. refl.
      }
      des. force_r. exists (rret_tgt).
      steps. force_r; et.
      steps. force_r. exists vret_src.
      steps. force_r; et.
      steps. deflag. gbase. eapply CIH; ss.
      eapply URA.updatable_add; et. refl.
    }
    destruct s.
    { resub. destruct p.
      { ired_both. force_l. force_r. ired_both.
        force_l. force_r. ired_both. steps. deflag.
        gbase. eapply CIH; ss. }
      { ired_both. force_l. force_r. ired_both. steps. deflag.
        gbase. eapply CIH; ss. }
    }
    { resub. destruct e.
      { ired_both. force_r. i. force_l. exists x. steps. deflag.
        gbase. eapply CIH; ss. }
      { ired_both. force_l. i. force_r. exists x. steps. deflag.
        gbase. eapply CIH; ss. }
      { steps. deflag. gbase. eapply CIH; ss. }
    }
    Unshelve. all: ss. all: try exact 0.
  Qed.

  Variable fsp_src fsp_tgt: fspec.
  Hypothesis fsp_weaker: fspec_weaker fsp_src fsp_tgt.

  Variable body: (option mname * Any.t) -> itree hEs Any.t.

  Lemma weakening_fn arg mrs_src mrs_tgt (WF: wf tt (mrs_src, mrs_tgt)):
    sim_itree wf top2 false false tt
              (mrs_src, fun_to_tgt mn stb_src (mk_specbody fsp_src body) arg)
              (mrs_tgt, fun_to_tgt mn stb_tgt (mk_specbody fsp_tgt body) arg).
  Proof.
    red in WF. des. subst.
    Local Transparent HoareFun. unfold fun_to_tgt, HoareFun, mput, mget. Local Opaque HoareFun.
    destruct arg as [mn_caller varg_tgt]. ss. des. clarify.
    ginit. steps.
    hexploit (fsp_weaker x mn_caller). i. des.
    assert (exists rarg_tgt,
               (<<PRETGT: precond fsp_tgt mn_caller x_tgt x0 varg_tgt rarg_tgt>>) /\
               (<<VALIDTGT: URA.wf (mr ⋅ rarg_tgt)>>) /\
               (<<UPD: URA.updatable x1 rarg_tgt>>)).
    { hexploit PRE. i. uipropall. hexploit (H x1); et.
      { eapply URA.wf_mon; et. }
      i. des. esplits; et. eapply URA.updatable_wf; et. rewrite URA.add_comm.
      eapply URA.updatable_add; et. refl.
    }
    des. force_r. exists x_tgt.
    steps. force_r. exists x0.
    steps. force_r. exists (rarg_tgt).
    steps. force_r; et.
    steps. force_r; et.
    steps. deflag. guclo lbindC_spec. econs.
    { gfinal. right. r in MEASURE. des_ifs.
      - eapply weakening_itree; ss.
      - eapply weakening_itree; ss.
    }
    i. ss. des; clarify. steps.
    assert(T: URA.updatable (fr_src ⋅ mr0) (c0 ⋅ c1 ⋅ c)).
    { etrans; et. eapply URA.updatable_add; et. refl. }
    assert (exists rret_src,
               (<<POSTSRC: postcond fsp_src mn_caller x vret x2 rret_src>>) /\
               (<<VALIDSRC: URA.wf (rret_src ⋅ c)>>) /\
               (<<UPD: URA.updatable c0 rret_src>>)
           ).
    { hexploit POST. i. uipropall. hexploit (H c0); et.
      { eapply URA.wf_mon. instantiate (1:=c1 ⋅ c). rewrite URA.add_assoc. eapply URA.updatable_wf; et. }
      i. des. esplits; et. eapply URA.updatable_wf; et. etrans; et.
      replace (c0 ⋅ c1 ⋅ c) with ((c0 ⋅ c1) ⋅ c) by r_solve.
      eapply URA.updatable_add; et; try refl. etrans; et. eapply URA.extends_updatable. exists c1; r_solve.
    }
    des. force_l. exists x2.
    steps. force_l. exists (rret_src, ε, c).
    steps. force_l; et.
    { rewrite URA.unit_id. etrans; et. eapply URA.updatable_add; et; try refl. etrans; et.
      eapply URA.extends_updatable. exists c1; r_solve.
    }
    steps. force_l; et.
    steps. red. esplits; et. red. esplits; et.
    Unshelve. all: ss. all: try exact 0.
  Qed.

  Lemma weakening_fsem:
    sim_fsem wf top2
             (fun_to_tgt mn stb_src (mk_specbody fsp_src body))
             (fun_to_tgt mn stb_tgt (mk_specbody fsp_tgt body)).
  Proof.
    ii. destruct w. subst. eapply weakening_fn. auto.
  Qed.

End PROOF.

Section PROOF.
  Context `{EMSConfig}.
  Context `{Σ: GRA.t}.

  Theorem adequacy_weaken
          stb0 stb1
          md
          (WEAK: forall sk, stb_weaker (stb0 sk) (stb1 sk))
    :
      refines2 [SMod.to_tgt stb0 md] [SMod.to_tgt stb1 md]
  .
  Proof.
    eapply adequacy_local2. econs; cycle 1.
    { unfold SMod.to_tgt. cbn. eauto. }
    i. specialize (WEAK sk). r. econs.
    2:{ unfold SMod.to_tgt.
      unfold SMod.transl. ss.
      abstr (SModSem.fnsems (SMod.get_modsem md sk)) fnsems.
      eapply Forall2_apply_Forall2.
      { refl. }
      i. subst. destruct b. destruct f. econs.
      { rr. cbn. ss. }
      eapply weakening_fsem.
      { i. exploit WEAK; et. }
      { refl. }
    }
    { ss. }
    { ss. }
    exists tt. esplits; et.
  Qed.

End PROOF.
