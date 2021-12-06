Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
Require Import SimModSemOld.

Require Import HTacticsOld.
Require Import ProofMode.

From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.


Module TAC.
  Ltac steps := repeat (_steps oauto; des_ifs_safe).
  Ltac force_l := _force_l oauto.
  Ltac force_r := _force_r oauto.
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
        R mp (mr: Σ) ord_cur_src ord_cur_tgt (ORD: ord_weaker ord_cur_tgt ord_cur_src)  ctx itr,
        paco8 (_sim_itree wf top2) bot8 (Σ * R)%type (Σ * R)%type
              (fun st_src st_tgt vret_src vret_tgt =>
                 exists mp (mr: Σ) ctx vret,
                   st_src = Any.pair mp mr↑ /\
                   st_tgt = Any.pair mp mr↑ /\
                   vret_src = (ctx, vret) /\
                   vret_tgt = (ctx, vret))
              100 100 tt
              (Any.pair mp mr↑, interp_hCallE_tgt mn stb_src ord_cur_src itr ctx)
              (Any.pair mp mr↑, interp_hCallE_tgt mn stb_tgt ord_cur_tgt itr ctx).
  Proof.
    ginit. gcofix CIH. i. ides itr.
    { steps. gstep. econs. esplits; et. }
    { steps. gbase. eapply CIH; ss. }
    rewrite <- bind_trigger. steps.
    destruct e.
    { resub. destruct h. steps.
      hexploit stb_stronger; et. i. des. rewrite FINDSRC. steps.
      Local Transparent HoareCall. unfold HoareCall, mput, mget. Local Opaque HoareCall.
      steps. specialize (WEAKER x (Some mn)). des.
      assert (exists rarg_src,
                 (<<PRE: precond fsp_src (Some mn) x_tgt varg_src x0 rarg_src>>) /\
                 (<<VALID: URA.wf (rarg_src ⋅ c1 ⋅ ctx ⋅ c)>>)
             ).
      { hexploit PRE. i. uipropall. hexploit (H c0); et.
        { eapply URA.wf_mon. instantiate (1:=c1 ⋅ ctx ⋅ c). r_wf _GUARANTEE. }
        { instantiate (1:=c1 ⋅ ctx ⋅ c). r_wf _GUARANTEE. }
        i. des. esplits; et. r_wf H0.
      }
      des. force_l. exists (rarg_src, c1, c).
      steps. force_l; et.
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
      i. destruct w1. red in WF. des; clarify.
      rewrite Any.pair_split in _UNWRAPU. des; clarify.
      steps.
      assert (exists rret_tgt,
                 (<<POSTTGT: postcond f (Some mn) x x1 vret rret_tgt>>) /\
                 (<<VALIDTGT: URA.wf (rret_tgt ⋅ c1 ⋅ c3 ⋅ mr0)>>)
             ).
      { hexploit POST. i. uipropall. hexploit (H c2); et.
        { eapply URA.wf_mon. instantiate (1:=c1 ⋅ c3 ⋅ mr0). r_wf _ASSUME. }
        { instantiate (1:=c1 ⋅ c3 ⋅ mr0). r_wf _ASSUME. }
        i. des. esplits; et. r_wf H0.
      }
      des. force_r. exists (rret_tgt, c3).
      steps. force_r; et.
      steps. force_r. exists x1.
      steps. force_r; et.
      steps. gbase. eapply CIH; ss.
    }
    destruct s.
    { resub. destruct p.
      { ired_both. force_l. force_r. ired_both.
        force_l. force_r. ired_both. steps.
        gbase. eapply CIH; ss. }
      { ired_both. force_l. force_r. ired_both. steps.
        gbase. eapply CIH; ss. }
    }
    { resub. destruct e.
      { ired_both. force_r. i. force_l. exists x. steps.
        gbase. eapply CIH; ss. }
      { ired_both. force_l. i. force_r. exists x. steps.
        gbase. eapply CIH; ss. }
      { steps. gbase. eapply CIH; ss. }
    }
    Unshelve. all: ss. all: try exact 0.
  Qed.

  Variable fsp_src fsp_tgt: fspec.
  Hypothesis fsp_weaker: fspec_weaker fsp_src fsp_tgt.

  Variable body: (option mname * Any.t) -> itree hEs Any.t.

  Lemma weakening_fn arg mrs_src mrs_tgt (WF: wf tt (mrs_src, mrs_tgt)):
    sim_itree wf top2 200 200 tt
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
               (<<VALIDTGT: URA.wf (rarg_tgt ⋅ c0 ⋅ mr)>>)).
    { hexploit PRE; et. i. uipropall. hexploit (H c); et.
      { eapply URA.wf_mon. instantiate (1:=c0 ⋅ mr). r_wf _ASSUME. }
      { instantiate (1:=c0 ⋅ mr). r_wf _ASSUME. }
      i. des. esplits; et. r_wf H0.
    }
    des. force_r. exists x_tgt.
    steps. force_r. exists x0.
    steps. force_r. exists (rarg_tgt, c0).
    steps. force_r; et.
    steps. force_r; et.
    steps. guclo lordC_spec. econs.
    { instantiate (2:=(50 + 100)%ord).
      rewrite <- OrdArith.add_from_nat. eapply OrdArith.le_from_nat. refl. }
    { instantiate (2:=(50 + 100)%ord).
      rewrite <- OrdArith.add_from_nat. eapply OrdArith.le_from_nat. refl. }
    guclo lbindC_spec. econs.
    { gfinal. right. r in MEASURE. des_ifs.
      - eapply weakening_itree; ss.
      - eapply weakening_itree; ss.
    }
    i. ss. des; clarify. steps.
    assert (exists rret_src,
               (<<POSTSRC: postcond fsp_src mn_caller x vret x1 rret_src>>) /\
               (<<VALIDSRC: URA.wf (rret_src ⋅ ctx  ⋅ c2)>>)
           ).
    { hexploit POST; et. i. uipropall. hexploit (H c1); et.
      { eapply URA.wf_mon. instantiate (1:=(ctx ⋅ c2)). r_wf _GUARANTEE. }
      { instantiate (1:=(ctx ⋅ c2)). r_wf _GUARANTEE. }
      i. des. esplits; et. r_wf H0.
    }
    des. force_l. exists x1.
    steps. force_l. exists (rret_src, c2).
    steps. force_l; et.
    steps. force_l; et.
    steps. red. esplits; et. red. esplits; et.
    Unshelve. all: ss. all: try exact 0.
  Qed.

  Lemma weakening_fsem:
    sim_fsem wf top2
             (fun_to_tgt mn stb_src (mk_specbody fsp_src body))
             (fun_to_tgt mn stb_tgt (mk_specbody fsp_tgt body)).
  Proof.
    ii. eexists _, _. destruct w. subst. eapply weakening_fn. auto.
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
