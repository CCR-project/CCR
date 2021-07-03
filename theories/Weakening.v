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
Require Import Logic.

From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.




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
        R mp (mr: Σ) ord_cur ctx itr,
        paco7 (_sim_itree wf top2) bot7 (Σ * R)%type (Σ * R)%type
              (fun st_src st_tgt vret_src vret_tgt =>
                 exists mp (mr: Σ) ctx vret,
                   st_src = Any.pair mp mr↑ /\
                   st_tgt = Any.pair mp mr↑ /\
                   vret_src = (ctx, vret) /\
                   vret_tgt = (ctx, vret))
              100 tt
              (Any.pair mp mr↑, interp_hCallE_tgt mn stb_src ord_cur itr ctx)
              (Any.pair mp mr↑, interp_hCallE_tgt mn stb_tgt ord_cur itr ctx).
  Proof.
    ginit. gcofix CIH. i. ides itr.
    { steps. gstep. econs. esplits; et. }
    { steps. gbase. eapply CIH. }
    rewrite <- bind_trigger. steps.
    destruct e.
    { resub. destruct h. steps.
      hexploit stb_stronger; et. i. des. rewrite FINDSRC. steps.
      Local Transparent HoareCall. unfold HoareCall, mput, mget. Local Opaque HoareCall.
      steps. specialize (WEAKER x (Some mn)). des.
      assert (exists rarg_src,
                 (<<PRE: precond fsp_src (Some mn) x_tgt varg_src x0 x1 rarg_src>>) /\
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
      steps. force_l. exists x1.
      steps. force_l; et.
      steps. force_l; et.
      steps. gstep. econs; et.
      { red. esplits; et. }
      i. destruct w1. exists 200. red in WF. des; clarify. steps.
      assert (exists rret_tgt,
                 (<<POSTTGT: postcond f (Some mn) x x2 vret rret_tgt>>) /\
                 (<<VALIDTGT: URA.wf (rret_tgt ⋅ c1 ⋅ c3 ⋅ mr0)>>)
             ).
      { hexploit POST. i. uipropall. hexploit (H c2); et.
        { eapply URA.wf_mon. instantiate (1:=c1 ⋅ c3 ⋅ mr0). r_wf _ASSUME. }
        { instantiate (1:=c1 ⋅ c3 ⋅ mr0). r_wf _ASSUME. }
        i. des. esplits; et. r_wf H0.
      }
      des. force_r. exists (rret_tgt, c3).
      steps. force_r; et.
      steps. force_r. exists x2.
      steps. force_r; et.
      steps. guclo lordC_spec. econs.
      { instantiate (1:=100). eapply OrdArith.le_from_nat. lia. }
      gbase. eapply CIH.
    }
    destruct s.
    { resub. destruct p.
      { ired_both. force_l. force_r. ired_both.
        force_l. force_r. ired_both. steps.
        gbase. eapply CIH. }
      { ired_both. force_l. force_r. ired_both. steps.
        gbase. eapply CIH. }
    }
    { resub. destruct e.
      { ired_both. force_r. i. force_l. exists x. steps.
        gbase. eapply CIH. }
      { ired_both. force_l. i. force_r. exists x. steps.
        gbase. eapply CIH. }
      { steps. gstep. econs. i. exists 100. steps.
        gbase. eapply CIH. }
    }
    Unshelve. all: ss.
  Qed.

  Variable fsp_src fsp_tgt: fspec.
  Hypothesis fsp_weaker: fspec_weaker fsp_src fsp_tgt.

  Variable body: (option mname * Any.t) -> itree hEs Any.t.

  Lemma weakening_fn:
    sim_fsem wf top2
             (fun_to_tgt mn stb_src (mk_specbody fsp_src body))
             (fun_to_tgt mn stb_tgt (mk_specbody fsp_tgt body)).
  Proof.
    econs; ss. instantiate (1:=200). subst.
    Local Transparent HoareFun. unfold fun_to_tgt, HoareFun, mput, mget. Local Opaque HoareFun.
    destruct y as [mn_caller varg_tgt]. ss. des. clarify.
    ginit. steps.
    hexploit (fsp_weaker x mn_caller). i. des.
    assert (exists rarg_tgt,
               (<<PRETGT: precond fsp_tgt mn_caller x_tgt x0 varg_tgt x1 rarg_tgt>>) /\
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
    steps. force_r. exists x1.
    steps. force_r; et.
    steps. guclo lordC_spec. econs.
    { instantiate (1:=(50 + 100)%ord).
      rewrite <- OrdArith.add_from_nat. eapply OrdArith.le_from_nat. lia. }
    guclo lbindC_spec. econs.
    { gfinal. right. eapply weakening_itree. }
    i. ss. des; clarify. steps.
    assert (exists rret_src,
               (<<POSTSRC: postcond fsp_src mn_caller x vret x2 rret_src>>) /\
               (<<VALIDSRC: URA.wf (rret_src ⋅ ctx  ⋅ c2)>>)
           ).
    { hexploit POST; et. i. uipropall. hexploit (H c1); et.
      { eapply URA.wf_mon. instantiate (1:=(ctx ⋅ c2)). r_wf _GUARANTEE. }
      { instantiate (1:=(ctx ⋅ c2)). r_wf _GUARANTEE. }
      i. des. esplits; et. r_wf H0.
    }
    des. force_l. exists x2.
    steps. force_l. exists (rret_src, c2).
    steps. force_l; et.
    steps. force_l; et.
    steps. red. esplits; et. red. esplits; et.
    Unshelve. all: ss.
  Qed.

End PROOF.

Section PROOF.

  Context `{Σ: GRA.t}.

  Definition stb_weaker (stb0 stb1: gname -> option fspec): Prop :=
    forall fn fsp0 (FINDTGT: stb0 fn = Some fsp0),
    exists fsp1,
      (<<FINDSRC: stb1 fn = Some fsp1>>) /\
      (<<WEAKER: fspec_weaker fsp0 fsp1>>)
  .

  Global Program Instance stb_weaker_PreOrder: PreOrder stb_weaker.
  Next Obligation. ii. esplits; eauto. refl. Qed.
  Next Obligation.
    ii. r in H. r in H0. exploit H; et. intro T; des.
    exploit H0; et. intro U; des. esplits; eauto. etrans; et.
  Qed.

  Theorem incl_weaker: forall stb0 stb1 (NODUP: List.NoDup (List.map fst stb1)) (INCL: incl stb0 stb1), stb_weaker (to_stb stb0) (to_stb stb1).
  Proof.
    unfold to_stb.
    ii. eapply alist_find_some in FINDTGT.
    destruct (alist_find fn stb1) eqn:T.
    { eapply alist_find_some in T.
      eapply INCL in FINDTGT.
      destruct (classic (fsp0 = f)).
      { subst. esplits; et. refl. }
      exfalso.
      eapply NoDup_inj_aux in NODUP; revgoals.
      { eapply T. }
      { eapply FINDTGT. }
      { ii; clarify. }
      ss.
    }
    eapply alist_find_none in T; et. exfalso. et.
  Qed.

  Lemma app_weaker: forall stb0 stb1, stb_weaker (to_stb stb0) (to_stb (stb0 ++ stb1)).
  Proof.
    unfold to_stb.
    ii. eapply alist_find_app in FINDTGT. esplits; eauto. refl.
  Qed.

  Theorem adequacy_weaken
          stb0 stb1
          md
          (WEAK: forall sk, stb_weaker (stb0 sk) (stb1 sk))
    :
      <<SIM: ModPair.sim (SMod.to_tgt stb1 md) (SMod.to_tgt stb0 md)>>
  .
  Proof.
    econs; cycle 1.
    { unfold SMod.to_tgt. cbn. eauto. }
    i. specialize (WEAK sk). r. econs.
    2:{ unfold SMod.to_tgt.
      unfold SMod.transl. ss.
      abstr (SModSem.fnsems (SMod.get_modsem md sk)) fnsems.
      eapply Forall2_apply_Forall2.
      { refl. }
      i. subst. destruct b. destruct f. econs.
      { rr. cbn. ss. }
      eapply weakening_fn.
      { i. exploit WEAK; et. }
      { refl. }
    }
    { ss. }
    { ss. }
    exists tt. esplits; et.
  Qed.

End PROOF.
