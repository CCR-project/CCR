Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
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

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).


  Variable stb_src stb_tgt: list (gname * fspec).
  Hypothesis stb_stronger:
    forall fn fsp_tgt (FINDTGT: alist_find fn stb_tgt = Some (fsp_tgt)),
    exists fsp_src,
      (<<FINDSRC: alist_find fn stb_src = Some (fsp_src)>>) /\
      (<<WEAKER: fspec_weaker fsp_tgt fsp_src>>)
  .

  Variable mn: mname.
  Variable fn: gname.

  Variable fsp_src fsp_tgt: fspec.
  Hypothesis fsp_weaker: fspec_weaker fsp_src fsp_tgt.

  Variable body: (mname * Any.t) -> itree (hCallE +' pE +' eventE) Any.t.

  Let wf: unit -> W -> Prop :=
    fun _ '(mrps_src0, mrps_tgt0) =>
      exists (mr: Σ) (mp: Any.t),
        (<<SRC: mrps_src0 = (mr, mp)>>) /\
        (<<TGT: mrps_tgt0 = (mr, mp)>>)
  .

  Let liftRR: forall (R_src R_tgt: Type) (RR: R_src -> R_tgt -> Prop),
      (((Σ * Any.t)) * Σ) -> (((Σ * Any.t)) * Σ) ->
      (Σ * R_src) -> (Σ * R_tgt) -> Prop :=
    fun R_src R_tgt RR '(w_src, fr_src) '(w_tgt, fr_tgt) '(ctx_src, r_src) '(ctx_tgt, r_tgt) =>
      (<<CTX: ctx_src = ctx_tgt>>) /\
      (<<WF: wf tt (w_src, w_tgt)>>) /\
      (<<FRSRC: URA.wf (ctx_src ⋅ (fst w_src) ⋅ fr_src)>>) /\
      (<<FRTGT: URA.wf (ctx_tgt ⋅ (fst w_tgt) ⋅ fr_tgt)>>) /\
      (* (<<GWF: @URA.wf (GRA.to_URA Σ) (@URA.add (GRA.to_URA Σ) (fst w_src) fr_src)>>) /\ *)
      RR r_src r_tgt.

  Lemma weakening_fn:
    sim_fsem wf top2
             (fun_to_tgt mn stb_src (mk_specbody fsp_src body))
             (fun_to_tgt mn stb_tgt (mk_specbody fsp_tgt body)).
  Proof.
    Ltac mstep := ired_both; gstep; match goal with
                                    | [|- monotone7 (_sim_itree wf _)] => eapply sim_itree_mon
                                    | _ => idtac
                                    end. (* why? *)
    Ltac muclo H := guclo H; match goal with
                             | [|- monotone7 (_sim_itree wf _)] => eapply sim_itree_mon
                             | _ => idtac
                             end. (* why? *)

    assert (SELFSIM: forall R o fr_src fr_tgt st_src st_tgt ctx
                            (itr: itree (hCallE +' pE +' eventE) R)
                            (WF: wf tt (st_src, st_tgt))
                            (FRSRC: URA.wf (ctx ⋅ (fst (st_src)) ⋅ fr_src))
                            (FRTGT: URA.wf (ctx ⋅ (fst (st_tgt)) ⋅ fr_tgt))
                            (* (GWF: @URA.wf (GRA.to_URA Σ) (@URA.add (GRA.to_URA Σ) (fst st_src) fr)) *),
               gpaco7 (_sim_itree wf top2) (cpn7 (_sim_itree wf top2)) bot7 bot7 _ _ (liftRR eq) 200 tt (st_src, fr_src, interp_hCallE_tgt mn stb_src o itr ctx) (st_tgt, fr_tgt, interp_hCallE_tgt mn stb_tgt o itr ctx)).
    { Local Transparent interp_hCallE_tgt.
      unfold interp_hCallE_tgt. gcofix CIH. i. ides itr.
      { mstep. ired. red in WF. des; subst. eapply sim_itree_ret; et.
        { red. esplits; et. }
        { red. ss. esplits; et. }
      }
      { mstep. ired. eapply sim_itree_tau; ss.
        gbase. eapply CIH; eauto. }
      rewrite <- bind_trigger. destruct e as [|[|]]; ss.
      { destruct h. repeat interp_red2. ired. cbn.
        unfold unwrapN, triggerNB. des; subst.
        destruct (alist_find fn0 stb_tgt) eqn:EQ.
        { eapply stb_stronger in EQ. des.
          rewrite FINDSRC. rewrite ! bind_ret_l. rewrite ! bind_bind.
          { muclo lordC_spec. econs.
            { instantiate (1:=(100+100)%ord). rewrite <- OrdArith.add_from_nat; et. refl. }
            muclo lbindC_spec. econs.
            { instantiate (2:=liftRR eq).
              unfold HoareCall, put, discard, forge, checkWf, assume, guarantee.

              (* target arguments *)
              mstep. eapply sim_itree_choose_tgt; eauto with ord_step. intros (mr0, fr0).
              mstep. eapply sim_itree_mget_tgt; eauto with ord_step.
              mstep. eapply sim_itree_fget_tgt; eauto with ord_step.
              mstep. eapply sim_itree_choose_tgt; eauto with ord_step. intros VALID.
              mstep. eapply sim_itree_fput_tgt; eauto with ord_step.
              mstep. eapply sim_itree_mput_tgt; eauto with ord_step.
              mstep. eapply sim_itree_choose_tgt; eauto with ord_step. intros rarg_tgt.
              mstep. eapply sim_itree_fget_tgt; eauto with ord_step.
              mstep. eapply sim_itree_choose_tgt; eauto with ord_step. intros rrest.
              mstep. eapply sim_itree_choose_tgt; eauto with ord_step. i. subst.
              mstep. eapply sim_itree_fput_tgt; eauto with ord_step.
              mstep. eapply sim_itree_choose_tgt; eauto with ord_step. intros x_src.
              mstep. eapply sim_itree_choose_tgt; eauto with ord_step. intros varg_tgt.
              mstep. eapply sim_itree_choose_tgt; eauto with ord_step. intros o0.
              mstep. eapply sim_itree_choose_tgt; eauto with ord_step. intros PRE.

              specialize (WEAKER x_src mn). des.
              assert (exists rarg_src,
                         (<<PRE: precond fsp_src0 mn x_tgt varg_src varg_tgt o0 rarg_src>>) /\
                         (<<VALID: URA.wf (ctx ⋅ (mr0 ⋅ (rarg_src ⋅ rrest)))>>)
                     ).
              { hexploit PRE0. i. uipropall. hexploit (H rarg_tgt); et.
                { eapply URA.wf_mon. instantiate (1:=ctx ⋅ (mr0 ⋅ (rrest))).
                  replace (rarg_tgt ⋅ (ctx ⋅ (mr0 ⋅ rrest))) with (ctx ⋅ (mr0 ⋅ (rarg_tgt ⋅ rrest))); auto.
                  r_solve.
                }
                { instantiate (1:=ctx ⋅ (mr0 ⋅ (rrest))).
                  replace (rarg_tgt ⋅ (ctx ⋅ (mr0 ⋅ rrest))) with (ctx ⋅ (mr0 ⋅ (rarg_tgt ⋅ rrest))); auto.
                  r_solve.
                }
                i. des. esplits; et.
                replace (ctx ⋅ (mr0 ⋅ (r1 ⋅ rrest))) with (r1 ⋅ (ctx ⋅ (mr0 ⋅ rrest))); auto. r_solve.
              }
              des.

              (* source arguments *)
              mstep. eapply sim_itree_choose_src; eauto with ord_step. exists (mr0, (rarg_src ⋅ rrest)).
              mstep. eapply sim_itree_mget_src; eauto with ord_step.
              mstep. eapply sim_itree_fget_src; eauto with ord_step.
              mstep. eapply sim_itree_choose_src; eauto with ord_step. unshelve esplit; et.
              mstep. eapply sim_itree_fput_src; eauto with ord_step.
              mstep. eapply sim_itree_mput_src; eauto with ord_step.
              mstep. eapply sim_itree_choose_src; eauto with ord_step. exists rarg_src.
              mstep. eapply sim_itree_fget_src; eauto with ord_step.
              mstep. eapply sim_itree_choose_src; eauto with ord_step. exists rrest.
              mstep. eapply sim_itree_choose_src; eauto with ord_step. unshelve esplit; et.
              mstep. eapply sim_itree_fput_src; eauto with ord_step.
              mstep. eapply sim_itree_choose_src; eauto with ord_step. exists x_tgt.
              mstep. eapply sim_itree_choose_src; eauto with ord_step. exists varg_tgt.
              mstep. eapply sim_itree_choose_src; eauto with ord_step. exists o0.
              mstep. eapply sim_itree_choose_src; eauto with ord_step. unshelve esplit; et.

              mstep. eapply sim_itree_choose_both; eauto with ord_step. i. unshelve esplit; et. exists 0.
              mstep. eapply sim_itree_call; eauto with ord_step.
              { red. esplits; et. }
              i. exists 100.

              (* source return *)
              red in WF. des; subst.
              mstep. eapply sim_itree_take_src; eauto with ord_step. intros rret_src.
              mstep. eapply sim_itree_fget_src; eauto with ord_step.
              mstep. eapply sim_itree_fput_src; eauto with ord_step.
              mstep. eapply sim_itree_take_src; eauto with ord_step. intros vret_src.
              mstep. eapply sim_itree_take_src; eauto with ord_step. intros ctx0.
              mstep. eapply sim_itree_mget_src; eauto with ord_step.
              mstep. eapply sim_itree_fget_src; eauto with ord_step.
              mstep. eapply sim_itree_take_src; eauto with ord_step. intros VALIDSRC.
              mstep. eapply sim_itree_take_src; eauto with ord_step. intros POSTSRC.

              assert (exists rret_tgt,
                         (<<POSTTGT: postcond f mn x_src vret_src vret rret_tgt>>) /\
                         (<<VALIDTGT: URA.wf (ctx0 ⋅ (mr1 ⋅ (rrest ⋅ rret_tgt)))>>)
                     ).
              { hexploit POST. i. uipropall. hexploit (H rret_src); et.
                { eapply URA.wf_mon. instantiate (1:=ctx0 ⋅ (mr1 ⋅ (rrest))).
                  replace (rret_src ⋅ (ctx0 ⋅ (mr1 ⋅ rrest))) with (ctx0 ⋅ (mr1 ⋅ (rrest ⋅ rret_src))); auto.
                  r_solve.
                }
                { instantiate (1:=ctx0 ⋅ (mr1 ⋅ (rrest))).
                  replace (rret_src ⋅ (ctx0 ⋅ (mr1 ⋅ rrest))) with (ctx0 ⋅ (mr1 ⋅ (rrest ⋅ rret_src))); auto.
                  r_solve.
                }
                i. des. esplits; et.
                replace (ctx0 ⋅ (mr1 ⋅ (rrest ⋅ r1))) with (r1 ⋅ (ctx0 ⋅ (mr1 ⋅ rrest))); auto. r_solve.
              }
              des.

              mstep. eapply sim_itree_take_tgt; eauto with ord_step. exists rret_tgt.
              mstep. eapply sim_itree_fget_tgt; eauto with ord_step.
              mstep. eapply sim_itree_fput_tgt; eauto with ord_step.
              mstep. eapply sim_itree_take_tgt; eauto with ord_step. exists vret_src.
              mstep. eapply sim_itree_take_tgt; eauto with ord_step. exists ctx0.
              mstep. eapply sim_itree_mget_tgt; eauto with ord_step.
              mstep. eapply sim_itree_fget_tgt; eauto with ord_step.
              mstep. eapply sim_itree_take_tgt; eauto with ord_step. unshelve esplit; et.
              mstep. eapply sim_itree_take_tgt; eauto with ord_step. unshelve esplit; et.
              mstep. eapply sim_itree_ret.
              { red. esplits; et. }
              { ss. }
              { econs.
                { esplits; et. }
                { esplits; et; ss.
                  { replace (ctx0 ⋅ mr1 ⋅ (rrest ⋅ rret_src)) with (ctx0 ⋅ (mr1 ⋅ (rrest ⋅ rret_src))); auto. r_solve. }
                  { replace (ctx0 ⋅ mr1 ⋅ (rrest ⋅ rret_tgt)) with (ctx0 ⋅ (mr1 ⋅ (rrest ⋅ rret_tgt))); auto. r_solve. }
                }
              }
            }
            { i. red in SIM. destruct st_src1, st_tgt1. destruct vret_src, vret_tgt. des; subst.
              mstep. eapply sim_itree_tau; et. ired_both.
              gbase. eapply CIH; et. esplits; et.
            }
          }
        }
        { mstep. eapply sim_itree_choose_tgt; eauto with ord_step. ss. }
      }
      { des; subst. rewrite ! interp_state_bind. rewrite ! interp_state_trigger. destruct p; cbn.
        { mstep. eapply sim_itree_pput_both.
          mstep. eapply sim_itree_tau.
          ired_both. gbase. eapply CIH; et. esplits; et.
        }
        { mstep. eapply sim_itree_pget_both.
          mstep. eapply sim_itree_tau.
          ired_both. gbase. eapply CIH; et. esplits; et.
        }
      }
      { des; subst. rewrite ! interp_state_bind. rewrite ! interp_state_trigger. destruct e; cbn.
        { mstep. eapply sim_itree_choose_both. i. exists x_tgt. exists 0.
          mstep. eapply sim_itree_tau.
          ired_both. gbase. eapply CIH; et. esplits; et.
        }
        { mstep. eapply sim_itree_take_both. i. exists x_src. exists 0.
          mstep. eapply sim_itree_tau.
          ired_both. gbase. eapply CIH; et. esplits; et.
        }
        { mstep. eapply sim_itree_syscall. i. exists 0.
          mstep. eapply sim_itree_tau.
          ired_both. gbase. eapply CIH; et. esplits; et.
        }
      }
    }
    { Local Transparent HoareFun.
      unfold fun_to_tgt, fun_to_src, HoareFun, forge, checkWf, discard, put, assume, guarantee. ss.
      ii. exists 400. ginit.

      (* source argument *)
      red in SIMMRS. des; subst. destruct y as [mn_caller varg].
      mstep. eapply sim_itree_take_src; eauto with ord_step. intros ctx.
      mstep. eapply sim_itree_take_src; eauto with ord_step. intros varg_src.
      mstep. eapply sim_itree_take_src; eauto with ord_step. intros x_src.
      mstep. eapply sim_itree_take_src; eauto with ord_step. intros rarg_src.
      mstep. eapply sim_itree_fget_src; eauto with ord_step.
      mstep. eapply sim_itree_fput_src; eauto with ord_step.
      mstep. eapply sim_itree_mget_src; eauto with ord_step.
      mstep. eapply sim_itree_fget_src; eauto with ord_step.
      mstep. eapply sim_itree_take_src; eauto with ord_step. intros VALIDSRC.
      mstep. eapply sim_itree_take_src; eauto with ord_step. intros o.
      mstep. eapply sim_itree_take_src; eauto with ord_step. intros PRESRC.

      hexploit (fsp_weaker x_src mn_caller). i. des.
      assert (exists rarg_tgt,
                 (<<PRETGT: precond fsp_tgt mn_caller x_tgt varg_src varg o rarg_tgt>>) /\
                 (<<VALIDTGT: URA.wf (ctx ⋅ (mr ⋅ (ε ⋅ rarg_tgt)))>>)).
      { hexploit PRE; et. i. uipropall. hexploit (H rarg_src); et.
        { eapply URA.wf_mon. instantiate (1:=ctx ⋅ mr).
          replace (rarg_src ⋅ (ctx ⋅ mr)) with (ctx ⋅ (mr ⋅ (ε ⋅ rarg_src))); auto. r_solve. }
        { instantiate (1:=ctx ⋅ mr).
          replace (rarg_src ⋅ (ctx ⋅ mr)) with (ctx ⋅ (mr ⋅ (ε ⋅ rarg_src))); auto. r_solve. }
        i. destruct H0. des. exists x. esplits; et.
        replace (ctx ⋅ (mr ⋅ (ε ⋅ x))) with (x ⋅ (ctx ⋅ mr)); auto. r_solve.
      }
      des.

      (* target argument *)
      mstep. eapply sim_itree_take_tgt; eauto with ord_step. exists ctx.
      mstep. eapply sim_itree_take_tgt; eauto with ord_step. exists varg_src.
      mstep. eapply sim_itree_take_tgt; eauto with ord_step. exists x_tgt.
      mstep. eapply sim_itree_take_tgt; eauto with ord_step. exists rarg_tgt.
      mstep. eapply sim_itree_fget_tgt; eauto with ord_step.
      mstep. eapply sim_itree_fput_tgt; eauto with ord_step.
      mstep. eapply sim_itree_mget_tgt; eauto with ord_step.
      mstep. eapply sim_itree_fget_tgt; eauto with ord_step.
      mstep. eapply sim_itree_take_tgt; eauto with ord_step. unshelve esplit; et.
      mstep. eapply sim_itree_take_tgt; eauto with ord_step. exists o.
      mstep. eapply sim_itree_take_tgt; eauto with ord_step. unshelve esplit; et.

      ired_both. muclo lordC_spec. econs.
      { instantiate (1:=(_+200)%ord). rewrite <- OrdArith.add_from_nat; et.
        instantiate (1:=178). refl. }
      muclo lbindC_spec. econs.
      { eapply SELFSIM.
        { esplits; et. }
        { ss. replace (ctx ⋅ mr ⋅ (ε ⋅ rarg_src)) with (ctx ⋅ (mr ⋅ (ε ⋅ rarg_src))); et. r_solve. }
        { ss. replace (ctx ⋅ mr ⋅ (ε ⋅ rarg_tgt)) with (ctx ⋅ (mr ⋅ (ε ⋅ rarg_tgt))); et. r_solve. }
      }
      i. red in SIM.
      destruct st_src1, st_tgt1. destruct vret_src, vret_tgt. des; subst; ss.

      (* target return *)
      mstep. eapply sim_itree_choose_tgt; eauto with ord_step. intros ret_tgt.
      mstep. eapply sim_itree_choose_tgt; eauto with ord_step. intros (mr_tgt, fr_tgt).
      mstep. eapply sim_itree_mget_tgt; eauto with ord_step.
      mstep. eapply sim_itree_fget_tgt; eauto with ord_step.
      mstep. eapply sim_itree_choose_tgt; eauto with ord_step. intros VALIDTGT0.
      mstep. eapply sim_itree_fput_tgt; eauto with ord_step.
      mstep. eapply sim_itree_mput_tgt; eauto with ord_step.
      mstep. eapply sim_itree_choose_tgt; eauto with ord_step. intros rret_tgt.
      mstep. eapply sim_itree_choose_tgt; eauto with ord_step. intros POSTTGT.
      mstep. eapply sim_itree_fget_tgt; eauto with ord_step.
      mstep. eapply sim_itree_choose_tgt; eauto with ord_step. intros rrest.
      mstep. eapply sim_itree_choose_tgt; eauto with ord_step. i. subst.
      mstep. eapply sim_itree_fput_tgt; eauto with ord_step.

      assert (exists rret_src,
                 (<<POSTSRC: postcond fsp_src mn_caller x_src t0 ret_tgt rret_src>>) /\
                 (<<VALIDSRC: URA.wf (c2 ⋅ (mr_tgt ⋅ (rret_src ⋅ rrest)))>>)
             ).
      { hexploit POST; et. i. uipropall. hexploit (H rret_tgt); et.
        { eapply URA.wf_mon. instantiate (1:=(c2 ⋅ (mr_tgt ⋅ rrest))).
          replace (rret_tgt ⋅ (c2 ⋅ (mr_tgt ⋅ rrest))) with (c2 ⋅ (mr_tgt ⋅ (rret_tgt ⋅ rrest))); auto. r_solve. }
        { instantiate (1:=(c2 ⋅ (mr_tgt ⋅ rrest))).
          replace (rret_tgt ⋅ (c2 ⋅ (mr_tgt ⋅ rrest))) with (c2 ⋅ (mr_tgt ⋅ (rret_tgt ⋅ rrest))); auto. r_solve. }
        i. des. exists r1. esplits; et.
        replace (c2 ⋅ (mr_tgt ⋅ (r1 ⋅ rrest))) with (r1 ⋅ (c2 ⋅ (mr_tgt ⋅ rrest))); auto. r_solve.
      }
      des.

      (* source return *)
      mstep. eapply sim_itree_choose_src; eauto with ord_step. exists ret_tgt.
      mstep. eapply sim_itree_choose_src; eauto with ord_step. exists (mr_tgt, (rret_src ⋅ rrest)).
      mstep. eapply sim_itree_mget_src; eauto with ord_step.
      mstep. eapply sim_itree_fget_src; eauto with ord_step.
      mstep. eapply sim_itree_choose_src; eauto with ord_step. unshelve esplit; et.
      mstep. eapply sim_itree_fput_src; eauto with ord_step.
      mstep. eapply sim_itree_mput_src; eauto with ord_step.
      mstep. eapply sim_itree_choose_src; eauto with ord_step. exists rret_src.
      mstep. eapply sim_itree_choose_src; eauto with ord_step. unshelve esplit; et.
      mstep. eapply sim_itree_fget_src; eauto with ord_step.
      mstep. eapply sim_itree_choose_src; eauto with ord_step. exists rrest.
      mstep. eapply sim_itree_choose_src; eauto with ord_step. unshelve esplit; et.
      mstep. eapply sim_itree_fput_src; eauto with ord_step.
      mstep. eapply sim_itree_ret; et.
      red. esplits; et.
    }
    Unshelve. all: try (exact Ord.O). all: try (exact tt).
  Qed.

End PROOF.

Section PROOF.

  Context `{Σ: GRA.t}.

  Definition stb_weaker (stb0 stb1: list (gname * fspec)): Prop :=
    forall fn fsp0 (FINDTGT: alist_find fn stb0 = Some fsp0),
    exists fsp1,
      (<<FINDSRC: alist_find fn stb1 = Some fsp1>>) /\
      (<<WEAKER: fspec_weaker fsp0 fsp1>>)
  .

  Global Program Instance stb_weaker_PreOrder: PreOrder stb_weaker.
  Next Obligation. ii. esplits; eauto. refl. Qed.
  Next Obligation.
    ii. r in H. r in H0. exploit H; et. intro T; des.
    exploit H0; et. intro U; des. esplits; eauto. etrans; et.
  Qed.

  Theorem incl_weaker: forall stb0 stb1 (NODUP: List.NoDup (List.map fst stb1)) (INCL: incl stb0 stb1), stb_weaker stb0 stb1.
  Proof.
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

  Lemma app_weaker: forall stb0 stb1, stb_weaker stb0 (stb0 ++ stb1).
  Proof.
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
    { instantiate (1:=fun (_ _: unit) => True). ss. }
    { instantiate (1:=fun _ '(x, y) => x = y).
      unfold SMod.to_tgt.
      unfold SMod.transl. ss.
      abstr (SModSem.fnsems (SMod.get_modsem md sk)) fnsems.
      induction fnsems; ss.
      econs; et. destruct a. cbn. split; cbn.
      { rr. cbn. ss. }
      r. cbn.
      destruct f.
      replace (fun '(x, y) => x = y) with
          (fun '(mrps_src0, mrps_tgt0) => exists (mr: Σ) (mp: Any.t), (<<SRC: mrps_src0 = (mr, mp)>>)
                                                                      /\ <<TGT: mrps_tgt0 = (mr, mp)>>); cycle 1.
      { apply func_ext. i. des_ifs. apply Axioms.prop_ext. split; i; des; subst; et. destruct p0. esplits; et. }
      eapply weakening_fn; ss.
      refl.
    }
    { ss. }
    { ss. }
  Qed.

End PROOF.
