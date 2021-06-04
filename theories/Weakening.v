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

  Variable m: mname.

  Variable fn: gname.

  Variable fsp_src fsp_tgt: fspec.
  Hypothesis fsp_weaker: fspec_weaker fsp_src fsp_tgt.

  Variable body_src: fsp_src.(AA) -> itree (hCallE +' pE +' eventE) fsp_src.(AR).
  Variable body_tgt: fsp_tgt.(AA) -> itree (hCallE +' pE +' eventE) fsp_tgt.(AR).
  Hypothesis body_eq: JMeq body_src body_tgt.

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mr: Σ) (mp: Any.t),
        (<<SRC: mrps_src0 = (mr, mp)>>) /\
        (<<TGT: mrps_tgt0 = (mr, mp)>>)
  .

  Let liftRR: forall (R_src R_tgt: Type) (RR: R_src -> R_tgt -> Prop),
      (((Σ * Any.t)) * Σ) -> (((Σ * Any.t)) * Σ) ->
      R_src -> R_tgt -> Prop :=
    fun R_src R_tgt RR '(w_src, fr_src) '(w_tgt, fr_tgt) r_src r_tgt =>
      (<<WF: wf (w_src, w_tgt)>>) /\
      (<<FR: fr_src = fr_tgt>>) /\
      (<<GWF: @URA.wf (GRA.to_URA Σ) (@URA.add (GRA.to_URA Σ) (fst w_src) fr_src)>>) /\
      RR r_src r_tgt.

  Lemma weakening_fn:
    sim_fsem wf
             (fun_to_tgt stb_src (mk_specbody fsp_src body_src))
             (fun_to_tgt stb_tgt (mk_specbody fsp_tgt body_tgt)).
  Proof.
    Ltac mstep := gstep; match goal with
                         | [|- monotone6 (_sim_itree wf)] => eapply sim_itree_mon
                         | _ => idtac
                         end. (* why? *)
    Ltac muclo H := guclo H; match goal with
                             | [|- monotone6 (_sim_itree wf)] => eapply sim_itree_mon
                             | _ => idtac
                             end. (* why? *)
    inv fsp_weaker. ss. subst.

    assert (SELFSIM: forall R o fr st_src st_tgt ctx
                            (itr: itree (hCallE +' pE +' eventE) R)
                            (WF: wf (st_src, st_tgt))
                            (GWF: @URA.wf (GRA.to_URA Σ) (@URA.add (GRA.to_URA Σ) (fst st_src) fr)),
               gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) bot6 bot6 _ _ (liftRR eq) 1 (st_src, fr, interp_hCallE_tgt stb_src o itr ctx) (st_tgt, fr, interp_hCallE_tgt stb_tgt o itr ctx)).
    { Local Transparent interp_hCallE_tgt.
      unfold interp_hCallE_tgt. gcofix CIH. i. ides itr.
      { repeat interp_red2.
        mstep. ired. eapply sim_itree_ret; ss. }
      { repeat interp_red.
        mstep. ired. eapply sim_itree_tau; ss.
        gbase. eapply CIH; eauto. }
      rewrite <- bind_trigger. destruct e as [|[|]]; ss.
      { destruct h. repeat interp_red2. ired. cbn.
        unfold unwrapN, triggerNB.
        destruct (alist_find fn0 stb_tgt) eqn:EQ.
        { eapply stb_stronger in EQ. des. inv WEAKER.
          rewrite FINDSRC. rewrite ! bind_ret_l. rewrite ! bind_bind.
          destruct (Any.downcast varg_src); ss.
          { rewrite ! bind_ret_l. rewrite ! bind_bind.
            muclo lordC_spec. econs.
            { instantiate (1:=(1+0)%ord). rewrite Ord.from_nat_O. eapply OrdArith.add_O_r. }
            muclo lbindC_spec. econs.
            { instantiate (1:=liftRR eq).
              unfold HoareCall, put, discard, forge, checkWf, assume, guarantee.
              mstep. eapply sim_itree_choose_both.
              intros (mr0, fr0). exists (mr0, fr0). exists 0.
              rewrite ! bind_bind.
              mstep. eapply sim_itree_mget_both.
              mstep. eapply sim_itree_fget_both.
              mstep. eapply sim_itree_choose_both. i. split; ss. exists 0.
              rewrite ! bind_ret_l.
              mstep. eapply sim_itree_fput_both.
              mstep. eapply sim_itree_mput_both.
              mstep. eapply sim_itree_choose_both.
              intros rarg. exists rarg. exists 0.
              rewrite ! bind_bind.
              mstep. eapply sim_itree_fget_both.
              rewrite ! bind_bind.
              mstep. eapply sim_itree_choose_both.
              intros rret. exists rret. exists 0.
              rewrite ! bind_bind.
              mstep. eapply sim_itree_choose_both. i. split; auto. exists 0.
              rewrite ! bind_ret_l.
              mstep. eapply sim_itree_fput_both.
              mstep. eapply sim_itree_choose_both.
              intros x_src. specialize (WEAK0 x_src). des.
              exists x_tgt1. exists 0.
              mstep. eapply sim_itree_choose_both.
              intros varg_tgt. exists varg_tgt. exists 0.
              mstep. eapply sim_itree_choose_both.
              intros o0. exists o0. exists 0.
              rewrite ! bind_bind.
              mstep. eapply sim_itree_choose_both. i. split; eauto.
              { admit "fix it after changin hcall".
                (* subst. exploit PRE; eauto. *)
                (* { exploit (x_tgt ε). *)
                (*   { erewrite URA.unit_id. auto. } *)
                (*   { i. erewrite URA.unit_idl. erewrite URA.unit_id in x0. *)
                (*     erewrite URA.add_comm in x0. eapply URA.wf_mon in x0. *)
                (*     eapply URA.wf_mon in x0. auto. } *)
                (* } *)
                (* { erewrite URA.unit_idl. auto. } *)
              }
              exists 0.
              rewrite ! bind_ret_l.
              mstep. eapply sim_itree_choose_both. i. split; eauto. exists 0.
              mstep. eapply sim_itree_call.
              { unfold wf. esplits; eauto. }
              i. unfold wf in WF. des; clarify. exists 0.
              mstep. eapply sim_itree_take_both. i. exists x_src0. exists 0.
              rewrite ! bind_bind.
              mstep. eapply sim_itree_fget_both.
              mstep. eapply sim_itree_fput_both.
              mstep. eapply sim_itree_take_both. i. exists x_src1. exists 0.
              mstep. eapply sim_itree_take_both. i. exists x_src2. exists 0.
              rewrite ! bind_bind.
              mstep. eapply sim_itree_mget_both.
              rewrite ! bind_bind.
              mstep. eapply sim_itree_fget_both.
              rewrite ! bind_bind.
              mstep. eapply sim_itree_take_both. i. split; auto. exists 0.
              rewrite ! bind_ret_l.
              mstep. eapply sim_itree_take_both. i. split; eauto.
              {  eauto.

admit "fix it after changin hcall".
                (* exploit POST; eauto. *)
                (* { erewrite URA.unit_idl. *)
                (*   erewrite URA.add_comm in x_src2. eapply URA.wf_mon in x_src2. *)
                (*   erewrite URA.add_comm in x_src2. eapply URA.wf_mon in x_src2. auto. *)
                (* } *)
                (* { erewrite URA.unit_idl. auto. } *)
              }
              exists 0.
              mstep. eapply sim_itree_ret.
              { unfold wf. esplits; eauto. }
              { unfold liftRR. esplits; eauto. }
            }
            i. rewrite ! bind_ret_l. rewrite ! bind_tau.
            mstep. eapply sim_itree_tau. rewrite ! bind_ret_l.
            destruct st_src1 as [st_src1 fr0'].
            destruct st_tgt1 as [st_tgt1 fr0]. ss. des; subst.
            gbase. eapply CIH; auto. esplits; eauto.
          }
          { rewrite ! bind_bind.
            mstep. eapply sim_itree_choose_both. i; ss. }
        }
        rewrite ! bind_bind. mstep. eapply sim_itree_choose_tgt; ss. eauto with ord_step.
      }
      { des; subst. repeat interp_red. rewrite ! bind_bind. destruct p.
        { cbn.
          mstep. eapply sim_itree_pput_both.
          rewrite ! bind_tau.
          mstep. eapply sim_itree_tau.
          rewrite ! bind_ret_l. gbase. eapply CIH; auto. esplits; eauto.
        }
        { cbn.
          mstep. eapply sim_itree_pget_both.
          rewrite ! bind_tau.
          mstep. eapply sim_itree_tau.
          rewrite ! bind_ret_l. gbase. eapply CIH; auto. esplits; eauto.
        }
      }
      { des; subst. repeat interp_red. rewrite ! bind_bind. destruct e.
        { cbn.
          mstep. eapply sim_itree_choose_both. intros x. exists x.
          eexists. rewrite ! bind_tau.
          mstep. eapply sim_itree_tau.
          rewrite ! bind_ret_l. gbase. eapply CIH; auto. esplits; eauto.
        }
        { cbn.
          mstep. eapply sim_itree_take_both. intros x. exists x.
          eexists. rewrite ! bind_tau.
          mstep. eapply sim_itree_tau.
          rewrite ! bind_ret_l. gbase. eapply CIH; auto. esplits; eauto.
        }
        { cbn.
          mstep. eapply sim_itree_syscall. i. eexists.
          rewrite ! bind_tau.
          mstep. eapply sim_itree_tau.
          rewrite ! bind_ret_l. gbase. eapply CIH; auto. esplits; eauto.
        }
      }
    }
    ii. subst. exists 1.
    unfold fun_to_tgt. ss. des; subst. repeat rewrite HoareFun_parse.
    ginit.
    muclo lordC_spec. econs.
    { instantiate (1:=(1+0)%ord). rewrite Ord.from_nat_O. eapply OrdArith.add_O_r. }
    muclo lbindC_spec. econs; eauto.
    { unfold HoareFunArg, forge, checkWf, assume.
      mstep. eapply sim_itree_take_both.
      intros varg_src. exists varg_src. exists 0.
      mstep. eapply sim_itree_take_both.
      intros x_src. specialize (WEAK x_src). des. exists x_tgt. exists 0.
      mstep. eapply sim_itree_take_both.
      intros rarg. exists rarg. exists 0. rewrite ! bind_bind.
      mstep. eapply sim_itree_fget_both.
      mstep. eapply sim_itree_fput_both.
      mstep. eapply sim_itree_mget_both.
      rewrite ! bind_bind.
      mstep. eapply sim_itree_fget_both. rewrite ! bind_bind.
      mstep. eapply sim_itree_take_both. i. esplit; ss. exists 0.
      rewrite ! bind_ret_l.
      mstep. eapply sim_itree_take_both.
      intros o. exists o. exists 0.
      rewrite ! bind_bind.
      mstep. eapply sim_itree_take_both. i. esplit; eauto.
      { admit "fix it after changin hcall".
        (* subst. exploit PRE; eauto. *)
        (* { erewrite URA.add_comm in x_src0. eapply URA.wf_mon in x_src0. auto. } *)
        (* { erewrite URA.unit_idl. auto. } *)
      }
      exists 0.
      rewrite ! bind_ret_l.
      mstep. eapply sim_itree_ret.
      { unfold wf. esplits; eauto. }

      instantiate (1:=liftRR (fun '(x_src, varg_src, o_src) '(x_tgt, varg_tgt, o_tgt) =>
                                varg_src = varg_tgt /\ o_src = o_tgt /\
                                (<<PRE: forall (arg_src : Y) (arg_tgt : Any.t) (o : ord),
                                    ((precond ftsp_src x_src arg_src arg_tgt o: iProp) -∗
                                                                                       #=> (precond ftsp_tgt x_tgt arg_src arg_tgt o: iProp))>>) /\
                                (<<POST: forall (ret_src : Z) (ret_tgt : Any.t),
                                    (postcond ftsp_tgt x_tgt ret_src ret_tgt: iProp) -∗
                                                                                     #=> (postcond ftsp_src x_src ret_src ret_tgt: iProp)>>))).
      unfold liftRR, wf. esplits; eauto.
    }
    ss. i.
    destruct st_src1 as [w_src fr_src]. destruct st_tgt1 as [w_tgt fr_tgt].
    destruct vret_src as [[x_src varg'] o']. destruct vret_tgt as [[x_tgt varg] o].
    unfold liftRR in SIM. des; subst.
    muclo lordC_spec. econs.
    { instantiate (1:=(0+1)%ord). rewrite Ord.from_nat_O. eapply OrdArith.add_O_l. }
    muclo lbindC_spec.
    econs; eauto.
    { instantiate (1:= liftRR eq). destruct o.
      { muclo lordC_spec. econs.
        { instantiate (1:=(0+1)%ord). rewrite Ord.from_nat_O. eapply OrdArith.add_O_l. }
        muclo lbindC_spec. econs; eauto.
        { eapply SELFSIM; auto. esplits; eauto. }
        { i. ired_both.
          destruct st_src1 as [w_src fr_src0]. destruct st_tgt1 as [w_tgt fr_tgt0].
          unfold liftRR in SIM. des; subst.
          ired_both.
          mstep. eapply sim_itree_choose_both.
          intros vret_src. exists vret_src. exists 0.
          mstep. eapply sim_itree_ret.
          { esplit; eauto. }
          { esplit; eauto. }
        }
      }
      { eapply SELFSIM; auto. esplits; eauto. }
    }
    i. destruct st_src1 as [w_src fr_src1]. destruct st_tgt1 as [w_tgt fr_tgt1].
    unfold liftRR in SIM. des; subst.
    unfold HoareFunRet, discard, put, guarantee.
    mstep. eapply sim_itree_choose_both.
    intros vret_tgt0. exists vret_tgt0. exists 0.
    mstep. eapply sim_itree_choose_both.
    intros (mret, fret). exists (mret, fret). exists 0.
    mstep. rewrite ! bind_bind. eapply sim_itree_mget_both.
    rewrite ! bind_bind.
    mstep. eapply sim_itree_fget_both.
    rewrite ! bind_bind.
    mstep. eapply sim_itree_choose_both. i. esplits; ss.
    rewrite ! bind_ret_l.
    mstep. eapply sim_itree_fput_both.
    mstep. eapply sim_itree_mput_both.
    mstep. eapply sim_itree_choose_both. intros rret. exists rret. exists 20.
    rewrite ! bind_bind.

    mstep. eapply sim_itree_choose_tgt.
    { eauto with ord_step. }
    intros H. mstep. rewrite ! bind_ret_l. eapply sim_itree_fget_tgt.
    { eauto with ord_step. }
    mstep. rewrite ! bind_bind. eapply sim_itree_choose_tgt.
    { eauto with ord_step. }
    i. mstep. rewrite ! bind_bind. eapply sim_itree_choose_tgt.
    { eauto with ord_step. }
    mstep. i. subst. eapply sim_itree_choose_src.
    { eauto with ord_step. }
    split.
    { admit "fix it after changin hcall".
      (* exploit POST; eauto. *)
      (* { erewrite URA.unit_idl. *)
      (*   exploit (x_tgt0 ε). *)
      (*   { erewrite URA.unit_id. auto. } *)
      (*   erewrite URA.unit_id. i. *)
      (*   erewrite URA.add_comm in x1. eapply URA.wf_mon in x1. *)
      (*   eapply URA.wf_mon in x1. auto. *)
      (* } *)
      (* { erewrite URA.unit_idl. auto. } *)
    }
    mstep. rewrite ! bind_ret_l. eapply sim_itree_fget_src.
    { eauto with ord_step. }
    mstep. rewrite ! bind_bind. eapply sim_itree_choose_src.
    { eauto with ord_step. }
    exists x. mstep. rewrite ! bind_bind. eapply sim_itree_choose_src.
    { eauto with ord_step. }
    split; ss.
    steps. exists mret, mp1. split; ss.
    Unshelve. all: exact 0.
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
    { i. admit "ez - wf". }
    i. specialize (WEAK sk). r. eapply adequacy_lift. econs.
    { instantiate (1:=fun '(x, y) => x = y).
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
