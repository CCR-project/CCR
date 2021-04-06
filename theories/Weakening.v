Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import SimModSem.

Require Import HTactics.

From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.




Section PROOF.

  Context `{Σ: GRA.t}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).

  Variant fspec_weaker (fsp_src fsp_tgt: fspec): Prop :=
  | fspec_weaker_intro
      mn X_src X_tgt AA AR P_src P_tgt Q_src Q_tgt
      (FSPEC0: fsp_src = @mk _ mn X_src AA AR P_src Q_src)
      (FSPEC1: fsp_tgt = @mk _ mn X_tgt AA AR P_tgt Q_tgt)
      (WEAK: forall (x_src: X_src),
          exists (x_tgt: X_tgt),
            (<<PRE: P_src x_src <4= P_tgt x_tgt>>) /\
            (<<POST: Q_tgt x_tgt <3= Q_src x_src>>))
  .

  Global Program Instance fspec_weaker_PreOrder: PreOrder fspec_weaker.
  Next Obligation.
  Proof.
    ii. destruct x. econs; eauto.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H; inv H0. dependent destruction FSPEC0.
    econs; eauto. i. hexploit WEAK; eauto. i. des.
    hexploit WEAK0; eauto. i. des. esplits; eauto.
  Qed.

  Variable stb_src stb_tgt: list (gname * fspec).
  Hypothesis stb_stronger:
    forall fn fn_tgt fsp_tgt (FINDTGT: List.find (fun '(_fn, _) => dec fn _fn) stb_tgt = Some (fn_tgt, fsp_tgt)),
    exists fn_src fsp_src,
      (<<FINDSRC: List.find (fun '(_fn, _) => dec fn _fn) stb_src = Some (fn_src, fsp_src)>>) /\
      (<<WEAKER: fspec_weaker fsp_tgt fsp_src>>)
  .

  Variable m: mname.

  Variable fn: gname.

  Variable fsp_src fsp_tgt: fspec.
  Hypothesis fsp_weaker: fspec_weaker fsp_src fsp_tgt.

  Hypothesis MNAME: fsp_src.(mn) = m.

  Variable body_src: fsp_src.(AA) -> itree (hCallE +' pE +' eventE) fsp_src.(AR).
  Variable body_tgt: fsp_tgt.(AA) -> itree (hCallE +' pE +' eventE) fsp_tgt.(AR).
  Hypothesis body_eq: JMeq body_src body_tgt.

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists (mr: Σ) (mp: Any.t),
        (<<SRC: mrps_src0 = Maps.add m (mr, mp) Maps.empty>>) /\
        (<<TGT: mrps_tgt0 = Maps.add m (mr, mp) Maps.empty>>)
  .

  Let liftRR: forall (R_src R_tgt: Type) (RR: R_src -> R_tgt -> Prop),
      ((alist mname (Σ * Any.t)) * Σ) -> ((alist mname (Σ * Any.t)) * Σ) ->
      R_src -> R_tgt -> Prop :=
    fun R_src R_tgt RR '(w_src, fr_src) '(w_tgt, fr_tgt) r_src r_tgt =>
      (<<WF: wf (w_src, w_tgt)>>) /\
      (<<FR: fr_src = fr_tgt>>) /\
      RR r_src r_tgt.

  Lemma weakening_fn:
    sim_fsem wf
             (fun_to_tgt stb_src fn (mk_specbody fsp_src body_src))
             (fun_to_tgt stb_tgt fn (mk_specbody fsp_tgt body_tgt)).
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

    assert (SELFSIM: forall R o fr st_src st_tgt
                            (itr: itree (hCallE +' pE +' eventE) R)
                            (WF: wf (st_src, st_tgt)),
               gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) bot6 bot6 R R (liftRR eq) 1 (st_src, fr, interp_hCallE_tgt stb_src mn o itr) (st_tgt, fr, interp_hCallE_tgt stb_tgt mn o itr)).
    { Local Transparent interp_hCallE_tgt.
      unfold interp_hCallE_tgt. gcofix CIH. i. ides itr.
      { repeat interp_red.
        mstep. eapply sim_itree_ret; ss. }
      { repeat interp_red.
        mstep. eapply sim_itree_tau; ss.
        gbase. eapply CIH. eauto. }
      rewrite <- bind_trigger. destruct e as [|[|]]; ss.
      { destruct h. repeat interp_red. cbn.
        unfold unwrapN, triggerNB. rewrite ! bind_bind.
        destruct (find (fun '(_fn, _) => dec fn0 _fn) stb_tgt) eqn:EQ.
        { destruct p. eapply stb_stronger in EQ. des. inv WEAKER.
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
              { instantiate (1:=mp). instantiate (1:=mr). admit "ez". }
              { instantiate (1:=mp). instantiate (1:=mr). admit "ez". }
              rewrite ! bind_bind.
              mstep. eapply sim_itree_fget_both.
              rewrite ! bind_bind.
              mstep. eapply sim_itree_choose_both. i. split; ss. exists 0.
              rewrite ! bind_ret_l.
              mstep. eapply sim_itree_fput_both.
              mstep. eapply sim_itree_mput_both.
              { instantiate (1:=mp). instantiate (1:=mr). admit "ez". }
              { instantiate (1:=mp). instantiate (1:=mr). admit "ez". }
              { ss. }
              { ss. }
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
              mstep. eapply sim_itree_choose_both. i. split; eauto. exists 0.
              rewrite ! bind_ret_l.
              mstep. eapply sim_itree_choose_both. i. split; eauto. exists 0.
              mstep. eapply sim_itree_call.
              { unfold wf. esplits; eauto.
                { instantiate (1:=mp). instantiate (1:=mr0). admit "ez". }
                { admit "ez". }
              }
              i. unfold wf in WF. des; clarify. exists 0.
              mstep. eapply sim_itree_take_both. i. exists x_src0. exists 0.
              rewrite ! bind_bind.
              mstep. eapply sim_itree_fget_both.
              mstep. eapply sim_itree_fput_both.
              mstep. eapply sim_itree_take_both. i. exists x_src1. exists 0.
              rewrite ! bind_bind.
              mstep. eapply sim_itree_mget_both.
              { instantiate (1:=mp0). instantiate (1:=mr1). admit "ez". }
              { instantiate (1:=mp0). instantiate (1:=mr1). admit "ez". }
              rewrite ! bind_bind.
              mstep. eapply sim_itree_fget_both.
              rewrite ! bind_bind.
              mstep. eapply sim_itree_take_both. i. split; auto. exists 0.
              rewrite ! bind_ret_l.
              mstep. eapply sim_itree_take_both. i. split; eauto. exists 0.
              mstep. eapply sim_itree_ret.
              { unfold wf. esplits; eauto. }
              { unfold liftRR. esplits; eauto. }
            }
            i. rewrite ! bind_ret_l. rewrite ! bind_tau.
            mstep. eapply sim_itree_tau. rewrite ! bind_ret_l.
            destruct st_src1 as [st_src1 fr0'].
            destruct st_tgt1 as [st_tgt1 fr0]. ss. des; subst.
            gbase. eapply CIH. esplits; eauto.
          }
          { rewrite ! bind_bind.
            mstep. eapply sim_itree_choose_both. i; ss. }
        }
        rewrite ! bind_bind. mstep. eapply sim_itree_choose_tgt; ss. eauto with ord_step.
      }
      { des; subst. repeat interp_red. rewrite ! bind_bind. destruct p.
        { cbn.
          mstep. eapply sim_itree_pput_both.
          { instantiate (1:=mp). instantiate (1:=mr). admit "ez". }
          { instantiate (1:=mp). instantiate (1:=mr). admit "ez". }
          { ss. }
          { ss. }
          rewrite ! bind_tau.
          mstep. eapply sim_itree_tau.
          rewrite ! bind_ret_l. gbase. eapply CIH. esplits; eauto.
          { instantiate (1:=p). instantiate (1:=mr). admit "ez". }
          { admit "ez". }
        }
        { cbn.
          mstep. eapply sim_itree_pget_both.
          { instantiate (1:=mp). instantiate (1:=mr). admit "ez". }
          { instantiate (1:=mp). instantiate (1:=mr). admit "ez". }
          rewrite ! bind_tau.
          mstep. eapply sim_itree_tau.
          rewrite ! bind_ret_l. gbase. eapply CIH. esplits; eauto.
        }
      }
      { des; subst. repeat interp_red. rewrite ! bind_bind. destruct e.
        { cbn.
          mstep. eapply sim_itree_choose_both. intros x. exists x.
          eexists. rewrite ! bind_tau.
          mstep. eapply sim_itree_tau.
          rewrite ! bind_ret_l. gbase. eapply CIH. esplits; eauto.
        }
        { cbn.
          mstep. eapply sim_itree_take_both. intros x. exists x.
          eexists. rewrite ! bind_tau.
          mstep. eapply sim_itree_tau.
          rewrite ! bind_ret_l. gbase. eapply CIH. esplits; eauto.
        }
        { cbn.
          mstep. eapply sim_itree_syscall. i. eexists.
          rewrite ! bind_tau.
          mstep. eapply sim_itree_tau.
          rewrite ! bind_ret_l. gbase. eapply CIH. esplits; eauto.
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
      { instantiate (1:=mp). instantiate (1:=mr). admit "ez". }
      { instantiate (1:=mp). instantiate (1:=mr). admit "ez". }
      rewrite ! bind_bind.
      mstep. eapply sim_itree_fget_both. rewrite ! bind_bind.
      mstep. eapply sim_itree_take_both. i. esplit; ss. exists 0.
      rewrite ! bind_ret_l.
      mstep. eapply sim_itree_take_both.
      intros o. exists o. exists 0.
      rewrite ! bind_bind.
      mstep. eapply sim_itree_take_both. i. esplit; eauto. exists 0.
      rewrite ! bind_ret_l.
      mstep. eapply sim_itree_ret.
      { unfold wf. esplits; eauto. }
      instantiate (1:=liftRR (fun '(x_src, varg_src, o_src) '(x_tgt, varg_tgt, o_tgt) =>
                                varg_src = varg_tgt /\ o_src = o_tgt /\
                                (<<PRE: P_src x_src <4= P_tgt x_tgt>>) /\
                                (<<POST: Q_tgt x_tgt <3= Q_src x_src>>))).
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
        { eapply SELFSIM. esplits; eauto. }
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
      { eapply SELFSIM. esplits; eauto. }
    }
    i. destruct st_src1 as [w_src fr_src1]. destruct st_tgt1 as [w_tgt fr_tgt1].
    unfold liftRR in SIM. des; subst.
    unfold HoareFunRet, discard, put, guarantee.
    mstep. eapply sim_itree_choose_both.
    intros vret_tgt0. exists vret_tgt0. exists 0.
    mstep. eapply sim_itree_choose_both.
    intros (mret, fret). exists (mret, fret). exists 0.
    mstep. rewrite ! bind_bind. eapply sim_itree_mget_both.
    { instantiate (1:=mp1). instantiate (1:=mr1). admit "ez". }
    { instantiate (1:=mp1). instantiate (1:=mr1). admit "ez". }
    rewrite ! bind_bind.
    mstep. eapply sim_itree_fget_both.
    rewrite ! bind_bind.
    mstep. eapply sim_itree_choose_both. i. esplits; ss.
    rewrite ! bind_ret_l.
    mstep. eapply sim_itree_fput_both.
    mstep. eapply sim_itree_mput_both.
    { instantiate (1:=mp1). instantiate (1:=mr1). admit "ez". }
    { instantiate (1:=mp1). instantiate (1:=mr1). admit "ez". }
    { ss. }
    { ss. }
    mstep. eapply sim_itree_choose_both. intros rret. exists rret. exists 0.
    rewrite ! bind_bind.
    mstep. eapply sim_itree_choose_both. i. esplit; eauto. exists 0.
    rewrite ! bind_ret_l.
    mstep. eapply sim_itree_fget_both.
    rewrite ! bind_bind.
    mstep. eapply sim_itree_choose_both. intros rmod. exists rmod. exists 0.
    rewrite ! bind_bind.
    mstep. eapply sim_itree_choose_both. i. esplits; ss.
    rewrite ! bind_ret_l.
    mstep. eapply sim_itree_fput_both.
    mstep. eapply sim_itree_ret; ss.
    exists mret, mp1. admit "ez".
    Unshelve. all: exact 0.
  Qed.

End PROOF.
