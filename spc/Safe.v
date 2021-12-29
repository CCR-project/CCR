Require Import Coqlib AList.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
From Ordinal Require Export Ordinal Arithmetic Inaccessible.
Require Import Any.
Require Import Red IRed.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import SimGlobal.
Require Import HoareDef.
Require Import List.

Local Open Scope nat.

Set Implicit Arguments.


Module SafeModSem.
Section SAFEMODSEM.
  Context `{EMSConfig}.
  Context `{Σ: GRA.t}.

  Variable stb: gname -> Prop.

  CoFixpoint safe_itree: itree hEs Any.t :=
    break <- trigger (Choose _);;
    if break: bool
    then
      ret <- trigger (Choose _);;
      guarantee (finalize ret <> None);;;
      Ret ret
    else
      '(fn, varg) <- trigger (Choose _);;
      guarantee (stb fn);;;
      trigger (Call fn varg);;;
      tau;; safe_itree.

  Lemma safe_itree_red:
    safe_itree =
    break <- trigger (Choose _);;
    if break: bool
    then
      ret <- trigger (Choose _);;
      guarantee (finalize ret <> None);;;
                Ret ret
    else
      '(fn, varg) <- trigger (Choose _);;
      guarantee (stb fn);;;
                trigger (Call fn varg);;;
                tau;; safe_itree.
  Proof.
    eapply itree_eta_eq. ss.
  Qed.

  Definition safe_specbody (fsp: fspec): fspecbody :=
    mk_specbody fsp (fun _ => safe_itree).

  Record t: Type := mk {
    fnsems: list (gname * fspec);
    mn: mname;
    initial_mr: Σ;
    initial_st: Any.t;
  }
  .

  Definition to_smodsem (md: t): SModSem.t :=
    {|
    SModSem.fnsems := map (map_snd safe_specbody) md.(fnsems);
    SModSem.mn := md.(mn);
    SModSem.initial_mr := md.(initial_mr);
    SModSem.initial_st := md.(initial_st);
    |}.
End SAFEMODSEM.
End SafeModSem.
Coercion SafeModSem.to_smodsem: SafeModSem.t >-> SModSem.t.

Module SafeMod.
Section SAFEMOD.
  Context `{EMSConfig}.
  Context `{Σ: GRA.t}.

  Variable stb: gname -> Prop.

  Record t: Type := mk {
    get_modsem: Sk.t -> SafeModSem.t;
    sk: Sk.t;
  }
  .

  Definition to_smod (md: t): SMod.t :=
    {|
    SMod.get_modsem := SafeModSem.to_smodsem stb ∘ md.(get_modsem);
    SMod.sk := md.(sk)
    |}.
End SAFEMOD.
End SafeMod.
Coercion SafeMod.to_smod: SafeMod.t >-> SMod.t.


Section LEMMAS.
  Context `{EMSConfig}.

  Variable prog: ModL.t.
  Let L := ModL.compile prog.

  Variant _safe_state
          (safe_state: forall R, (R -> Prop) -> itree eventE R -> Prop)
          R (safe_retval: R -> Prop):
    forall (itr: itree eventE R), Prop :=
  | safe_state_ret
      (ret: R)
      (SAFE: safe_retval ret)
    :
      _safe_state safe_state safe_retval (Ret ret)
  | safe_state_tau
      (itr: itree eventE R)
      (SAFE: safe_state R safe_retval itr)
    :
      _safe_state safe_state safe_retval (tau;; itr)
  | safe_state_choose
      X (ktr: X -> itree eventE R)
      (SAFE: forall x, safe_state R safe_retval (ktr x))
    :
      _safe_state safe_state safe_retval (trigger (Choose X) >>= ktr)
  | safe_state_take
      X (ktr: X -> itree eventE R)
      (SAFE: exists x, safe_state R safe_retval (ktr x))
    :
      _safe_state safe_state safe_retval (trigger (Take X) >>= ktr)
  .

  Lemma safe_state_mon: monotone3 _safe_state.
  Proof.
    ii. inv IN; et.
    { econs 1; et. }
    { econs 2; et. }
    { econs 3; et. }
    { des. econs 4; et. }
  Qed.
  Hint Resolve safe_state_mon: paco.

  Definition safe_state := paco3 _safe_state bot3.
  Arguments safe_state [_] _ _.

  Variant safe_bind_clo
          (r: forall R, (R -> Prop) -> itree eventE R -> Prop)
    :
      forall R (safe_reval: R -> Prop) (itr: itree eventE R), Prop :=
  | safe_bind_clo_intro
      R0 R1
      (itr: itree eventE R0) (ktr: R0 -> itree eventE R1)
      safe_retval0 safe_retval1
      (SAFE0: r R0 safe_retval0 itr)
      (SAFE1: forall x (SAFE: safe_retval0 x),
          r R1 safe_retval1 (ktr x))
    :
      safe_bind_clo r safe_retval1 (itr >>= ktr)
  .

  Lemma safe_bind_clo_mon: monotone3 safe_bind_clo.
  Proof.
    ii. destruct IN. econs; et.
  Qed.
  Hint Resolve safe_bind_clo_mon: paco.

  Lemma safe_bind_clo_wrespectful: wrespectful3 (_safe_state) safe_bind_clo.
  Proof.
    econs; eauto with paco.
    ii. destruct PR. hexploit GF; et. i. inv H0.
    { rewrite bind_ret_l. eapply safe_state_mon; et.
      i. eapply rclo3_base. et. }
    { rewrite bind_tau. econs.
      eapply rclo3_clo. econs.
      { eapply rclo3_base. et. }
      { i. eapply rclo3_base. et. }
    }
    { rewrite bind_bind. econs. i.
      eapply rclo3_clo. econs.
      { eapply rclo3_base. et. }
      { i. eapply rclo3_base. et. }
    }
    { des. rewrite bind_bind. econs. exists x.
      eapply rclo3_clo. econs.
      { eapply rclo3_base. et. }
      { i. eapply rclo3_base. et. }
    }
  Qed.

  Lemma safe_bind_clo_spec: safe_bind_clo <4= gupaco3 _safe_state (cpn3 _safe_state).
  Proof.
    intros. eapply wrespect3_uclo; eauto with paco.
    eapply safe_bind_clo_wrespectful.
  Qed.

  Definition safe_retval: Any.t -> Prop :=
    fun x => finalize x <> None.

  Lemma safe_state_no_ub st (SAFE: safe_state safe_retval st)
    :
      ~ Beh.of_state L st Tr.ub.
  Proof.
    ii. punfold H0. remember Tr.ub. revert Heqt SAFE.
    induction H0 using Beh.of_state_ind; ss.
    { i. inv STEP. des. clarify. eapply IH; auto.
      punfold SAFE. inv SAFE.
      { unfold ModSemL.state_sort in SRT. ss. des_ifs. }
      { eapply step_tau_iff in STEP. des; subst. inv SAFE0; ss. }
      { eapply step_trigger_choose_iff in STEP. des; subst.
        specialize (SAFE0 x). inv SAFE0; ss. }
      { unfold ModSemL.state_sort in SRT. ss. }
    }
    { i. punfold SAFE. inv SAFE.
      { unfold ModSemL.state_sort in SRT. ss. des_ifs. }
      { unfold ModSemL.state_sort in SRT. ss. }
      { unfold ModSemL.state_sort in SRT. ss. }
      { des. inv SAFE0; ss. exploit STEP.
        { eapply step_trigger_take. }
        { i. des; clarify. eapply IH; et. }
      }
    }
  Qed.
End LEMMAS.
Hint Resolve safe_state_mon: paco.
Hint Resolve safe_bind_clo_mon: paco.


Section SAFETY.
  Context `{EMSConfig}.
  Context `{Σ: GRA.t}.

  Variable smds: list SafeMod.t.
  Variable stb: gname -> Prop.

  Let mds: list Mod.t := map (SMod.to_src ∘ SafeMod.to_smod stb) smds.
  Hypothesis WF: ModL.wf (Mod.add_list mds).

  Hypothesis stb_sound:
    forall fn (IN: stb fn),
      In fn (map fst (ModL.enclose (Mod.add_list mds)).(ModSemL.fnsems)).
  Hypothesis MAIN:
    stb "main".

  Ltac ired := try (prw _red_gen 1 0).
  Ltac step :=
    unfold assume, guarantee, unwrapN, triggerUB, triggerNB;
    ired;
    try (gstep; econs)
  .
  Ltac steps := repeat (step; i).


  Lemma fnsems_find_safe fn
    :
      alist_find fn (ModSemL.fnsems (ModL.enclose (Mod.add_list mds))) = None \/
      exists mn,
        alist_find fn (ModSemL.fnsems (ModL.enclose (Mod.add_list mds)))
        =
        Some (transl_all (T:=_) mn ∘ fun_to_src (fun _ => SafeModSem.safe_itree stb)).
  Proof.
    unfold ModL.enclose, mds. unfold Sk.canon. ss.
    change (alist string Sk.gdef) with Sk.t.
    generalize (Sk.sort (ModL.sk (Mod.add_list (map (SMod.to_src ∘ SafeMod.to_smod stb) smds)))).
    i. rewrite ! Mod.add_list_fnsems.
    rewrite <- fold_right_app_flat_map. rewrite ! flat_map_map.
    generalize smds. induction smds0; ss; auto.
    rewrite ! alist_find_app_o. rewrite ! alist_find_map_snd. uo.
    change (fun '(fn0, sb) => (fn0: string, fun_to_src (fsb_body sb))) with
        (map_snd (A:=string) (fun_to_src ∘ fsb_body)).
    rewrite ! alist_find_map_snd. uo.
    des_ifs. right. esplits; et.
  Qed.

  Lemma call_safe:
    forall md fn arg st
           (IN: stb fn),
      paco3 _safe_state bot3 _
            (fun '(st, retv) => safe_retval retv)
            (EventsL.interp_Es
               (ModSemL.prog (ModL.enclose (Mod.add_list mds)))
               (ModSemL.prog (ModL.enclose (Mod.add_list mds))
                             (EventsL.Call md fn arg)) st).
  Proof.
    ginit. gcofix CIH. i. steps.
    hexploit stb_sound; et. i.
    eapply in_map_iff in H0. des. destruct x. clarify.
    unfold unwrapU. des_ifs.
    2: { exfalso. eapply alist_find_none in Heq; et. }
    Local Opaque ModSemL.prog. ss.
    hexploit (fnsems_find_safe s). i. des; clarify. steps.
    guclo safe_bind_clo_spec. econs.
    { instantiate (1:=fun '(st, retv) => safe_retval retv).
      unfold fun_to_src, body_to_src. generalize st. gcofix CIH0. i.
      rewrite SafeModSem.safe_itree_red. steps. i. destruct x.
      { steps. ss. }
      { steps. destruct x. steps. guclo safe_bind_clo_spec. econs.
        { gbase. eapply CIH. et. }
        { i. destruct x0. steps. gbase. eapply CIH0. }
      }
    }
    { i. destruct x. steps. auto. }
  Qed.

  Theorem safe_mods_safe:
    ~ Beh.of_program (ModL.compile (Mod.add_list mds)) Tr.ub.
  Proof.
    eapply safe_state_no_ub. ginit.
    ss. unfold ModSemL.initial_itr.
    step. unshelve esplits; et. unfold ITree.map. steps.
    guclo safe_bind_clo_spec. econs.
    { gfinal. right. eapply call_safe. auto. }
    i. destruct x. steps. ss.
  Qed.
End SAFETY.
