Require Import Coqlib AList.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
From Ordinal Require Export Ordinal Arithmetic Inaccessible.
Require Import Any.
Require Import IRed.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import HoareDef.
Require Import List.

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

  Variant safe_bind_clo
          (r: forall R, (R -> Prop) -> itree eventE R -> Prop)
    :
      forall R (safe_reval: R -> Prop) (itr: itree eventE R), Prop
    :=
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

  Definition safe_ret_val: Any.t -> Prop :=
    fun x => finalize x <> None.

  Lemma safe_state_no_ub st (SAFE: @safe_state Any.t safe_ret_val st)
    :
      ~ Beh.of_state L st Tr.ub.
  Proof.
  Admitted.
End LEMMAS.


Section SAFETY.
  Context `{EMSConfig}.
  Context `{Σ: GRA.t}.

  Variable smds: list SafeMod.t.

  Variable stb: gname -> Prop.
  (* Hypothesis stb_sound: *)
  (*   forall fn (IN: stb fn), In fn (flat_map (fun smd => Safesmd *)

  Let mds: list Mod.t := map (SMod.to_src ∘ SafeMod.to_smod stb) smds.
  Hypothesis WF: ModL.wf (Mod.add_list mds).

  Theorem safe_mods_safe:
    ~ Beh.of_program (ModL.compile (Mod.add_list mds)) Tr.ub.
  Proof.
  Admitted.
End SAFETY.
