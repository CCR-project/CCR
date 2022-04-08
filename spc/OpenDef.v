Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Export ProofMode.
Require Import HoareDef STB.
Require Import Red IRed.

Set Implicit Arguments.



(*** TODO: remove redundancy ***)
Ltac my_red_both := try (prw _red_gen 2 0); try (prw _red_gen 1 0).

(*** TODO: move to Coqlib ***)
Definition my_if X (b: bool) (x0 x1: X): X := if b then x0 else x1.
Lemma my_if_same: forall X b (x: X), my_if b x x = x. i. destruct b; ss. Qed.



(********************************************* KNOWN ***********************************************)
(********************************************* KNOWN ***********************************************)
(********************************************* KNOWN ***********************************************)

Section AUX.
  Context `{Σ: GRA.t}.

  Record kspecbody := mk_kspecbody {
    ksb_fspec:> fspec;                                            (*** K -> K ***)
    ksb_ubody: (option mname * Any.t) -> itree hEs Any.t;     (*** U -> K ***)
    ksb_kbody: (option mname * Any.t) -> itree hEs Any.t;     (*** K -> K ***)
  }
  .

  Definition ksb_trivial (body: (option mname * Any.t) -> itree hEs Any.t): kspecbody :=
    mk_kspecbody fspec_trivial body body
  .

End AUX.


(* TODO: move it to somewhere *)
Global Program Instance option_Dec A `{Dec A}: Dec (option A).
Next Obligation.
Proof.
  i. destruct a0, a1.
  - destruct (H a a0).
    + left. f_equal. apply e.
    + right. ii. inversion H0. et.
  - right. ss.
  - right. ss.
  - left. refl.
Defined.

Module KModSem.
Section KMODSEM.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    (* fnsems: list (gname * (list val -> itree (oCallE +' pE +' eventE) val)); *)
    fnsems: list (gname * kspecbody);
    mn: mname;
    initial_mr: Σ;
    initial_st: Any.t;
  }
  .

  (************************* TGT ***************************)
  (************************* TGT ***************************)
  (************************* TGT ***************************)

  Definition transl_kCallE_mid: callE ~> callE :=
    fun _ '(Call fn args) => Call fn (Any.pair true↑ args)
  .

  Definition transl_event_mid: hEs ~> hEs :=
    (bimap (id_ _) (bimap transl_kCallE_mid (id_ _)))
  .

  Definition transl_itr_mid: itree hEs ~> itree hEs :=
    fun _ => interp (T:=_) (fun _ e => trigger (transl_event_mid e))
  .

  Definition transl_fun_mid (ktr: (option mname * Any.t) -> itree hEs Any.t):
    (option mname * Any.t) -> itree hEs Any.t :=
    (transl_itr_mid (T:=_)) ∘ ktr
  .

  Definition disclose_mid (fs: fspec): fspec :=
    mk_fspec (meta:=option fs.(meta))
             (fun ox => match ox with | Some x => fs.(measure) x | _ => ord_top end)
             (fun mn ox argh argl =>
                match ox with
                | Some x => (∃ argh', ⌜argh = Any.pair true↑ argh'⌝ ∧ fs.(precond) mn x argh' argl)%I
                | None => (⌜argh = Any.pair false↑ argl⌝)%I
                end)
             (fun mn ox reth retl =>
                map_or_else ox (fun x => (fs.(postcond) mn x reth retl)) (⌜reth = retl⌝)%I)
  .

  Definition disclose_ksb_mid (ksb: kspecbody): fspecbody :=
    mk_specbody (disclose_mid ksb)
                (fun '(mn, argh) =>
                   '(kf, argh) <- (Any.split argh)ǃ;; kf <- kf↓ǃ;;
                   my_if kf
                         (transl_fun_mid ksb.(ksb_kbody) (mn, argh))
                         (transl_fun_mid ksb.(ksb_ubody) (mn, argh)))
  .

  Definition transl_mid (ms: t): SModSem.t := {|
    SModSem.fnsems := List.map (map_snd disclose_ksb_mid) ms.(fnsems);
    SModSem.mn := ms.(mn);
    SModSem.initial_mr := ms.(initial_mr);
    SModSem.initial_st := ms.(initial_st);
  |}
  .



  Variable (_frds: list mname).
  Let frds: list (option mname) := None :: (List.map Some _frds).

  Definition disclose_ksb_src (ksb: kspecbody): option string * Any.t -> itree Es Any.t :=
    fun '(mn, argh) =>
      my_if (@in_dec _ (@option_Dec _ _) mn frds) (* why typeclass search fail... *)
            (body_to_src ksb.(ksb_kbody) (mn, argh))
            (body_to_src ksb.(ksb_ubody) (mn, argh))
  .

  Definition disclose_ksb_tgt (mn: mname) (stb: string -> option fspec)
             (ksb: kspecbody): option string * Any.t -> itree Es Any.t :=
    fun arg =>
      b <- trigger (Take bool);;
      if (b: bool) then
        fun_to_tgt mn stb (mk_specbody ksb.(ksb_fspec) (ksb.(ksb_kbody))) arg
      else
        fun_to_tgt mn stb (mk_specbody fspec_trivial (ksb.(ksb_ubody))) arg
  .

  Definition transl_src (ms: t): ModSem.t := {|
    ModSem.fnsems := List.map (map_snd disclose_ksb_src) ms.(fnsems);
    ModSem.mn := ms.(mn);
    ModSem.initial_st := ms.(initial_st);
  |}
  .

  Definition transl_tgt stb (ms: t): ModSem.t := {|
    ModSem.fnsems := List.map (map_snd (disclose_ksb_tgt ms.(mn) stb)) ms.(fnsems);
    ModSem.mn := ms.(mn);
    ModSem.initial_st := Any.pair ms.(initial_st) ms.(initial_mr)↑
  |}
  .

  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)

  Lemma transl_itr_mid_bind
        (R S: Type)
        (s: itree _ R) (k : R -> itree _ S)
    :
      (transl_itr_mid (s >>= k))
      =
      ((transl_itr_mid s) >>= (fun r => transl_itr_mid (k r))).
  Proof.
    unfold transl_itr_mid in *. grind.
  Qed.

  Lemma transl_itr_mid_tau
        (U: Type)
        (t : itree _ U)
    :
      (transl_itr_mid (Tau t))
      =
      (Tau (transl_itr_mid t)).
  Proof.
    unfold transl_itr_mid in *. grind.
  Qed.

  Lemma transl_itr_mid_ret
        (U: Type)
        (t: U)
    :
      ((transl_itr_mid (Ret t)))
      =
      Ret t.
  Proof.
    unfold transl_itr_mid in *. grind.
  Qed.

  Lemma transl_itr_mid_triggerp
        (R: Type)
        (i: pE R)
    :
      (transl_itr_mid (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr_mid in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_mid_triggere
        (R: Type)
        (i: eventE R)
    :
      (transl_itr_mid (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr_mid in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_mid_call
        (R: Type)
        (i: callE R)
    :
      (transl_itr_mid (trigger i))
      =
      (trigger (transl_kCallE_mid i) >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr_mid in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_mid_hapc
        (R: Type)
        (i: hAPCE R)
    :
      (transl_itr_mid (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr_mid in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_mid_triggerUB
        (R: Type)
    :
      (transl_itr_mid (triggerUB))
      =
      triggerUB (A:=R).
  Proof.
    unfold transl_itr_mid, triggerUB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma transl_itr_mid_triggerNB
        (R: Type)
    :
      (transl_itr_mid (triggerNB))
      =
      triggerNB (A:=R).
  Proof.
    unfold transl_itr_mid, triggerNB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma transl_itr_mid_unwrapU
        (R: Type)
        (i: option R)
    :
      (transl_itr_mid (unwrapU i))
      =
      (unwrapU i).
  Proof.
    unfold transl_itr_mid, unwrapU in *. des_ifs.
    { etrans.
      { eapply transl_itr_mid_ret. }
      { grind. }
    }
    { etrans.
      { eapply transl_itr_mid_triggerUB. }
      { unfold triggerUB. grind. }
    }
  Qed.

  Lemma transl_itr_mid_unwrapN
        (R: Type)
        (i: option R)
    :
      (transl_itr_mid (unwrapN i))
      =
      (unwrapN i).
  Proof.
    unfold transl_itr_mid, unwrapN in *. des_ifs.
    { etrans.
      { eapply transl_itr_mid_ret. }
      { grind. }
    }
    { etrans.
      { eapply transl_itr_mid_triggerNB. }
      { unfold triggerNB. grind. }
    }
  Qed.

  Lemma transl_itr_mid_assume
        P
    :
      (transl_itr_mid (assume P))
      =
      (assume P;;; tau;; Ret tt)
  .
  Proof.
    unfold assume. rewrite transl_itr_mid_bind. rewrite transl_itr_mid_triggere. grind. eapply transl_itr_mid_ret.
  Qed.

  Lemma transl_itr_mid_guarantee
        P
    :
      (transl_itr_mid (guarantee P))
      =
      (guarantee P;;; tau;; Ret tt).
  Proof.
    unfold guarantee. rewrite transl_itr_mid_bind. rewrite transl_itr_mid_triggere. grind. eapply transl_itr_mid_ret.
  Qed.

  Lemma transl_itr_mid_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (transl_itr_mid itr0)
      =
      (transl_itr_mid itr1)
  .
  Proof. subst; et. Qed.

  Global Opaque transl_itr_mid.

End KMODSEM.
End KModSem.



Section RDB.
  Context `{Σ: GRA.t}.

  Global Program Instance ktransl_itr_mid_rdb: red_database (mk_box (@KModSem.transl_itr_mid)) :=
    mk_rdb
      0
      (mk_box KModSem.transl_itr_mid_bind)
      (mk_box KModSem.transl_itr_mid_tau)
      (mk_box KModSem.transl_itr_mid_ret)
      (mk_box KModSem.transl_itr_mid_call)
      (mk_box KModSem.transl_itr_mid_triggere)
      (mk_box KModSem.transl_itr_mid_triggerp)
      (mk_box KModSem.transl_itr_mid_hapc)
      (mk_box KModSem.transl_itr_mid_triggerUB)
      (mk_box KModSem.transl_itr_mid_triggerNB)
      (mk_box KModSem.transl_itr_mid_unwrapU)
      (mk_box KModSem.transl_itr_mid_unwrapN)
      (mk_box KModSem.transl_itr_mid_assume)
      (mk_box KModSem.transl_itr_mid_guarantee)
      (mk_box KModSem.transl_itr_mid_ext)
  .

End RDB.


Module KMod.
Section KMOD.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    get_modsem: Sk.t -> KModSem.t;
    sk: Sk.t;
  }
  .

  Definition get_stb (mds: list t): Sk.t -> alist gname fspec :=
    fun sk => map (map_snd ksb_fspec) (flat_map (KModSem.fnsems ∘ (flip get_modsem sk)) mds).

  Definition get_sk (mds: list t): Sk.t :=
    Sk.sort (fold_right Sk.add Sk.unit (List.map sk mds)).

  Definition get_frds (mds: list t): Sk.t -> list mname :=
    fun sk => (map (KModSem.mn ∘ (flip get_modsem sk)) mds).

  Definition get_initial_mrs (mds: list t): Sk.t -> Σ :=
    fun sk => fold_left (⋅) (List.map (KModSem.initial_mr ∘ (flip get_modsem sk)) mds) ε.

  Definition transl_mid (md: t): SMod.t := {|
    SMod.get_modsem := fun sk => KModSem.transl_mid (md.(get_modsem) sk);
    SMod.sk := md.(sk);
  |}
  .

  Lemma transl_mid_comm: forall md sk, KModSem.transl_mid (md.(get_modsem) sk) =
                                       (transl_mid md).(SMod.get_modsem) sk.
  Proof. i. refl. Qed.

  Definition transl_src (frds: Sk.t -> list mname) (md: t): Mod.t := {|
    Mod.get_modsem := fun sk => KModSem.transl_src (frds sk) (md.(get_modsem) sk);
    Mod.sk := md.(sk);
  |}
  .

  Lemma transl_src_comm: forall md frds sk, KModSem.transl_src (frds sk) (md.(get_modsem) sk) =
                                            (transl_src frds md).(Mod.get_modsem) sk.
  Proof. i. refl. Qed.

  Definition transl_tgt stb (md: t): Mod.t := {|
    Mod.get_modsem := fun sk => KModSem.transl_tgt (stb sk) (md.(get_modsem) sk);
    Mod.sk := md.(sk);
  |}
  .

  Lemma transl_tgt_comm stb: forall md sk, KModSem.transl_tgt (stb sk) (md.(get_modsem) sk) =
                                           (transl_tgt stb md).(Mod.get_modsem) sk.
  Proof. i. refl. Qed.

  Definition transl_tgt_list (mds: list t): list Mod.t :=
    map (transl_tgt (to_closed_stb ∘ get_stb mds)) mds.

  Definition transl_src_list (mds: list t): list Mod.t :=
    map (transl_src (get_frds mds)) mds.
End KMOD.
End KMod.

Arguments in_dec: simpl never.
