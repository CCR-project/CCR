Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic.
Require Import TODO.
(* Require Import Mem0 MemOpen. *)
Require Import HoareDef.
Require Import Red IRed.

Set Implicit Arguments.


(* Definition dot {A B C} (g: B -> C) (f: A -> B): A -> C := g ∘ f. *)
(* Notation "(∘)" := dot (at level 40, left associativity). *)
Notation "(∘)" := (fun g f => g ∘ f) (at level 0, left associativity).

(*** TODO: remove redundancy with SimModSemL && migrate related lemmas ***)
Variant option_rel A B (P: A -> B -> Prop): option A -> option B -> Prop :=
| option_rel_some
    a b (IN: P a b)
  :
    option_rel P (Some a) (Some b)
| option_rel_none
  :
    option_rel P None None
.
Hint Constructors option_rel: core.


Section AUX.
  Context `{Σ: GRA.t}.
  Definition fspec_trivial: fspec := (mk_simple (fun (_: unit) => (fun _ o => (⌜o = ord_top⌝: iProp)%I, fun _ => (⌜True⌝: iProp)%I))).

  (*** U should always be called with "inr"; I use sum type just in order to unify type with KMod ***)
  Definition fspec_trivial2: fspec :=
    @mk _ unit (unit + list val)%type (val)
        (fun _ argh argl o => (⌜exists vargs, argl↓ = Some vargs /\ argh = inr vargs /\ o = ord_top⌝: iProp)%I)
        (fun _ reth retl => (⌜reth↑ = retl⌝: iProp)%I)
  .

End AUX.


(*** TODO: remove redundancy ***)
Ltac my_red_both := try (prw _red_gen 2 0); try (prw _red_gen 1 0).



(******************************************* UNKNOWN ***********************************************)
(******************************************* UNKNOWN ***********************************************)
(******************************************* UNKNOWN ***********************************************)
Section AUX.
  Variant uCallE: Type -> Type :=
  | uCall (fn: gname) (varg: list val): uCallE Any.t
  .
End AUX.

Module UModSem.
Section UMODSEM.

  Context `{Σ: GRA.t}.

  (**** TODO: maybe "val" is more appropriate return type??? Check this later ****)
  (**** TODO: maybe "val" is more appropriate return type??? Check this later ****)
  (**** TODO: maybe "val" is more appropriate return type??? Check this later ****)
  (**** TODO: maybe "val" is more appropriate return type??? Check this later ****)
  (**** TODO: maybe "val" is more appropriate return type??? Check this later ****)
  (**** TODO: maybe "val" is more appropriate return type??? Check this later ****)

  Record t: Type := mk {
    fnsems: list (gname * (list val -> itree (uCallE +' pE +' eventE) val));
    mn: mname;
    initial_st: Any.t;
  }
  .

  (************************* MOD ***************************)
  (************************* MOD ***************************)
  (************************* MOD ***************************)

  Definition transl_uCallE_mod: uCallE ~> callE :=
    fun T '(uCall fn args) => Call fn args↑
  .

  Definition transl_event_mod: (uCallE +' pE +' eventE) ~> (callE +' pE +' eventE) :=
    (bimap transl_uCallE_mod (bimap (id_ _) (id_ _)))
  .

  Definition transl_itr_mod: itree (uCallE +' pE +' eventE) ~> itree Es :=
    fun _ itr => resum_itr (E:=callE +' pE +' eventE) (F:=Es)
                           (interp (T:=_) (fun _ e => trigger (transl_event_mod e)) itr)
  .

  Definition transl_fun_mod: (list val -> itree (uCallE +' pE +' eventE) val) -> (Any.t -> itree Es Any.t) :=
    fun ktr => cfun (transl_itr_mod (T:=val) ∘ ktr)
  .

  Definition to_modsem (ms: t): ModSem.t := {|
    (* ModSem.fnsems := List.map (map_snd (((∘)∘(∘)) (resum_itr (T:=Any.t)) cfun)) ms.(fnsems); *)
    ModSem.fnsems := List.map (map_snd transl_fun_mod) ms.(fnsems);
    ModSem.mn := ms.(mn);
    ModSem.initial_mr := ε;
    ModSem.initial_st := ms.(initial_st);
  |}
  .

  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)

  Lemma transl_itr_mod_bind
        (R S: Type)
        (s: itree (uCallE +' pE +' eventE) R) (k : R -> itree (uCallE +' pE +' eventE) S)
    :
      (transl_itr_mod (s >>= k))
      =
      ((transl_itr_mod s) >>= (fun r => transl_itr_mod (k r))).
  Proof.
    unfold transl_itr_mod in *. grind. my_red_both. grind.
  Qed.

  Lemma transl_itr_mod_tau
        (U: Type)
        (t : itree _ U)
    :
      (transl_itr_mod (Tau t))
      =
      (Tau (transl_itr_mod t)).
  Proof.
    unfold transl_itr_mod in *. grind. my_red_both. grind.
  Qed.

  Lemma transl_itr_mod_ret
        (U: Type)
        (t: U)
    :
      ((transl_itr_mod (Ret t)))
      =
      Ret t.
  Proof.
    unfold transl_itr_mod in *. grind. my_red_both. grind.
  Qed.

  Lemma transl_itr_mod_triggerp
        (R: Type)
        (i: pE R)
    :
      (transl_itr_mod (trigger i))
      =
      (trigger i >>= (fun r => tau;; tau;; Ret r)).
  Proof.
    unfold transl_itr_mod in *.
    repeat rewrite interp_trigger. repeat (my_red_both; grind; resub).
  Qed.

  Lemma transl_itr_mod_triggere
        (R: Type)
        (i: eventE R)
    :
      (transl_itr_mod (trigger i))
      =
      (trigger i >>= (fun r => tau;; tau;; Ret r)).
  Proof.
    unfold transl_itr_mod in *.
    repeat rewrite interp_trigger. repeat (my_red_both; grind; resub).
  Qed.

  Lemma transl_itr_mod_ucall
        (R: Type)
        (i: uCallE R)
    :
      (transl_itr_mod (trigger i))
      =
      (trigger (transl_uCallE_mod i) >>= (fun r => tau;; tau;; Ret r)).
  Proof.
    unfold transl_itr_mod in *.
    repeat rewrite interp_trigger. repeat (my_red_both; grind; resub).
  Qed.

  Lemma transl_itr_mod_triggerUB
        (R: Type)
    :
      (transl_itr_mod (triggerUB))
      =
      triggerUB (A:=R).
  Proof.
    unfold transl_itr_mod, triggerUB in *. rewrite unfold_interp. cbn. repeat (my_red_both; grind; resub).
  Qed.

  Lemma transl_itr_mod_triggerNB
        (R: Type)
    :
      (transl_itr_mod (triggerNB))
      =
      triggerNB (A:=R).
  Proof.
    unfold transl_itr_mod, triggerNB in *. rewrite unfold_interp. cbn. repeat (my_red_both; grind; resub).
  Qed.

  Lemma transl_itr_mod_unwrapU
        (R: Type)
        (i: option R)
    :
      (transl_itr_mod (unwrapU i))
      =
      (unwrapU i).
  Proof.
    unfold transl_itr_mod, unwrapU in *. des_ifs.
    { etrans.
      { eapply transl_itr_mod_ret. }
      { grind. }
    }
    { etrans.
      { eapply transl_itr_mod_triggerUB. }
      { unfold triggerUB. grind. }
    }
  Qed.

  Lemma transl_itr_mod_unwrapN
        (R: Type)
        (i: option R)
    :
      (transl_itr_mod (unwrapN i))
      =
      (unwrapN i).
  Proof.
    unfold transl_itr_mod, unwrapN in *. des_ifs.
    { etrans.
      { eapply transl_itr_mod_ret. }
      { grind. }
    }
    { etrans.
      { eapply transl_itr_mod_triggerNB. }
      { unfold triggerNB. grind. }
    }
  Qed.

  Lemma transl_itr_mod_assume
        P
    :
      (transl_itr_mod (assume P))
      =
      (assume P;;; tau;; tau;; Ret tt)
  .
  Proof.
    unfold assume. rewrite transl_itr_mod_bind. rewrite transl_itr_mod_triggere.
    repeat (my_red_both; grind; resub).
    eapply transl_itr_mod_ret.
  Qed.

  Lemma transl_itr_mod_guarantee
        P
    :
      (transl_itr_mod (guarantee P))
      =
      (guarantee P;;; tau;; tau;; Ret tt).
  Proof.
    unfold guarantee. rewrite transl_itr_mod_bind. rewrite transl_itr_mod_triggere.
    repeat (my_red_both; grind; resub).
    eapply transl_itr_mod_ret.
  Qed.

  Lemma transl_itr_mod_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (transl_itr_mod itr0)
      =
      (transl_itr_mod itr1)
  .
  Proof. subst; et. Qed.












  (************************* SMOD ***************************)
  (************************* SMOD ***************************)
  (************************* SMOD ***************************)

  Definition transl_uCallE_smod: uCallE ~> hCallE :=
    fun T '(uCall fn args) => hCall false fn (@inr unit _ args)↑
  .

  Definition transl_event_smod: (uCallE +' pE +' eventE) ~> (hCallE +' pE +' eventE) :=
    (bimap transl_uCallE_smod (bimap (id_ _) (id_ _)))
  .

  Definition transl_itr_smod: itree (uCallE +' pE +' eventE) ~> itree (hCallE +' pE +' eventE) :=
    (* embed ∘ transl_event *) (*** <- it works but it is not handy ***)
    fun _ => interp (T:=_) (fun _ e => trigger (transl_event_smod e))
    (* fun _ => translate (T:=_) transl_event  *)
  .

  Definition transl_fun_smod (ktr: list val -> itree (uCallE +' pE +' eventE) val):
    (unit + list val -> itree (hCallE +' pE +' eventE) val) :=
    (fun vargs => match vargs with
                  | inl _ => triggerNB
                  | inr vargs => (transl_itr_smod (T:=_) (ktr vargs))
                  end)
  .

  Definition transl_fsb_smod: (list val -> itree (uCallE +' pE +' eventE) val) -> fspecbody :=
    fun ktr =>
      (* mk_specbody fspec_trivial2 (fun '(vargs, _) => interp (T:=val) transl_itr (ktr vargs)) *)
      (* mk_specbody fspec_trivial2 (transl_itr_smod (T:=_) ∘ ktr) *)
      mk_specbody fspec_trivial2 (transl_fun_smod ktr)
  .

  Definition to_smodsem (ms: t): SModSem.t := {|
    SModSem.fnsems := List.map (map_snd transl_fsb_smod) ms.(fnsems);
    SModSem.mn := ms.(mn);
    SModSem.initial_mr := ε;
    SModSem.initial_st := ms.(initial_st);
  |}
  .

  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)

  Lemma transl_itr_smod_bind
        (R S: Type)
        (s: itree (uCallE +' pE +' eventE) R) (k : R -> itree (uCallE +' pE +' eventE) S)
    :
      (transl_itr_smod (s >>= k))
      =
      ((transl_itr_smod s) >>= (fun r => transl_itr_smod (k r))).
  Proof.
    unfold transl_itr_smod in *. grind.
  Qed.

  Lemma transl_itr_smod_tau
        (U: Type)
        (t : itree _ U)
    :
      (transl_itr_smod (Tau t))
      =
      (Tau (transl_itr_smod t)).
  Proof.
    unfold transl_itr_smod in *. grind.
  Qed.

  Lemma transl_itr_smod_ret
        (U: Type)
        (t: U)
    :
      ((transl_itr_smod (Ret t)))
      =
      Ret t.
  Proof.
    unfold transl_itr_smod in *. grind.
  Qed.

  Lemma transl_itr_smod_triggerp
        (R: Type)
        (i: pE R)
    :
      (transl_itr_smod (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr_smod in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_smod_triggere
        (R: Type)
        (i: eventE R)
    :
      (transl_itr_smod (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr_smod in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_smod_ucall
        (R: Type)
        (i: uCallE R)
    :
      (transl_itr_smod (trigger i))
      =
      (trigger (transl_uCallE_smod i) >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr_smod in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_smod_triggerUB
        (R: Type)
    :
      (transl_itr_smod (triggerUB))
      =
      triggerUB (A:=R).
  Proof.
    unfold transl_itr_smod, triggerUB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma transl_itr_smod_triggerNB
        (R: Type)
    :
      (transl_itr_smod (triggerNB))
      =
      triggerNB (A:=R).
  Proof.
    unfold transl_itr_smod, triggerNB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma transl_itr_smod_unwrapU
        (R: Type)
        (i: option R)
    :
      (transl_itr_smod (unwrapU i))
      =
      (unwrapU i).
  Proof.
    unfold transl_itr_smod, unwrapU in *. des_ifs.
    { etrans.
      { eapply transl_itr_smod_ret. }
      { grind. }
    }
    { etrans.
      { eapply transl_itr_smod_triggerUB. }
      { unfold triggerUB. grind. }
    }
  Qed.

  Lemma transl_itr_smod_unwrapN
        (R: Type)
        (i: option R)
    :
      (transl_itr_smod (unwrapN i))
      =
      (unwrapN i).
  Proof.
    unfold transl_itr_smod, unwrapN in *. des_ifs.
    { etrans.
      { eapply transl_itr_smod_ret. }
      { grind. }
    }
    { etrans.
      { eapply transl_itr_smod_triggerNB. }
      { unfold triggerNB. grind. }
    }
  Qed.

  Lemma transl_itr_smod_assume
        P
    :
      (transl_itr_smod (assume P))
      =
      (assume P;;; tau;; Ret tt)
  .
  Proof.
    unfold assume. rewrite transl_itr_smod_bind. rewrite transl_itr_smod_triggere. grind. eapply transl_itr_smod_ret.
  Qed.

  Lemma transl_itr_smod_guarantee
        P
    :
      (transl_itr_smod (guarantee P))
      =
      (guarantee P;;; tau;; Ret tt).
  Proof.
    unfold guarantee. rewrite transl_itr_smod_bind. rewrite transl_itr_smod_triggere. grind. eapply transl_itr_smod_ret.
  Qed.

  Lemma transl_itr_smod_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (transl_itr_smod itr0)
      =
      (transl_itr_smod itr1)
  .
  Proof. subst; et. Qed.

End UMODSEM.
End UModSem.

Section RDB.
  Context `{Σ: GRA.t}.

  Global Program Instance transl_itr_mod_rdb: red_database (mk_box (@UModSem.transl_itr_mod)) :=
    mk_rdb
      0
      (mk_box UModSem.transl_itr_mod_bind)
      (mk_box UModSem.transl_itr_mod_tau)
      (mk_box UModSem.transl_itr_mod_ret)
      (mk_box UModSem.transl_itr_mod_ucall)
      (mk_box UModSem.transl_itr_mod_triggere)
      (mk_box UModSem.transl_itr_mod_triggerp)
      (mk_box True)
      (mk_box UModSem.transl_itr_mod_triggerUB)
      (mk_box UModSem.transl_itr_mod_triggerNB)
      (mk_box UModSem.transl_itr_mod_unwrapU)
      (mk_box UModSem.transl_itr_mod_unwrapN)
      (mk_box UModSem.transl_itr_mod_assume)
      (mk_box UModSem.transl_itr_mod_guarantee)
      (mk_box UModSem.transl_itr_mod_ext)
  .

  Global Program Instance transl_itr_smod_rdb: red_database (mk_box (@UModSem.transl_itr_smod)) :=
    mk_rdb
      0
      (mk_box UModSem.transl_itr_smod_bind)
      (mk_box UModSem.transl_itr_smod_tau)
      (mk_box UModSem.transl_itr_smod_ret)
      (mk_box UModSem.transl_itr_smod_ucall)
      (mk_box UModSem.transl_itr_smod_triggere)
      (mk_box UModSem.transl_itr_smod_triggerp)
      (mk_box True)
      (mk_box UModSem.transl_itr_smod_triggerUB)
      (mk_box UModSem.transl_itr_smod_triggerNB)
      (mk_box UModSem.transl_itr_smod_unwrapU)
      (mk_box UModSem.transl_itr_smod_unwrapN)
      (mk_box UModSem.transl_itr_smod_assume)
      (mk_box UModSem.transl_itr_smod_guarantee)
      (mk_box UModSem.transl_itr_smod_ext)
  .
End RDB.




Module UMod.
Section UMOD.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    get_modsem: Sk.t -> UModSem.t;
    sk: Sk.t;
  }
  .

  Definition to_mod (md: t): Mod.t := {|
    Mod.get_modsem := UModSem.to_modsem ∘ md.(get_modsem);
    Mod.sk := md.(sk);
  |}
  .

  Lemma to_mod_comm: forall md skenv, UModSem.to_modsem (md.(get_modsem) skenv) = (to_mod md).(Mod.get_modsem) skenv.
  Proof. i. refl. Qed.


  Definition to_smod (md: t): SMod.t := {|
    SMod.get_modsem := UModSem.to_smodsem ∘ md.(get_modsem);
    SMod.sk := md.(sk);
  |}
  .

  Lemma to_smod_comm: forall md skenv, UModSem.to_smodsem (md.(get_modsem) skenv) = (to_smod md).(SMod.get_modsem) skenv.
  Proof. i. refl. Qed.

End UMOD.
End UMod.





















(********************************************* KNOWN ***********************************************)
(********************************************* KNOWN ***********************************************)
(********************************************* KNOWN ***********************************************)

  (* Definition disclose_smodsem (ms: SModSem.t): SModSem.t := {| *)
  (*   SModSem.fnsems     := List.map (map_snd disclose_fsb) ms.(SModSem.fnsems); *)
  (*   SModSem.mn         := ms.(SModSem.mn); *)
  (*   SModSem.initial_mr := ms.(SModSem.initial_mr); *)
  (*   SModSem.initial_st := ms.(SModSem.initial_st); *)
  (* |} *)
  (* . *)

  (* Definition disclose_smod (ms: SMod.t): SMod.t := {| *)
  (*   SMod.get_modsem := disclose_smodsem ∘ ms.(SMod.get_modsem); *)
  (*   SMod.sk := ms.(SMod.sk); *)
  (* |} *)
  (* . *)

Section AUX.
  Context `{Σ: GRA.t}.

  Variant kCallE: Type -> Type :=
  | kCall (fn: gname) (varg: unit + list val): kCallE Any.t
  .

  Record kspecbody := mk_kspecbody {
    ksb_fspec:> ftspec unit unit;                               (*** K -> K ***)
    ksb_body: list val -> itree (kCallE +' pE +' eventE) val;   (*** U -> K ***)
  }
  .

  Definition mk_ksimple {X: Type} (PQ: X -> ((Any.t -> ord -> iProp) * (Any.t -> iProp))):
    ftspec unit unit := @mk_ftspec _ _ _ X (fun x _ a o => (fst ∘ PQ) x a o) (fun x _ a => (snd ∘ PQ) x a)
  .

  Definition kspec_trivial_bottom: ftspec unit unit :=
    (mk_ksimple (fun (_: unit) => ((fun _ _ => (⌜False⌝: iProp)%I),
                                   (fun _ => (⌜True⌝: iProp)%I))))
  .

  Program Fixpoint _APCK (at_most: Ord.t) {wf Ord.lt at_most}: itree (kCallE +' pE +' eventE) unit :=
    break <- trigger (Choose _);;
    if break: bool
    then Ret tt
    else
      n <- trigger (Choose Ord.t);;
      trigger (Choose (n < at_most)%ord);;;
      fn <- trigger (Choose _);;
      trigger (kCall fn (inl tt));;;
      _APCK n.
  Next Obligation. ss. Qed.
  Next Obligation. eapply Ord.lt_well_founded. Qed.

  Definition APCK: itree (kCallE +' pE +' eventE) unit :=
    at_most <- trigger (Choose _);;
    guarantee(at_most < kappa)%ord;;;
    _APCK at_most
  .

  Lemma unfold_APCK:
    forall at_most, _APCK at_most =
                    break <- trigger (Choose _);;
                    if break: bool
                    then Ret tt
                    else
                      n <- trigger (Choose Ord.t);;
                      guarantee (n < at_most)%ord;;;
                      fn <- trigger (Choose _);;
                      trigger (kCall fn (inl tt));;;
                      _APCK n.
  Proof.
    i. unfold _APCK. rewrite Fix_eq; eauto.
    { repeat f_equal. extensionality break. destruct break; ss.
      repeat f_equal. extensionality n.
      unfold guarantee. rewrite bind_bind.
      repeat f_equal. extensionality p.
      rewrite bind_ret_l. repeat f_equal. }
    { i. replace g with f; auto. extensionality o. eapply H. }
  Qed.
  Global Opaque _APCK.

End AUX.

Module KModSem.
Section KMODSEM.

  Context `{Σ: GRA.t}.

  (*** K -> K: unit; tbr == true ***)
  (*** K -> U: list val; tbr == false ***)
  (**** TODO: maybe "val" is more appropriate return type??? Check this later ****)
  (**** TODO: maybe "val" is more appropriate return type??? Check this later ****)
  (**** TODO: maybe "val" is more appropriate return type??? Check this later ****)
  (**** TODO: maybe "val" is more appropriate return type??? Check this later ****)
  (**** TODO: maybe "val" is more appropriate return type??? Check this later ****)
  (**** TODO: maybe "val" is more appropriate return type??? Check this later ****)
  (**** TODO: maybe "val" is more appropriate return type??? Check this later ****)

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

  Definition disclose (fs: ftspec unit unit): fspec :=
    @HoareDef.mk _ (option fs.(X)) (unit + list val)%type val
                 (fun ox argh argl o =>
                    match ox, argh with
                    | Some x, inl argh => ((fs.(precond) x argh argl o: iProp) ** ⌜is_pure o⌝)%I
                    | None, inr varg => (⌜varg↑ = argl /\ o = ord_top⌝: iProp)%I
                    | _, _ => (⌜False⌝: iProp)%I
                    end)
                 (fun ox reth retl =>
                    match ox with
                    | Some x => fs.(postcond) x tt retl
                    | None => (⌜reth↑ = retl⌝: iProp)%I
                    end)
  .

  Definition transl_kCallE_tgt: kCallE ~> hCallE :=
    fun T '(kCall fn args) => match args with
                              | inl _ => hCall true fn args↑
                              | inr _ => hCall false fn args↑
                              end
  .

  Definition transl_event_tgt: (kCallE +' pE +' eventE) ~> (hCallE +' pE +' eventE) :=
    (bimap transl_kCallE_tgt (bimap (id_ _) (id_ _)))
  .

  Definition transl_itr_tgt: itree (kCallE +' pE +' eventE) ~> itree (hCallE +' pE +' eventE) :=
    fun _ => interp (T:=_) (fun _ e => trigger (transl_event_tgt e))
  .

  Definition transl_fun_tgt (ktr: list val -> itree (kCallE +' pE +' eventE) val):
    (unit + list val) -> itree (hCallE +' pE +' eventE) val :=
    (fun argh => match argh with
                 (*** K -> K ***)
                 (*** YJ: We may generalize this to APC ***)
                 (*** YJ: We may further generalize this to any pure itree without pE ***)
                 | inl _ => trigger (Choose _)
                 (*** U -> K ***)
                 | inr varg => transl_itr_tgt (ktr varg)
                 end)
  .

  Definition disclose_ksb (ksb: kspecbody): fspecbody :=
    mk_specbody (disclose ksb) (transl_fun_tgt ksb.(ksb_body))
  .

  Definition to_tgt (ms: t): SModSem.t := {|
    SModSem.fnsems := List.map (map_snd disclose_ksb) ms.(fnsems);
    SModSem.mn := ms.(mn);
    SModSem.initial_mr := ms.(initial_mr);
    SModSem.initial_st := ms.(initial_st);
  |}
  .

  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)

  Lemma transl_itr_tgt_bind
        (R S: Type)
        (s: itree _ R) (k : R -> itree _ S)
    :
      (transl_itr_tgt (s >>= k))
      =
      ((transl_itr_tgt s) >>= (fun r => transl_itr_tgt (k r))).
  Proof.
    unfold transl_itr_tgt in *. grind.
  Qed.

  Lemma transl_itr_tgt_tau
        (U: Type)
        (t : itree _ U)
    :
      (transl_itr_tgt (Tau t))
      =
      (Tau (transl_itr_tgt t)).
  Proof.
    unfold transl_itr_tgt in *. grind.
  Qed.

  Lemma transl_itr_tgt_ret
        (U: Type)
        (t: U)
    :
      ((transl_itr_tgt (Ret t)))
      =
      Ret t.
  Proof.
    unfold transl_itr_tgt in *. grind.
  Qed.

  Lemma transl_itr_tgt_triggerp
        (R: Type)
        (i: pE R)
    :
      (transl_itr_tgt (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr_tgt in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_tgt_triggere
        (R: Type)
        (i: eventE R)
    :
      (transl_itr_tgt (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr_tgt in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_tgt_kcall
        (R: Type)
        (i: kCallE R)
    :
      (transl_itr_tgt (trigger i))
      =
      (trigger (transl_kCallE_tgt i) >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr_tgt in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_tgt_triggerUB
        (R: Type)
    :
      (transl_itr_tgt (triggerUB))
      =
      triggerUB (A:=R).
  Proof.
    unfold transl_itr_tgt, triggerUB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma transl_itr_tgt_triggerNB
        (R: Type)
    :
      (transl_itr_tgt (triggerNB))
      =
      triggerNB (A:=R).
  Proof.
    unfold transl_itr_tgt, triggerNB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma transl_itr_tgt_unwrapU
        (R: Type)
        (i: option R)
    :
      (transl_itr_tgt (unwrapU i))
      =
      (unwrapU i).
  Proof.
    unfold transl_itr_tgt, unwrapU in *. des_ifs.
    { etrans.
      { eapply transl_itr_tgt_ret. }
      { grind. }
    }
    { etrans.
      { eapply transl_itr_tgt_triggerUB. }
      { unfold triggerUB. grind. }
    }
  Qed.

  Lemma transl_itr_tgt_unwrapN
        (R: Type)
        (i: option R)
    :
      (transl_itr_tgt (unwrapN i))
      =
      (unwrapN i).
  Proof.
    unfold transl_itr_tgt, unwrapN in *. des_ifs.
    { etrans.
      { eapply transl_itr_tgt_ret. }
      { grind. }
    }
    { etrans.
      { eapply transl_itr_tgt_triggerNB. }
      { unfold triggerNB. grind. }
    }
  Qed.

  Lemma transl_itr_tgt_assume
        P
    :
      (transl_itr_tgt (assume P))
      =
      (assume P;;; tau;; Ret tt)
  .
  Proof.
    unfold assume. rewrite transl_itr_tgt_bind. rewrite transl_itr_tgt_triggere. grind. eapply transl_itr_tgt_ret.
  Qed.

  Lemma transl_itr_tgt_guarantee
        P
    :
      (transl_itr_tgt (guarantee P))
      =
      (guarantee P;;; tau;; Ret tt).
  Proof.
    unfold guarantee. rewrite transl_itr_tgt_bind. rewrite transl_itr_tgt_triggere. grind. eapply transl_itr_tgt_ret.
  Qed.

  Lemma transl_itr_tgt_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (transl_itr_tgt itr0)
      =
      (transl_itr_tgt itr1)
  .
  Proof. subst; et. Qed.

  Global Opaque transl_itr_tgt.










  (************************* SRC ***************************)
  (************************* SRC ***************************)
  (************************* SRC ***************************)

  Definition handle_kCallE_src: kCallE ~> itree Es :=
    fun T '(kCall fn args) =>
      match args with
      | inl _ => tau;; trigger (Choose _)
      | inr args => trigger (Call fn args↑)
      end
  .

  Notation Es' := (kCallE +' pE +' eventE).

  Definition interp_kCallE_src: itree Es' ~> itree Es :=
    interp (case_ (bif:=sum1) (handle_kCallE_src)
                  ((fun T X => trigger X): _ ~> itree Es))
  .

  Definition body_to_src {AA AR} (body: AA -> itree (kCallE +' pE +' eventE) AR): AA -> itree Es AR :=
    fun varg_src => interp_kCallE_src (body varg_src)
  .

  Definition fun_to_src {AA AR} (body: AA -> itree (kCallE +' pE +' eventE) AR): (Any.t -> itree Es Any.t) :=
    (cfun (body_to_src body))
  .

  Definition to_src (ms: t): ModSem.t := {|
    ModSem.fnsems := List.map (map_snd (fun_to_src ∘ ksb_body)) ms.(fnsems);
    ModSem.mn := ms.(mn);
    ModSem.initial_mr := ε;
    ModSem.initial_st := ms.(initial_st);
  |}
  .

  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)

  Lemma interp_kCallE_src_bind
        (R S: Type)
        (s: itree _ R) (k : R -> itree _ S)
    :
      (interp_kCallE_src (s >>= k))
      =
      ((interp_kCallE_src s) >>= (fun r => interp_kCallE_src (k r))).
  Proof.
    unfold interp_kCallE_src in *. grind.
  Qed.

  Lemma interp_kCallE_src_tau
        (U: Type)
        (t : itree _ U)
    :
      (interp_kCallE_src (Tau t))
      =
      (Tau (interp_kCallE_src t)).
  Proof.
    unfold interp_kCallE_src in *. grind.
  Qed.

  Lemma interp_kCallE_src_ret
        (U: Type)
        (t: U)
    :
      ((interp_kCallE_src (Ret t)))
      =
      Ret t.
  Proof.
    unfold interp_kCallE_src in *. grind.
  Qed.

  Lemma interp_kCallE_src_triggerp
        (R: Type)
        (i: pE R)
    :
      (interp_kCallE_src (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold interp_kCallE_src in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma interp_kCallE_src_triggere
        (R: Type)
        (i: eventE R)
    :
      (interp_kCallE_src (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold interp_kCallE_src in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma interp_kCallE_src_kcall
        (R: Type)
        (i: kCallE R)
    :
      (interp_kCallE_src (trigger i))
      =
      (handle_kCallE_src i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold interp_kCallE_src in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma interp_kCallE_src_triggerUB
        (R: Type)
    :
      (interp_kCallE_src (triggerUB))
      =
      triggerUB (A:=R).
  Proof.
    unfold interp_kCallE_src, triggerUB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma interp_kCallE_src_triggerNB
        (R: Type)
    :
      (interp_kCallE_src (triggerNB))
      =
      triggerNB (A:=R).
  Proof.
    unfold interp_kCallE_src, triggerNB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma interp_kCallE_src_unwrapU
        (R: Type)
        (i: option R)
    :
      (interp_kCallE_src (unwrapU i))
      =
      (unwrapU i).
  Proof.
    unfold interp_kCallE_src, unwrapU in *. des_ifs.
    { etrans.
      { eapply interp_kCallE_src_ret. }
      { grind. }
    }
    { etrans.
      { eapply interp_kCallE_src_triggerUB. }
      { unfold triggerUB. grind. }
    }
  Qed.

  Lemma interp_kCallE_src_unwrapN
        (R: Type)
        (i: option R)
    :
      (interp_kCallE_src (unwrapN i))
      =
      (unwrapN i).
  Proof.
    unfold interp_kCallE_src, unwrapN in *. des_ifs.
    { etrans.
      { eapply interp_kCallE_src_ret. }
      { grind. }
    }
    { etrans.
      { eapply interp_kCallE_src_triggerNB. }
      { unfold triggerNB. grind. }
    }
  Qed.

  Lemma interp_kCallE_src_assume
        P
    :
      (interp_kCallE_src (assume P))
      =
      (assume P;;; tau;; Ret tt)
  .
  Proof.
    unfold assume. rewrite interp_kCallE_src_bind. rewrite interp_kCallE_src_triggere. grind. eapply interp_kCallE_src_ret.
  Qed.

  Lemma interp_kCallE_src_guarantee
        P
    :
      (interp_kCallE_src (guarantee P))
      =
      (guarantee P;;; tau;; Ret tt).
  Proof.
    unfold guarantee. rewrite interp_kCallE_src_bind. rewrite interp_kCallE_src_triggere. grind. eapply interp_kCallE_src_ret.
  Qed.

  Lemma interp_kCallE_src_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (interp_kCallE_src itr0)
      =
      (interp_kCallE_src itr1)
  .
  Proof. subst; et. Qed.

  Global Opaque interp_kCallE_src.

End KMODSEM.
End KModSem.
Coercion KModSem.disclose_ksb: kspecbody >-> fspecbody.



Section RDB.
  Context `{Σ: GRA.t}.

  Global Program Instance transl_itr_tgt_rdb: red_database (mk_box (@KModSem.transl_itr_tgt)) :=
    mk_rdb
      0
      (mk_box KModSem.transl_itr_tgt_bind)
      (mk_box KModSem.transl_itr_tgt_tau)
      (mk_box KModSem.transl_itr_tgt_ret)
      (mk_box KModSem.transl_itr_tgt_kcall)
      (mk_box KModSem.transl_itr_tgt_triggere)
      (mk_box KModSem.transl_itr_tgt_triggerp)
      (mk_box True)
      (mk_box KModSem.transl_itr_tgt_triggerUB)
      (mk_box KModSem.transl_itr_tgt_triggerNB)
      (mk_box KModSem.transl_itr_tgt_unwrapU)
      (mk_box KModSem.transl_itr_tgt_unwrapN)
      (mk_box KModSem.transl_itr_tgt_assume)
      (mk_box KModSem.transl_itr_tgt_guarantee)
      (mk_box KModSem.transl_itr_tgt_ext)
  .

  Global Program Instance interp_kCallE_src_rdb: red_database (mk_box (@KModSem.interp_kCallE_src)) :=
    mk_rdb
      0
      (mk_box KModSem.interp_kCallE_src_bind)
      (mk_box KModSem.interp_kCallE_src_tau)
      (mk_box KModSem.interp_kCallE_src_ret)
      (mk_box KModSem.interp_kCallE_src_kcall)
      (mk_box KModSem.interp_kCallE_src_triggere)
      (mk_box KModSem.interp_kCallE_src_triggerp)
      (mk_box True)
      (mk_box KModSem.interp_kCallE_src_triggerUB)
      (mk_box KModSem.interp_kCallE_src_triggerNB)
      (mk_box KModSem.interp_kCallE_src_unwrapU)
      (mk_box KModSem.interp_kCallE_src_unwrapN)
      (mk_box KModSem.interp_kCallE_src_assume)
      (mk_box KModSem.interp_kCallE_src_guarantee)
      (mk_box KModSem.interp_kCallE_src_ext)
  .

End RDB.

Require Import SimModSem HTactics.
Section KTACTICS.

  Context `{Σ: GRA.t}.

  Lemma APCK_start_clo
        (at_most: Ord.t) (n1: Ord.t)
        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx

        (ATMOST: (at_most < kappa)%ord)
        (FUEL: (n1 + 5 < n0)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                       (mr_src0, mp_src0, fr_src0,
                       (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK at_most)) ctx) >>= k_src)
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
              (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt APCK) ctx) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    unfold APCK. steps. force_l.
    exists at_most. ired_l.  _step; [by eauto with ord_step|]. steps; [by eauto with ord_step|].
    unfold guarantee. ired_both. force_l. esplits; et.
    ired_both. _step; [by eauto with ord_step|]. steps; [by eauto with ord_step|]. ss.
    guclo lordC_spec. econs; et. rewrite OrdArith.add_O_r. refl.
  Qed.

  Lemma APCK_step_clo
        (fn: gname) (next: Ord.t) (n1: Ord.t)

        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (at_most: Ord.t)
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx0

        (FUEL: (n1 + 11 < n0)%ord)
        (ftsp: ftspec unit unit)
        (FIND: alist_find fn stb = Some (KModSem.disclose ftsp))
        (NEXT: (next < at_most)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                      (mr_src0, mp_src0, fr_src0,
                       '(ctx1, _) <- (HoareCall true o (KModSem.disclose ftsp) fn (inl tt) ctx0);;
                       tau;; tau;; (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK next)) ctx1)
                                     >>= k_src)
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
             (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK at_most)) ctx0) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    rewrite unfold_APCK. steps. force_l. exists false. ired_both.
    _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l. esplits; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l. esplits; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    rewrite FIND. ired_both. rewrite Any.upcast_downcast. ired_both.
    guclo lordC_spec. econs; et. { rewrite OrdArith.add_O_r. refl. }
    match goal with
    | [SIM: gpaco6 _ _ _ _ _ _ _ _ ?i0 _ |- gpaco6 _ _ _ _ _ _ _ _ ?i1 _] =>
      replace i1 with i0; auto
    end.
    f_equal. grind. ired_both. grind. ired_both. grind.
  Qed.

  Lemma APCK_stop_clo
        (n1: Ord.t)

        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (at_most: Ord.t)
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx

        (FUEL: (n1 + 2 < n0)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                      (mr_src0, mp_src0, fr_src0, k_src (ctx, ()))
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
              (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK at_most)) ctx) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    rewrite unfold_APCK. steps. force_l. exists true.
    ired_both; _step; [by eauto with ord_step|].
    ired_both; _step; [by eauto with ord_step|].
    steps.
    guclo lordC_spec. econs; et. { rewrite OrdArith.add_O_r. refl. }
  Qed.

End KTACTICS.

Ltac kstart _at_most :=
  eapply (APCK_start_clo) with (at_most := _at_most);
  [eauto with ord_kappa|
   (try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
  ]
.

Ltac kstep _fn :=
  eapply (@APCK_step_clo _ _fn);
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
   (try by (stb_tac; refl))|
   (eapply OrdArith.lt_from_nat; eapply Nat.lt_succ_diag_r)|
  ].

Ltac kcatch :=
  match goal with
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?fn _) >>= _)) ] =>
    kstep fn
  end.

Ltac kstop :=
  eapply APCK_stop_clo;
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|].



Module KMod.
Section KMOD.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    get_modsem: Sk.t -> KModSem.t;
    sk: Sk.t;
  }
  .

  Definition to_src (md: t): Mod.t := {|
    Mod.get_modsem := fun skenv => KModSem.to_src (md.(get_modsem) skenv);
    Mod.sk := md.(sk);
  |}
  .

  Definition to_tgt (md: t): SMod.t := {|
    SMod.get_modsem := fun skenv => KModSem.to_tgt (md.(get_modsem) skenv);
    SMod.sk := md.(sk);
  |}
  .

  Lemma to_src_comm: forall md skenv, KModSem.to_src (md.(get_modsem) skenv) = (to_src md).(Mod.get_modsem) skenv.
  Proof. i. refl. Qed.

  Lemma to_tgt_comm: forall md skenv, KModSem.to_tgt (md.(get_modsem) skenv) = (to_tgt md).(SMod.get_modsem) skenv.
  Proof. i. refl. Qed.

End KMOD.
End KMod.
