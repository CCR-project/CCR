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
(* Require Import Mem0 MemOpen. *)
Require Import HoareDef.
Require Import Red IRed.

Set Implicit Arguments.



Section AUX.
  Context `{Σ: GRA.t}.
  Definition fspec_trivial: fspec :=
    mk_fspec (meta:=unit) (fun _ argh argl o => (⌜argh = argl ∧ o = ord_top⌝: iProp)%I)
             (fun _ reth retl => (⌜reth = retl⌝: iProp)%I)
  .

End AUX.


(*** TODO: remove redundancy ***)
Ltac my_red_both := try (prw _red_gen 2 0); try (prw _red_gen 1 0).



(******************************************* UNKNOWN ***********************************************)
(******************************************* UNKNOWN ***********************************************)
(******************************************* UNKNOWN ***********************************************)
Section AUX.
  Variant uCallE: Type -> Type :=
  | uCall (fn: gname) {X} (args: X): uCallE Any.t
  .
  Constraint uCallE.u1 < Any.t.u0.
End AUX.

Module UModSem.
Section UMODSEM.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    fnsems: list (gname * (Any.t -> itree (uCallE +' pE +' eventE) Any.t));
    mn: mname;
    initial_st: Any.t;
  }
  .

  (************************* MOD ***************************)
  (************************* MOD ***************************)
  (************************* MOD ***************************)

  Definition transl_uCallE: uCallE ~> callE :=
    fun T '(uCall fn args) => Call fn args↑
  .

  Definition transl_event: (uCallE +' pE +' eventE) ~> (callE +' pE +' eventE) :=
    (bimap transl_uCallE (bimap (id_ _) (id_ _)))
  .

  Definition transl_itr: itree (uCallE +' pE +' eventE) ~> itree Es :=
    fun _ itr => resum_itr (E:=callE +' pE +' eventE) (F:=Es)
                           (interp (T:=_) (fun _ e => trigger (transl_event e)) itr)
  .

  Definition transl_fun: (Any.t -> itree (uCallE +' pE +' eventE) Any.t) -> (Any.t -> itree Es Any.t) :=
    fun ktr => (transl_itr (T:=_) ∘ ktr)
  .

  Definition transl (ms: t): ModSem.t := {|
    (* ModSem.fnsems := List.map (map_snd (((∘)∘(∘)) (resum_itr (T:=Any.t)) cfun)) ms.(fnsems); *)
    ModSem.fnsems := List.map (map_snd transl_fun) ms.(fnsems);
    ModSem.mn := ms.(mn);
    ModSem.initial_mr := ε;
    ModSem.initial_st := ms.(initial_st);
  |}
  .

  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)

  Lemma transl_itr_bind
        (R S: Type)
        (s: itree (uCallE +' pE +' eventE) R) (k : R -> itree (uCallE +' pE +' eventE) S)
    :
      (transl_itr (s >>= k))
      =
      ((transl_itr s) >>= (fun r => transl_itr (k r))).
  Proof.
    unfold transl_itr in *. grind. my_red_both. grind.
  Qed.

  Lemma transl_itr_tau
        (U: Type)
        (t : itree _ U)
    :
      (transl_itr (Tau t))
      =
      (Tau (transl_itr t)).
  Proof.
    unfold transl_itr in *. grind. my_red_both. grind.
  Qed.

  Lemma transl_itr_ret
        (U: Type)
        (t: U)
    :
      ((transl_itr (Ret t)))
      =
      Ret t.
  Proof.
    unfold transl_itr in *. grind. my_red_both. grind.
  Qed.

  Lemma transl_itr_triggerp
        (R: Type)
        (i: pE R)
    :
      (transl_itr (trigger i))
      =
      (trigger i >>= (fun r => tau;; tau;; Ret r)).
  Proof.
    unfold transl_itr in *.
    repeat rewrite interp_trigger. repeat (my_red_both; grind; resub).
  Qed.

  Lemma transl_itr_triggere
        (R: Type)
        (i: eventE R)
    :
      (transl_itr (trigger i))
      =
      (trigger i >>= (fun r => tau;; tau;; Ret r)).
  Proof.
    unfold transl_itr in *.
    repeat rewrite interp_trigger. repeat (my_red_both; grind; resub).
  Qed.

  Lemma transl_itr_ucall
        (R: Type)
        (i: uCallE R)
    :
      (transl_itr (trigger i))
      =
      (trigger (transl_uCallE i) >>= (fun r => tau;; tau;; Ret r)).
  Proof.
    unfold transl_itr in *.
    repeat rewrite interp_trigger. repeat (my_red_both; grind; resub).
  Qed.

  Lemma transl_itr_triggerUB
        (R: Type)
    :
      (transl_itr (triggerUB))
      =
      triggerUB (A:=R).
  Proof.
    unfold transl_itr, triggerUB in *. rewrite unfold_interp. cbn. repeat (my_red_both; grind; resub).
  Qed.

  Lemma transl_itr_triggerNB
        (R: Type)
    :
      (transl_itr (triggerNB))
      =
      triggerNB (A:=R).
  Proof.
    unfold transl_itr, triggerNB in *. rewrite unfold_interp. cbn. repeat (my_red_both; grind; resub).
  Qed.

  Lemma transl_itr_unwrapU
        (R: Type)
        (i: option R)
    :
      (transl_itr (unwrapU i))
      =
      (unwrapU i).
  Proof.
    unfold transl_itr, unwrapU in *. des_ifs.
    { etrans.
      { eapply transl_itr_ret. }
      { grind. }
    }
    { etrans.
      { eapply transl_itr_triggerUB. }
      { unfold triggerUB. grind. }
    }
  Qed.

  Lemma transl_itr_unwrapN
        (R: Type)
        (i: option R)
    :
      (transl_itr (unwrapN i))
      =
      (unwrapN i).
  Proof.
    unfold transl_itr, unwrapN in *. des_ifs.
    { etrans.
      { eapply transl_itr_ret. }
      { grind. }
    }
    { etrans.
      { eapply transl_itr_triggerNB. }
      { unfold triggerNB. grind. }
    }
  Qed.

  Lemma transl_itr_assume
        P
    :
      (transl_itr (assume P))
      =
      (assume P;;; tau;; tau;; Ret tt)
  .
  Proof.
    unfold assume. rewrite transl_itr_bind. rewrite transl_itr_triggere.
    repeat (my_red_both; grind; resub).
    eapply transl_itr_ret.
  Qed.

  Lemma transl_itr_guarantee
        P
    :
      (transl_itr (guarantee P))
      =
      (guarantee P;;; tau;; tau;; Ret tt).
  Proof.
    unfold guarantee. rewrite transl_itr_bind. rewrite transl_itr_triggere.
    repeat (my_red_both; grind; resub).
    eapply transl_itr_ret.
  Qed.

  Lemma transl_itr_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (transl_itr itr0)
      =
      (transl_itr itr1)
  .
  Proof. subst; et. Qed.












  (************************* SMOD ***************************)
  (************************* SMOD ***************************)
  (************************* SMOD ***************************)

  Definition massage_uCallE: uCallE ~> hCallE :=
    fun T '(uCall fn args) => hCall false fn (args↑)
  .

  Definition massage_event: (uCallE +' pE +' eventE) ~> (hCallE +' pE +' eventE) :=
    (bimap massage_uCallE (bimap (id_ _) (id_ _)))
  .

  Definition massage_itr: itree (uCallE +' pE +' eventE) ~> itree (hCallE +' pE +' eventE) :=
    (* embed ∘ massage_event *) (*** <- it works but it is not handy ***)
    fun _ => interp (T:=_) (fun _ e => trigger (massage_event e))
    (* fun _ => massageate (T:=_) massage_event  *)
  .

  Definition massage_fun (ktr: Any.t -> itree (uCallE +' pE +' eventE) Any.t):
    (Any.t -> itree (hCallE +' pE +' eventE) Any.t) :=
    (massage_itr (T:=_) ∘ ktr)
  .

  Definition massage_fsb: (Any.t -> itree (uCallE +' pE +' eventE) Any.t) -> fspecbody :=
    fun ktr => mk_specbody fspec_trivial (massage_fun ktr)
  .

  Definition massage (ms: t): SModSem.t := {|
    SModSem.fnsems := List.map (map_snd massage_fsb) ms.(fnsems);
    SModSem.mn := ms.(mn);
    SModSem.initial_mr := ε;
    SModSem.initial_st := ms.(initial_st);
  |}
  .

  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)

  Lemma massage_itr_bind
        (R S: Type)
        (s: itree (uCallE +' pE +' eventE) R) (k : R -> itree (uCallE +' pE +' eventE) S)
    :
      (massage_itr (s >>= k))
      =
      ((massage_itr s) >>= (fun r => massage_itr (k r))).
  Proof.
    unfold massage_itr in *. grind.
  Qed.

  Lemma massage_itr_tau
        (U: Type)
        (t : itree _ U)
    :
      (massage_itr (Tau t))
      =
      (Tau (massage_itr t)).
  Proof.
    unfold massage_itr in *. grind.
  Qed.

  Lemma massage_itr_ret
        (U: Type)
        (t: U)
    :
      ((massage_itr (Ret t)))
      =
      Ret t.
  Proof.
    unfold massage_itr in *. grind.
  Qed.

  Lemma massage_itr_triggerp
        (R: Type)
        (i: pE R)
    :
      (massage_itr (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold massage_itr in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma massage_itr_triggere
        (R: Type)
        (i: eventE R)
    :
      (massage_itr (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold massage_itr in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma massage_itr_ucall
        (R: Type)
        (i: uCallE R)
    :
      (massage_itr (trigger i))
      =
      (trigger (massage_uCallE i) >>= (fun r => tau;; Ret r)).
  Proof.
    unfold massage_itr in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma massage_itr_triggerUB
        (R: Type)
    :
      (massage_itr (triggerUB))
      =
      triggerUB (A:=R).
  Proof.
    unfold massage_itr, triggerUB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma massage_itr_triggerNB
        (R: Type)
    :
      (massage_itr (triggerNB))
      =
      triggerNB (A:=R).
  Proof.
    unfold massage_itr, triggerNB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma massage_itr_unwrapU
        (R: Type)
        (i: option R)
    :
      (massage_itr (unwrapU i))
      =
      (unwrapU i).
  Proof.
    unfold massage_itr, unwrapU in *. des_ifs.
    { etrans.
      { eapply massage_itr_ret. }
      { grind. }
    }
    { etrans.
      { eapply massage_itr_triggerUB. }
      { unfold triggerUB. grind. }
    }
  Qed.

  Lemma massage_itr_unwrapN
        (R: Type)
        (i: option R)
    :
      (massage_itr (unwrapN i))
      =
      (unwrapN i).
  Proof.
    unfold massage_itr, unwrapN in *. des_ifs.
    { etrans.
      { eapply massage_itr_ret. }
      { grind. }
    }
    { etrans.
      { eapply massage_itr_triggerNB. }
      { unfold triggerNB. grind. }
    }
  Qed.

  Lemma massage_itr_assume
        P
    :
      (massage_itr (assume P))
      =
      (assume P;;; tau;; Ret tt)
  .
  Proof.
    unfold assume. rewrite massage_itr_bind. rewrite massage_itr_triggere. grind. eapply massage_itr_ret.
  Qed.

  Lemma massage_itr_guarantee
        P
    :
      (massage_itr (guarantee P))
      =
      (guarantee P;;; tau;; Ret tt).
  Proof.
    unfold guarantee. rewrite massage_itr_bind. rewrite massage_itr_triggere. grind. eapply massage_itr_ret.
  Qed.

  Lemma massage_itr_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (massage_itr itr0)
      =
      (massage_itr itr1)
  .
  Proof. subst; et. Qed.

End UMODSEM.
End UModSem.

Coercion UModSem.transl: UModSem.t >-> ModSem.t.
Coercion UModSem.massage: UModSem.t >-> SModSem.t.

Section RDB.
  Context `{Σ: GRA.t}.

  Global Program Instance utransl_itr_rdb: red_database (mk_box (@UModSem.transl_itr)) :=
    mk_rdb
      0
      (mk_box UModSem.transl_itr_bind)
      (mk_box UModSem.transl_itr_tau)
      (mk_box UModSem.transl_itr_ret)
      (mk_box UModSem.transl_itr_ucall)
      (mk_box UModSem.transl_itr_triggere)
      (mk_box UModSem.transl_itr_triggerp)
      (mk_box True)
      (mk_box UModSem.transl_itr_triggerUB)
      (mk_box UModSem.transl_itr_triggerNB)
      (mk_box UModSem.transl_itr_unwrapU)
      (mk_box UModSem.transl_itr_unwrapN)
      (mk_box UModSem.transl_itr_assume)
      (mk_box UModSem.transl_itr_guarantee)
      (mk_box UModSem.transl_itr_ext)
  .

  Global Program Instance umassage_itr_rdb: red_database (mk_box (@UModSem.massage_itr)) :=
    mk_rdb
      0
      (mk_box UModSem.massage_itr_bind)
      (mk_box UModSem.massage_itr_tau)
      (mk_box UModSem.massage_itr_ret)
      (mk_box UModSem.massage_itr_ucall)
      (mk_box UModSem.massage_itr_triggere)
      (mk_box UModSem.massage_itr_triggerp)
      (mk_box True)
      (mk_box UModSem.massage_itr_triggerUB)
      (mk_box UModSem.massage_itr_triggerNB)
      (mk_box UModSem.massage_itr_unwrapU)
      (mk_box UModSem.massage_itr_unwrapN)
      (mk_box UModSem.massage_itr_assume)
      (mk_box UModSem.massage_itr_guarantee)
      (mk_box UModSem.massage_itr_ext)
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

  Definition transl (md: t): Mod.t := {|
    Mod.get_modsem := UModSem.transl ∘ md.(get_modsem);
    Mod.sk := md.(sk);
  |}
  .

  Lemma transl_comm: forall md skenv, UModSem.transl (md.(get_modsem) skenv) = (transl md).(Mod.get_modsem) skenv.
  Proof. i. refl. Qed.


  Definition massage (md: t): SMod.t := {|
    SMod.get_modsem := UModSem.massage ∘ md.(get_modsem);
    SMod.sk := md.(sk);
  |}
  .

  Lemma to_smod_comm: forall md skenv, UModSem.massage (md.(get_modsem) skenv) = (massage md).(SMod.get_modsem) skenv.
  Proof. i. refl. Qed.

End UMOD.
End UMod.

Coercion UMod.transl: UMod.t >-> Mod.t.
Coercion UMod.massage: UMod.t >-> SMod.t.





















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

  Variant kflag: Type := (** known and **) pure | (** known and **) impure | unknown.

  Variant kCallE: Type -> Type :=
  | kCall (kf: kflag) (fn: gname) (varg: Any.t): kCallE Any.t
  .

  Record kspecbody := mk_kspecbody {
    ksb_fspec:> fspec;                                            (*** K -> K ***)
    ksb_ubody: Any.t -> itree (kCallE +' pE +' eventE) Any.t;     (*** U -> K ***)
    ksb_kbody: Any.t -> itree (kCallE +' pE +' eventE) Any.t;     (*** K -> K ***)
  }
  .

  Definition ksb_trivial (body: Any.t -> itree (kCallE +' pE +' eventE) Any.t): kspecbody :=
    mk_kspecbody fspec_trivial body body
  .

  Program Fixpoint _APCK (at_most: Ord.t) {wf Ord.lt at_most}: itree (kCallE +' pE +' eventE) unit :=
    break <- trigger (Choose _);;
    if break: bool
    then Ret tt
    else
      n <- trigger (Choose Ord.t);;
      trigger (Choose (n < at_most)%ord);;;
      '(fn, varg) <- trigger (Choose _);;
      trigger (kCall pure fn varg);;;
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
                      '(fn, varg) <- trigger (Choose _);;
                      trigger (kCall pure fn varg);;;
                      _APCK n.
  Proof.
    i. unfold _APCK. rewrite Fix_eq; eauto.
    { repeat f_equal. extensionality break. destruct break; ss.
      repeat f_equal. extensionality n.
      unfold guarantee. rewrite bind_bind.
      repeat f_equal. extensionality p.
      rewrite bind_ret_l.
      repeat f_equal. extensionality x. des_ifs. }
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

  Definition transl_kCallE: kCallE ~> hCallE :=
    fun _ '(kCall kf fn args) =>
      match kf with
      | pure => hCall true fn (Any.pair tt↑ args)
      | impure => hCall false fn (Any.pair tt↑ args)
      | unknown => hCall false fn args
      end
  .

  Definition transl_event: (kCallE +' pE +' eventE) ~> (hCallE +' pE +' eventE) :=
    (bimap transl_kCallE (bimap (id_ _) (id_ _)))
  .

  Definition transl_itr: itree (kCallE +' pE +' eventE) ~> itree (hCallE +' pE +' eventE) :=
    fun _ => interp (T:=_) (fun _ e => trigger (transl_event e))
  .

  Definition transl_fun (ktr: Any.t -> itree (kCallE +' pE +' eventE) Any.t):
    Any.t -> itree (hCallE +' pE +' eventE) Any.t :=
    (transl_itr (T:=_)) ∘ ktr
  .

  Definition disclose (fs: fspec): fspec :=
    mk_fspec (meta:=option fs.(meta))
             (fun ox argh argl o =>
                match ox, Any.split argh with
                | Some x, Some (_, argh) => (fs.(precond) x argh argl o)
                | None, None => ((⌜argh = argl /\ o = ord_top⌝): iProp)%I
                | _, _ => (⌜False⌝: iProp)%I
                end)
             (fun ox reth retl =>
                map_or_else ox (fun x => (fs.(postcond) x reth retl)) (⌜reth = retl⌝: iProp)%I)
  .

  Definition disclose_ksb (ksb: kspecbody): fspecbody :=
    mk_specbody (disclose ksb)
                (fun argh =>
                   map_or_else (Any.split argh) (fun '(_, argh) => (transl_fun ksb.(ksb_kbody)) argh)
                               ((transl_fun ksb.(ksb_ubody)) argh))
  .

  Definition transl (ms: t): SModSem.t := {|
    SModSem.fnsems := List.map (map_snd disclose_ksb) ms.(fnsems);
    SModSem.mn := ms.(mn);
    SModSem.initial_mr := ms.(initial_mr);
    SModSem.initial_st := ms.(initial_st);
  |}
  .

  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)

  Lemma transl_itr_bind
        (R S: Type)
        (s: itree _ R) (k : R -> itree _ S)
    :
      (transl_itr (s >>= k))
      =
      ((transl_itr s) >>= (fun r => transl_itr (k r))).
  Proof.
    unfold transl_itr in *. grind.
  Qed.

  Lemma transl_itr_tau
        (U: Type)
        (t : itree _ U)
    :
      (transl_itr (Tau t))
      =
      (Tau (transl_itr t)).
  Proof.
    unfold transl_itr in *. grind.
  Qed.

  Lemma transl_itr_ret
        (U: Type)
        (t: U)
    :
      ((transl_itr (Ret t)))
      =
      Ret t.
  Proof.
    unfold transl_itr in *. grind.
  Qed.

  Lemma transl_itr_triggerp
        (R: Type)
        (i: pE R)
    :
      (transl_itr (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_triggere
        (R: Type)
        (i: eventE R)
    :
      (transl_itr (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_kcall
        (R: Type)
        (i: kCallE R)
    :
      (transl_itr (trigger i))
      =
      (trigger (transl_kCallE i) >>= (fun r => tau;; Ret r)).
  Proof.
    unfold transl_itr in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma transl_itr_triggerUB
        (R: Type)
    :
      (transl_itr (triggerUB))
      =
      triggerUB (A:=R).
  Proof.
    unfold transl_itr, triggerUB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma transl_itr_triggerNB
        (R: Type)
    :
      (transl_itr (triggerNB))
      =
      triggerNB (A:=R).
  Proof.
    unfold transl_itr, triggerNB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma transl_itr_unwrapU
        (R: Type)
        (i: option R)
    :
      (transl_itr (unwrapU i))
      =
      (unwrapU i).
  Proof.
    unfold transl_itr, unwrapU in *. des_ifs.
    { etrans.
      { eapply transl_itr_ret. }
      { grind. }
    }
    { etrans.
      { eapply transl_itr_triggerUB. }
      { unfold triggerUB. grind. }
    }
  Qed.

  Lemma transl_itr_unwrapN
        (R: Type)
        (i: option R)
    :
      (transl_itr (unwrapN i))
      =
      (unwrapN i).
  Proof.
    unfold transl_itr, unwrapN in *. des_ifs.
    { etrans.
      { eapply transl_itr_ret. }
      { grind. }
    }
    { etrans.
      { eapply transl_itr_triggerNB. }
      { unfold triggerNB. grind. }
    }
  Qed.

  Lemma transl_itr_assume
        P
    :
      (transl_itr (assume P))
      =
      (assume P;;; tau;; Ret tt)
  .
  Proof.
    unfold assume. rewrite transl_itr_bind. rewrite transl_itr_triggere. grind. eapply transl_itr_ret.
  Qed.

  Lemma transl_itr_guarantee
        P
    :
      (transl_itr (guarantee P))
      =
      (guarantee P;;; tau;; Ret tt).
  Proof.
    unfold guarantee. rewrite transl_itr_bind. rewrite transl_itr_triggere. grind. eapply transl_itr_ret.
  Qed.

  Lemma transl_itr_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (transl_itr itr0)
      =
      (transl_itr itr1)
  .
  Proof. subst; et. Qed.

  Global Opaque transl_itr.

End KMODSEM.
End KModSem.
Coercion KModSem.disclose_ksb: kspecbody >-> fspecbody.
Coercion KModSem.transl: KModSem.t >-> SModSem.t.



Section RDB.
  Context `{Σ: GRA.t}.

  Global Program Instance ktransl_itr_rdb: red_database (mk_box (@KModSem.transl_itr)) :=
    mk_rdb
      0
      (mk_box KModSem.transl_itr_bind)
      (mk_box KModSem.transl_itr_tau)
      (mk_box KModSem.transl_itr_ret)
      (mk_box KModSem.transl_itr_kcall)
      (mk_box KModSem.transl_itr_triggere)
      (mk_box KModSem.transl_itr_triggerp)
      (mk_box True)
      (mk_box KModSem.transl_itr_triggerUB)
      (mk_box KModSem.transl_itr_triggerNB)
      (mk_box KModSem.transl_itr_unwrapU)
      (mk_box KModSem.transl_itr_unwrapN)
      (mk_box KModSem.transl_itr_assume)
      (mk_box KModSem.transl_itr_guarantee)
      (mk_box KModSem.transl_itr_ext)
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
                       (interp_hCallE_tgt stb o (KModSem.transl_itr (_APCK at_most)) ctx) >>= k_src)
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
              (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o (KModSem.transl_itr APCK) ctx) >>= k_src)
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
        (fn: gname) (args: Any.t) (next: Ord.t) (n1: Ord.t)

        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (at_most: Ord.t)
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx0

        (FUEL: (n1 + 11 < n0)%ord)
        (ftsp: fspec)
        (FIND: alist_find fn stb = Some (KModSem.disclose ftsp))
        (NEXT: (next < at_most)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                      (mr_src0, mp_src0, fr_src0,
                       '(ctx1, _) <- (HoareCall true o (KModSem.disclose ftsp) fn (Any.pair tt↑ args) ctx0);;
                       tau;; tau;; (interp_hCallE_tgt stb o (KModSem.transl_itr (_APCK next)) ctx1)
                                     >>= k_src)
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
             (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o (KModSem.transl_itr (_APCK at_most)) ctx0) >>= k_src)
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
    force_l. exists (fn, args). esplits; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    rewrite FIND. ired_both.
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
              (interp_hCallE_tgt stb o (KModSem.transl_itr (_APCK at_most)) ctx) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    rewrite unfold_APCK. steps. force_l. exists true.
    ired_both; _step; [by eauto with ord_step|].
    ired_both; _step; [by eauto with ord_step|].
    steps.
    guclo lordC_spec. econs; et. { rewrite OrdArith.add_O_r. refl. }
  Qed.

  Lemma trivial_init_clo
        A
        (R_src: A -> Any.t -> Any.t -> iProp) (R_tgt: A -> Any.t -> Any.t -> iProp)
        fn f_tgt gstb body
        (POST: forall a mp_src mp_tgt mr_src mr_tgt fr_src ctx varg
                      (RTGT: R_tgt a mp_src mp_tgt mr_tgt)
                      (ACC: current_iPropL ctx [("INV", R_src a mp_src mp_tgt)])
          ,
            gpaco6 (_sim_itree (mk_wf R_src R_tgt)) (cpn6 (_sim_itree (mk_wf R_src R_tgt))) bot6 bot6
                   _ _
                   (fun _ _ => eq)
                   89
                   (((mr_src, mp_src), fr_src),
                    ((interp_hCallE_tgt gstb ord_top (KModSem.transl_fun body varg) ctx)
                      >>= (HoareFunRet (fun (_: unit) (reth retl: Any.t) => (⌜reth = retl⌝%I): iProp) tt))
                   )
                   (((mr_tgt, mp_tgt), ε), (f_tgt varg))
        )
    :
      sim_fnsem (mk_wf R_src R_tgt) (fn, fun_to_tgt gstb (mk_kspecbody fspec_trivial body body)) (fn, f_tgt)
  .
  Proof.
    init. harg. rename a into aa.
    Ltac dull_tac :=
      match goal with
      | ord_cur: ord |- _ =>
        assert(ord_cur = ord_top) by (on_current ltac:(fun ACC => clear - ACC); mClear "INV";
                                      des_ifs; mDesAll; des; ss);
        subst
      end;
      match goal with
      | |- context[map_or_else (Any.split ?v) ?l (KModSem.transl_fun ?body ?varg_src)] =>
        let r := constr:(KModSem.transl_fun body varg_src) in
        let varg := match goal with | [H: context[varg_src = ?varg] |- _] => varg end in
        replace (map_or_else (Any.split v) l r) with (KModSem.transl_fun body varg);
        [|on_current ltac:(fun ACC => clear - ACC); mClear "INV"; des_ifs; mDesAll; ss; des; subst; ss; fail]
      end;
      mClear "PRE"; rename x into _unused.
    dull_tac.
    exploit POST; et. intro SIM.
    match goal with
    | [SIM: gpaco6 _ _ _ _ _ _ _ _ ?i0 _ |- gpaco6 _ _ _ _ _ _ _ _ ?i1 _] =>
      replace i1 with i0; eauto
    end.
    repeat f_equal. Local Transparent HoareFunRet. unfold HoareFunRet. Local Opaque HoareFunRet.
    extensionality x. des_ifs. grind. rewrite map_or_else_same. ss.
  Qed.

End KTACTICS.

Ltac kstart _at_most :=
  eapply (APCK_start_clo) with (at_most := _at_most);
  [eauto with ord_kappa|
   (try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
  ]
.

Ltac kstep _fn _args :=
  eapply (@APCK_step_clo _ _fn _args);
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
   (try by (stb_tac; refl))|
   (eapply OrdArith.lt_from_nat; eapply Nat.lt_succ_diag_r)|
  ].

Ltac kcatch :=
  match goal with
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?fn ?args) >>= _)) ] =>
    kstep fn args
  end.

Ltac kstop :=
  eapply APCK_stop_clo;
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|].

Ltac trivial_init := eapply trivial_init_clo; i; des_u.



Module KMod.
Section KMOD.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    get_modsem: Sk.t -> KModSem.t;
    sk: Sk.t;
  }
  .

  Definition transl (md: t): SMod.t := {|
    SMod.get_modsem := fun skenv => KModSem.transl (md.(get_modsem) skenv);
    SMod.sk := md.(sk);
  |}
  .

  Lemma transl_comm: forall md skenv, KModSem.transl (md.(get_modsem) skenv) = (transl md).(SMod.get_modsem) skenv.
  Proof. i. refl. Qed.

End KMOD.
End KMod.

Coercion KMod.transl: KMod.t >-> SMod.t.
