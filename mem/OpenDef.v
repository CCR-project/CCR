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
Require Import IRed.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.


(* Definition dot {A B C} (g: B -> C) (f: A -> B): A -> C := g ∘ f. *)
(* Notation "(∘)" := dot (at level 40, left associativity). *)
Notation "(∘)" := (fun g f => g ∘ f) (at level 40, left associativity).

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

Lemma upcast_pair_downcast
      A B (a: A) (b: B)
  :
    (Any.pair a↑ b↑)↓ = Some (a, b)
.
Proof. admit "ez". Qed.


Section AUX.
  Context `{Σ: GRA.t}.
  Definition fspec_trivial: fspec := (mk_simple (fun (_: unit) => (fun _ o => ⌜o = ord_top⌝, fun _ => ⌜True⌝))).

  Definition fspec_trivial2: fspec :=
    @mk _ unit ((list val) * bool)%type (val)
        (fun _ argh argl o => ⌜(Any.pair argl false↑)↓ = Some argh /\ o = ord_top⌝)
        (fun _ reth retl => ⌜reth↑ = retl⌝)
  .

End AUX.

Lemma dummy_lemma: True. ss. Qed.




(******************************************* UNKNOWN ***********************************************)
(******************************************* UNKNOWN ***********************************************)
(******************************************* UNKNOWN ***********************************************)

Module UModSem.
Section UMODSEM.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    fnsems: list (gname * (list val -> itree (callE +' pE +' eventE) val));
    mn: mname;
    initial_st: Any.t;
  }
  .

  Definition to_modsem (ms: t): ModSem.t := {|
    ModSem.fnsems := List.map (map_snd (((∘)∘(∘)) (resum_itr (T:=Any.t)) cfun)) ms.(fnsems);
    ModSem.mn := ms.(mn);
    ModSem.initial_mr := ε;
    ModSem.initial_st := ms.(initial_st);
  |}
  .

  Definition transl_callE: callE ~> hCallE :=
    fun T '(Call fn args) => hCall false fn (Any.pair args false↑)
  .

  Definition transl_event: (callE +' pE +' eventE) ~> (hCallE +' pE +' eventE) :=
    (bimap transl_callE (bimap (id_ _) (id_ _)))
  .

  Definition transl_itr: itree (callE +' pE +' eventE) ~> itree (hCallE +' pE +' eventE) :=
    (* embed ∘ transl_event *) (*** <- it works but it is not handy ***)
    fun _ => interp (T:=_) (fun _ e => trigger (transl_event e))
    (* fun _ => translate (T:=_) transl_event  *)
  .

  Definition transl_fun: (list val -> itree (callE +' pE +' eventE) val) -> fspecbody :=
    fun ktr =>
      (* mk_specbody fspec_trivial2 (fun '(vargs, _) => interp (T:=val) transl_itr (ktr vargs)) *)
      mk_specbody fspec_trivial2 (transl_itr (T:=_) ∘ ktr ∘ fst)
  .

  Definition to_smodsem (ms: t): SModSem.t := {|
    SModSem.fnsems := List.map (map_snd transl_fun) ms.(fnsems);
    SModSem.mn := ms.(mn);
    SModSem.initial_mr := ε;
    SModSem.initial_st := ms.(initial_st);
  |}
  .

  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)

  Lemma transl_itr_bind
        (R S: Type)
        (s: itree (callE +' pE +' eventE) R) (k : R -> itree (callE +' pE +' eventE) S)
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

  Lemma transl_itr_hcall
        (R: Type)
        (i: callE R)
    :
      (transl_itr (trigger i))
      =
      (trigger (transl_callE i) >>= (fun r => tau;; Ret r)).
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
      (assume P;; tau;; Ret tt)
  .
  Proof.
    unfold assume. rewrite transl_itr_bind. rewrite transl_itr_triggere. grind. eapply transl_itr_ret.
  Qed.

  Lemma transl_itr_guarantee
        P
    :
      (transl_itr (guarantee P))
      =
      (guarantee P;; tau;; Ret tt).
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

  Global Program Instance transl_itr_rdb: red_database (mk_box (@transl_itr)) :=
    mk_rdb
      0
      (mk_box transl_itr_bind)
      (mk_box transl_itr_tau)
      (mk_box transl_itr_ret)
      (mk_box transl_itr_hcall)
      (mk_box transl_itr_triggere)
      (mk_box transl_itr_triggerp)
      (mk_box dummy_lemma)
      (mk_box transl_itr_triggerUB)
      (mk_box transl_itr_triggerNB)
      (mk_box transl_itr_unwrapU)
      (mk_box transl_itr_unwrapN)
      (mk_box transl_itr_assume)
      (mk_box transl_itr_guarantee)
      (mk_box transl_itr_ext)
  .
End UMODSEM.
End UModSem.




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

Section AUX.
  Context `{Σ: GRA.t}.

  Definition disclose (fs: fspec): fspec :=
    @mk _ (option fs.(X)) (fs.(AA) * bool)%type (fs.(AR))
        (fun ox '(argh, is_k) argl o => ⌜is_some ox = is_k⌝ **
                                        ((Exists x, ⌜ox = Some x⌝ ** fs.(precond) x argh argl o ** ⌜is_pure o⌝) ∨
                                         (⌜ox = None /\ argh↑ = argl /\ o = ord_top⌝)))
        (fun ox reth retl => ((Exists x, ⌜ox = Some x⌝ ** fs.(postcond) x reth retl) ∨ (⌜ox = None /\ reth↑ = retl⌝)))
  .

  Definition disclose_fsb (fsb: fspecbody): fspecbody :=
    mk_specbody (disclose fsb) (fun '(argh, is_k) => if is_k
                                                     then trigger (Choose _)
                                                                  (*** YJ: We may generalize this to APC ***)
                                                                  (*** YJ: We may further generalize this to any itree without pE ***)
                                                     (* else interp transl_itr (fsb.(fsb_body) argh) *)
                                                     else (fsb.(fsb_body) argh)
                               )
  .

  Definition disclose_smodsem (ms: SModSem.t): SModSem.t := {|
    SModSem.fnsems     := List.map (map_snd disclose_fsb) ms.(SModSem.fnsems);
    SModSem.mn         := ms.(SModSem.mn);
    SModSem.initial_mr := ms.(SModSem.initial_mr);
    SModSem.initial_st := ms.(SModSem.initial_st);
  |}
  .

  Definition disclose_smod (ms: SMod.t): SMod.t := {|
    SMod.get_modsem := disclose_smodsem ∘ ms.(SMod.get_modsem);
    SMod.sk := ms.(SMod.sk);
  |}
  .

End AUX.





Module KModSem.
Section KMODSEM.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    (* fnsems: list (gname * (list val -> itree (oCallE +' pE +' eventE) val)); *)
    fnsems: list (gname * fspecbody);
    mn: mname;
    initial_mr: Σ;
    initial_st: Any.t;
  }
  .

  (************************* TGT ***************************)
  (************************* TGT ***************************)
  (************************* TGT ***************************)

  (*** N.B. tbr == is_k. i.e., known calls will always be removed ***)
  Definition transl_hCallE_tgt: hCallE ~> hCallE :=
    fun T '(hCall tbr fn args) => hCall tbr fn (Any.pair args tbr↑)
  .

  Definition transl_event_tgt: (hCallE +' pE +' eventE) ~> (hCallE +' pE +' eventE) :=
    (bimap transl_hCallE_tgt (bimap (id_ _) (id_ _)))
  .

  Definition transl_itr_tgt: itree (hCallE +' pE +' eventE) ~> itree (hCallE +' pE +' eventE) :=
    fun _ => interp (T:=_) (fun _ e => trigger (transl_event_tgt e))
  .

  Definition transl_fsb (fsb: fspecbody): HoareDef.fspecbody :=
    HoareDef.mk_specbody fsb (transl_itr_tgt (T:=_) ∘ fsb.(fsb_body))
  .

  Coercion transl_fsb: fspecbody >-> HoareDef.fspecbody.

  Definition to_tgt (ms: t): SModSem.t := {|
    SModSem.fnsems := List.map (map_snd transl_fsb) ms.(fnsems);
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

  Lemma transl_itr_tgt_hcall
        (R: Type)
        (i: hCallE R)
    :
      (transl_itr_tgt (trigger i))
      =
      (trigger (transl_hCallE_tgt i) >>= (fun r => tau;; Ret r)).
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
      (assume P;; tau;; Ret tt)
  .
  Proof.
    unfold assume. rewrite transl_itr_tgt_bind. rewrite transl_itr_tgt_triggere. grind. eapply transl_itr_tgt_ret.
  Qed.

  Lemma transl_itr_tgt_guarantee
        P
    :
      (transl_itr_tgt (guarantee P))
      =
      (guarantee P;; tau;; Ret tt).
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

  Global Program Instance transl_itr_tgt_rdb: red_database (mk_box (@transl_itr_tgt)) :=
    mk_rdb
      0
      (mk_box transl_itr_tgt_bind)
      (mk_box transl_itr_tgt_tau)
      (mk_box transl_itr_tgt_ret)
      (mk_box transl_itr_tgt_hcall)
      (mk_box transl_itr_tgt_triggere)
      (mk_box transl_itr_tgt_triggerp)
      (mk_box dummy_lemma)
      (mk_box transl_itr_tgt_triggerUB)
      (mk_box transl_itr_tgt_triggerNB)
      (mk_box transl_itr_tgt_unwrapU)
      (mk_box transl_itr_tgt_unwrapN)
      (mk_box transl_itr_tgt_assume)
      (mk_box transl_itr_tgt_guarantee)
      (mk_box transl_itr_tgt_ext)
  .

  Global Opaque transl_itr_tgt.





  (************************* SRC ***************************)
  (************************* SRC ***************************)
  (************************* SRC ***************************)

  Definition handle_hCallE_src: hCallE ~> itree Es :=
    fun T '(hCall tbr fn args) =>
      match tbr with
      | true => tau;; trigger (Choose _)
      | false => trigger (Call fn args)
      end
  .

  Definition interp_hCallE_src `{E -< Es}: itree (hCallE +' E) ~> itree Es :=
    interp (case_ (bif:=sum1) (handle_hCallE_src)
                  ((fun T X => trigger X): E ~> itree Es))
  .

  Definition body_to_src {AA AR} (body: AA -> itree (hCallE +' pE +' eventE) AR): AA -> itree Es AR :=
    fun varg_src => interp_hCallE_src (body varg_src)
  .

  Definition fun_to_src {AA AR} (body: AA -> itree (hCallE +' pE +' eventE) AR): (Any.t -> itree Es Any.t) :=
    (cfun (body_to_src body))
  .

  Definition to_src (ms: t): ModSem.t := {|
    ModSem.fnsems := List.map (map_snd (fun_to_src ∘ fsb_body)) ms.(fnsems);
    ModSem.mn := ms.(mn);
    ModSem.initial_mr := ε;
    ModSem.initial_st := ms.(initial_st);
  |}
  .

  (*****************************************************)
  (****************** Reduction Lemmas *****************)
  (*****************************************************)

  Lemma interp_hCallE_src_bind
        (R S: Type)
        (s: itree _ R) (k : R -> itree _ S)
    :
      (interp_hCallE_src (s >>= k))
      =
      ((interp_hCallE_src s) >>= (fun r => interp_hCallE_src (k r))).
  Proof.
    unfold interp_hCallE_src in *. grind.
  Qed.

  Lemma interp_hCallE_src_tau
        (U: Type)
        (t : itree _ U)
    :
      (interp_hCallE_src (Tau t))
      =
      (Tau (interp_hCallE_src t)).
  Proof.
    unfold interp_hCallE_src in *. grind.
  Qed.

  Lemma interp_hCallE_src_ret
        (U: Type)
        (t: U)
    :
      ((interp_hCallE_src (Ret t)))
      =
      Ret t.
  Proof.
    unfold interp_hCallE_src in *. grind.
  Qed.

  Lemma interp_hCallE_src_triggerp
        (R: Type)
        (i: pE R)
    :
      (interp_hCallE_src (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold interp_hCallE_src in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma interp_hCallE_src_triggere
        (R: Type)
        (i: eventE R)
    :
      (interp_hCallE_src (trigger i))
      =
      (trigger i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold interp_hCallE_src in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma interp_hCallE_src_hcall
        (R: Type)
        (i: hCallE R)
    :
      (interp_hCallE_src (trigger i))
      =
      (handle_hCallE_src i >>= (fun r => tau;; Ret r)).
  Proof.
    unfold interp_hCallE_src in *.
    repeat rewrite interp_trigger. grind.
  Qed.

  Lemma interp_hCallE_src_triggerUB
        (R: Type)
    :
      (interp_hCallE_src (triggerUB))
      =
      triggerUB (A:=R).
  Proof.
    unfold interp_hCallE_src, triggerUB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma interp_hCallE_src_triggerNB
        (R: Type)
    :
      (interp_hCallE_src (triggerNB))
      =
      triggerNB (A:=R).
  Proof.
    unfold interp_hCallE_src, triggerNB in *. rewrite unfold_interp. cbn. grind.
  Qed.

  Lemma interp_hCallE_src_unwrapU
        (R: Type)
        (i: option R)
    :
      (interp_hCallE_src (unwrapU i))
      =
      (unwrapU i).
  Proof.
    unfold interp_hCallE_src, unwrapU in *. des_ifs.
    { etrans.
      { eapply interp_hCallE_src_ret. }
      { grind. }
    }
    { etrans.
      { eapply interp_hCallE_src_triggerUB. }
      { unfold triggerUB. grind. }
    }
  Qed.

  Lemma interp_hCallE_src_unwrapN
        (R: Type)
        (i: option R)
    :
      (interp_hCallE_src (unwrapN i))
      =
      (unwrapN i).
  Proof.
    unfold interp_hCallE_src, unwrapN in *. des_ifs.
    { etrans.
      { eapply interp_hCallE_src_ret. }
      { grind. }
    }
    { etrans.
      { eapply interp_hCallE_src_triggerNB. }
      { unfold triggerNB. grind. }
    }
  Qed.

  Lemma interp_hCallE_src_assume
        P
    :
      (interp_hCallE_src (assume P))
      =
      (assume P;; tau;; Ret tt)
  .
  Proof.
    unfold assume. rewrite interp_hCallE_src_bind. rewrite interp_hCallE_src_triggere. grind. eapply interp_hCallE_src_ret.
  Qed.

  Lemma interp_hCallE_src_guarantee
        P
    :
      (interp_hCallE_src (guarantee P))
      =
      (guarantee P;; tau;; Ret tt).
  Proof.
    unfold guarantee. rewrite interp_hCallE_src_bind. rewrite interp_hCallE_src_triggere. grind. eapply interp_hCallE_src_ret.
  Qed.

  Lemma interp_hCallE_src_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      (interp_hCallE_src itr0)
      =
      (interp_hCallE_src itr1)
  .
  Proof. subst; et. Qed.

  Global Program Instance interp_hCallE_src_rdb: red_database (mk_box (@interp_hCallE_src)) :=
    mk_rdb
      0
      (mk_box interp_hCallE_src_bind)
      (mk_box interp_hCallE_src_tau)
      (mk_box interp_hCallE_src_ret)
      (mk_box interp_hCallE_src_hcall)
      (mk_box interp_hCallE_src_triggere)
      (mk_box interp_hCallE_src_triggerp)
      (mk_box interp_hCallE_src_triggerp)
      (mk_box interp_hCallE_src_triggerUB)
      (mk_box interp_hCallE_src_triggerNB)
      (mk_box interp_hCallE_src_unwrapU)
      (mk_box interp_hCallE_src_unwrapN)
      (mk_box interp_hCallE_src_assume)
      (mk_box interp_hCallE_src_guarantee)
      (mk_box interp_hCallE_src_ext)
  .

  Global Opaque interp_hCallE_src.

End KMODSEM.
End KModSem.



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

