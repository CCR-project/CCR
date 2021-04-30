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
Require Import Hoare.

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

  Definition transl_itr: (callE +' pE +' eventE) ~> itree (hCallE +' pE +' eventE) :=
    (* embed ∘ transl_event *) (*** <- it works but it is not handy ***)
    fun _ e => trigger (transl_event e)
  .

  Definition transl_fun: (list val -> itree (callE +' pE +' eventE) val) -> fspecbody :=
    fun ktr =>
      (* mk_specbody fspec_trivial2 (fun '(vargs, _) => interp (T:=val) transl_itr (ktr vargs)) *)
      mk_specbody fspec_trivial2 (interp (T:=val) transl_itr ∘ ktr ∘ fst)
  .

  Definition to_smodsem (ms: t): SModSem.t := {|
    SModSem.fnsems := List.map (map_snd transl_fun) ms.(fnsems);
    SModSem.mn := ms.(mn);
    SModSem.initial_mr := ε;
    SModSem.initial_st := ms.(initial_st);
  |}
  .

End UMODSEM.
End UModSem.




Module UMod.
Section UMOD.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    get_modsem: SkEnv.t -> UModSem.t;
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

  Definition transl_itr_tgt: (hCallE +' pE +' eventE) ~> itree (hCallE +' pE +' eventE) :=
    fun _ e => trigger (transl_event_tgt e)
  .

  Definition transl_fsb (fsb: fspecbody): HoareDef.fspecbody :=
    HoareDef.mk_specbody fsb (interp (T:=_) transl_itr_tgt ∘ fsb.(fsb_body))
  .

  Coercion transl_fsb: fspecbody >-> HoareDef.fspecbody.

  Definition to_tgt (ms: t): SModSem.t := {|
    SModSem.fnsems := List.map (map_snd transl_fsb) ms.(fnsems);
    SModSem.mn := ms.(mn);
    SModSem.initial_mr := ms.(initial_mr);
    SModSem.initial_st := ms.(initial_st);
  |}
  .

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

  Lemma interp_oCallE_src_bind
        `{E -< Es} A B
        (itr: itree (hCallE +' E) A) (ktr: A -> itree (hCallE +' E) B)
    :
      interp_hCallE_src (v <- itr ;; ktr v) = v <- interp_hCallE_src (itr);; interp_hCallE_src (ktr v)
  .
  Proof. unfold interp_hCallE_src. ired. grind. Qed.

End KMODSEM.
End KModSem.




Module KMod.
Section KMOD.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    get_modsem: SkEnv.t -> KModSem.t;
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






Global Program Instance Forall2_Reflexive `{Reflexive A R}: Reflexive (Forall2 R).
Next Obligation. induction x; ii; ss. econs; ss. Qed.

Global Program Instance Forall2_Transitive `{Transitive A R}: Transitive (Forall2 R).
Next Obligation.
  revert_until x. induction x; ii; ss.
  { inv H0. inv H1. ss. }
  inv H0. inv H1. econs; ss; et.
Qed.

Global Program Instance Forall2_PreOrder `{PreOrder A R}: PreOrder (Forall2 R).







Require Import SimModSem.
Require Import Hoare.
Require Import HTactics YPM.

Lemma resum_itr_bind
      E F R S
      `{E -< F}
      (itr: itree E R) (ktr: ktree E R S)
  :
    resum_itr (F:=F) (itr >>= ktr) = resum_itr itr >>= (fun r => resum_itr (ktr r))
.
Proof. unfold resum_itr. grind. Qed.

Lemma resum_itr_ret
      E F R
      `{E -< F}
      (r: R)
  :
    resum_itr (F:=F) (Ret r) = Ret r
.
Proof. unfold resum_itr. grind. Qed.

Lemma resum_itr_tau
      E F R
      `{E -< F}
      (itr: itree E R)
  :
    resum_itr (F:=F) (tau;; itr) = tau;; resum_itr itr
.
Proof. unfold resum_itr. grind. Qed.

Lemma transl_event_pE
      T (e: pE T)
  :
    (UModSem.transl_event (|e|)) = (|e|)%sum
.
Proof. grind. Qed.

Lemma transl_event_eventE
      T (e: eventE T)
  :
    (UModSem.transl_event (||e)) = (||e)%sum
.
Proof. grind. Qed.

Lemma transl_event_callE
      fn args
  :
    (UModSem.transl_event ((Call fn args)|))%sum = ((hCall false fn (Any.pair args false↑))|)%sum
.
Proof. grind. Qed.

Section RESUM.

  Context {E F: Type -> Type}.
  Context `{eventE -< E}.
  Context `{E -< F}.

  (* Global Program Instance ReSum_PreOrder: CRelationClasses.PreOrder (ReSum IFun). *)
  (* Next Obligation. ii. eapply X. Defined. *)
  (* Next Obligation. ii. eapply X0. eapply X. eapply X1. Defined. *)

  Let eventE_F: eventE -< F. rr. ii. eapply H0. eapply H. eapply X. Defined.
  Local Existing Instance eventE_F.

  Lemma resum_itr_triggerNB
        X
    :
      resum_itr (triggerNB: itree E X) = (triggerNB: itree F X)
  .
  Proof. unfold resum_itr, triggerNB. rewrite unfold_interp. cbn. grind. Qed.

  Lemma resum_itr_unwrapN
        X (x: option X)
    :
      resum_itr (unwrapN x: itree E X) = (unwrapN x: itree F X)
  .
  Proof.
    destruct x.
    - cbn. rewrite resum_itr_ret. refl.
    - cbn. rewrite resum_itr_triggerNB. refl.
  Qed.

  Lemma resum_itr_triggerUB
        X
    :
      resum_itr (triggerUB: itree E X) = (triggerUB: itree F X)
  .
  Proof. unfold resum_itr, triggerUB. rewrite unfold_interp. cbn. grind. Qed.

  Lemma resum_itr_unwrapU
        X (x: option X)
    :
      resum_itr (unwrapU x: itree E X) = (unwrapU x: itree F X)
  .
  Proof.
    destruct x.
    - cbn. rewrite resum_itr_ret. refl.
    - cbn. rewrite resum_itr_triggerUB. refl.
  Qed.

End RESUM.

Lemma pair_downcast_lemma2
      T U (v0 v1: T) x (u: U)
  :
    (Any.pair x v0↑)↓ = Some (u, v1) -> v0 = v1 /\ x↓ = Some u
.
Proof.
  admit "ez".
Qed.




Section LEMMA.

  Context `{Σ: GRA.t}.

  Lemma hcall_clo
        (mr_src1 fr_src1 rarg_src: Σ)
        R0 R1
        (o: ord) (fs: fspec) (x: __shelve__ fs.(X))
        r rg (n: nat) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)

        (UPDATABLE: URA.updatable (URA.add mr_src0 fr_src0) (URA.add mr_src1 (URA.add rarg_src fr_src1)))
        (FUEL: (15 < n)%ord)
        (PRE: fs.(precond) x varg_src varg_tgt o rarg_src)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))
        (WF: wf ((mr_src1, mp_src0), mrs_tgt))
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> R0 -> R1 -> Prop)
        (POST: forall (vret_tgt : Any.t) (mrs_src1 mrs_tgt1 : (Σ * Any.t))
                      (rret: Σ) vret_src
                      (WF: wf (mrs_src1, mrs_tgt1)),
            exists (mr_src2: Σ) (mp_src2: Any.t),
              (<<LOOKUP: mrs_src1 = (mr_src2, mp_src2)>>) /\
              forall (VALID: URA.wf (URA.add mr_src2 (URA.add fr_src1 rret)))
                     (POST: fs.(postcond) x vret_src vret_tgt rret),
                gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr 100
                       (mrs_src1, URA.add fr_src1 rret, k_src vret_src) (mrs_tgt1, frs_tgt, k_tgt vret_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n
             (mr_src0, mp_src0, fr_src0, (HoareCall tbr ord_cur fs fn varg_src) >>= k_src)
             (mrs_tgt, frs_tgt, trigger (Call fn varg_tgt) >>= k_tgt).
  Proof.
  Admitted.

  Lemma hcall_clo2
        R0 R1
        (mr_src1 fr_src1 rarg_src: Σ)
        (o: ord) X (x: __shelve__ X)
        r rg (n: nat) mr_src0 mp_src0 fr_src0 Y Z
        (P: X -> Y -> Any.t -> ord -> Σ -> Prop)
        (Q: X -> Z -> Any.t -> Σ -> Prop)
        mrs_tgt frs_tgt k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)

        (UPDATABLE: URA.updatable (URA.add mr_src0 fr_src0) (URA.add mr_src1 (URA.add rarg_src fr_src1)))
        (FUEL: (15 < n)%ord)
        (PRE: P x varg_src varg_tgt o rarg_src)
        (PURE: ord_lt o ord_cur /\
               (tbr = true -> is_pure o) /\ (tbr = false -> o = ord_top))
        (WF: wf ((mr_src1, mp_src0), mrs_tgt))
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> R0 -> R1 -> Prop)
        (POST: forall (vret_tgt : Any.t) (mrs_src1 mrs_tgt1 : (Σ * Any.t))
                      (rret: Σ) (vret_src: Z)
                      (WF: wf (mrs_src1, mrs_tgt1)),
            exists (mr_src2: Σ) (mp_src2: Any.t),
              (<<LOOKUP: mrs_src1 = (mr_src2, mp_src2)>>) /\
              forall (VALID: URA.wf (URA.add mr_src2 (URA.add fr_src1 rret)))
                     (POST: Q x vret_src vret_tgt rret),
                gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr 100
                       (mrs_src1, URA.add fr_src1 rret, k_src vret_src) (mrs_tgt1, frs_tgt, k_tgt vret_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n
             (mr_src0, mp_src0, fr_src0, (HoareCall tbr ord_cur (mk P Q) fn varg_src) >>= k_src)
             (mrs_tgt, frs_tgt, trigger (Call fn varg_tgt) >>= k_tgt).
  Proof.
  Admitted.

End LEMMA.









Section ADQ.
  Context `{Σ: GRA.t}.

  Variable _kmds: list KMod.t.
  Let kmds: list SMod.t := List.map (disclose_smod ∘ KMod.to_tgt) _kmds.
  Let kmds_top: list Mod.t := List.map KMod.to_src _kmds.
  Variable umds: list UMod.t.

  Let sk_link: Sk.t := fold_right Sk.add Sk.unit ((List.map SMod.sk kmds) ++ (List.map UMod.sk umds)).
  Let skenv: SkEnv.t := Sk.load_skenv sk_link.

  Let _kmss: SkEnv.t -> list SModSem.t := fun ske => List.map (flip SMod.get_modsem ske) kmds.
  Let _umss: SkEnv.t -> list UModSem.t := fun ske => List.map (flip UMod.get_modsem ske) umds.
  Let _gstb: SkEnv.t -> list (gname * fspec) := fun ske =>
    (flat_map (List.map (map_snd fsb_fspec) ∘ SModSem.fnsems) (_kmss ske))
      ++ (flat_map (List.map (map_snd (fun _ => fspec_trivial2)) ∘ UModSem.fnsems) (_umss ske)).

  Let kmss: list SModSem.t := Eval red in (_kmss skenv).
  Let umss: list UModSem.t := Eval red in (_umss skenv).
  Let gstb: list (gname * fspec) := Eval red in (_gstb skenv).
  (* Let gstb: list (gname * fspec) := *)
  (*   (flat_map (List.map (map_snd fsb_fspec) ∘ SModSem.fnsems) kmss) *)
  (*     ++ (flat_map (List.map (map_snd (fun _ => fspec_trivial2)) ∘ UModSem.fnsems) umss). *)

  (* Lemma resub_l *)
  (*       (E1 E2: Type -> Type) *)
  (*       `{E1 -< E} *)
  (*       `{E2 -< E} *)
  (*       T (e: E1 T) *)
  (*   : *)
  (*     subevent (F:=E) _ (@inl1 E1 E2 _ e)%sum = subevent _ e *)
  (* . *)
  (* Proof. refl. Qed. *)

  (* Lemma resub_r *)
  (*       (E1 E2: Type -> Type) *)
  (*       `{E1 -< E} *)
  (*       `{E2 -< E} *)
  (*       T (e: E2 T) *)
  (*   : *)
  (*     (* subevent (F:=E) _ (@inr1 E1 E2 _ e)%sum = subevent _ e *) *)
  (*     subevent _ (@inr1 E1 E2 _ e)%sum = subevent _ e *)
  (* . *)
  (* Proof. refl. Qed. *)

  Ltac red_resum := repeat (try rewrite resum_itr_bind; try rewrite resum_itr_tau; try rewrite resum_itr_ret;
                            try rewrite resum_itr_triggerNB; try rewrite resum_itr_unwrapN;
                            try rewrite resum_itr_triggerUB; try rewrite resum_itr_unwrapU
                           ).

  Lemma my_lemma1_aux
        mrs ktr arg ske
    :
      sim_itree (fun '(x, y) => x = y) 100%nat
                (mrs, ε, fun_to_tgt (_gstb ske) (UModSem.transl_fun ktr) arg)
                (mrs, ε, resum_itr (cfun ktr arg))
  .
  Proof.
    destruct mrs as [mr st].
    ginit.
    revert_until gstb. gcofix CIH. i.
    unfold cfun. unfold UModSem.transl_fun. unfold fun_to_tgt. cbn.
    unfold HoareFun, put, forge, checkWf, discard. ss.
    steps. des. subst.
    red_resum. steps. red_resum.
    r in _ASSUME0. des. subst. destruct x as [argl is_k]. apply pair_downcast_lemma2 in _ASSUME0. des. subst.
    clarify.
    guclo lordC_spec. econs.
    { instantiate (1:=(45 + 45)%ord). rewrite <- OrdArith.add_from_nat. eapply OrdArith.le_from_nat. lia. }
    red_resum.
    guclo lbindC_spec. econs; cycle 1.
    - instantiate (1:=fun '(mr0, st0, fr0) '(mr1, st1, fr1) y0 y1 => mr0 = mr1 /\ st0 = st1 /\ y0 = y1).
      i. ss. des_ifs. des; subst.
      red_resum.
      force_l. esplits. force_l. eexists (_, _). steps. force_l. { refl. } steps.
      force_l. esplits. force_l. { esplits; ss; et. } steps.
      force_l. esplits. force_l. { rewrite URA.unit_id. refl. } steps.
    - unfold body_to_tgt. steps.
      abstr (ktr argl) itr. clear arg _UNWRAPN argl ktr.
      (* clear _ASSUME0. *)
      des_u. rewrite URA.unit_idl in *.
      revert itr. revert st. revert_until CIH. gcofix CIH0. i.
      ides itr.
      { interp_red. cbn. steps. red_resum. gstep. econs; eauto. }
      { interp_red. cbn. red_resum. steps. red_resum. steps. gbase. eapply CIH0; et. }
      destruct e; cycle 1.
      {
        rewrite unfold_interp. steps.
        destruct s; ss.
        { destruct p; ss.
          - unfold UModSem.transl_itr at 2.
            rewrite <- bind_trigger. red_resum. unfold resum_itr at 2. rewrite transl_event_pE.
            rewrite ! unfold_interp. cbn.
            repeat match goal with
            | [ |- context[trigger ?e]] =>
              replace (trigger e%sum) with (trigger e: itree (hCallE +' pE +' eventE) _) by refl
            | [ |- context[trigger ?e]] =>
              replace (trigger e%sum) with (trigger e: itree Es _) by refl
            end.
            ired_both.
            gstep. econs. steps.
            interp_red. steps.
            gbase. eapply CIH0; et.
          - unfold UModSem.transl_itr at 2.
            rewrite <- bind_trigger. red_resum. unfold resum_itr at 2. rewrite transl_event_pE.
            rewrite ! unfold_interp. cbn.
            repeat match goal with
            | [ |- context[trigger ?e]] =>
              replace (trigger e%sum) with (trigger e: itree (hCallE +' pE +' eventE) _) by refl
            | [ |- context[trigger ?e]] =>
              replace (trigger e%sum) with (trigger e: itree Es _) by refl
            end.
            ired_both.
            gstep. econs. steps. 
            interp_red. steps.
            gbase. eapply CIH0; et.
        }
        { destruct e.
          - unfold UModSem.transl_itr at 2.
            rewrite <- bind_trigger. red_resum. unfold resum_itr at 2. rewrite transl_event_eventE.
            rewrite ! unfold_interp. cbn.
            repeat match goal with
            | [ |- context[trigger ?e]] =>
              replace (trigger e%sum) with (trigger e: itree (hCallE +' pE +' eventE) _) by refl
            | [ |- context[trigger ?e]] =>
              replace (trigger e%sum) with (trigger e: itree Es _) by refl
            end.
            ired_both.
            gstep. econs. i. esplits. steps.
            interp_red. steps.
            gbase. eapply CIH0; et.
          - unfold UModSem.transl_itr at 2.
            rewrite <- bind_trigger. red_resum. unfold resum_itr at 2. rewrite transl_event_eventE.
            rewrite ! unfold_interp. cbn.
            repeat match goal with
            | [ |- context[trigger ?e]] =>
              replace (trigger e%sum) with (trigger e: itree (hCallE +' pE +' eventE) _) by refl
            | [ |- context[trigger ?e]] =>
              replace (trigger e%sum) with (trigger e: itree Es _) by refl
            end.
            ired_both.
            gstep. econs. i. esplits. steps. 
            interp_red. steps.
            gbase. eapply CIH0; et.
          - unfold UModSem.transl_itr at 2.
            rewrite <- bind_trigger. red_resum. unfold resum_itr at 2. rewrite transl_event_eventE.
            rewrite ! unfold_interp. cbn.
            repeat match goal with
            | [ |- context[trigger ?e]] =>
              replace (trigger e%sum) with (trigger e: itree (hCallE +' pE +' eventE) _) by refl
            | [ |- context[trigger ?e]] =>
              replace (trigger e%sum) with (trigger e: itree Es _) by refl
            end.
            ired_both.
            gstep. econs. i. esplits. steps. 
            interp_red. steps.
            gbase. eapply CIH0; et.
        }
      }
      destruct c.
      rewrite <- bind_trigger.
      red_resum. interp_red. steps. interp_red. steps.
      unfold UModSem.transl_itr at 2. rewrite transl_event_callE. steps.
      force_l.
      { admit "TODO". }
      steps. force_l.
      { admit "TODO". }
      steps.
      replace (resum_itr (F:=Es) (ITree.trigger (Call fn args|)%sum)) with
          (r <- trigger (Call fn args);; tau;; Ret r: itree Es _); cycle 1.
      { unfold resum_itr. interp_red. grind. }
      rename _UNWRAPN into T. ired_both.

      {
        assert (GWF: ☀) by (split; [refl|exact _ASSUME]); clear _ASSUME.
        iRefresh.
        eapply find_some in T. des; des_sumbool; subst. unfold _gstb in T. rewrite in_app_iff in *. des; ss.
        - rewrite in_flat_map in *. des; ss. rewrite in_map_iff in *. des. unfold map_snd in T0. des_ifs.
          unfold _kmss in T. rewrite in_map_iff in *. des. subst. unfold flip in T1.
          unfold kmds in T0. rewrite in_map_iff in *. des. subst. ss. rewrite in_map_iff in *. des.
          unfold map_snd in T1. des_ifs. ss.
          destruct a. eapply pair_downcast_lemma2 in _UNWRAPN0. des. subst.
          eapply hcall_clo with (fs:=disclose f); try refl.
          { rewrite URA.unit_idl. refl. }
          { eapply OrdArith.lt_from_nat. lia. }
          { instantiate (1:=ord_top). instantiate(1:=None). cbn. iRefresh.
            iSplitP; ss.
            right; iRefresh. repeat split; ss. eapply Any.downcast_upcast; et. }
          { ss. }
          i. subst. ss. destruct mrs_tgt1. esplits; et. i.
          clear GWF. assert(GWF: ☀) by (split; [refl|exact VALID]).
          iRefresh.
          destruct POST; iRefresh.
          { iDestruct H. iDestruct H. iPure H. ss. }
          iPure H. des; subst.
          steps. gbase. eapply CIH0; et.
        - rewrite in_flat_map in *. des; ss. rewrite in_map_iff in *. des. unfold map_snd in T0. des_ifs.
          destruct a as [argl is_k].
          eapply pair_downcast_lemma2 in _UNWRAPN0. des. subst.
          eapply hcall_clo; try refl.
          { rewrite URA.unit_idl. refl. }
          { eapply OrdArith.lt_from_nat. lia. }
          { instantiate (1:=ord_top). instantiate(1:=tt). cbn. split; ss. admit "should be ez". }
          { ss. }
          i. subst. ss. destruct mrs_tgt1. esplits; et. i.
          clear GWF. assert(GWF: ☀) by (split; [refl|exact VALID]).
          iRefresh.
          destruct POST; iRefresh.
          steps. gbase. eapply CIH0; et.
      }
  Unshelve.
    all: try (by apply Ord.O).
  Qed.

  Lemma my_lemma1
        umd
        (IN: In umd umds)
    :
      ModPair.sim (SMod.to_tgt _gstb (UMod.to_smod umd)) (UMod.to_mod umd)
  .
  Proof.
    econs; ss; cycle 1.
    { admit "ez - wf". }
    i. r. eapply adequacy_lift.
    econs.
    { instantiate (1:=fun '(x, y) => x = y). ss.
      set (ums:=UMod.get_modsem umd skenv0) in *.
      rewrite ! List.map_map.
      eapply Forall2_apply_Forall2.
      { refl. }
      i. subst. unfold map_snd. des_ifs.
      rr. split; ss. r. ii. subst. ss. esplits; et. eapply my_lemma1_aux.
    }
    { ss. }
    { ss. }
  Qed.

  Lemma sk_link_eq: sk_link = (fold_right Sk.add Sk.unit (List.map SMod.sk
                                          (kmds ++ List.map UMod.to_smod umds))).
  Proof.
    unfold sk_link. f_equal. rewrite List.map_app. f_equal; ss.
    { rewrite List.map_map; ss. }
  Qed.

  Declare Scope l_monad_scope.
  Local Open Scope l_monad_scope.
  Notation "'do' X <- A ; B" := (List.flat_map (fun X => B) A) : l_monad_scope.
  Notation "'do' ' X <- A ; B" := (List.flat_map (fun _x => match _x with | X => B end) A) : l_monad_scope.
  Notation "'ret'" := (fun X => [X]) (at level 60) : l_monad_scope.

  Require Import SimGlobal.

  Ltac steps := HoareDef.steps.

  Let ms_src := (ModL.enclose (Mod.add_list (kmds_top ++ List.map UMod.to_mod umds))).
  Let p_src := (ModSemL.prog ms_src).
  Let ms_tgt := (ModL.enclose (Mod.add_list (List.map SMod.to_src (kmds ++ List.map UMod.to_smod umds)))).
  Let p_tgt := (ModSemL.prog ms_tgt).

  Lemma add_list_fnsems
        mds ske
    :
      (ModSemL.fnsems (ModL.get_modsem (Mod.add_list mds) ske)) =
      flat_map ModSemL.fnsems (List.map (flip ModL.get_modsem ske ∘ Mod.lift) mds)
  .
  Proof. induction mds; ss. f_equal. et. Qed.

  Let sk_link_eq2: sk_link = (ModL.sk (Mod.add_list (List.map SMod.to_src (kmds ++ List.map UMod.to_smod umds)))).
  Proof. { rewrite sk_link_eq. unfold SMod.to_src. rewrite SMod.transl_sk. refl. } Qed.

  Lemma add_list_sk
        xs ys
        (SIM: Forall2 (fun x y => Mod.sk x = Mod.sk y) xs ys)
    :
      ModL.sk (Mod.add_list xs) = ModL.sk (Mod.add_list ys)
  .
  Proof. induction SIM; ss. unfold Mod.add_list in IHSIM. rewrite IHSIM. f_equal. et. Qed.

  Let sk_link_eq3: sk_link = (ModL.sk (Mod.add_list (kmds_top ++ List.map UMod.to_mod umds))).
  Proof.
    rewrite sk_link_eq2. eapply add_list_sk. rewrite map_app. eapply Forall2_app.
    - unfold kmds_top. unfold kmds.
      rewrite List.map_map. eapply Forall2_apply_Forall2. { refl. } i. subst. ss.
    - rewrite List.map_map. eapply Forall2_apply_Forall2. { refl. } i. subst. ss.
  Qed.

  Inductive _sim_body (sim_body: forall [T], Ord.t -> itree EventsL.Es T -> itree EventsL.Es T -> Prop):
    forall [T], Ord.t -> itree EventsL.Es T -> itree EventsL.Es T -> Prop :=
  | sim_body_tau
      o0 o1
      T (itr0 itr1: itree _ T)
      (SIM: sim_body o1 itr0 itr1)
    :
      _sim_body sim_body o0 (tau;; itr0) (tau;; itr1)
  | sim_body_ret
      o0
      T (t: T)
    :
      _sim_body sim_body o0 (Ret t) (Ret t)
  | sim_body_call
      o0 o1
      fn args T (ktr0 ktr1: ktree _ _ T)
      (SIM: forall rv, sim_body o1 (ktr0 rv) (ktr1 rv))
    :
      _sim_body sim_body o0 (trigger EventsL.PushFrame;; trigger (Call fn args) >>= ktr0)
                (trigger EventsL.PushFrame;; trigger (Call fn (Any.pair args false↑)) >>= ktr1)
  | sim_rE
      o0 o1
      T (re: EventsL.rE T) S (ktr0 ktr1: ktree _ _ S)
      (SIM: forall rv, sim_body o1 (ktr0 rv) (ktr1 rv))
    :
      _sim_body sim_body o0 (trigger re >>= ktr0) (trigger re >>= ktr1)
  | sim_pE
      o0 o1
      T (pe: EventsL.pE T) S (ktr0 ktr1: ktree _ _ S)
      (SIM: forall rv, sim_body o1 (ktr0 rv) (ktr1 rv))
    :
      _sim_body sim_body o0 (trigger pe >>= ktr0) (trigger pe >>= ktr1)
  | sim_eventE
      o0 o1
      T (ee: eventE T) S (ktr0 ktr1: ktree _ _ S)
      (SIM: forall rv, sim_body o1 (ktr0 rv) (ktr1 rv))
    :
      _sim_body sim_body o0 (trigger ee >>= ktr0) (trigger ee >>= ktr1)

  | sim_body_tauL
      o0 o1
      T (itr0 itr1: itree _ T)
      (SIM: sim_body o1 itr0 itr1)
      (LT: (o1 < o0)%ord)
    :
      _sim_body sim_body o0 (tau;; itr0) (itr1)
  | sim_body_tauR
      o0 o1
      T (itr0 itr1: itree _ T)
      (SIM: sim_body o1 itr0 itr1)
      (LT: (o1 < o0)%ord)
    :
      _sim_body sim_body o0 (itr0) (tau;; itr1)
  .

  Definition sim_body: forall [T], Ord.t -> itree EventsL.Es T -> itree EventsL.Es T -> Prop := paco4 _sim_body bot4.

  Lemma sim_body_mon: monotone4 _sim_body.
  Proof.
    ii. dependent destruction IN; try (by econs; et).
  Qed.

  Hint Constructors _sim_body.
  Hint Unfold sim_body.
  Hint Resolve sim_body_mon: paco.

  Lemma sim_body_mon_ord r S i0 i1 (ORD: (i0 <= i1)%ord): @_sim_body r S i0 <2= @_sim_body r S i1.
  Proof.
    ii. dependent destruction PR; try (by econs; et).
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
  Qed.

  Variant bbindR (r s: forall S, Ord.t -> (itree EventsL.Es S) -> (itree EventsL.Es S) -> Prop):
    forall S, Ord.t -> (itree _ S) -> (itree _ S) -> Prop :=
  | bbindR_intro
      o0 o1

      R
      (i_src i_tgt: itree _ R)
      (SIM: r _ o0 i_src i_tgt)

      S
      (k_src k_tgt: ktree _ R S)
      (SIMK: forall vret, s _ o1 (k_src vret) (k_tgt vret))
    :
      bbindR r s (o1 + o0)%ord (i_src >>= k_src) (i_tgt >>= k_tgt)
  .

  Hint Constructors bbindR: core.

  Lemma bbindR_mon
        r1 r2 s1 s2
        (LEr: r1 <4= r2) (LEs: s1 <4= s2)
    :
      bbindR r1 s1 <4= bbindR r2 s2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Definition bbindC r := bbindR r r.
  Hint Unfold bbindC: core.

  Lemma bbindC_wrespectful: wrespectful4 (_sim_body) bbindC.
  Proof.
    econstructor; repeat intro.
    { eapply bbindR_mon; eauto. }
    rename l into llll.
    eapply bbindR_mon in PR; cycle 1.
    { eapply GF. }
    { i. eapply PR0. }
    inv PR. csc. dependent destruction SIM.
    + irw. econs; eauto.
      { econs 2; eauto with paco. econs; eauto with paco. }
    + irw.
      exploit SIMK; eauto. i.
      eapply sim_body_mon_ord.
      { instantiate (1:=o1). eapply OrdArith.add_base_l. }
      eapply sim_body_mon; eauto with paco.
    + rewrite ! bind_bind.
      econs; eauto. ii.
      { econs 2; eauto with paco. econs; eauto with paco. }
    + rewrite ! bind_bind. econs; eauto. ii.
      { econs 2; eauto with paco. econs; eauto with paco. }
    + rewrite ! bind_bind. econs; eauto. ii.
      { econs 2; eauto with paco. econs; eauto with paco. }
    + rewrite ! bind_bind. econs; eauto. ii.
      { econs 2; eauto with paco. econs; eauto with paco. }
    + ired. econsr; eauto.
      { econs 2; eauto with paco. econs; eauto with paco. }
      eapply OrdArith.lt_add_r; et.
    + ired. econsr; eauto.
      { econs 2; eauto with paco. econs; eauto with paco. }
      eapply OrdArith.lt_add_r; et.
  Qed.

  Lemma bbindC_spec: bbindC <5= gupaco4 (_sim_body) (cpn4 (_sim_body)).
  Proof.
    intros. eapply wrespect4_uclo; eauto with paco. eapply bbindC_wrespectful.
  Qed.

  Definition sim_fun T (f0 f1: (Any.t -> itree EventsL.Es T)): Prop :=
    forall args, sim_body 100 (f0 args) (f1 (Any.pair args false↑))
  .

  Ltac red_transl_all :=
    repeat (try rewrite transl_all_bind; try rewrite transl_all_ret; try rewrite transl_all_tau;
            try rewrite transl_all_triggerNB;
            try rewrite transl_all_triggerUB;
            try rewrite Hoareproof0.transl_all_unwrapN;
            try rewrite Hoareproof0.transl_all_unwrapU;
            try rewrite Hoareproof0.transl_all_assume;
            try rewrite Hoareproof0.transl_all_guarantee;
            try rewrite transl_all_eventE;
            try rewrite transl_all_rE;
            try rewrite transl_all_pE;
            try rewrite transl_all_callE
           )
  .




  Lemma sim_known_aux
        T mn (itr: itree _ T)
    :
      sim_body 100 (transl_all mn (KModSem.interp_hCallE_src itr))
               (transl_all mn (interp_hCallE_src (interp KModSem.transl_itr_tgt itr)))
  .
  Proof.
    ginit. { eapply cpn4_wcompat; eauto with paco. } revert itr. gcofix CIH. i.
    ides itr.
    { red_resum. red_transl_all. rewrite interp_ret. unfold interp_hCallE_src, KModSem.interp_hCallE_src.
      rewrite ! interp_ret. red_transl_all. gstep; econs; et. }
    { red_resum. red_transl_all. rewrite interp_tau. unfold interp_hCallE_src, KModSem.interp_hCallE_src.
      rewrite ! interp_tau. red_transl_all. gstep; econs; et. gbase. eapply CIH. }
    destruct e.
    { destruct h.
      rewrite unfold_interp. cbn.
      unfold KModSem.interp_hCallE_src. rewrite unfold_interp. cbn.
      rewrite interp_hCallE_src_bind.
      red_transl_all.
      unfold KModSem.transl_itr_tgt at 2. cbn.
      unfold interp_hCallE_src at 2. rewrite unfold_interp. cbn.
      ired. red_transl_all. ired.
      des_ifs.
      - red_transl_all. ired.
        gstep; econs; et.
        gstep; econs; et. ii.
        red_transl_all. ired.
        gstep; econs; et.
        red_transl_all. ired.
        gstep; econs; et.
        unfold interp_hCallE_src at 1. rewrite interp_tau. red_transl_all.
        instantiate (1:=101).
        gstep; econs; et; [|by eapply OrdArith.lt_from_nat; ss].
        gbase. eapply CIH; et.
      - red_transl_all. ired.
        gstep; econs; et. ii.
        red_transl_all. ired.
        gstep; econs; et.
        red_transl_all. ired.
        gstep; econs; et.
        unfold interp_hCallE_src at 1. rewrite interp_tau. red_transl_all.
        gstep; econs; et.
        instantiate (1:=101).
        gstep; econs; et; [|by eapply OrdArith.lt_from_nat; ss].
        gbase. eapply CIH; et.
    }
    destruct s.
    { rewrite unfold_interp. cbn.
      unfold KModSem.interp_hCallE_src. rewrite unfold_interp. cbn.
      rewrite interp_hCallE_src_bind.
      red_transl_all.
      unfold KModSem.transl_itr_tgt at 2. cbn.
      unfold interp_hCallE_src at 2. rewrite unfold_interp. cbn.
      ired. red_transl_all. ired.
      gstep; econs; et. ii.
      red_transl_all. ired.
      gstep; econs; et.
      red_transl_all. ired.
      gstep; econs; et.
      unfold interp_hCallE_src at 1. rewrite interp_tau. red_transl_all.
      instantiate (1:=101).
      gstep; econs; et; [|by eapply OrdArith.lt_from_nat; ss].
      gbase. eapply CIH; et.
    }
    { rewrite unfold_interp. cbn.
      unfold KModSem.interp_hCallE_src. rewrite unfold_interp. cbn.
      rewrite interp_hCallE_src_bind.
      red_transl_all.
      unfold KModSem.transl_itr_tgt at 2. cbn.
      unfold interp_hCallE_src at 2. rewrite unfold_interp. cbn.
      ired. red_transl_all. ired.
      gstep; econs; et. ii.
      red_transl_all. ired.
      gstep; econs; et.
      red_transl_all. ired.
      gstep; econs; et.
      unfold interp_hCallE_src at 1. rewrite interp_tau. red_transl_all.
      instantiate (1:=101).
      gstep; econs; et; [|by eapply OrdArith.lt_from_nat; ss].
      gbase. eapply CIH; et.
    }
  Unshelve.
    all: try (by exact Ord.O).
  Qed.

  Lemma sim_known
        mn (f0: fspecbody)
    :
      sim_fun (transl_all mn ∘ KModSem.fun_to_src (fsb_body f0))
              (transl_all mn ∘ fun_to_src
                          (fun pat => match pat with
                                      | (_, true) => trigger (Choose _)
                                      | (argh, false) => interp KModSem.transl_itr_tgt (fsb_body f0 argh)
                                      end))
  .
  Proof.
    ii.
    esplits.
    unfold fun_to_src. unfold body_to_src. unfold cfun.
    unfold KModSem.fun_to_src. unfold KModSem.body_to_src. unfold cfun.
    red_resum.
    red_transl_all.
    destruct (args↓) eqn:A; cycle 1.
    { cbn.
      destruct ((Any.pair args false↑)↓) eqn:B.
      { ss. destruct p. eapply pair_downcast_lemma2 in B. des. clarify. }
      { ss.
        Fail rewrite transl_all_triggerNB. (******** WHY??? FIXME *********)
        unfold triggerNB. red_transl_all. ired.
        ginit. { eapply cpn4_wcompat; eauto with paco. } gstep. econs; et. ii; ss.
      }
    }
    cbn. erewrite <- Any.downcast_upcast with (a:=args); et. rewrite upcast_pair_downcast. ss. ired.
    red_transl_all. ired. red_resum. red_transl_all.
    replace (Ord.from_nat 100) with ((Ord.from_nat 0) + (Ord.from_nat 100))%ord; cycle 1.
    { admit "ez - ordC spec". }
    ginit. { eapply cpn4_wcompat; eauto with paco. } guclo bbindC_spec.
    econs.
    { gfinal. right. eapply sim_known_aux. }
    ii. red_resum. red_transl_all. gstep; econs; et.
  Unshelve.
    all: try (by exact Ord.O).
  Qed.

  Lemma sim_unknown_aux
        mn (itr: itree _ val)
    :
      sim_body 100 (transl_all mn (resum_itr itr))
               (transl_all mn (interp_hCallE_src (interp UModSem.transl_itr itr)))
  .
  Proof.
    ginit. { eapply cpn4_wcompat; eauto with paco. } revert itr. gcofix CIH. i.
    ides itr.
    { red_resum. red_transl_all. rewrite interp_ret. unfold interp_hCallE_src. rewrite interp_ret. red_transl_all.
      gstep; econs; et. }
    { red_resum. red_transl_all. rewrite interp_tau. unfold interp_hCallE_src. rewrite interp_tau. red_transl_all.
      gstep; econs; et. gbase. eapply CIH. }
    destruct e.
    { destruct c.
      rewrite <- bind_trigger.
      red_resum. red_transl_all.
      set (fun x => transl_all mn (resum_itr (k x))) as ksrc.
      interp_red. rewrite interp_hCallE_src_bind. red_transl_all.
      set (fun x => transl_all mn (interp_hCallE_src (interp UModSem.transl_itr (k x)))) as ktgt.
      rewrite unfold_interp. cbn. unfold resum_itr. rewrite unfold_interp. cbn.
      red_transl_all. ired.
      rewrite interp_hCallE_src_bind. red_transl_all.
      unfold UModSem.transl_itr at 2. cbn.
      unfold interp_hCallE_src at 2. rewrite interp_trigger. cbn.
      red_transl_all. ired.
      gstep; econs; et. ii.
      ired.
      gstep; econs; et. ii.
      gstep; econs; et.
      red_transl_all. ired.
      gstep; econs; et.
      unfold interp_hCallE_src. rewrite interp_tau. rewrite interp_ret. red_transl_all. ired.
      instantiate (1:=101).
      gstep; econs; et; [|by eapply OrdArith.lt_from_nat; ss].
      gbase. eapply CIH; et.
    }
    destruct s.
    { rewrite <- bind_trigger.
      red_resum. red_transl_all.
      set (fun x => transl_all mn (resum_itr (k x))) as ksrc.
      interp_red. rewrite interp_hCallE_src_bind. red_transl_all.
      set (fun x => transl_all mn (interp_hCallE_src (interp UModSem.transl_itr (k x)))) as ktgt.
      rewrite unfold_interp. cbn. unfold resum_itr. rewrite unfold_interp. cbn.
      red_transl_all. ired.
      rewrite interp_hCallE_src_bind. red_transl_all.
      unfold UModSem.transl_itr at 2. cbn.
      unfold interp_hCallE_src at 2. rewrite interp_trigger. cbn.
      red_transl_all. ired.
      gstep; econs; et. ii. ired.
      gstep; econs; et. ii. red_transl_all. ired.
      gstep; econs; et. ii. unfold interp_hCallE_src.
      rewrite unfold_interp; cbn.
      rewrite unfold_interp; cbn.
      red_transl_all. ired.
      instantiate (1:=101).
      gstep; econs; et; [|by eapply OrdArith.lt_from_nat; ss].
      gbase. eapply CIH; et.
    }
    { rewrite <- bind_trigger.
      red_resum. red_transl_all.
      set (fun x => transl_all mn (resum_itr (k x))) as ksrc.
      interp_red. rewrite interp_hCallE_src_bind. red_transl_all.
      set (fun x => transl_all mn (interp_hCallE_src (interp UModSem.transl_itr (k x)))) as ktgt.
      rewrite unfold_interp. cbn. unfold resum_itr. rewrite unfold_interp. cbn.
      red_transl_all. ired.
      rewrite interp_hCallE_src_bind. red_transl_all.
      unfold UModSem.transl_itr at 2. cbn.
      unfold interp_hCallE_src at 2. rewrite interp_trigger. cbn.
      red_transl_all. ired.
      gstep; econs; et. ii. ired.
      gstep; econs; et. ii. red_transl_all. ired.
      gstep; econs; et. ii. unfold interp_hCallE_src.
      rewrite unfold_interp; cbn.
      rewrite unfold_interp; cbn.
      red_transl_all. ired.
      instantiate (1:=101).
      gstep; econs; et; [|by eapply OrdArith.lt_from_nat; ss].
      gbase. eapply CIH; et.
    }
  Unshelve.
    all: try (by exact Ord.O).
  Qed.

  Lemma sim_unknown
        (ktr: list val -> itree _ val) mn
    :
      sim_fun (fun args => transl_all mn (resum_itr (cfun ktr args)))
              (transl_all mn ∘ fun_to_src (fun (x: list val * bool) => interp UModSem.transl_itr (ktr (fst x))))
  .
  Proof.
    ii.
    esplits.
    unfold fun_to_src. unfold body_to_src. unfold cfun.
    red_resum.
    red_transl_all.
    destruct (args↓) eqn:A; cycle 1.
    { cbn.
      destruct ((Any.pair args false↑)↓) eqn:B.
      { ss. destruct p. eapply pair_downcast_lemma2 in B. des. clarify. }
      { ss.
        Fail rewrite transl_all_triggerNB. (******** WHY??? FIXME *********)
        unfold triggerNB. red_transl_all. ired. unfold transl_all at 3. rewrite unfold_interp. cbn. ired.
        ginit. { eapply cpn4_wcompat; eauto with paco. } gstep. econs; et. ii; ss.
      }
    }
    cbn. erewrite <- Any.downcast_upcast with (a:=args); et. rewrite upcast_pair_downcast. ss. ired.
    red_transl_all. ired. red_resum. red_transl_all.
    replace (Ord.from_nat 100) with ((Ord.from_nat 0) + (Ord.from_nat 100))%ord; cycle 1.
    { admit "ez - ordC spec". }
    ginit. { eapply cpn4_wcompat; eauto with paco. } guclo bbindC_spec.
    econs.
    { gfinal. right. eapply sim_unknown_aux. }
    ii. red_resum. red_transl_all. gstep; econs; et.
  Unshelve.
    all: try (by exact Ord.O).
  Qed.

  Lemma find_sim
        fn
    :
        option_rel (fun '(fn0, fsem0) '(fn1, fsem1) => fn0 = fn1 /\ sim_fun fsem0 fsem1)
                   (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_src))
                   (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_tgt))
  .
  Proof.
    destruct (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_src)) eqn:T.
    - Ltac _list_tac :=
        match goal with
        | [ H: find _ _ = Some _ |- _ ] => apply find_some in H; des; des_sumbool; subst
        | [ H: context[ModL.enclose] |- _ ] => unfold ModL.enclose in H; try rewrite add_list_fnsems in H
        | [ H: In _ (flat_map _ _) |- _ ] => apply in_flat_map in H; des
        | [ H: In _ (List.map _ _) |- _ ] => apply in_map_iff in H; des
        | [ H: ModSem.map_snd _ _ = _ |- _ ] => unfold ModSem.map_snd in H; ss
        | [ H: map_snd _ _ = _ |- _ ] => unfold map_snd in H; ss
        | [ H: flip _ _ _ = _ |- _ ] => unfold flip in H; ss

        | [ |- context[ModL.enclose] ] => unfold ModL.enclose; try rewrite add_list_fnsems
        | [ |- In _ (flat_map _ _) ] => apply in_flat_map; esplits; et
        | [ |- In _ (List.map _ _) ] => apply in_map_iff; esplits; et
        | [ |- ModSem.map_snd _ _ = _ ] => unfold ModSem.map_snd; ss
        | [ |- map_snd _ _ = _ ] => unfold map_snd; ss
        | [ |- flip _ _ _ = _ ] => unfold flip; ss
        end
      .
      Ltac list_tac := repeat _list_tac.
      list_tac.
      unfold ms_src in T.
      list_tac.
      rewrite <- sk_link_eq3 in *. folder. subst.
      ss. list_tac. subst. des_ifs. ss. subst. list_tac. des_ifs.
      rewrite in_app_iff in *. des.
      + destruct (find (fun fnsem => dec s (fst fnsem)) (ModSemL.fnsems ms_tgt)) eqn:U.
        * list_tac. unfold ms_tgt in U. list_tac. subst. ss. list_tac.
          des_ifs. ss. rewrite <- sk_link_eq2 in *. folder.
          rewrite in_app_iff in *. des.
          { unfold kmds in U2. unfold kmds_top in T1. list_tac. subst. ss. list_tac. des_ifs. ss.
            assert(x = x1) by admit "ez - uniqueness"; subst.
            assert(f = f0) by admit "ez - uniqueness"; subst.
            econs. split; ss.
            eapply sim_known.
          }
          { unfold kmds_top in *. list_tac. subst. exfalso. admit "ez - uniqueness". }
        * exfalso.
          ss. list_tac. des_ifs. ss.
          unfold kmds_top in *. list_tac. subst. ss. list_tac. des_ifs.
          eapply find_none in U; cycle 1.
          { unfold ms_tgt. list_tac.
            { rewrite in_app_iff. left. unfold kmds. list_tac. }
            rewrite <- sk_link_eq2. folder.
            unfold flip. ss.
            list_tac.
          }
          ss. des_sumbool; ss.
      + destruct (find (fun fnsem => dec s (fst fnsem)) (ModSemL.fnsems ms_tgt)) eqn:U.
        * unfold ms_tgt in U. list_tac. subst. ss. list_tac. des_ifs. ss. econs. split; ss.
          rewrite <- sk_link_eq2 in *. folder.
          rewrite in_app_iff in *. des.
          { exfalso. unfold kmds in U2. list_tac. subst. ss. list_tac. des_ifs. admit "ez - uniqueness". }
          list_tac. subst. ss. list_tac. des_ifs. ss.
          assert(x = x3) by admit "ez - uniqueness"; subst.
          assert(i = i1) by admit "ez - uniqueness"; subst. clear_tac.
          eapply sim_unknown.
        * exfalso.
          ss. list_tac. subst. ss. list_tac. des_ifs. ss.
          eapply find_none in U; cycle 1.
          { unfold ms_tgt. list_tac.
            { rewrite in_app_iff. right. list_tac. }
            rewrite <- sk_link_eq2. folder.
            unfold flip. ss.
            list_tac.
          }
          ss. des_sumbool; ss.
    - destruct (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_tgt)) eqn:U.
      + exfalso.
        list_tac. unfold ms_tgt in U. list_tac. subst. ss. list_tac. des_ifs. ss.
        rewrite <- sk_link_eq2 in *. folder.
        rewrite in_app_iff in *. des.
        * unfold kmds in U2. list_tac. subst. ss. list_tac. des_ifs.
          eapply find_none in T; cycle 1.
          { unfold ms_src. list_tac.
            { rewrite in_app_iff. left; et. unfold kmds_top. list_tac. }
            ss. list_tac.
            rewrite <- sk_link_eq3 in *. folder. et.
          }
          ss. des_sumbool; ss.
        * list_tac. subst. ss. list_tac. des_ifs.
          eapply find_none in T; cycle 1.
          { unfold ms_src. list_tac.
            { rewrite in_app_iff. right; et. list_tac. }
            ss. list_tac.
            rewrite <- sk_link_eq3 in *. folder. et.
          }
          ss. des_sumbool; ss.
      + econs.
  Qed.

  Lemma my_lemma2_aux
        fn args st0
    :
        simg eq 200
             (* (EventsL.interp_Es p_src (trigger (Call fn args)) st0) *)
             (* (EventsL.interp_Es p_tgt (trigger (Call fn (Any.pair args false↑))) st0) *)
             (EventsL.interp_Es p_src (p_src (Call fn args)) st0)
             (EventsL.interp_Es p_tgt (p_tgt (Call fn (Any.pair args false↑))) st0)
  .
  Proof.
    ginit. { eapply cpn5_wcompat; eauto with paco. } revert_until p_tgt. gcofix CIH. i.
    cbn. steps.
    generalize (find_sim fn). intro T. inv T; cbn; steps.
    des; subst. specialize (IN0 args).
    abstr (i args) itr_src. abstr (i0 (Any.pair args (Any.upcast false))) itr_tgt. clear i i0 args H H0. clear_tac.
    revert_until sk_link_eq3. gcofix CIH. i.
    guclo ordC_spec. econs.
    { instantiate (1:=(100 + 100)%ord). rewrite <- OrdArith.add_from_nat. cbn. refl. }
    (* instantiate (1:=(100 + 100)%ord). *)
    guclo bindC_spec. econs; cycle 1.
    { instantiate (1:=eq). ii. subst. des_ifs. steps. }
    revert_until CIH0. generalize (Ord.from_nat 100) as idx. gcofix CIH.
    i. punfold IN0. destruct st0 as [rst0 pst0].  destruct rst0 as [mrs0 frs0].
    dependent destruction IN0; pclearbot.
    - steps. gbase. eapply CIH1; et.
    - steps.
    - (*** call case ***)
      steps. des_ifs.
      { unfold triggerNB. steps. }
      Local Opaque p_src p_tgt. steps. Local Transparent p_src p_tgt.
      guclo bindC_spec. econs.
      { gbase. eapply CIH; et. }
      ii. subst. des_ifs. gbase. eapply CIH1; et.
    - steps. destruct frs0.
      { unfold triggerNB. steps. }
      destruct re; cbn; steps; try (by gbase; eapply CIH1; et).
    - steps. destruct pe; cbn; steps; try (by gbase; eapply CIH1; et).
    - steps. destruct ee; cbn; steps; try (by gbase; eapply CIH1; et).
      + esplits. spc SIM. steps. gbase; eapply CIH1; et.
      + esplits. spc SIM. steps. gbase; eapply CIH1; et.
    - steps. gbase; eapply CIH1; et.
    - steps. gbase; eapply CIH1; et.
  Unshelve.
    all: (try by apply Ord.O).
  Qed.

  Lemma add_list_initial_mrs
        mds ske
    :
      ModSemL.initial_mrs (ModL.get_modsem (Mod.add_list mds) ske) =
      flat_map ModSemL.initial_mrs (List.map (flip ModL.get_modsem ske ∘ Mod.lift) mds)
  .
  Proof. induction mds; ii; ss. f_equal; et. Qed.

  (*** TODO: move to Coqlib ***)
  Lemma flat_map_ext_h
        A0 A1 B0 B1
        (f0: A0 -> list B0) (f1: A1 -> list B1)
        (RA: A0 -> A1 -> Prop) (RB: B0 -> B1 -> Prop)
        l0 l1
        (HD: Forall2 RA l0 l1)
        (TL: forall a0 a1 (SIM: RA a0 a1), Forall2 RB (f0 a0) (f1 a1))
    :
      Forall2 RB (do X <- l0; f0 X) (do X <- l1; f1 X)
  .
  Proof. induction HD; ii; ss. eapply Forall2_app; et. Qed.

  Lemma my_lemma2
        :
          refines_closed (Mod.add_list (List.map SMod.to_src (kmds ++ List.map UMod.to_smod umds)))
                         (Mod.add_list (kmds_top ++ List.map UMod.to_mod umds))
  .
  Proof.
    r. eapply adequacy_global. exists 100.
    ginit.
    { eapply cpn5_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr. Local Opaque ModSemL.prog. ss.
    unfold ITree.map.
    unfold assume. folder.
    steps.
    esplits; et. { admit "ez - wf". } steps.
    instantiate (1:=(200 + 200)%ord).
    match goal with | [ |- gpaco5 _ _ _ _ _ _ _ ?src ?tgt ] => remember src as tmp end.
    replace ([]↑) with (Any.pair ([]: list val)↑ false↑); cycle 1.
    { admit "ez - parameterize initial argument && use transitivity of refinement". }
    subst.
    assert(STEQ: (ModSemL.initial_r_state ms_src, ModSemL.initial_p_state ms_src)
                 = (ModSemL.initial_r_state ms_tgt, ModSemL.initial_p_state ms_tgt)).
    { assert(forall fn, find (fun mnr => dec fn (fst mnr)) (ModSemL.initial_mrs ms_src) =
                        find (fun mnr => dec fn (fst mnr)) (ModSemL.initial_mrs ms_tgt)).
      { i. f_equal.
        unfold ms_src, ms_tgt. unfold ModL.enclose.
        rewrite ! add_list_initial_mrs.
        rewrite <- sk_link_eq3. folder.
        rewrite <- sk_link_eq2. folder.
        rewrite ! map_app. rewrite ! flat_map_app. f_equal.
        + eapply Forall2_eq.
          eapply flat_map_ext_h with (RA:=fun ms0 ms1 => ms0.(ModSemL.initial_mrs) = ms1.(ModSemL.initial_mrs)).
          { unfold kmds, kmds_top. rewrite ! List.map_map. eapply Forall2_apply_Forall2; try refl. i; subst. ss. }
          i. rewrite SIM. refl.
        + eapply Forall2_eq.
          eapply flat_map_ext_h with (RA:=fun ms0 ms1 => ms0.(ModSemL.initial_mrs) = ms1.(ModSemL.initial_mrs)).
          { unfold kmds, kmds_top. rewrite ! List.map_map. eapply Forall2_apply_Forall2; try refl. i; subst. ss. }
          i. rewrite SIM. refl.
      }
      f_equal.
      - unfold ModSemL.initial_r_state. f_equal. apply func_ext. i. rewrite H; refl.
      - unfold ModSemL.initial_p_state. f_equal. apply func_ext. i. rewrite H; refl.
    }
    rewrite STEQ.
    guclo bindC_spec. econs.
    { gfinal. right. eapply my_lemma2_aux. }
    i. subst. steps.
  Qed.

  Lemma gstb_eq: forall ske,
    _gstb ske =
    (List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec)))
       (flat_map SModSem.fnsems
          (List.map
             (flip SMod.get_modsem ske)
             (kmds ++ List.map UMod.to_smod umds))))
  .
  Proof.
    i. unfold _gstb.
    unfold _kmss, _umss.
    rewrite map_app. rewrite flat_map_app. rewrite map_app.
    f_equal.
    - rewrite <- ! SMod.red_do_ret. erewrite ! SMod.flat_map_assoc. ss.
    - rewrite <- ! SMod.red_do_ret. erewrite ! SMod.flat_map_assoc.
      eapply flat_map_ext. intro umd. unfold flip. ss.
      rewrite <- ! SMod.red_do_ret. erewrite ! SMod.flat_map_assoc. rewrite ! List.app_nil_r.
      eapply flat_map_ext. intro. unfold map_snd. des_ifs.
  Qed.

  Variable entry_r: Σ.
  Variable mainpre: Any.t -> ord -> Σ -> Prop.
  Variable (mainbody: list val -> itree (hCallE +' pE +' eventE) val).
  Hypothesis MAINPRE: mainpre ([]: list val)↑ ord_top entry_r.

  Hypothesis WFR: URA.wf (entry_r ⋅ (List.fold_left (⋅) (List.map (SModSem.initial_mr) kmss) ε)).
  Hypothesis MAINM: In (SMod.main mainpre mainbody) kmds.

  Theorem adequacy_open:
    refines_closed (Mod.add_list (List.map (SMod.to_tgt _gstb) kmds ++ List.map UMod.to_mod umds))
                   (Mod.add_list (kmds_top ++ List.map UMod.to_mod umds))
  .
  Proof.
    etrans.
    { eapply refines_close.
      rewrite Mod.add_list_app.
      eapply refines_proper_l.
      eapply adequacy_local_list.
      instantiate (1:=(List.map (SMod.to_tgt _gstb ∘ UMod.to_smod) umds)).
      eapply Forall2_apply_Forall2.
      { instantiate (1:=eq). refl. }
      i. subst. eapply my_lemma1; ss.
    }
    rewrite <- Mod.add_list_app.
    etrans.
    { rewrite <- List.map_map with (f:=UMod.to_smod).
      rewrite <- map_app.
      eapply adequacy_type2.
      - instantiate (1:=(kmds ++ List.map UMod.to_smod umds)).
        rewrite <- List.map_id with (l:=(kmds ++ List.map UMod.to_smod umds)) at 1.
        eapply Forall2_apply_Forall2.
        { instantiate (1:=eq). refl. }
        i. subst. exists _gstb. split; ss. r. intro ske. rewrite <- gstb_eq. refl.
      - eauto.
      - ss. rewrite ! URA.unit_id. admit "should be ez".
      - rewrite in_app_iff. eauto.
    }
    eapply my_lemma2.
  Qed.

End ADQ.
