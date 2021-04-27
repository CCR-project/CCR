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
    (* ModSem.fnsems := List.map (map_snd (fun ktr arg => resum_itr (T:=Any.t) (cfun ktr arg))) ms.(fnsems); *)
    (* ModSem.fnsems := List.map (map_snd (fun ktr => resum_itr (T:=Any.t) ∘ cfun ktr)) ms.(fnsems); *)
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

  (* Record fspecbodyk: Type := mk_fsbk { *)
  (*   fsbk_fspec:> fspec; *)
  (*   (* fsbk_body: (fsbk_fspec.(AA) * bool) -> itree (hCallE +' pE +' eventE) fsbk_fspec.(AR); *) *)
  (*   (*** <--- this is not handy when removing the "is_k" argument at the top level ***) *)

  (*   (* fsbk_bodyk: fsbk_fspec.(AA) -> itree (hCallE +' pE +' eventE) fsbk_fspec.(AR); *) *)
  (*   (* fsbk_bodyu: fsbk_fspec.(AA) -> itree (hCallE +' pE +' eventE) fsbk_fspec.(AR); *) *)
  (*   (*** <--- do we need fsbk_bodyk at all? it will always be APC (or just choose) because the k-cases will all be removed ***) *)

  (*   fsbk_bodyu: fsbk_fspec.(AA) -> itree (hCallE +' pE +' eventE) fsbk_fspec.(AR); *)
  (*   (*** <--- Now fspecbodyk has the same type with fspecbody! we don't need this definition ***) *)
  (* } *)
  (* . *)

  Definition disclose (fs: fspec): fspec :=
    @mk _ (option fs.(X)) (fs.(AA) * bool)%type (fs.(AR))
        (fun ox '(argh, is_k) argl o => ⌜is_some ox = is_k⌝ **
                                        ((Exists x, ⌜ox = Some x⌝ ** fs.(precond) x argh argl o ** ⌜is_pure o⌝) ∨
                                         (⌜ox = None⌝)))
        (fun ox reth retl => ((Exists x, ⌜ox = Some x⌝ ** fs.(postcond) x reth retl) ∨ (⌜ox = None /\ reth↑ = retl⌝)))
  .
  (* Definition disclose (fs: fspec): fspec := *)
  (*   @mk _ (fs.(X) * bool)%type (fs.(AA) * bool)%type (fs.(AR)) *)
  (*       (fun '(x, is_k) '(argh, is_k') argl o => ⌜is_k = is_k'⌝ ** (⌜is_k⌝ -* fs.(precond) x argh argl o ** ⌜is_pure o⌝)) *)
  (*       (fun '(x, is_k) reth retl =>                               (⌜is_k⌝ -* fs.(postcond) x reth retl)) *)
  (* . *)
  (*** YJ: We may generalize a bit further and not require "is_pure o"
-- by defining an equiv-class of physical state and proving that the is_k cases behave same upto the equiv class && is_u cases change the state upto equiv class --
   but it looks like an over-engineering at the moment. ***)

  Definition disclose_fsb (fsb: fspecbody): fspecbody :=
    mk_specbody (disclose fsb) (fun '(argh, is_k) => if is_k
                                                     then trigger (Choose _) (*** YJ: We may generalize this to APC ***)
                                                     else fsb.(fsb_body) argh)
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


(* Module KModSem. *)
(* Section KMODSEM. *)

(*   Context `{Σ: GRA.t}. *)

(*   Record t: Type := mk { *)
(*     fnsems: list (gname * (list val -> itree (callE +' pE +' eventE) val)); *)
(*     mn: mname; *)
(*     initial_st: Any.t; *)
(*   } *)
(*   . *)

(*   Definition to_modsem (ms: t): ModSem.t := {| *)
(*     (* ModSem.fnsems := List.map (map_snd (fun ktr arg => resum_itr (T:=Any.t) (cfun ktr arg))) ms.(fnsems); *) *)
(*     (* ModSem.fnsems := List.map (map_snd (fun ktr => resum_itr (T:=Any.t) ∘ cfun ktr)) ms.(fnsems); *) *)
(*     ModSem.fnsems := List.map (map_snd (((∘)∘(∘)) (resum_itr (T:=Any.t)) cfun)) ms.(fnsems); *)
(*     ModSem.mn := ms.(mn); *)
(*     ModSem.initial_mr := ε; *)
(*     ModSem.initial_st := ms.(initial_st); *)
(*   |} *)
(*   . *)




(*   Definition transl_callE: callE ~> hCallE := *)
(*     fun T '(Call fn args) => hCall false fn args *)
(*   . *)

(*   Definition transl_event: (callE +' pE +' eventE) ~> (hCallE +' pE +' eventE) := *)
(*     (bimap transl_callE (bimap (id_ _) (id_ _))) *)
(*   . *)

(*   Definition transl_itr: (callE +' pE +' eventE) ~> itree (hCallE +' pE +' eventE) := *)
(*     embed ∘ transl_event *)
(*   . *)

(*   Definition transl_fun: (list val -> itree (callE +' pE +' eventE) val) -> fspecbody := *)
(*     fun ktr => *)
(*       mk_specbody fspec_trivial (interp (T:=val) transl_itr ∘ ktr) *)
(*   . *)

(*   Definition to_smodsem (ms: t): SModSem.t := {| *)
(*     SModSem.fnsems := List.map (map_snd transl_fun) ms.(fnsems); *)
(*     SModSem.mn := ms.(mn); *)
(*     SModSem.initial_mr := ε; *)
(*     SModSem.initial_st := ms.(initial_st); *)
(*   |} *)
(*   . *)

(* End KMODSEM. *)
(* End KModSem. *)




(* Module KMod. *)
(* Section KMOD. *)

(*   Context `{Σ: GRA.t}. *)

(*   Record t: Type := mk { *)
(*     get_modsem: SkEnv.t -> UModSem.t; *)
(*     sk: Sk.t; *)
(*   } *)
(*   . *)

(*   Definition to_mod (md: t): Mod.t := {| *)
(*     Mod.get_modsem := UModSem.to_modsem ∘ md.(get_modsem); *)
(*     Mod.sk := md.(sk); *)
(*   |} *)
(*   . *)

(*   Lemma to_mod_comm: forall md skenv, UModSem.to_modsem (md.(get_modsem) skenv) = (to_mod md).(Mod.get_modsem) skenv. *)
(*   Proof. i. refl. Qed. *)


(*   Definition to_smod (md: t): SMod.t := {| *)
(*     SMod.get_modsem := UModSem.to_smodsem ∘ md.(get_modsem); *)
(*     SMod.sk := md.(sk); *)
(*   |} *)
(*   . *)

(*   Lemma to_smod_comm: forall md skenv, UModSem.to_smodsem (md.(get_modsem) skenv) = (to_smod md).(SMod.get_modsem) skenv. *)
(*   Proof. i. refl. Qed. *)

(* End KMOD. *)
(* End KMod. *)






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

  Variable _kmds: list SMod.t.
  Let kmds: list SMod.t := List.map disclose_smod _kmds.
  Let kmds_top: list Mod.t := List.map SMod.to_src _kmds.
  Variable umds: list UMod.t.

  Let sk_link: Sk.t := fold_right Sk.add Sk.unit ((List.map SMod.sk kmds) ++ (List.map UMod.sk umds)).
  Let skenv: SkEnv.t := Sk.load_skenv sk_link.

  Let kmss: list SModSem.t := List.map (flip SMod.get_modsem skenv) kmds.
  Let umss: list UModSem.t := List.map (flip UMod.get_modsem skenv) umds.

  Let gstb: list (gname * fspec) :=
    (flat_map (List.map (map_snd fsb_fspec) ∘ SModSem.fnsems) kmss)
      ++ (flat_map (List.map (map_snd (fun _ => fspec_trivial2)) ∘ UModSem.fnsems) umss).

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
        mrs ktr arg
    :
      sim_itree (fun '(x, y) => x = y) 100%nat
                (mrs, ε, fun_to_tgt gstb (UModSem.transl_fun ktr) arg)
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
        eapply find_some in T. des; des_sumbool; subst. unfold gstb in T. rewrite in_app_iff in *. des; ss.
        - rewrite in_flat_map in *. des; ss. rewrite in_map_iff in *. des. unfold map_snd in T0. des_ifs.
          unfold kmss in T. rewrite in_map_iff in *. des. subst. unfold flip in T1.
          unfold kmds in T0. rewrite in_map_iff in *. des. subst. ss. rewrite in_map_iff in *. des.
          unfold map_snd in T1. des_ifs. ss.
          destruct a. eapply pair_downcast_lemma2 in _UNWRAPN0. des. subst.
          eapply hcall_clo with (fs:=disclose f); try refl.
          { rewrite URA.unit_idl. refl. }
          { eapply OrdArith.lt_from_nat. lia. }
          { instantiate (1:=ord_top). instantiate(1:=None). cbn. iRefresh.
            iSplitP; ss.
            right; iRefresh. ss. }
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

  (* Lemma my_lemma1_aux *)
  (*       s i *)
  (*   : *)
  (*     sim_fnsem (fun '(x, y) => x = y) (s, fun_to_tgt gstb (UModSem.transl_fun i)) (s, resum_itr (T:=_) ∘ cfun i) *)
  (* . *)
  (* Proof. *)
  (*   rr. split; ss. r. *)
  (*   ii. subst. cbn. rename y into arg. rename i into f. rename s into fn. *)
  (*   revert s i. pcofix CIH. *)
  (* Qed. *)

  Lemma my_lemma1
        umd
        (IN: In umd umds)
    :
      ModPair.sim (SMod.to_tgt (fun _ => gstb) (UMod.to_smod umd)) (UMod.to_mod umd)
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

  Lemma gstb_eq:
    gstb =
    (List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec)))
       (flat_map SModSem.fnsems
          (List.map
             (flip SMod.get_modsem (Sk.load_skenv (fold_right Sk.add Sk.unit (List.map SMod.sk
                                   (kmds ++ List.map UMod.to_smod umds)))))
             (kmds ++ List.map UMod.to_smod umds))))
  .
  Proof.
    rewrite <- sk_link_eq. folder. unfold gstb.
    unfold kmss, umss.
    rewrite map_app. rewrite flat_map_app. rewrite map_app.
    f_equal.
    - rewrite <- ! SMod.red_do_ret. erewrite ! SMod.flat_map_assoc. ss.
      (* eapply flat_map_ext. intro kmd. rewrite ! List.app_nil_r. *)
      (* rewrite SMod.red_do_ret. rewrite List.map_map. apply List.map_ext. i. des_ifs. unfold map_snd in *. des_ifs. *)
    - rewrite <- ! SMod.red_do_ret. erewrite ! SMod.flat_map_assoc.
      eapply flat_map_ext. intro umd. unfold flip. ss.
      rewrite <- ! SMod.red_do_ret. erewrite ! SMod.flat_map_assoc. rewrite ! List.app_nil_r.
      eapply flat_map_ext. intro. unfold map_snd. des_ifs.
  Qed.

  Require Import SimGlobal.

  Definition fsem_irr (fsem: Any.t -> itree Es Any.t): Prop :=
    forall a0 a1 (SIM: a0 = a1), fsem a0 = fsem a1
  .

  (* Lemma my_lemma2_aux *)
  (*     AA AR args o0 body st0 mn *)
  (*   : *)
  (*     simg eq 100%ord *)
  (*          (EventsL.interp_Es p_src (transl_all mn (if is_pure o0 then trigger (Choose _) else ((fun_to_src (AA:=AA) (AR:=AR) body) args))) st_src0) *)
  (*          (EventsL.interp_Es p_mid (transl_all mn ((fun_to_mid body) (Any.pair o0↑ args))) st_tgt0) *)
  (* . *)
  (* Proof. *)
  (* Qed. *)

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

  (* Lemma add_list_fnsems *)
  (*       mds *)
  (*   : *)
  (*     (ModSemL.fnsems (ModL.enclose (Mod.add_list mds))) = *)
  (*     (ModSemL.fnsems (ModL.enclose (Mod.add_list mds))) *)
  (* . *)
  (* Proof. *)
  (* Qed. *)
  (* (ModSemL.fnsems (ModL.enclose (Mod.add_list (kmds_top ++ List.map UMod.to_mod umds)))) *)

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

  Lemma upcast_pair_downcast
        A B (a: A) (b: B)
    :
      (Any.pair a↑ b↑)↓ = Some (a, b)
  .
  Proof. admit "ez". Qed.

  Lemma sim_prog
        fn args
    :
      p_src (Call fn args) = p_tgt (Call fn (Any.pair args false↑))
  .
  Proof.
    subst p_src p_tgt. ss.
    destruct (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_src)) eqn:T; cycle 1.
    - destruct (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_tgt)) eqn:U.
      + exfalso.
        eapply find_some in U. des. des_sumbool. subst.
        subst ms_tgt. unfold ModL.enclose in U.
        rewrite <- sk_link_eq2 in *. folder.
        rewrite add_list_fnsems in U. rewrite in_flat_map in U. des.
        rewrite in_map_iff in *. des. subst. ss.
        rewrite in_map_iff in *. des. subst. ss.
        rewrite in_map_iff in *. des. subst. ss.
        destruct x0 as [fn body]. ss.
        rewrite in_app_iff in *. des.
        * unfold kmds in U3.
          rewrite in_map_iff in *. des. subst. ss.
          rewrite in_map_iff in *. des. destruct x0 as [fn0 body0]. ss. clarify.
          assert(exists y, In (fn, y) (ModSemL.fnsems ms_src)); cycle 1.
          { des. eapply find_none in T; et. ss. des_sumbool; ss. }
          unfold ms_src. unfold ModL.enclose. rewrite add_list_fnsems. rewrite <- sk_link_eq3. folder.
          esplits. eapply in_flat_map. esplits; et.
          { rewrite in_map_iff. esplits; et. rewrite in_app_iff. left. unfold kmds_top.
            rewrite in_map_iff. esplits; et. }
          ss. rewrite List.map_map. rewrite in_map_iff. esplits; et. ss.
        * rewrite in_map_iff in *. des. subst. ss.
          rewrite in_map_iff in *. des. destruct x0 as [fn0 body0]. ss. clarify.
          assert(exists y, In (fn, y) (ModSemL.fnsems ms_src)); cycle 1.
          { des. eapply find_none in T; et. ss. des_sumbool; ss. }
          unfold ms_src. unfold ModL.enclose. rewrite add_list_fnsems. rewrite <- sk_link_eq3. folder.
          esplits. eapply in_flat_map. esplits; et.
          { rewrite in_map_iff. esplits; et. rewrite in_app_iff. right.
            rewrite in_map_iff. esplits; et. }
          ss. rewrite List.map_map. rewrite in_map_iff. esplits; et. ss.
      + cbn. unfold triggerUB. grind.
    - eapply find_some in T. des. des_sumbool. subst. cbn. rewrite bind_ret_l. des_ifs. rewrite bind_ret_r.
      subst ms_src. unfold ModL.enclose in T.
      rewrite <- sk_link_eq3 in *. folder.
      rewrite add_list_fnsems in T. rewrite in_flat_map in T. des.
      rewrite in_map_iff in *. des. subst. ss.
      rewrite in_map_iff in *. des. unfold ModSem.map_snd in *. des_ifs.
      rewrite in_app_iff in *. des.
      * unfold kmds_top in T1.
        rewrite in_map_iff in *. des. subst. ss.
        rewrite in_map_iff in *. des. destruct x0 as [fn0 body0]. ss. clarify.
        destruct (find (fun fnsem => dec s (fst fnsem)) (ModSemL.fnsems ms_tgt)) eqn:U.
        { cbn. irw. des_ifs. irw.
          eapply find_some in U. des. des_sumbool. subst. ss.
          subst ms_tgt. unfold ModL.enclose in U.
          rewrite <- sk_link_eq2 in *. folder.
          rewrite add_list_fnsems in U. rewrite in_flat_map in U. des.
          rewrite in_map_iff in *. des. subst. ss.
          rewrite in_map_iff in *. des. unfold ModSem.map_snd in *. des_ifs. ss.
          rewrite in_map_iff in *. des. des_ifs.
          rewrite in_app_iff in *. des.
          { unfold kmds in U3.
            rewrite in_map_iff in *. des. subst. ss.
            rewrite in_map_iff in *. des. destruct x1 as [fn body]. unfold map_snd in *. clarify.
            assert(x = x0). { admit "ez - uniqueness". } subst.
            assert(body = body0). { admit "ez - uniqueness". } subst.
            f_equal.
            ss. unfold fun_to_src. unfold cfun. destruct (args↓) eqn:A.
            { cbn. irw. erewrite <- Any.downcast_upcast with (a:=args); et. rewrite upcast_pair_downcast. ss. irw. ss. }
            ss.
            destruct ((Any.pair args (Any.upcast false))↓) eqn:B.
            { exfalso. destruct p. eapply pair_downcast_lemma2 in B. des. clarify. }
            ss. unfold triggerNB. grind.
          }
          { rewrite in_map_iff in *. des. subst. ss.
            rewrite in_map_iff in *. des. unfold map_snd in *. des_ifs.
            clear - T0 T1 U1 U2. exfalso.
            admit "uniqueness of fname".
          }
        }
        { unfold ms_tgt in U. eapply find_none in U; cycle 1.
          { unfold ModL.enclose. rewrite add_list_fnsems. rewrite in_flat_map. esplits; et.
            { rewrite List.map_map.
              rewrite in_map_iff. esplits; et. 
              rewrite in_app_iff. left.
              unfold kmds. rewrite in_map_iff. esplits; et.
            }
            ss. rewrite ! List.map_map.
            rewrite in_map_iff. esplits ;et.
            rewrite <- sk_link_eq2. folder. et.
          }
          ss. des_sumbool; ss.
        }
      * rewrite in_map_iff in *. des. subst. ss.
        rewrite in_map_iff in *. des. destruct x0 as [fn0 body0]. ss. clarify.
        destruct (find (fun fnsem => dec s (fst fnsem)) (ModSemL.fnsems ms_tgt)) eqn:U.
        { cbn. irw. des_ifs. irw.
          eapply find_some in U. des. des_sumbool. subst. ss.
          subst ms_tgt. unfold ModL.enclose in U.
          rewrite <- sk_link_eq2 in *. folder.
          rewrite add_list_fnsems in U. rewrite in_flat_map in U. des.
          rewrite in_map_iff in *. des. subst. ss.
          rewrite in_map_iff in *. des. unfold ModSem.map_snd in *. des_ifs. ss.
          rewrite in_map_iff in *. des. des_ifs.
          rewrite in_app_iff in *. des.
          { unfold kmds in U3.
            rewrite in_map_iff in *. des. subst. ss.
            rewrite in_map_iff in *. des. unfold map_snd in *. des_ifs.
            clear - T0 T1 U1 U2. exfalso.
            admit "uniqueness of fname".
          }
          { rewrite in_map_iff in *. des. subst. ss.
            rewrite in_map_iff in *. des. destruct x1 as [fn body]. unfold map_snd in *. clarify.
            assert(x = x0). { admit "ez - uniqueness". } subst.
            assert(body = body0). { admit "ez - uniqueness". } subst.
            f_equal.
            unfold fun_to_src.
            unfold UModSem.transl_fun; ss.
            unfold cfun.
            red_resum.
            destruct (args↓) eqn:A.
            { ss. irw. erewrite <- Any.downcast_upcast with (a:=args); et. rewrite upcast_pair_downcast. ss.
              irw. unfold body_to_src. ss.
              abstr (body0 l) itr. revert itr. clear_until sk_link_eq3.

              i. rewrite resum_itr_bind. f_equiv.
              { apply func_ext. i. rewrite resum_itr_ret. ss. }
              unfold resum_itr. unfold interp_hCallE_src. rewrite interp_interp.
              f_equal. apply func_ext_dep. intro T.
              unfold UModSem.transl_itr. apply func_ext. intro e.
              destruct e.
              { destruct c. ss. cbn. rewrite unfold_interp. ss. unfold UModSem.transl_callE. cbn.
  Abort.

  Notation "(≈)" := (fun itr0 itr1 => itr0 ≈ itr1).

  (* Definition sim_body T (b0 b1: itree EventsL.Es T): Prop := b0 ≈ b1. *)
  Definition sim_fun T (f0 f1: (Any.t -> itree EventsL.Es T)): Prop :=
    forall args, (f0 args) ≈ (f1 (Any.pair args false↑))
  .

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

  Lemma find_sim
        fn
    :
        option_rel (fun '(fn0, fsem0) '(fn1, fsem1) => fn0 = fn1 /\ sim_fun fsem0 fsem1)
                   (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_src))
                   (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_tgt))
  .
  Proof.
    admit "TODO".
    (* destruct (find (fun fnsem => dec fn (fst fnsem)) (ModSemL.fnsems ms_src)) eqn:T. *)
  Qed.

  Lemma sim_prog
        fn args
    :
      p_src (Call fn args) ≈ p_tgt (Call fn (Any.pair args false↑))
  .
  Proof.
    admit "TODO".
  Qed.

  Lemma my_lemma2_aux
        fn args st0
    :
      (str <- EventsL.interp_Es p_src (p_src (Call fn args)) st0;; Ret (snd str))
        ≈ (str <- EventsL.interp_Es p_tgt (p_tgt (Call fn (Any.pair args false↑))) st0;; Ret (snd str))
  .
  Proof.
    {
      ss. steps.
      generalize (find_sim fn). intro T. inv T; ss; steps; cycle 1.
      { unfold triggerUB. steps. f_equiv; ss. refl. }
      des; subst. specialize (IN0 args).
      abstr (i args) itr_src. abstr (i0 (Any.pair args (Any.upcast false))) itr_tgt. clear i i0 args H H0. clear_tac.
      f_equiv.
      - admit "".
      - ii. des_ifs. steps. refl.
      revert_until sk_link_eq3. gcofix CIH. i.
    }


    ginit. { eapply cpn2_wcompat; eauto with paco. } revert_until p_tgt. gcofix CIH. i.
    ss. steps.
    generalize (find_sim fn). intro T. inv T; ss; steps.
    des; subst. specialize (IN0 args).
    abstr (i args) itr_src. abstr (i0 (Any.pair args (Any.upcast false))) itr_tgt. clear i i0 args H H0. clear_tac.
    revert_until sk_link_eq3. gcofix CIH. i.
  Qed.

(` x : r_state * p_state * Any.t <-
 EventsL.interp_Es p_src (p_src (Call "main" (Any.upcast []))) (ModSemL.initial_r_state ms_src, ModSemL.initial_p_state ms_src);;
 Ret (snd x))
(` x : r_state * p_state * Any.t <-
 EventsL.interp_Es p_tgt (p_tgt (Call "main" (Any.upcast []))) (ModSemL.initial_r_state ms_tgt, ModSemL.initial_p_state ms_tgt);;
 Ret (snd x))

  @gpaco5 Type (fun R : Type => forall (_ : R) (_ : R), Prop) (fun (R : Type) (_ : forall (_ : R) (_ : R), Prop) => Ord.t)
    (fun (R : Type) (_ : forall (_ : R) (_ : R), Prop) (_ : Ord.t) => itree eventE R)
    (fun (R : Type) (_ : forall (_ : R) (_ : R), Prop) (_ : Ord.t) (_ : itree eventE R) => itree eventE R) _simg
    (@cpn5 Type (fun R : Type => forall (_ : R) (_ : R), Prop) (fun (R : Type) (_ : forall (_ : R) (_ : R), Prop) => Ord.t)
       (fun (R : Type) (_ : forall (_ : R) (_ : R), Prop) (_ : Ord.t) => itree eventE R)
       (fun (R : Type) (_ : forall (_ : R) (_ : R), Prop) (_ : Ord.t) (_ : itree eventE R) => itree eventE R) _simg)
    (@bot5 Type (fun R : Type => forall (_ : R) (_ : R), Prop) (fun (R : Type) (_ : forall (_ : R) (_ : R), Prop) => Ord.t)
       (fun (R : Type) (_ : forall (_ : R) (_ : R), Prop) (_ : Ord.t) => itree eventE R)
       (fun (R : Type) (_ : forall (_ : R) (_ : R), Prop) (_ : Ord.t) (_ : itree eventE R) => itree eventE R))
    (@bot5 Type (fun R : Type => forall (_ : R) (_ : R), Prop) (fun (R : Type) (_ : forall (_ : R) (_ : R), Prop) => Ord.t)
       (fun (R : Type) (_ : forall (_ : R) (_ : R), Prop) (_ : Ord.t) => itree eventE R)
       (fun (R : Type) (_ : forall (_ : R) (_ : R), Prop) (_ : Ord.t) (_ : itree eventE R) => itree eventE R)) Any.t 
    (@eq Any.t) ?i1
    (@ITree.bind' eventE (prod (prod (@r_state Σ) p_state) Any.t) Any.t
       (fun x : prod (prod (@r_state Σ) p_state) Any.t =>
        @go eventE Any.t (@RetF eventE Any.t (itree eventE Any.t) (@snd (prod (@r_state Σ) p_state) Any.t x)))
       (@EventsL.interp_Es Σ Any.t p_src
          (@p_src Any.t
             (Call
                (String (Ascii.Ascii true false true true false true true false)
                   (String (Ascii.Ascii true false false false false true true false)
                      (String (Ascii.Ascii true false false true false true true false)
                         (String (Ascii.Ascii false true true true false true true false) EmptyString))))
                (@Any.upcast (list val) (@nil val))))
          (@pair (@r_state Σ) p_state (@ModSemL.initial_r_state Σ ms_src) (@ModSemL.initial_p_state Σ ms_src))))
    (@ITree.bind' eventE (prod (prod (@r_state Σ) p_state) Any.t) Any.t
       (fun x : prod (prod (@r_state Σ) p_state) Any.t =>
        @go eventE Any.t (@RetF eventE Any.t (itree eventE Any.t) (@snd (prod (@r_state Σ) p_state) Any.t x)))
       (@EventsL.interp_Es Σ Any.t p_tgt
          (@p_tgt Any.t
             (Call
                (String (Ascii.Ascii true false true true false true true false)
                   (String (Ascii.Ascii true false false false false true true false)
                      (String (Ascii.Ascii true false false true false true true false)
                         (String (Ascii.Ascii false true true true false true true false) EmptyString))))
                (@Any.upcast (list val) (@nil val))))
          (@pair (@r_state Σ) p_state (@ModSemL.initial_r_state Σ ms_tgt) (@ModSemL.initial_p_state Σ ms_tgt))))

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
    unfold assume.
    steps.
    esplits; et. { admit "ez - wf". } steps.
    Local Transparent ModSemL.prog.
    unfold ModSemL.prog at 4.
    unfold ModSemL.prog at 2.
    Local Opaque ModSemL.prog.
    folder.
    ss. steps.
    (* Opaque ModSemL.initial_r_state. *)
    (* Opaque ModSemL.initial_p_state. *)
    fold ms_src. fold ms_mid.
    set (rs_src0 := initial_r_state ms_src) in *.
    set (rs_tgt0 := initial_r_state ms_mid) in *.
    assert(exists mrs_src0 hd_src tl_src, rs_src0 = (mrs_src0, hd_src :: tl_src)).
    { esplits. refl. }
    assert(exists mrs_tgt0 hd_tgt tl_tgt, rs_tgt0 = (mrs_tgt0, hd_tgt :: tl_tgt)).
    { esplits. refl. }
    des. clearbody rs_src0 rs_tgt0. subst.
    unfold unwrapU at 1. des_ifs; cycle 1.
    { unfold triggerUB. myred. ss. }
    unfold unwrapU. des_ifs; cycle 1.
    { admit "unwrapN!!!!!!!!!!". }


    unfold ms_mid, mds_mid, SMod.to_mid in Heq0. rewrite SMod.transl_fnsems in Heq0.
    unfold SMod.load_fnsems in Heq0. apply find_some in Heq0. des; ss. des_sumbool; subst.
    rewrite in_flat_map in Heq0. des; ss. rewrite in_flat_map in Heq2. des; ss. des_ifs. ss; des; ss; clarify. ss. subst.
    rename Heq2 into INF. rename Heq0 into IN.
    rename x into md0. fold sk in INF. fold skenv in INF.

    unfold ms_src, mds_src, SMod.to_src in Heq. rewrite SMod.transl_fnsems in Heq.
    unfold SMod.load_fnsems in Heq. apply find_some in Heq. des; ss. destruct p; ss. des_sumbool; subst.
    rewrite in_flat_map in Heq. des; ss. rewrite in_flat_map in Heq0. des; ss. des_ifs. ss; des; ss; clarify.
    rename Heq0 into INF0. rename Heq into IN0.
    rename x into md1. fold sk in INF0. fold skenv in INF0.

    assert(md0 = md1); subst.
    { admit "ez - uniqueness". }
    assert(f = f0).
    { admit "ez - uniqueness". }
    subst.
    fold ms_src. fold ms_mid. fold p_src. fold p_mid.

    steps.

    match goal with
    | [ |- gpaco5 _ _ _ _ _ _ _ ?i_src _ ] => remember i_src as tmp
    end.
    replace (([]: list val)↑) with (Any.pair ord_top↑ ([]: list val)↑) by admit "TODO".
    subst tmp.

    guclo ordC_spec. econs.
    { eapply OrdArith.add_base_l. }
    guclo bindC_spec.
    econs.
    - hexploit adequacy_type_aux; cycle 1.
      { intro T. gfinal. right. instantiate (3:=ord_top) in T. ss. eapply T. }
      ss. unfold ms_src, ms_mid. unfold initial_p_state.
      apply func_ext. intro mn. unfold mds_src, mds_mid, SMod.to_src, SMod.to_mid.
      rewrite ! SMod.transl_initial_mrs. ss.
    - ii. rr in SIM. des_ifs. des; ss. subst. r in SIM. des_ifs.
      myred.
      steps.
  Unshelve.
    all: ss.
    all: try (by exact Ord.O).
    all: try (by econs; et).

    admit "".
  Qed.

  (* Let ms_tgt: ModSemL.t := admit "". *)
  (* Let rsum: r_state -> Σ := *)
  (*   fun '(mrs_tgt, frs_tgt) => (fold_left (⋅) (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε) ⋅ (fold_left (⋅) frs_tgt ε). *)
  (* Hypothesis WFR: URA.wf (entry_r ⋅ rsum (ModSemL.initial_r_state ms_tgt)). *)

  Variable entry_r: Σ.
  Variable mainpre: Any.t -> ord -> Σ -> Prop.
  Variable (mainbody: list val -> itree (hCallE +' pE +' eventE) val).
  Hypothesis MAINPRE: mainpre ([]: list val)↑ ord_top entry_r.

  Hypothesis WFR: URA.wf (entry_r ⋅ (List.fold_left (⋅) (List.map (SModSem.initial_mr) kmss) ε)).
  Hypothesis MAINM: In (SMod.main mainpre mainbody) kmds.

  Theorem adequacy_open:
    refines_closed (Mod.add_list (List.map (SMod.to_tgt gstb) kmds ++ List.map UMod.to_mod umds))
                   (Mod.add_list (kmds_top ++ List.map UMod.to_mod umds))
  .
  Proof.
    etrans.
    { eapply refines_close.
      rewrite Mod.add_list_app.
      eapply refines_proper_l.
      eapply adequacy_local_list.
      instantiate (1:=(List.map (SMod.to_tgt gstb ∘ UMod.to_smod) umds)).
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
        i. subst. exists gstb. split; ss. r. rewrite <- gstb_eq. refl.
      - eauto.
      - ss. rewrite ! URA.unit_id. admit "should be ez".
      - rewrite in_app_iff. eauto.
    }
    eapply my_lemma2.
  Qed.

End ADQ.
















  Let gstb := (imds ++ (List.map CMod.to_smod ctxs))
    (List.map (fun '(fn, fs) => (fn, fs))
              (flat_map SModSem.fnsems
                 (List.map (flip SMod.get_modsem (Sk.load_skenv (fold_right Sk.add Sk.unit (List.map SMod.sk mds)))) mds)))

  Theorem meta2
          (cmd: CMod.t)
          gstb
          (DUMMYPROP: True)
    :
      ModPair.sim (SMod.to_tgt gstb (CMod.to_smod cmd)) (CMod.to_mod cmd)
  .
  Proof.
    admit "".
  Qed.

  Theorem meta1
          (cmd: CMod.t)
    :
      ModPair.sim (CMod.to_mod cmd) (SMod.to_src (CMod.to_smod cmd))
  .
  Proof.
    admit "".
  Qed.

  Theorem open_refinement: forall ctx,
      refines_closed (Mod.add_list (Mem0.Mem :: (List.map CMod.to_mod ctx)))
                     (Mod.add_list (MemOpen.Mem :: (List.map CMod.to_mod ctx))).
  Proof.
    admit "hard -- somehow".
  Qed.

End ADQ.



Section PROOF.
  Context `{@GRA.inG memRA Σ}.

  Theorem open_refinement: forall ctx,
      refines_closed (Mod.add_list (Mem0.Mem :: (List.map CMod.to_mod ctx)))
                     (Mod.add_list (MemOpen.Mem :: (List.map CMod.to_mod ctx))).
  Proof.
    admit "hard -- somehow".
  Qed.

End PROOF.
