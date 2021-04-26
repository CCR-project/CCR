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
      mk_specbody fspec_trivial (interp (T:=val) transl_itr ∘ ktr)
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
      ++ (flat_map (List.map (map_snd (fun _ => fspec_trivial)) ∘ UModSem.fnsems) umss).

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

(* (********** TODO: remove below Notation after the fix in HTactics ***************) *)
(* Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 tgt1 '------------------------------------------------------------------' src2 tgt2" *)
(*   := *)
(*     (gpaco6 (_sim_itree wf) _ _ _ _ _ _ n ((src0, src1), src2) ((tgt0, tgt1), tgt2)) *)
(*       (at level 60, *)
(*        format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' tgt1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' "). *)













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


  Lemma pair_downcast_lemma2
        T U (v0 v1: T) x (u: U)
    :
      (Any.pair x v0↑)↓ = Some (u, v1) -> v0 = v1 /\ x↓ = Some u
  .
  Proof.
    admit "ez".
  Qed.

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
    Ltac red_resum := repeat (try rewrite resum_itr_bind; try rewrite resum_itr_tau; try rewrite resum_itr_ret).
    red_resum.
    rewrite Any.upcast_downcast. ss.
    red_resum.
    steps.
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
      abstr (ktr x) itr. clear x ktr.
      clear _ASSUME0. des_u. rewrite URA.unit_idl in *.
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
          eapply pair_downcast_lemma2 in _UNWRAPN0. des. subst.
          eapply hcall_clo; try refl.
          { rewrite URA.unit_idl. refl. }
          { eapply OrdArith.lt_from_nat. lia. }
          { instantiate (1:=ord_top). instantiate(1:=tt). cbn. split; ss. iRefresh.
            iSplitP; ss.
            right; iRefresh. ss. }
          { ss. }

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
      }
      (* { *)
      (*   eapply find_some in T. des; des_sumbool; subst. unfold gstb in T. rewrite in_app_iff in *. des; ss. *)
      (*   - rewrite in_flat_map in *. des; ss. rewrite in_map_iff in *. des. unfold map_snd in T0. des_ifs. *)
      (*     unfold kmss in T. rewrite in_map_iff in *. des. subst. unfold flip in T1. *)
      (*     unfold kmds in T0. rewrite in_map_iff in *. des. subst. ss. rewrite in_map_iff in *. des. *)
      (*     unfold map_snd in T1. des_ifs. ss. *)
      (*   - *)
      (*   eapply hcall_clo2 with (wf:=(fun '(x, y) => x = y)) (R0:=val) (R1:=val). *)
      (* } *)
      (* assert(WF: exists r0, URA.wf r0). { esplits. eapply URA.wf_unit. } des. *)
      assert (GWF: ☀) by (split; [refl|exact _ASSUME]); clear _ASSUME.
      iRefresh.
      ired_both.
      match goal with
      | [ |- gpaco6 _ _ _ _ _ _ _ _ (_, _, _, _ >>= ?ktr0) (_, _, _, _ >>= ?ktr1) ] =>
        remember ktr0 as tmp0; remember ktr1 as tmp1
      (* | [ |- gpaco6 _ _ _ _ _ _ _ _ _ _ ] => idtac *)
      end.

      eapply hcall_clo2 with (wf:=(fun '(x, y) => x = y)) (R0:=val) (R1:=val).
      eapply hcall_clo with (wf:=(fun '(x, y) => x = y)) (R0:=val) (R1:=val).
      remember _sim_itree as ggg.
      erewrite f_equal.
      evar (xyz: (Σ * Any.t * Σ * itree Es val)%type).
      match goal with
      | [ |- gpaco6 _ _ _ _ _ _ _ _ ?left _ ] => replace left with xyz
      end. subst xyz.
      Set Printing All. subst ggg.
      eapply hcall_clo with (wf:=(fun '(x, y) => x = y)) (R0:=val) (R1:=val).
      eapply hcall_clo with (wf:=(fun '(x, y) => x = y)).




      subst ggg.
      replace (mr, st, x1, ` x : _ <- HoareCall false ord_top f fn a;; tmp0 x) with xyz.
      eapply hcall_clo.
      rapply hcall_clo.
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n
             (mr_src0, mp_src0, fr_src0, (HoareCall tbr ord_cur (mk P Q) fn varg_src) >>= k_src)
             (mrs_tgt, frs_tgt, trigger (Call fn varg_tgt) >>= k_tgt).

gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg Any.t Any.t (fun _ _ : Σ * Any.t * Σ => eq) n
  (mr_src0, mp_src0, fr_src0, ` x : _ <- HoareCall tbr ord_cur P Q fn varg_src;; k_src x)
  (mrs_tgt, frs_tgt, ` x : _ <- trigger (Call fn varg_tgt);; k_tgt x)
      hcall_tac __ ord_top (@URA.unit Σ) (@URA.unit Σ) (@URA.unit Σ); ss; et.
           eapply (hcall_clo _ (o:=o) (mr_src1:=mr_src1) (fr_src1:=fr_src1) (rarg_src:=rarg_src));
            [ tac0 | eapply OrdArith.lt_from_nat; lia | .. | tac1 ]

      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ (fun _ _ => @eq Any.t) n
             (mr_src0, mp_src0, fr_src0, (HoareCall tbr ord_cur P Q fn varg_src) >>= k_src)
             (mrs_tgt, frs_tgt, trigger (Call fn varg_tgt) >>= k_tgt)

      eapply find_some in T. des; ss. des_sumbool. subst.
      unfold gstb in T. rewrite in_app_iff in T. des; ss.
      + rewrite in_flat_map in T. des; ss. rewrite in_map_iff in *. des; subst.
        unfold map_snd in *. des_ifs. unfold kmss in T. rewrite in_map_iff in *. des; subst.
        unfold kmds in *. rewrite in_map_iff in *. des; subst. ss. rewrite in_map_iff in *. des; subst.
        unfold map_snd in *. des_ifs. ss.

        unfold HoareCall, put, discard, forge, checkWf.
        steps.
        force_l. eexists (_, _). steps. force_l. { refl. } steps. force_l. esplits. steps.
        force_l. esplits. force_l. { refl. } steps. force_l. eexists (_, false). steps. force_l. esplits. steps.
        force_l. esplits. force_l. { TTTTTTTTTTTTTTTTTTTTTTTTTTT
      +
        
      unfold HoareCall, put, discard, forge, checkWf.
      steps.
      force_l. eexists (_, _). steps. force_l. { refl. } steps. force_l. esplits. steps.
      force_l. esplits. force_l. { refl. } steps. force_l. esplits. steps. force_l. esplits. steps.
      force_l. esplits. force_l. {

          - unfold UModSem.transl_itr at 2.
            Local Opaque subevent.
            unfold resum_itr. rewrite transl_event_pE.
            rewrite ! unfold_interp. cbn.
            repeat match goal with
            | [ |- context[trigger(|?e|)%sum]] =>
              replace (trigger (|e|)%sum) with (trigger e: itree (hCallE +' pE +' eventE) _) by refl
            | [ |- context[trigger(|?e|)%sum]] =>
              replace (trigger (|e|)%sum) with (trigger e: itree Es _) by refl
            end.
            rewrite interp_tgt_triggerp.
            gstep. eapply sim_itree_pput_both. steps.
            gbase.
            steps.









            Local Opaque subevent.
            rewrite <- bind_trigger. red_resum.
            unfold resum_itr at 2. rewrite transl_event_pE.
            rewrite ! unfold_interp. cbn.
            replace (trigger (|PPut p|)%sum) with (trigger (PPut p): itree (hCallE +' pE +' eventE) _) by refl.
            replace (trigger (|PPut p|)%sum) with (trigger (PPut p): itree Es _) by refl.
            rewrite interp_tgt_triggerp.
            (* replace ((bimap (id_ pE) (id_ eventE) >>> inr_) unit (PPut p|)%sum) with (PPut p). *)
            unfold bimap, Bimap_Coproduct. unfold cat, Cat_IFun. cbn. unfold id_, Id_IFun. cbn.
            unfold inr_, inl_, Inr_sum1, Inl_sum1.
            (trigger (|PPut p|)%sum)
            match goal with
            | [ |- context[trigger ?x] ] => idtac x; replace (trigger x) with (trigger (PPut p)) 
            end.
            Set Printing All.
            rewrite interp_tgt_triggerp.
            replace (inr_ unit (inl_ unit (PPut p))) with (inr_ unit (inl_ unit (PPut p))).
            (subevent _ (PPut p)).
            steps.
            replace (trigger (inr_ ()%type (inl_ ()%type (PPut p)))) with (trigger (PPut p)).
            ired_both.
            steps.
            unfold embed, Embeddable_forall. cbn.
            unfold embed.
        }
        unfold interp_hCallE_tgt. try rewrite ! unfold_interp; cbn; myred.
        destruct s; ss.
        {
          destruct st_src0 as [rst_src0 pst_src0]; ss. destruct st_tgt0 as [rst_tgt0 pst_tgt0]; ss.
          destruct p; ss.
          - steps. myred. steps. instantiate (1:=100). myred. steps. instantiate (1:=100). gbase. eapply CIH0; ss; et.
          - steps. myred. steps. instantiate (1:=100). myred. steps. instantiate (1:=100). gbase. eapply CIH0; ss; et.
        }
        { dependent destruction e.
          - steps. myred. steps. unshelve esplits; et. instantiate (1:=100). myred. steps. instantiate (1:=100).
            myred. steps. instantiate (1:=100). gbase. eapply CIH0; ss; et.
          - steps. myred. steps. unshelve esplits; et. instantiate (1:=100). myred. steps. instantiate (1:=100).
            myred. steps. instantiate (1:=100). gbase. eapply CIH0; ss; et.
          - steps. myred. steps. unshelve esplits; et. instantiate (1:=100). myred. steps. instantiate (1:=100).
            gbase. eapply CIH0; ss; et.
        }
      }
      dependent destruction h.


      clear CIH0 CIH1.
      +
    TT
    (* repeat rewrite URA.unit_idl in *. repeat rewrite URA.unit_id in *. iRefresh. *)
    r in _ASSUME0.
  Qed.

  Lemma my_lemma1_aux
        s i
    :
      sim_fnsem (fun '(x, y) => x = y) (s, fun_to_tgt gstb (UModSem.transl_fun i)) (s, resum_itr (T:=_) ∘ cfun i)
  .
  Proof.
    rr. split; ss. r.
    ii. subst. cbn. rename y into arg. rename i into f. rename s into fn.
    revert s i. pcofix CIH.
  Qed.

  Lemma my_lemma1
        umd
        (IN: In umd umds)
    :
      ModPair.sim (SMod.to_tgt gstb (UMod.to_smod umd)) (UMod.to_mod umd)
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

  Variable entry_r: Σ.
  Variable mainpre: Any.t -> ord -> Σ -> Prop.
  Variable (mainbody: list val -> itree (hCallE +' pE +' eventE) val).
  Hypothesis MAINPRE: mainpre ([]: list val)↑ ord_top entry_r.

  Hypothesis WFR: URA.wf (entry_r ⋅ (List.fold_left (⋅) (List.map (SModSem.initial_mr) kmss) ε)).

  (* Let ms_tgt: ModSemL.t := admit "". *)
  (* Let rsum: r_state -> Σ := *)
  (*   fun '(mrs_tgt, frs_tgt) => (fold_left (⋅) (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε) ⋅ (fold_left (⋅) frs_tgt ε). *)
  (* Hypothesis WFR: URA.wf (entry_r ⋅ rsum (ModSemL.initial_r_state ms_tgt)). *)

  Hypothesis MAINM: In (SMod.main mainpre mainbody) kmds.

  Lemma my_lemma2
        :
          refines_closed (Mod.add_list (List.map SMod.to_src (kmds ++ List.map UMod.to_smod umds)))
                         (Mod.add_list (kmds_top ++ List.map UMod.to_mod umds))
  .
  Proof.
    admit "".
  Qed.

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
