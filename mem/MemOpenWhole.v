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
Require Import Mem0 MemOpen.
Require Import Hoare.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.


(* Definition dot {A B C} (g: B -> C) (f: A -> B): A -> C := g ∘ f. *)
(* Notation "(∘)" := dot (at level 40, left associativity). *)
Notation "(∘)" := (fun g f => g ∘ f) (at level 40, left associativity).



Section AUX.
  Context `{Σ: GRA.t}.
  Definition fspec_trivial: fspec := (mk_simple (fun (_: unit) => (fun _ _ => ⌜True⌝, fun _ => ⌜True⌝))).

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
    fun T '(Call fn args) => hCall false fn args
  .

  Definition transl_event: (callE +' pE +' eventE) ~> (hCallE +' pE +' eventE) :=
    (bimap transl_callE (bimap (id_ _) (id_ _)))
  .

  Definition transl_itr: (callE +' pE +' eventE) ~> itree (hCallE +' pE +' eventE) :=
    embed ∘ transl_event
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
    @mk _ (fs.(X) * bool)%type (fs.(AA) * bool)%type (fs.(AR))
        (fun '(x, is_k) '(argh, is_k') argl o => ⌜is_k = is_k'⌝ ** (⌜is_k⌝ -* fs.(precond) x argh argl o ** ⌜is_pure o⌝))
        (fun '(x, is_k) reth retl =>                               (⌜is_k⌝ -* fs.(postcond) x reth retl))
  .
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

  Lemma my_lemma1
        umd
        (IN: In umd umds)
    :
      ModPair.sim (SMod.to_tgt gstb (UMod.to_smod umd)) (UMod.to_mod umd)
  .
  Proof.
    admit "somehow".
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
