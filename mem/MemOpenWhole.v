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

  Record fspecbodyk: Type := mk_fsbk {
    fsbk_fspec:> fspec;
    (* fsbk_body: (fsbk_fspec.(AA) * bool) -> itree (hCallE +' pE +' eventE) fsbk_fspec.(AR); *)
    (*** <--- this is not handy when removing the "is_k" argument at the top level ***)

    (* fsbk_bodyk: fsbk_fspec.(AA) -> itree (hCallE +' pE +' eventE) fsbk_fspec.(AR); *)
    (* fsbk_bodyu: fsbk_fspec.(AA) -> itree (hCallE +' pE +' eventE) fsbk_fspec.(AR); *)
    (*** <--- do we need fsbk_bodyk at all? it will always be APC (or just choose) because the k-cases will all be removed ***)

    fsbk_bodyu: fsbk_fspec.(AA) -> itree (hCallE +' pE +' eventE) fsbk_fspec.(AR);
    (*** <--- Now fspecbodyk has the same type with fspecbody! we don't need this definition ***)
  }
  .

  Definition disclose (fs: fspec): fspec :=
    @mk _ (fs.(X) * bool)%type (fs.(AA) * bool)%type (fs.(AR))
        (fun '(x, is_k) '(argh, is_k') argl o => ⌜is_k = is_k'⌝ ** (⌜is_k⌝ -* fs.(precond) x argh argl o ** ⌜is_pure o⌝))
        (fun '(x, is_k) reth retl =>                               (⌜is_k⌝ -* fs.(postcond) x reth retl))
  .

  Definition disclose_fsbk (fsbk: fspecbodyk): fspecbody :=
    mk_specbody (disclose fsbk) fsbk.(fsbk_body)
  .

  Definition disclose_smodsem (ms: SModSem.t): SModSem.t := {|
    SModSem.fnsems
  |}
  .

  Definition expose_smod (md: SMod.t): SMod.t.

End AUX.

Module KModSem.
Section KMODSEM.

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

End KMODSEM.
End KModSem.




Module KMod.
Section KMOD.

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

End KMOD.
End KMod.














Require Import SimModSem.
Require Import Hoare.


Section ADQ.
  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.
  Variable ctxs: list UMod.t.

  Let sk_link: Sk.t := fold_right Sk.add Sk.unit ((List.map SMod.sk mds) ++ (List.map UMod.sk ctxs)).
  Let skenv: SkEnv.t := Sk.load_skenv sk_link.

  Let imss: list SModSem.t := List.map (flip SMod.get_modsem skenv) mds.
  Let emss: list UModSem.t := List.map (flip UMod.get_modsem skenv) ctxs.

  Let gstb: list (gname * fspec) :=
    (flat_map (List.map (map_snd fsb_fspec) ∘ SModSem.fnsems) imss)
      ++ (flat_map (List.map (map_snd (fun _ => fspec_trivial)) ∘ UModSem.fnsems) emss).

  Lemma my_lemma1
        ctx
        (IN: In ctx ctxs)
    :
      ModPair.sim (SMod.to_tgt gstb (UMod.to_smod ctx)) (UMod.to_mod ctx)
  .
  Proof.
    admit "somehow".
  Qed.

  (* Lemma my_lemma2 *)
  (*       ctx *)
  (*       (IN: In ctx ctxs) *)
  (*   : *)
  (*     ModPair.sim (UMod.to_mod ctx) (SMod.to_tgt gstb (UMod.to_smod ctx)) *)
  (* . *)
  (* Proof. *)
  (* Qed. *)

  Lemma sk_link_eq: sk_link = (fold_right Sk.add Sk.unit (List.map SMod.sk (mds ++ List.map UMod.to_smod ctxs))).
  Proof.
    unfold sk_link. f_equal. rewrite List.map_app. f_equal. rewrite List.map_map. ss.
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
             (flip SMod.get_modsem (Sk.load_skenv (fold_right Sk.add Sk.unit (List.map SMod.sk (mds ++ List.map UMod.to_smod ctxs)))))
             (mds ++ List.map UMod.to_smod ctxs))))
  .
  Proof.
    rewrite <- sk_link_eq. folder. unfold gstb.
    unfold imss, emss.
    rewrite map_app. rewrite flat_map_app. rewrite map_app.
    f_equal.
    - rewrite <- ! SMod.red_do_ret. erewrite ! SMod.flat_map_assoc. ss.
    - rewrite <- ! SMod.red_do_ret. erewrite ! SMod.flat_map_assoc.
      eapply flat_map_ext. intro ctx. unfold flip. ss.
      rewrite <- ! SMod.red_do_ret. erewrite ! SMod.flat_map_assoc. rewrite ! List.app_nil_r.
      eapply flat_map_ext. intro. unfold map_snd. des_ifs.
  Qed.

  Variable entry_r: Σ.
  Variable mainpre: Any.t -> ord -> Σ -> Prop.
  Variable (mainbody: list val -> itree (hCallE +' pE +' eventE) val).
  Hypothesis MAINPRE: mainpre ([]: list val)↑ ord_top entry_r.

  Hypothesis WFR: URA.wf (entry_r ⋅ (List.fold_left (⋅) (List.map (SModSem.initial_mr) imss) ε)).

  (* Let ms_tgt: ModSemL.t := admit "". *)
  (* Let rsum: r_state -> Σ := *)
  (*   fun '(mrs_tgt, frs_tgt) => (fold_left (⋅) (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε) ⋅ (fold_left (⋅) frs_tgt ε). *)
  (* Hypothesis WFR: URA.wf (entry_r ⋅ rsum (ModSemL.initial_r_state ms_tgt)). *)

  Hypothesis MAINM: In (SMod.main mainpre mainbody) mds.

  Theorem adequacy_open:
    refines_closed (Mod.add_list (List.map (SMod.to_tgt gstb) mds ++ List.map UMod.to_mod ctxs))
                   (Mod.add_list (List.map SMod.to_src mds ++ List.map UMod.to_mod ctxs))
  .
  Proof.
    etrans.
    { eapply refines_close.
      rewrite Mod.add_list_app.
      eapply refines_proper_l.
      eapply adequacy_local_list.
      instantiate (1:=(List.map (SMod.to_tgt gstb ∘ UMod.to_smod) ctxs)).
      eapply Forall2_apply_Forall2.
      { instantiate (1:=eq). admit "ez - generalize this lemma to iff: Forall2_eq". }
      i. subst. eapply my_lemma1; ss.
    }
    rewrite <- Mod.add_list_app.
    etrans.
    { rewrite <- List.map_map with (f:=UMod.to_smod).
      rewrite <- map_app.
      eapply adequacy_type2.
      - instantiate (1:=(mds ++ List.map UMod.to_smod ctxs)).
        rewrite <- List.map_id with (l:=(mds ++ List.map UMod.to_smod ctxs)) at 1.
        eapply Forall2_apply_Forall2.
        { instantiate (1:=eq). admit "ez - ditto". }
        i. subst. exists gstb. split; ss. r. rewrite <- gstb_eq. refl.
      - eauto.
      - ss. rewrite ! URA.unit_id. admit "should be ez".
      - rewrite in_app_iff. eauto.
    }
    rewrite map_app. rewrite List.map_map.
    etrans.
    {
  Qed.

















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
