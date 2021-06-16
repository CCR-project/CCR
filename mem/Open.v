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
Require Import HoareDef Hoare.
Require Import OpenDef.
Require Import IRed.

Set Implicit Arguments.






Global Program Instance Forall2_Reflexive `{Reflexive A R}: Reflexive (Forall2 R).
Next Obligation. induction x; ii; ss. econs; ss. Qed.

Global Program Instance Forall2_Transitive `{Transitive A R}: Transitive (Forall2 R).
Next Obligation.
  i. revert_until x. induction x; ii; ss.
  { inv H0. inv H1. ss. }
  inv H0. inv H1. econs; ss; et.
Qed.

Global Program Instance Forall2_PreOrder `{PreOrder A R}: PreOrder (Forall2 R).


Section AUX.
  (* TODO: move to AList.v *)
  Lemma map_snd_map_snd A B0 B1 B2 (f0: B0 -> B1) (f1: B1 -> B2):
    (map_snd (A:=A) f1) ∘ (map_snd f0) = map_snd (f1 ∘ f0).
  Proof. apply func_ext. i. destruct x; ss. Qed.

  Lemma find_alist_find
        `{Dec K} V (k: K) (kvs: list (K * V))
    :
      alist_find k kvs = o_map (find (fun '(k0, _) => dec k k0) kvs) snd
  .
  Proof.
    ginduction kvs; ii; ss. des_ifs; rewrite eq_rel_dec_correct in *; des_sumbool; des_ifs.
  Qed.

  Lemma alist_find_app2 K `{Dec K} V (k: K) (l0 l1: alist K V) (v: V)
        (FIND0: alist_find k l0 = None)
        (FIND1: alist_find k l1 = Some v)
    :
      alist_find k (l0 ++ l1) = Some v.
  Proof.
    ginduction l0; ii; ss. des_ifs; try rewrite eq_rel_dec_correct in *; des_sumbool; des_ifs.
    eapply IHl0; et.
  Qed.

  Lemma alist_find_flat_map
        `{Dec K} V0 V1 (k: K) (f: V0 -> alist K V1) (l: list V0)

        kvs v
        (FIND0: find (is_some ∘ alist_find k) (map f l) = Some kvs)
        (FIND1: alist_find k kvs = Some v)
    :
      alist_find k (flat_map f l) = Some v
  .
  Proof.
    ginduction l; ii; ss. des_ifs; try rewrite eq_rel_dec_correct in *; des_sumbool; des_ifs.
    - erewrite alist_find_app; et.
    - erewrite alist_find_app2; et. unfold is_some in Heq. des_ifs.
  Qed.

  Lemma in_alist_find
        `{Dec K} V kv kvs
        (IN: In kv kvs)
    :
      exists (v: V), alist_find (fst kv) kvs = Some v
  .
  Proof.
    ginduction kvs; ii; ss. des; subst.
    - des_ifs; try rewrite eq_rel_dec_correct in *; des_sumbool; des_ifs; et.
    - des_ifs; try rewrite eq_rel_dec_correct in *; des_sumbool; des_ifs; et.
  Qed.

  Lemma alist_find_flat_map_const
        `{Dec K} V0 V1 V2 (k: K) (f: V0 -> alist K V1) (l: list V0)

        (c: V2)
        (IN: In k (concat (map (map fst ∘ f) l)))
        (* (FIND0: find (is_some ∘ alist_find k) (map f l) = Some kvs) *)
    :
      alist_find k (flat_map (map (map_snd (fun _ => c)) ∘ f) l) = Some c
  .
  Proof.
    ginduction l; ii; ss.
    rewrite in_app_iff in *; des.
    - rewrite in_map_iff in *. des; subst.
      erewrite alist_find_app; et. unfold map_snd. erewrite alist_find_map.
      exploit in_alist_find; et. intro T; des. rewrite T. ss.
    - destruct (alist_find k (map (map_snd (λ _ : V1, c)) (f a))) eqn:T.
      + erewrite alist_find_app; et. unfold map_snd. erewrite alist_find_map.
        dup T. eapply alist_find_some in T0. rewrite in_map_iff in *. des; subst. destruct x; ss; clarify.
        eapply in_alist_find in T1. des. ss. rewrite T1. ss.
      + erewrite alist_find_app2; et.
  Qed.

End AUX.

Lemma fold_right_add
      X (add: X -> X -> X) zero xs ys
      (ZERO: forall x, add zero x = x)
      (ASSOC: forall x y z, add (add x y) z = add x (add y z))
  (* (COMM: forall x y, add x y = add y x) *)
  :
    add (foldr add zero xs) (foldr add zero ys) = foldr add zero (xs ++ ys)
.
Proof.
  revert ys. induction xs; ii; ss.
  rewrite fold_right_app. rewrite ASSOC. f_equal. rewrite IHxs. rewrite fold_right_app. ss.
Qed.





Require Import SimModSem.
Require Import Hoare.
Require Import HTactics ProofMode.




Section ADQ.
  Context `{Σ: GRA.t}.

  Variable _kmds: list KMod.t.
  Let kmds: list SMod.t := List.map (KMod.transl) _kmds.
  Variable umds: list UMod.t.

  Let sk_link: Sk.t := Sk.sort (fold_right Sk.add Sk.unit ((List.map SMod.sk kmds) ++ (List.map UMod.sk umds))).
  Let skenv: SkEnv.t := Sk.load_skenv sk_link.

  Let _kmss: Sk.t -> list SModSem.t := fun ske => List.map (flip SMod.get_modsem ske) kmds.
  Let _umss: Sk.t -> list UModSem.t := fun ske => List.map (flip UMod.get_modsem ske) umds.
  Let _gstb: Sk.t -> list (gname * fspec) := fun ske =>
    (flat_map (List.map (map_snd fsb_fspec) ∘ SModSem.fnsems) (_kmss ske))
      ++ (flat_map (List.map (map_snd (fun _ => fspec_trivial)) ∘ UModSem.fnsems) (_umss ske)).

  Let kmss: list SModSem.t := Eval red in (_kmss sk_link).
  Let umss: list UModSem.t := Eval red in (_umss sk_link).
  Let gstb: list (gname * fspec) := Eval red in (_gstb sk_link).
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


  Lemma add_list_fnsems
        mds ske
    :
      (ModSemL.fnsems (ModL.get_modsem (Mod.add_list mds) ske)) =
      flat_map ModSemL.fnsems (List.map (flip ModL.get_modsem ske ∘ Mod.lift) mds)
  .
  Proof. induction mds; ss. f_equal. et. Qed.

  Ltac _list_tac :=
    match goal with
    | [ H: alist_find _ _ = Some _ |- _ ] => apply alist_find_some in H; des; des_sumbool; subst
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


  Lemma my_lemma1_aux'
        (ske: Sk.t) mrs (A: Type) (itr: itree (uCallE +' pE +' eventE) A) (ctx: Σ)
        (WF: URA.wf (ctx ⋅ fst mrs)) fr
    :
      paco6
        (_sim_itree (fun '(st_src, st_tgt) => st_src = st_tgt))
        bot6
        (Σ * A)%type A
        (fun '(mrs_src, fr_src) '(mrs_tgt, fr_tgt) '(ctx, r_src) r_tgt => mrs_src = mrs_tgt /\ r_src = r_tgt
                                                                          /\ URA.wf (ctx ⋅ fst mrs_src))
        40%nat
        (mrs, fr, interp_hCallE_tgt (_gstb ske) ord_top (UModSem.massage_itr (_gstb ske) itr) ctx)
        (mrs, ε, UModSem.transl_itr (T:=A) itr)
  .
  Proof.
    ginit. revert mrs A itr ctx WF fr. gcofix CIH. i. ides itr.
    { steps. }
    { steps. gbase. eapply CIH; et. }
    rewrite <- bind_trigger.
    destruct e; cycle 1.
    {
      destruct s; ss.
      { destruct p; ss.
        - resub. ired_both. destruct mrs. gstep. econs; et. steps. gbase. eapply CIH; et.
        - resub. ired_both. destruct mrs. gstep. econs; et. steps. gbase. eapply CIH; et.
      }
      { destruct e; ss.
        - resub. ired_both. destruct mrs. gstep. econs; et.
          i. exists x_tgt. eexists. steps. gbase. eapply CIH; et.
        - resub. ired_both. destruct mrs. gstep. econs; et.
          i. exists x_src. eexists. steps. gbase. eapply CIH; et.
        - resub. ired_both. destruct mrs. gstep. econs; et.
          i. eexists. steps. gbase. eapply CIH; et.
      }
    }
    destruct u. resub. ired_both. steps. rewrite _UNWRAPU. steps.
    rename _UNWRAPU into T.
    eapply alist_find_some in T. unfold _gstb in T. rewrite in_app_iff in *. des; ss.
    - list_tac.
      des_ifs. unfold _kmss in T. list_tac. subst. unfold kmds in T0. list_tac. subst.
      ss. list_tac. des_ifs. ss.
      unfold HoareCall, discard, forge, put, checkWf. steps.
      destruct mrs.
      force_l. exists (c, ε). steps.
      force_l.
      { rewrite ! URA.unit_id. auto. }
      steps. force_l. exists ε. steps.
      force_l. exists ε. steps. force_l.
      { rewrite URA.unit_id. auto. }
      steps. force_l. exists None. steps.
      force_l. exists (args↑). steps.
      force_l. exists ord_top. steps.
      force_l.
      { rewrite Any.upcast_split. eapply to_semantic; [|eapply URA.wf_unit]. iIntros. iPureIntro. esplits; et. }
      steps. force_l.
      { split; et. }
      steps. gstep. econs; et. i. subst. destruct mrs_tgt1. eexists. steps.
      red in _ASSUME0. uipropall. subst.
      gbase. eapply CIH. ss.
      eapply URA.wf_mon. instantiate (1:=x0).
      replace (x2 ⋅ c0 ⋅ x0) with (x2 ⋅ (c0 ⋅ (ε ⋅ x0))); auto. r_solve.
    - list_tac.
      des_ifs. unfold _umss in T. list_tac. subst.
      unfold HoareCall, discard, forge, put, checkWf. steps.
      destruct mrs.
      force_l. exists (c, ε). steps.
      force_l.
      { rewrite ! URA.unit_id. auto. }
      steps. force_l. exists ε. steps.
      force_l. exists ε. steps. force_l.
      { rewrite URA.unit_id. auto. }
      steps. force_l. exists tt. steps.
      force_l. exists (args↑). steps.
      force_l. exists ord_top. steps.
      force_l.
      { eapply to_semantic; [|eapply URA.wf_unit]. iIntros. iPureIntro. esplits; et. }
      steps. force_l.
      { split; et. }
      steps. gstep. econs; et. i. subst. destruct mrs_tgt1. eexists. steps.
      red in _ASSUME0. uipropall. subst.
      gbase. eapply CIH. ss.
      eapply URA.wf_mon. instantiate (1:=x).
      replace (x2 ⋅ c0 ⋅ x) with (x2 ⋅ (c0 ⋅ (ε ⋅ x))); auto. r_solve.
    Unshelve.
    all: try (exact Ord.O).
    all: try (exact 0%nat).
  Qed.

  Ltac r_wf H := eapply prop_ext_rev; [eapply f_equal|]; [|eapply H]; r_solve.

  Lemma my_lemma1_aux
        mrs ktr arg ske
    :
      sim_itree (fun '(x, y) => x = y) 100%nat
                (mrs, ε, fun_to_tgt (_gstb ske) (UModSem.massage_fsb (_gstb ske) ktr) arg)
                (mrs, ε, (UModSem.transl_fun ktr) arg)
  .
  Proof.
    destruct mrs as [mr st].
    unfold fun_to_tgt, UModSem.transl_fun, HoareFun, discard, forge, checkWf, put, cfun.
    ginit. steps. red in _ASSUME0. uipropall. des. clarify.
    unfold UModSem.massage_fun.
    guclo lordC_spec. econs.
    { instantiate (1:=(49 + 40)%ord). rewrite <- OrdArith.add_from_nat. eapply OrdArith.le_from_nat. lia. }
    erewrite idK_spec with (i0:=UModSem.transl_itr (ktr arg)).
    guclo lbindC_spec. econs.
    { gfinal. right. eapply my_lemma1_aux'.
      eapply URA.wf_mon. instantiate (1:=x2). r_wf _ASSUME. }
    i. destruct st_src1, st_tgt1. destruct vret_src. ss. des; subst. destruct p0.
    force_l. eexists. force_l. eexists (_, _). steps.
    force_l.
    { instantiate (1:=ε). instantiate (1:=c2). r_wf SIM1. }
    steps. force_l. eexists.
    force_l.
    { red. uipropall. }
    steps. force_l. eexists. force_l.
    { instantiate (1:=ε). instantiate (1:=ε). rewrite URA.unit_id. auto. }
    steps.
    (* can not Qed bcz of Coq bug... *)
  Admitted.

  Lemma my_lemma1
        umd
        (IN: In umd umds)
    :
      ModPair.sim (SMod.to_tgt _gstb (UMod.massage _gstb umd)) (UMod.transl umd)
  .
  Proof.
    econs; ss.
    i. r. econs.
    { instantiate (1:=fun '(x, y) => x = y). ss.
      set (ums:=UMod.get_modsem umd sk) in *.
      rewrite ! List.map_map.
      eapply Forall2_apply_Forall2.
      { refl. }
      i. subst. unfold map_snd. des_ifs.
      rr. split; ss. r. ii. subst. ss. esplits; et. eapply my_lemma1_aux.
    }
    { ss. }
    { ss. }
  Qed.

  (* Lemma my_lemma2_aux *)
  (*       mrs ktr arg *)
  (*   : *)
  (*     sim_itree (fun '(x, y) => x = y) 100%nat *)
  (*               (mrs, ε, (UModSem.transl_fun ktr) arg) *)
  (*               (mrs, ε, fun_to_src (fsb_body (UModSem.massage_fsb gstb ktr)) arg) *)
  (* . *)
  (* Proof. *)
  (*   destruct mrs as [mr st]. ss. *)
  (*   unfold fun_to_src, UModSem.transl_fun, UModSem.massage_fun, body_to_src. *)
  (*   ginit. abstr (ktr arg) itr. clear ktr arg. revert_until gstb. gcofix CIH. i. *)
  (*   ides itr. *)
  (*   { steps. } *)
  (*   { steps. gbase. eapply CIH; et. } *)
  (*   rewrite <- bind_trigger. *)
  (*   destruct e; cycle 1. *)
  (*   { *)
  (*     destruct s; ss. *)
  (*     { destruct p; ss. *)
  (*       - resub. ired_both. gstep; econs; eauto. steps. gbase. eapply CIH; et. *)
  (*       - resub. ired_both. gstep; econs; eauto. steps. gbase. eapply CIH; et. *)
  (*     } *)
  (*     { destruct e; ss. *)
  (*       - resub. ired_both. gstep; econs; et. i. esplits; et. steps. gbase. eapply CIH; et. *)
  (*       - resub. ired_both. gstep; econs; et. i. esplits; et. steps. gbase. eapply CIH; et. *)
  (*       - resub. ired_both. gstep; econs; et. i. esplits; et. steps. gbase. eapply CIH; et. *)
  (*     } *)
  (*   } *)
  (*   destruct u. resub. ired_both. gstep; econs; eauto. i. subst. destruct mrs_tgt1. esplits. steps. *)
  (*   gbase. eapply CIH. *)
  (* Unshelve. *)
  (*   all: try (exact Ord.O). *)
  (* Qed. *)

  (* Lemma my_lemma2 *)
  (*       umd *)
  (*       (IN: In umd umds) *)
  (*   : *)
  (*     ModPair.sim (UMod.transl umd) (SMod.to_src (UMod.massage umd)) *)
  (* . *)
  (* Proof. *)
  (*   econs; ss. *)
  (*   i. r. econs. *)
  (*   { instantiate (1:=fun '(x, y) => x = y). ss. *)
  (*     set (ums:=UMod.get_modsem umd sk) in *. *)
  (*     rewrite ! List.map_map. *)
  (*     eapply Forall2_apply_Forall2. *)
  (*     { refl. } *)
  (*     i. subst. unfold map_snd. des_ifs. *)
  (*     rr. split; ss. r. ii. subst. ss. esplits; et. eapply my_lemma2_aux. *)
  (*   } *)
  (*   { ss. } *)
  (*   { ss. } *)
  (* Qed. *)

  (* refines_closed (Mod.add_list (map SMod.to_src (kmds ++ map (Σ _gstb) umds))) *)
  (*   (Mod.add_list (map SMod.to_src kmds ++ map Σ umds)) *)

  Ltac steps := HoareDef.steps.

  (* Lemma stb_find_iff fn *)
  (*   : *)
  (*     ((<<NONE: alist_find fn stb = None>>) /\ *)
  (*      (<<FINDSRC: alist_find fn (fnsems ms_src) = None>>) /\ *)
  (*      (<<FINDMID: alist_find fn (fnsems ms_mid) = None>>)) \/ *)

  (*     (exists md (f: fspecbody), *)
  (*         (<<SOME: alist_find fn stb = Some (f: fspec)>>) /\ *)
  (*         (<<FINDSRC: alist_find fn (fnsems ms_src) = *)
  (*                     Some (transl_all *)
  (*                             (SModSem.mn *)
  (*                                (SMod.get_modsem md sk)) *)
  (*                             ∘ fun_to_src (fsb_body f))>>) /\ *)
  (*         (<<FINDMID: alist_find fn (fnsems ms_mid) = *)
  (*                     Some (transl_all *)
  (*                             (SModSem.mn *)
  (*                                (SMod.get_modsem md sk)) *)
  (*                             ∘ fun_to_mid stb (fsb_body f))>>)). *)
  (* Proof. *)
  (*   unfold ms_src, ms_mid, mds_mid, mds_src, SMod.to_src, SMod.to_mid. *)
  (*   rewrite SMod.transl_fnsems. rewrite SMod.transl_fnsems. fold sk. *)
  (*   unfold stb at 1 3. unfold sbtb, mss. rewrite alist_find_map. *)
  (*   generalize mds. induction mds0; ss; auto. rewrite ! alist_find_app_o. *)
  (*   erewrite ! SMod.red_do_ret2. rewrite ! alist_find_map. uo. *)
  (*   destruct (alist_find fn (SModSem.fnsems (SMod.get_modsem a sk))) eqn:FIND. *)
  (*   { right. esplits; et. } *)
  (*   des. *)
  (*   { left. esplits; et. } *)
  (*   { right. esplits; et. } *)
  (* Qed. *)

  Let src_fns :=
    (ModSemL.fnsems (ModL.enclose (Mod.add_list (map SMod.to_src kmds ++ map UMod.transl umds)))).
  Let tgt_fns :=
    (ModSemL.fnsems (ModL.enclose (Mod.add_list (map SMod.to_src kmds ++
                                                     map SMod.to_src (map (UMod.massage _gstb) umds))))).

  Let sk_link0 := (Sk.sort
                     (Sk.add (ModL.sk (Mod.add_list (map SMod.to_src kmds)))
                             (ModL.sk (Mod.add_list (map SMod.to_src (map (UMod.massage _gstb) umds)))))).
  Let sk_link1 := (Sk.sort
                   (Sk.add (ModL.sk (Mod.add_list (map SMod.to_src kmds)))
                           (ModL.sk (Mod.add_list (map UMod.transl umds))))).

  Lemma sk_link0_eq: sk_link0 = sk_link.
  Proof.
    unfold sk_link, sk_link0.
    f_equal. rewrite ! Mod.add_list_sk. rewrite fold_right_add; ss; cycle 1.
    { i. unfold Sk.add. rewrite List.app_assoc. ss. }
    f_equal. rewrite ! map_map. ss.
  Qed.

  Lemma sk_link1_eq: sk_link1 = sk_link.
  Proof.
    unfold sk_link, sk_link1.
    f_equal. rewrite ! Mod.add_list_sk. rewrite fold_right_add; ss; cycle 1.
    { i. unfold Sk.add. rewrite List.app_assoc. ss. }
    f_equal. rewrite ! map_map. ss.
  Qed.

  Lemma alist_find_iff
        fn
    :
      (<<NONE: (alist_find fn src_fns) = None /\ (alist_find fn tgt_fns) = None>>) \/
      (<<CTX: exists fsem, (alist_find fn src_fns) = Some fsem /\
                           (alist_find fn tgt_fns) = Some fsem>>) \/
      (<<HIT: exists mn fsem,
          (alist_find fn src_fns) = Some (transl_all mn ∘ (UModSem.transl_fun fsem)) /\
          (alist_find fn tgt_fns) = Some (transl_all mn ∘ (fun_to_src (fsb_body (UModSem.massage_fsb gstb fsem)
                                         )))>>)
  .
  Proof.
    destruct (alist_find fn src_fns) eqn:T.
    - right. ss. unfold src_fns in T. rewrite Mod.add_list_app in T. ss.
      rewrite alist_find_app_o in *. des_ifs.
      + left. esplits; et. unfold tgt_fns. rewrite Mod.add_list_app. ss.
        folder; rewrite sk_link0_eq in *; rewrite sk_link1_eq in *.
        rewrite alist_find_app_o in *. des_ifs.
      + right. unfold tgt_fns. rewrite Mod.add_list_app. ss.
        folder; rewrite sk_link0_eq in *; rewrite sk_link1_eq in *.
        rewrite alist_find_app_o in *. des_ifs.
        (* rewrite Mod.add_list_fns in *. rewrite ! List.map_map. f_equal. *)
        rewrite add_list_fnsems in *. ss.
        esplits; et.
    -
    subst src_fns tgt_fns. ss.
    destruct src_fns.
  Qed.

  Lemma my_lemma2
    :
      refines_closed
        (Mod.add_list ((map SMod.to_src kmds) ++ (map SMod.to_src (map (UMod.massage _gstb) umds))))
        (Mod.add_list ((map SMod.to_src kmds) ++ (map (UMod.transl) umds)))
  .
  Proof.
    r. i. eapply SimGlobal.adequacy_global_itree; et.
    exists 100.
    ginit.
    unfold ModSemL.initial_itr, ModSemL.initial_itr_arg. Local Opaque ModSemL.prog. ss.
    unfold ITree.map. steps.
    des. esplits; et.
    { admit "ez". }
    { admit "ez". }
    steps.
    Local Transparent ModSemL.prog.
    unfold ModSemL.prog at 4.
    unfold ModSemL.prog at 2.
    Local Opaque ModSemL.prog.
    steps.

    2: {
      Local Transparent ModSemL.prog.
      unfold ModSemL.prog at 4.
      unfold ModSemL.prog at 2.
      Local Opaque ModSemL.prog.
      ss. steps_strong.
      esplits; et.
      { des. split.
        { inv WF. econs.
          { rewrite fns_eq. auto. }
          { pose proof initial_mrs_eq. unfold ms_mid, ms_src in H.
            rewrite H. auto. }
        }
        { ss. rewrite sk_eq. auto. }
      }
      steps.

      (* stb main *)
      hexploit (stb_find_iff "main"). i. des.
      { unfold ms_src in FINDSRC. rewrite FINDSRC. steps. }
      unfold stb in SOME.
      rewrite alist_find_map in SOME. unfold o_map in SOME. des_ifs.
      destruct f. ss. subst. ss.

      fold ms_src. fold ms_mid.
      rewrite FINDSRC. rewrite FINDMID. steps.
      unfold fun_to_src, fun_to_mid, cfun. steps.

      rewrite Any.pair_split. steps.
      rewrite Any.upcast_downcast. steps.

      guclo ordC_spec. econs.
      { eapply OrdArith.add_base_l. }
      guclo bindC_spec. econs.
      { gfinal. right. eapply adequacy_type_aux. ss.
        unfold initial_r_state, initial_p_state.
        rewrite initial_mrs_eq. auto. }
      { i. subst. instantiate (1:=10). steps. }
    }
    { instantiate (1:=O).
      ss. repeat (rewrite <- OrdArith.add_from_nat). ss.
      eapply OrdArith.lt_from_nat. lia. }
    Unshelve.
    all: try (by exact Ord.O).
    all: try (by exact 0).
  Qed.



  Declare Scope l_monad_scope.
  Local Open Scope l_monad_scope.
  Notation "'do' X <- A ; B" := (List.flat_map (fun X => B) A) : l_monad_scope.
  Notation "'do' ' X <- A ; B" := (List.flat_map (fun _x => match _x with | X => B end) A) : l_monad_scope.
  Notation "'ret'" := (fun X => [X]) (at level 60) : l_monad_scope.

  Lemma gstb_eq: forall ske,
    _gstb ske =
    (List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec)))
       (flat_map SModSem.fnsems
          (List.map
             (flip SMod.get_modsem ske)
             (kmds ++ List.map (UMod.massage _gstb) umds))))
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

  Definition UMod_main (mainbody: Any.t -> itree (uCallE +' pE +' eventE) Any.t): UMod.t := {|
    UMod.get_modsem := fun _ => (UModSem.mk [("main", mainbody)] "Main" (tt↑));
    UMod.sk := Sk.unit;
  |}
  .

  Variable (mainbody: Any.t -> itree (uCallE +' pE +' eventE) Any.t).
  Hypothesis MAINU: In (UMod_main mainbody) umds.

  Let mains: SMod.t := UMod.massage _gstb (UMod_main mainbody).

  Hypothesis WFR: URA.wf (List.fold_left (⋅) (List.map (SModSem.initial_mr) kmss) ε).
  (* Hypothesis MAINM: In (SMod.main mainpre mainbody) kmds. *)

  Theorem adequacy_open:
    refines_closed (Mod.add_list (List.map (SMod.to_tgt _gstb) kmds ++ List.map UMod.transl umds))
                   (Mod.add_list (List.map (SMod.to_src) kmds ++ List.map UMod.transl umds))
  .
  Proof.
    etrans.
    { eapply refines_close.
      rewrite Mod.add_list_app.
      eapply refines_proper_l.
      eapply adequacy_local_list.
      instantiate (1:=(List.map (SMod.to_tgt _gstb ∘ (UMod.massage _gstb)) umds)).
      eapply Forall2_apply_Forall2.
      { instantiate (1:=eq). refl. }
      i. subst. eapply my_lemma1; ss.
    }
    rewrite <- Mod.add_list_app.
    etrans.
    { erewrite <- List.map_map with (f:=UMod.massage _gstb).
      rewrite <- map_app.
      eapply adequacy_type2.
      - instantiate (1:=(kmds ++ List.map (UMod.massage _gstb) umds)).
        erewrite <- List.map_id with (l:=(kmds ++ List.map (UMod.massage _gstb) umds)) at 1.
        eapply Forall2_apply_Forall2.
        { instantiate (1:=eq). refl. }
        i. subst. exists _gstb. split; ss. r. intro ske. rewrite <- gstb_eq. refl.
      - admit "main pre".
      - ss. instantiate (1:=ε). rewrite ! URA.unit_id. rewrite ! URA.unit_idl. admit "should be ez".
      - Check (UModSem.massage_fun gstb mainbody).
        admit "mid - main argument parameterization".
        (* instantiate (1:=UModSem.transl_fun_smod mainbody). rewrite in_app_iff. eauto. *)
    }
    etrans.
    { instantiate (1:=Mod.add_list ((map SMod.to_src kmds) ++ (List.map (UMod.transl) umds))).
      assert(G:=my_lemma2).
      r in G. specialize (G (map SMod.to_src kmds)). rewrite <- ! Mod.add_list_app in G.
      rewrite map_app. et.
    }
    rewrite Mod.add_list_app. refl.
  Unshelve.
    all: ss.
    { ii. apply True. }
    { ii. apply ITree.spin. }
  Qed.

End ADQ.
