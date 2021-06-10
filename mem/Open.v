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







Require Import SimModSem.
Require Import Hoare.
Require Import HTactics ProofMode.




Section ADQ.
  Context `{Σ: GRA.t}.

  Variable _kmds: list KMod.t.
  Let kmds: list SMod.t := List.map (KMod.to_tgt) _kmds.
  Let kmds_top: list Mod.t := List.map KMod.to_src _kmds.
  Variable umds: list UMod.t.

  Let sk_link: Sk.t := fold_right Sk.add Sk.unit ((List.map SMod.sk kmds) ++ (List.map UMod.sk umds)).
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
        (mrs, fr, interp_hCallE_tgt (_gstb ske) ord_top (UModSem.transl_itr_smod itr) ctx)
        (mrs, ε, UModSem.transl_itr_mod (T:=A) itr)
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
    destruct u. resub. ired_both. force_l.
    { admit "MID -- need to trigger UB beforehand
ANOTHER IDEA -- SOLVING TWO PROBLEM AT ONCE --
In HoareDef, instead of unwrapN
```
      f <- (alist_find fn stb)ǃ;;
```
match it and use trivial spec in case of None
". }
    steps.
    rename _UNWRAPN into T.
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
                (mrs, ε, fun_to_tgt (_gstb ske) (UModSem.transl_fsb_smod ktr) arg)
                (mrs, ε, (UModSem.transl_fun_mod ktr) arg)
  .
  Proof.
    destruct mrs as [mr st].
    unfold fun_to_tgt, UModSem.transl_fun_mod, HoareFun, discard, forge, checkWf, put, cfun.
    ginit. steps. red in _ASSUME0. uipropall. des. clarify.
    unfold UModSem.transl_fun_smod.
    guclo lordC_spec. econs.
    { instantiate (1:=(49 + 40)%ord). rewrite <- OrdArith.add_from_nat. eapply OrdArith.le_from_nat. lia. }
    erewrite idK_spec with (i0:=UModSem.transl_itr_mod (ktr arg)).
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
      ModPair.sim (SMod.to_tgt _gstb (UMod.to_smod umd)) (UMod.to_mod umd)
  .
  Proof.
    econs; ss; cycle 1.
    { admit "ez - wf". }
    i. r. eapply adequacy_lift.
    econs.
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

  Lemma my_lemma2_aux
        mrs ktr arg
    :
      sim_itree (fun '(x, y) => x = y) 100%nat
                (mrs, ε, (UModSem.transl_fun_mod ktr) arg)
                (mrs, ε, fun_to_src (fsb_body (UModSem.transl_fsb_smod ktr)) arg)
  .
  Proof.
    destruct mrs as [mr st]. ss.
    unfold fun_to_src, UModSem.transl_fun_mod, UModSem.transl_fun_smod, UModSem.transl_fun_smod, body_to_src.
    ginit. abstr (ktr arg) itr. clear ktr arg. revert_until gstb. gcofix CIH. i.
    ides itr.
    { steps. }
    { steps. gbase. eapply CIH; et. }
    rewrite <- bind_trigger.
    destruct e; cycle 1.
    {
      destruct s; ss.
      { destruct p; ss.
        - resub. ired_both. gstep; econs; eauto. steps. gbase. eapply CIH; et.
        - resub. ired_both. gstep; econs; eauto. steps. gbase. eapply CIH; et.
      }
      { destruct e; ss.
        - resub. ired_both. gstep; econs; et. i. esplits; et. steps. gbase. eapply CIH; et.
        - resub. ired_both. gstep; econs; et. i. esplits; et. steps. gbase. eapply CIH; et.
        - resub. ired_both. gstep; econs; et. i. esplits; et. steps. gbase. eapply CIH; et.
      }
    }
    destruct u. resub. ired_both. gstep; econs; eauto. i. subst. destruct mrs_tgt1. esplits. steps.
    gbase. eapply CIH.
  Unshelve.
    all: try (exact Ord.O).
  Qed.

  Lemma my_lemma2
        umd
        (IN: In umd umds)
    :
      ModPair.sim (UMod.to_mod umd) (SMod.to_src (UMod.to_smod umd))
  .
  Proof.
    econs; ss; cycle 1.
    { admit "ez - wf". }
    i. r. eapply adequacy_lift.
    econs.
    { instantiate (1:=fun '(x, y) => x = y). ss.
      set (ums:=UMod.get_modsem umd sk) in *.
      rewrite ! List.map_map.
      eapply Forall2_apply_Forall2.
      { refl. }
      i. subst. unfold map_snd. des_ifs.
      rr. split; ss. r. ii. subst. ss. esplits; et. eapply my_lemma2_aux.
    }
    { ss. }
    { ss. }
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

  Definition UMod_main (mainbody: Any.t -> itree (uCallE +' pE +' eventE) Any.t): UMod.t := {|
    UMod.get_modsem := fun _ => (UModSem.mk [("main", mainbody)] "Main" (tt↑));
    UMod.sk := Sk.unit;
  |}
  .

  Variable (mainbody: Any.t -> itree (uCallE +' pE +' eventE) Any.t).
  Hypothesis MAINU: In (UMod_main mainbody) umds.

  Let mains: SMod.t := UMod.to_smod (UMod_main mainbody).

  Hypothesis WFR: URA.wf (List.fold_left (⋅) (List.map (SModSem.initial_mr) kmss) ε).
  (* Hypothesis MAINM: In (SMod.main mainpre mainbody) kmds. *)

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
    { erewrite <- List.map_map with (f:=UMod.to_smod).
      rewrite <- map_app.
      eapply adequacy_type2.
      - instantiate (1:=(kmds ++ List.map UMod.to_smod umds)).
        erewrite <- List.map_id with (l:=(kmds ++ List.map UMod.to_smod umds)) at 1.
        eapply Forall2_apply_Forall2.
        { instantiate (1:=eq). refl. }
        i. subst. exists _gstb. split; ss. r. intro ske. rewrite <- gstb_eq. refl.
      - admit "main pre".
      - ss. instantiate (1:=ε). rewrite ! URA.unit_id. rewrite ! URA.unit_idl. admit "should be ez".
      - Check (UModSem.transl_fun_smod mainbody).
        admit "mid - main argument parameterization".
        (* instantiate (1:=UModSem.transl_fun_smod mainbody). rewrite in_app_iff. eauto. *)
    }
    eapply my_lemma2.
  Unshelve.
    all: ss.
    { ii. apply True. }
    { ii. apply ITree.spin. }
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
  Ltac ired_both := HoareDef.ired_both.

  Let ms_src := (ModL.enclose (Mod.add_list (kmds_top ++ List.map UMod.to_mod umds))).
  Let p_src := (ModSemL.prog ms_src).
  Let ms_tgt := (ModL.enclose (Mod.add_list (List.map SMod.to_src (kmds ++ List.map UMod.to_smod umds)))).
  Let p_tgt := (ModSemL.prog ms_tgt).

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
  TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT

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
      fn (args: Any.t) T (ktr0 ktr1: ktree _ _ T)
      (SIM: forall rv, sim_body o1 (ktr0 rv) (ktr1 rv))
    :
      _sim_body sim_body o0 (trigger EventsL.PushFrame;;; trigger (Call fn args) >>= ktr0)
                (trigger EventsL.PushFrame;;; trigger (Call fn (Any.pair tt↑ args)) >>= ktr1)
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
    forall (args: list val), sim_body 100 (f0 args↑) (f1 (@inr unit _ args)↑)
  .

  (* Definition sim_fun (f0: list val -> itree EventsL.Es val) *)
  (*            (f1: (unit + list val) -> itree EventsL.Es val): Prop := *)
  (*   forall args, sim_body 100 (f0 args) (f1 (inr args)) *)
  (* . *)





  Lemma sim_known_aux
        T mn (itr: itree _ T)
    :
      sim_body 100 (transl_all mn (KModSem.interp_kCallE_src itr))
               (transl_all mn (interp_hCallE_src (KModSem.transl_itr_tgt itr)))
  .
  Proof.
    ginit. { eapply cpn4_wcompat; eauto with paco. } revert itr. gcofix CIH. i.
    ides itr.
    { steps. }
    { steps. gbase. eapply CIH. }
    rewrite <- bind_trigger. resub.
    destruct e.
    { destruct k0.
      resub. steps.
      des_ifs.
      - steps. gbase. eapply CIH; et.
      - ired_both. ired. gstep; econs; et. i. steps. gbase. eapply CIH; et.
    }
    destruct s.
    { resub. steps. gbase. eapply CIH; et. }
    { resub. steps. gbase. eapply CIH; et. }
  Unshelve.
    all: try (by exact Ord.O).
  Qed.

  Lemma sim_known
        mn (f0: kspecbody)
    :
      sim_fun (transl_all mn ∘ KModSem.fun_to_src (ksb_body f0))
              (transl_all mn ∘ fun_to_src (KModSem.transl_fun_tgt f0.(ksb_body)))
  .
  Proof.
    ii.
    esplits.
    unfold fun_to_src. unfold body_to_src. unfold cfun.
    unfold KModSem.fun_to_src. unfold KModSem.body_to_src. unfold cfun.
    steps. rewrite ! Any.upcast_downcast. steps.
    replace (Ord.from_nat 100) with ((Ord.from_nat 0) + (Ord.from_nat 100))%ord; cycle 1.
    { admit "ez - ordC spec". }
    ginit. { eapply cpn4_wcompat; eauto with paco. } guclo bbindC_spec.
    econs.
    { gfinal. right. eapply sim_known_aux. }
    ii. steps.
  Unshelve.
    all: try (by exact Ord.O).
  Qed.

  Lemma sim_unknown_aux
        mn (itr: itree _ val)
    :
      sim_body 100 (transl_all mn (UModSem.transl_itr_mod itr))
               (transl_all mn (interp_hCallE_src (UModSem.transl_itr_smod itr)))
  .
  Proof.
    ginit. { eapply cpn4_wcompat; eauto with paco. } revert itr. gcofix CIH. i.
    ides itr.
    { steps. }
    { steps. gbase. eapply CIH. }
    rewrite <- bind_trigger. resub.
    destruct e.
    { destruct u. resub. ired_both. resub. ired_both. ired. gstep; econs; et. i. steps. gbase. eapply CIH; et. }
    destruct s.
    { resub. steps. resub. steps. gbase. eapply CIH; et. }
    { resub. steps. resub. steps. gbase. eapply CIH; et. }
  Unshelve.
    all: try (by exact Ord.O).
  Qed.

  Lemma sim_unknown
        (ktr: list val -> itree _ val) mn
    :
      sim_fun (transl_all mn ∘ (UModSem.transl_fun_mod ktr))
              (transl_all mn ∘ (fun_to_src (UModSem.transl_fun_smod ktr)))
  .
  Proof.
    ii.
    esplits.
    unfold fun_to_src. unfold body_to_src. unfold UModSem.transl_fun_mod. unfold cfun.
    steps.
    rewrite ! Any.upcast_downcast. steps.
    replace (Ord.from_nat 100) with ((Ord.from_nat 0) + (Ord.from_nat 100))%ord; cycle 1.
    { admit "ez - ordC spec". }
    ginit. { eapply cpn4_wcompat; eauto with paco. } guclo bbindC_spec.
    econs.
    { gfinal. right. eapply sim_unknown_aux. }
    ii. steps.
  Unshelve.
    all: try (by exact Ord.O).
  Qed.

  Lemma find_sim
        fn
    :
        option_rel (@sim_fun Any.t)
                   (alist_find fn (ModSemL.fnsems ms_src))
                   (alist_find fn (ModSemL.fnsems ms_tgt))
  .
  Proof.
    destruct (alist_find fn (ModSemL.fnsems ms_src)) eqn:T.
    - list_tac.
      unfold ms_src in T.
      list_tac.
      rewrite <- sk_link_eq3 in *. folder. subst.
      ss. list_tac. subst. des_ifs. ss. subst. list_tac. des_ifs.
      rewrite in_app_iff in *. des.
      + destruct (alist_find fn (ModSemL.fnsems ms_tgt)) eqn:U.
        * list_tac. unfold ms_tgt in U. list_tac. subst. ss. list_tac.
          des_ifs. ss. rewrite <- sk_link_eq2 in *. folder.
          rewrite in_app_iff in *. des.
          { unfold kmds in U2. unfold kmds_top in T1. list_tac. subst. ss. list_tac. des_ifs. ss.
            assert(x = x1) by admit "ez - uniqueness"; subst.
            assert(k = k0) by admit "ez - uniqueness"; subst.
            econs. split; ss.
            eapply sim_known.
          }
          { unfold kmds_top in *. list_tac. subst. exfalso. admit "ez - uniqueness". }
        * exfalso.
          unfold kmds_top in *. list_tac. subst. ss. list_tac. des_ifs.
          eapply alist_find_none in U.
          eapply U. unfold ms_tgt. list_tac.
          { rewrite in_app_iff. left. unfold kmds. list_tac. }
          rewrite <- sk_link_eq2. folder.
          unfold flip. ss.
          list_tac. ss.
      + destruct (alist_find fn (ModSemL.fnsems ms_tgt)) eqn:U.
        * unfold ms_tgt in U. list_tac. subst. ss. list_tac. des_ifs. ss. econs.
          rewrite <- sk_link_eq2 in *. folder.
          rewrite in_app_iff in *. des.
          { exfalso. unfold kmds in U2. list_tac. subst. ss. list_tac. des_ifs. admit "ez - uniqueness". }
          list_tac. subst. ss. list_tac. des_ifs. ss.
          assert(x = x3) by admit "ez - uniqueness"; subst.
          assert(i = i0) by admit "ez - uniqueness"; subst. clear_tac.
          eapply sim_unknown.
        * exfalso.
          ss. list_tac. subst. ss. list_tac. des_ifs.
          eapply alist_find_none in U. eapply U.
          unfold ms_tgt. list_tac.
          { rewrite in_app_iff. right. list_tac. }
          rewrite <- sk_link_eq2. folder.
          unfold flip. ss.
          list_tac. ss.
    - destruct (alist_find fn (ModSemL.fnsems ms_tgt)) eqn:U.
      + exfalso.
        list_tac. unfold ms_tgt in U. list_tac. subst. ss. list_tac. des_ifs. ss.
        rewrite <- sk_link_eq2 in *. folder.
        rewrite in_app_iff in *. des.
        * unfold kmds in U2. list_tac. subst. ss. list_tac. des_ifs.
          eapply alist_find_none in T. eapply T.
          { unfold ms_src. list_tac.
            { rewrite in_app_iff. left; et. unfold kmds_top. list_tac. }
            ss. list_tac; cycle 1.
            { rewrite <- sk_link_eq3 in *. folder. et. }
            ss.
          }
        * list_tac. subst. ss. list_tac. des_ifs.
          eapply alist_find_none in T. eapply T.
          { unfold ms_src. list_tac.
            { rewrite in_app_iff. right; et. list_tac. }
            ss. list_tac; cycle 1.
            { rewrite <- sk_link_eq3 in *. folder. et. }
            ss.
          }
      + econs.
  Qed.

  Lemma my_lemma2_aux
        fn (args: list val) st0
    :
        simg eq 200
             (* (EventsL.interp_Es p_src (trigger (Call fn args)) st0) *)
             (* (EventsL.interp_Es p_tgt (trigger (Call fn (Any.pair args false↑))) st0) *)
             (EventsL.interp_Es p_src (p_src (Call fn args↑)) st0)
             (EventsL.interp_Es p_tgt (p_tgt (Call fn (@inr unit _ args)↑)) st0)
  .
  Proof.
    ginit. revert_until p_tgt. gcofix CIH. i.
    cbn. steps.
    generalize (find_sim fn). intro T. inv T; cbn; steps.
    specialize (IN args). rename a into i. rename b into i0.
    abstr (i args↑) itr_src. abstr (i0 (@inr unit _ args)↑) itr_tgt. clear i i0 args H H0. clear_tac.
    revert_until sk_link_eq3. gcofix CIH. i.
    guclo ordC_spec. econs.
    { instantiate (1:=(100 + 100)%ord). rewrite <- OrdArith.add_from_nat. cbn. refl. }
    (* instantiate (1:=(100 + 100)%ord). *)
    guclo bindC_spec. econs; cycle 1.
    { instantiate (1:=eq). ii. subst. des_ifs. steps. }
    revert_until CIH0. generalize (Ord.from_nat 100) as idx. gcofix CIH.
    i. punfold IN. destruct st0 as [rst0 pst0].  destruct rst0 as [mrs0 frs0].
    dependent destruction IN; pclearbot.
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
    unfold ModSemL.initial_itr, ModSemL.initial_itr_arg. Local Opaque ModSemL.prog. ss.
    unfold ITree.map.
    unfold assume. folder.
    steps.
    esplits; et. { admit "ez - wf". } steps.
    instantiate (1:=(200 + 200)%ord).
    match goal with | [ |- gpaco6 _ _ _ _ _ _ _ _ ?src ?tgt ] => remember src as tmp end.
    replace ([]↑) with ((@inr unit _ ([]: list val))↑); cycle 1.
    { admit "ez - parameterize initial argument && use transitivity of refinement". }
    subst.
    assert(STEQ: (ModSemL.initial_r_state ms_src, ModSemL.initial_p_state ms_src)
                 = (ModSemL.initial_r_state ms_tgt, ModSemL.initial_p_state ms_tgt)).
    { assert(forall fn, alist_find fn (ModSemL.initial_mrs ms_src) =
                        alist_find fn (ModSemL.initial_mrs ms_tgt)).
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

  Definition UMod_main (mainbody: list val -> itree (uCallE +' pE +' eventE) val): UMod.t := {|
    UMod.get_modsem := fun _ => (UModSem.mk [("main", mainbody)] "Main" (tt↑));
    UMod.sk := Sk.unit;
  |}
  .

  Variable (mainbody: list val -> itree (uCallE +' pE +' eventE) val).
  Hypothesis MAINU: In (UMod_main mainbody) umds.

  Let mains: SMod.t := UMod.to_smod (UMod_main mainbody).

  Hypothesis WFR: URA.wf (List.fold_left (⋅) (List.map (SModSem.initial_mr) kmss) ε).
  (* Hypothesis MAINM: In (SMod.main mainpre mainbody) kmds. *)

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
    { erewrite <- List.map_map with (f:=UMod.to_smod).
      rewrite <- map_app.
      eapply adequacy_type2.
      - instantiate (1:=(kmds ++ List.map UMod.to_smod umds)).
        erewrite <- List.map_id with (l:=(kmds ++ List.map UMod.to_smod umds)) at 1.
        eapply Forall2_apply_Forall2.
        { instantiate (1:=eq). refl. }
        i. subst. exists _gstb. split; ss. r. intro ske. rewrite <- gstb_eq. refl.
      - admit "main pre".
      - ss. instantiate (1:=ε). rewrite ! URA.unit_id. rewrite ! URA.unit_idl. admit "should be ez".
      - Check (UModSem.transl_fun_smod mainbody).
        admit "mid - main argument parameterization".
        (* instantiate (1:=UModSem.transl_fun_smod mainbody). rewrite in_app_iff. eauto. *)
    }
    eapply my_lemma2.
  Unshelve.
    all: ss.
    { ii. apply True. }
    { ii. apply ITree.spin. }
  Qed.

End ADQ.
