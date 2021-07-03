Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import Permutation.

Set Implicit Arguments.


Notation gname := string (only parsing). (*** convention: not capitalized ***)
Notation mname := string (only parsing). (*** convention: capitalized ***)

(* TODO: move it to Coqlib *)
Lemma nodup_comm A (l0 l1: list A)
      (NODUP: NoDup (l0 ++ l1))
  :
    NoDup (l1 ++ l0).
Proof.
  eapply Permutation_NoDup; [|et].
  eapply Permutation_app_comm.
Qed.

Section EVENTSCOMMON.

  Variant eventE: Type -> Type :=
  | Choose (X: Type): eventE X
  | Take X: eventE X
  | Syscall (fn: gname) (args: list Z) (rvs: Z -> Prop): eventE Z
  .

  (* Notation "'Choose' X" := (trigger (Choose X)) (at level 50, only parsing). *)
  (* Notation "'Take' X" := (trigger (Take X)) (at level 50, only parsing). *)

  Definition triggerUB {E A} `{eventE -< E}: itree E A :=
    v <- trigger (Take void);; match v: void with end
  .

  Definition triggerNB {E A} `{eventE -< E}: itree E A :=
    v <- trigger (Choose void);; match v: void with end
  .

  Definition unwrapN {E X} `{eventE -< E} (x: option X): itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerNB
    end.

  Definition unwrapU {E X} `{eventE -< E} (x: option X): itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerUB
    end.

  Definition assume {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Take P) ;;; Ret tt.
  Definition guarantee {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Choose P) ;;; Ret tt.

  (* Notation "'unint?'" := (unwrapA <*> unint) (at level 57, only parsing). *)
  (* Notation "'unint﹗'" := (unwrapG <*> unint) (at level 57, only parsing). *)
  (* Notation "'Ret!' f" := (RetG f) (at level 57, only parsing). *)
  (* Notation "'Ret?' f" := (RetA f) (at level 57, only parsing). *)

End EVENTSCOMMON.

Notation "f '?'" := (unwrapU f) (at level 9, only parsing).
Notation "f 'ǃ'" := (unwrapN f) (at level 9, only parsing).
Notation "(?)" := (unwrapU) (only parsing).
Notation "(ǃ)" := (unwrapN) (only parsing).
Goal (tt ↑↓?) = Ret tt. rewrite Any.upcast_downcast. ss. Qed.
Goal (tt ↑↓ǃ) = Ret tt. rewrite Any.upcast_downcast. ss. Qed.







Section EVENTSCOMMON.

  Definition p_state: Type := (mname -> Any.t).

  (*** Same as State.pure_state, but does not use "Vis" directly ***)
  Definition pure_state {S E}: E ~> stateT S (itree E) := fun _ e s => x <- trigger e;; Ret (s, x).

  Lemma unfold_interp_state: forall {E F} {S R} (h: E ~> stateT S (itree F)) (t: itree E R) (s: S),
      interp_state h t s = _interp_state h (observe t) s.
  Proof. i. f. apply unfold_interp_state. Qed.

End EVENTSCOMMON.








Module EventsL.
Section EVENTSL.

  Inductive callE: Type -> Type :=
  | Call (mn: option mname) (fn: gname) (args: Any.t): callE Any.t
  .

  Inductive pE: Type -> Type :=
  | PPut (mn: mname) (p: Any.t): pE unit
  | PGet (mn: mname): pE Any.t
  .

  (*** TODO: we don't want to require "mname" here ***)
  (*** use dummy mname? ***)
  (* Definition FPut E `{rE -< E} (mn: mname) (fr: GRA): itree E unit := *)

  Definition Es: Type -> Type := (callE +' pE +' eventE).

  (* Inductive mdE: Type -> Type := *)
  (* | MPut (mn: mname) (r: GRA): mdE unit *)
  (* | MGet (mn: mname): mdE GRA *)
  (* . *)

  (* Inductive fnE: Type -> Type := *)
  (* | FPut (r: GRA): fnE unit *)
  (* | FGet: fnE GRA *)
  (* | FPush: fnE unit *)
  (* | FPop: fnE unit *)
  (* . *)






  (********************************************************************)
  (*************************** Interpretation *************************)
  (********************************************************************)

  Definition handle_pE {E}: pE ~> stateT p_state (itree E) :=
    fun _ e mps =>
      match e with
      | PPut mn p => Ret (update mps mn p, tt)
      | PGet mn => Ret (mps, mps mn)
      end.
  Definition interp_pE {E}: itree (pE +' E) ~> stateT p_state (itree E) :=
    (* State.interp_state (case_ ((fun _ e s0 => resum_itr (handle_pE e s0)): _ ~> stateT _ _) State.pure_state). *)
    State.interp_state (case_ handle_pE pure_state).

  (* Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (rst0: r_state) (pst0: p_state): itree eventE _ := *)
  (*   interp_pE (interp_rE (interp_mrec prog itr0) rst0) pst0 *)
  (* . *)
  Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (st0: p_state): itree eventE (p_state * _)%type :=
    '(st1, v) <- interp_pE (interp_mrec prog itr0) st0;;
    Ret (st1, v)
  .



  Lemma interp_Es_bind
        A B
        (itr: itree Es A) (ktr: A -> itree Es B)
        (prog: callE ~> itree Es)
        st0
    :
      interp_Es prog (v <- itr ;; ktr v) st0 =
      '(st1, v) <- interp_Es prog (itr) st0 ;; interp_Es prog (ktr v) st1
  .
  Proof. unfold interp_Es, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_tau
        (prog: callE ~> itree Es)
        A
        (itr: itree Es A)
        st0
    :
      interp_Es prog (tau;; itr) st0 = tau;; interp_Es prog itr st0
  .
  Proof. unfold interp_Es, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_ret
        T
        prog st0 (v: T)
    :
      interp_Es prog (Ret v) st0 = Ret (st0, v)
  .
  Proof. unfold interp_Es, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_callE
        p st0 T
        (* (e: Es Σ) *)
        (e: callE T)
    :
      interp_Es p (trigger e) st0 = tau;; (interp_Es p (p _ e) st0)
  .
  Proof. unfold interp_Es, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_pE
        p st0
        (* (e: Es Σ) *)
        T
        (e: pE T)
    :
      interp_Es p (trigger e) st0 =
      '(st1, r) <- handle_pE e st0;;
      tau;; tau;;
      Ret (st1, r)
  .
  Proof.
    unfold interp_Es, interp_pE. grind.
  Qed.

  Lemma interp_Es_eventE
        p st0
        (* (e: Es Σ) *)
        T
        (e: eventE T)
    :
      interp_Es p (trigger e) st0 = r <- trigger e;; tau;; tau;; Ret (st0, r)
  .
  Proof.
    unfold interp_Es, interp_pE. grind.
    unfold pure_state. grind.
  Qed.

  Lemma interp_Es_triggerUB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (interp_Es prog (triggerUB) st0: itree eventE (_ * A)) = triggerUB
  .
  Proof.
    unfold interp_Es, interp_pE, pure_state, triggerUB. grind.
  Qed.

  Lemma interp_Es_triggerNB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (interp_Es prog (triggerNB) st0: itree eventE (_ * A)) = triggerNB
  .
  Proof.
    unfold interp_Es, interp_pE, pure_state, triggerNB. grind.
  Qed.
  Opaque interp_Es.
End EVENTSL.
End EventsL.
Opaque EventsL.interp_Es.




Class BehConfig := { finalize: Any.t -> option Z; initial_arg: Any.t }.

Module ModSemL.
Import EventsL.
Section MODSEML.


  (* Record t: Type := mk { *)
  (*   state: Type; *)
  (*   local_data: Type; *)
  (*   step (skenv: SkEnv.t) (st0: state) (ev: option event) (st1: state): Prop; *)
  (*   state_sort: state -> sort; *)
  (*   initial_local_data: local_data; *)
  (*   sk: Sk.t; *)
  (*   name: string; *)
  (* } *)
  (* . *)

  Record t: Type := mk {
    (* initial_ld: mname -> GRA; *)
    fnsems: alist gname ((option mname * Any.t) -> itree Es Any.t);
    initial_mrs: alist mname Any.t;
  }
  .

  Record wf (ms: t): Prop := mk_wf {
    wf_fnsems: NoDup (List.map fst ms.(fnsems));
    wf_initial_mrs: NoDup (List.map fst ms.(initial_mrs));
  }
  .

  (*** using "Program Definition" makes the definition uncompilable; why?? ***)
  Definition add (ms0 ms1: t): t := {|
    (* sk := Sk.add md0.(sk) md1.(sk); *)
    (* initial_ld := URA.add (t:=URA.pointwise _ _) md0.(initial_ld) md1.(initial_ld); *)
    (* sem := fun _ '(Call fn args) => *)
    (*          (if List.in_dec string_dec fn md0.(sk) then md0.(sem) else md1.(sem)) _ (Call fn args); *)
    fnsems := app ms0.(fnsems) ms1.(fnsems);
    initial_mrs := app ms0.(initial_mrs) ms1.(initial_mrs);
  |}
  .



  Section INTERP.

  Variable ms: t.

  Definition prog: callE ~> itree Es :=
    fun _ '(Call mn fn args) =>
      sem <- (alist_find fn ms.(fnsems))?;;
      rv <- (sem (mn, args));;
      Ret rv
  .



  Definition initial_p_state: p_state :=
    (fun mn => match alist_find mn ms.(initial_mrs) with
               | Some r => r
               | None => tt↑
               end).

  Context `{BCONF: BehConfig}.
  Definition initial_itr (P: option Prop): itree (eventE) Any.t :=
    match P with
    | None => Ret tt
    | Some P' => assume (<<WF: P'>>)
    end;;;
    snd <$> interp_Es prog (prog (Call None "main" initial_arg)) (initial_p_state).



  Let state: Type := itree eventE Any.t.

  Definition state_sort (st0: state): sort :=
    match (observe st0) with
    | TauF _ => demonic
    | RetF rv =>
      match (finalize rv) with
      | Some rv => final rv
      | _ => angelic
      end
    | VisF (Choose X) k => demonic
    | VisF (Take X) k => angelic
    | VisF (Syscall fn args rvs) k => vis
    end
  .

  Inductive step: state -> option event -> state -> Prop :=
  | step_tau
      itr
    :
      step (Tau itr) None itr
  | step_choose
      X k (x: X)
    :
      step (Vis (subevent _ (Choose X)) k) None (k x)
  | step_take
      X k (x: X)
    :
      step (Vis (subevent _ (Take X)) k) None (k x)
  | step_syscall
      fn args rv (rvs: Z -> Prop) k
      (SYSCALL: syscall_sem (event_sys fn args rv))
      (RETURN: rvs rv)
    :
      step (Vis (subevent _ (Syscall fn args rvs)) k) (Some (event_sys fn args rv)) (k rv)
  .

  Lemma step_trigger_choose_iff X k itr e
        (STEP: step (trigger (Choose X) >>= k) e itr)
    :
      exists x,
        e = None /\ itr = k x.
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et.  }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
  Qed.

  Lemma step_trigger_take_iff X k itr e
        (STEP: step (trigger (Take X) >>= k) e itr)
    :
      exists x,
        e = None /\ itr = k x.
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et.  }
    { eapply f_equal with (f:=observe) in H0. ss. }
  Qed.

  Lemma step_tau_iff itr0 itr1 e
        (STEP: step (Tau itr0) e itr1)
    :
      e = None /\ itr0 = itr1.
  Proof.
    inv STEP. et.
  Qed.

  Lemma step_ret_iff rv itr e
        (STEP: step (Ret rv) e itr)
    :
      False.
  Proof.
    inv STEP.
  Qed.

  Lemma step_trigger_syscall_iff fn args rvs k e itr
        (STEP: step (trigger (Syscall fn args rvs) >>= k) e itr)
    :
      exists rv, itr = k rv /\ e = Some (event_sys fn args rv)
                 /\ <<RV: rvs rv>> /\ <<SYS: syscall_sem (event_sys fn args rv)>>.
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et. }
  Qed.


  Let itree_eta E R (itr0 itr1: itree E R)
      (OBSERVE: observe itr0 = observe itr1)
    :
      itr0 = itr1.
  Proof.
    rewrite (itree_eta_ itr0).
    rewrite (itree_eta_ itr1).
    rewrite OBSERVE. auto.
  Qed.

  Lemma step_trigger_choose X k x
    :
      step (trigger (Choose X) >>= k) None (k x).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (Choose X) k)
    end; ss.
    { econs. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.

  Lemma step_trigger_take X k x
    :
      step (trigger (Take X) >>= k) None (k x).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (Take X) k)
    end; ss.
    { econs. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.

  Lemma step_trigger_syscall fn args (rvs: Z -> Prop) k rv
        (RV: rvs rv) (SYS: syscall_sem (event_sys fn args rv))
    :
      step (trigger (Syscall fn args rvs) >>= k) (Some (event_sys fn args rv)) (k rv).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (Syscall fn args rvs) k)
    end; ss.
    { econs; et. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.


  Program Definition compile_itree: itree eventE Any.t -> semantics :=
    fun itr =>
      {|
        STS.state := state;
        STS.step := step;
        STS.initial_state := itr;
        STS.state_sort := state_sort;
      |}
  .
  Next Obligation. inv STEP; inv STEP0; ss. csc. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.

  Definition compile P: semantics :=
    compile_itree (initial_itr P).

  Lemma initial_itr_not_wf P
        (WF: ~ P)
        tr
    :
      Beh.of_program (compile_itree (initial_itr (Some P))) tr.
  Proof.
    eapply Beh.ub_top. pfold. econsr; ss; et. rr. ii; ss.
    unfold initial_itr, assume in *. rewrite bind_bind in STEP.
    eapply step_trigger_take_iff in STEP. des. subst. ss.
  Qed.

  Lemma compile_not_wf P
        (WF: ~ P)
        tr
    :
      Beh.of_program (compile (Some P)) tr.
  Proof.
    eapply initial_itr_not_wf; et.
  Qed.

  (* Program Definition interp_no_forge: semantics := {| *)
  (*   STS.state := state; *)
  (*   STS.step := step; *)
  (*   STS.initial_state := itr2'; *)
  (*   STS.state_sort := state_sort; *)
  (* |} *)
  (* . *)
  (* Next Obligation. inv STEP; inv STEP0; ss. csc. rewrite SYSCALL in *. csc. Qed. *)
  (* Next Obligation. inv STEP; ss. Qed. *)
  (* Next Obligation. inv STEP; ss. Qed. *)

  End INTERP.

  (*** TODO: probably we can make ModSemL.t as an RA too. (together with Sk.t) ***)
  (*** However, I am not sure what would be the gain; and there might be universe problem. ***)

  Context {BCONF: BehConfig}.

  Let add_comm_aux arg
      ms0 ms1 stl0 str0
      P
      (SIM: stl0 = str0)
    :
      <<COMM: Beh.of_state (compile_arg (add ms0 ms1) P arg) stl0
              <1=
              Beh.of_state (compile_arg (add ms1 ms0) P arg) str0>>
  .
  Proof.
    subst. revert str0. pcofix CIH. i. pfold.
    punfold PR. induction PR using Beh.of_state_ind; ss.
    - econs 1; et.
    - econs 2; et.
      clear CIH. clear_tac. revert st0 H.
      pcofix CIH. i. punfold H0. pfold.
      inv H0.
      + econs 1; eauto. ii. ss. exploit STEP; et. i; des. right. eapply CIH; et. pclearbot. ss.
      + econs 2; eauto. des. esplits; eauto. right. eapply CIH; et. pclearbot. ss.
    - econs 4; et. pclearbot. right. eapply CIH; et.
    - econs 5; et. rr in STEP. des. rr. esplits; et.
    - econs 6; et. ii. exploit STEP; et. i; des. clarify.
  Qed.

  Lemma wf_comm
        ms0 ms1
    :
      <<EQ: wf (add ms0 ms1) = wf (add ms1 ms0)>>
  .
  Proof.
    assert (forall ms0 ms1, wf (add ms0 ms1) -> wf (add ms1 ms0)).
    { i. inv H. econs; ss.
      { rewrite List.map_app in *.
        eapply nodup_comm; et. }
      { rewrite List.map_app in *.
        eapply nodup_comm; et. }
    }
    r. eapply prop_ext. split; i; auto.
  Qed.

  Theorem add_comm_arg arg
          ms0 ms1 (P0 P1: Prop) (IMPL: P1 -> P0)
          (WF: wf (add ms1 ms0))
    :
      <<COMM: Beh.of_program (compile_arg (add ms0 ms1) (Some P0) arg) <1= Beh.of_program (compile_arg (add ms1 ms0) (Some P1) arg)>>
  .
  Proof.
    destruct (classic (P1)); cycle 1.
    { ii. eapply initial_itr_arg_not_wf; et. }
    replace P0 with P1.
    2: { eapply prop_ext. split; auto. }
    ii. ss. r in PR. r. eapply add_comm_aux; et.
    rp; et. clear PR. ss. cbn. unfold initial_itr, initial_itr_arg. f_equal.
    { extensionality u. destruct u. f_equal.
      replace (@interp_Es Any.t (prog (add ms1 ms0))) with (@interp_Es Any.t (prog (add ms0 ms1))).
      { f_equal.
        { ss. f_equal. f_equal. eapply alist_permutation_find.
          { inv WF. et. }
          { eapply Permutation_app_comm. }
        }
        { unfold initial_p_state. extensionality mn. ss.
          erewrite alist_permutation_find; et.
          { inv WF. ss. }
          { eapply Permutation_app_comm. }
        }
      }
      f_equal. unfold prog. extensionality T. extensionality e. destruct e.
      f_equal. f_equal. symmetry. eapply alist_permutation_find; et.
      { inv WF. ss. }
      { eapply Permutation_app_comm. }
    }
  Qed.

  Theorem add_comm
          ms0 ms1 (P0 P1: Prop) (IMPL: P1 -> P0)
          (WF: wf (add ms1 ms0))
    :
      <<COMM: Beh.of_program (compile (add ms0 ms1) (Some P0)) <1= Beh.of_program (compile (add ms1 ms0) (Some P1))>>
  .
  Proof.
    eapply (@add_comm_arg (tt)↑ ms0 ms1 P0 P1 IMPL WF).
  Qed.

  Lemma add_assoc' ms0 ms1 ms2:
    add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
  Proof.
    induction ms2; ss. unfold add. f_equal; ss.
    { eapply app_assoc. }
    { eapply app_assoc. }
  Qed.

  Lemma add_assoc_eq ms0 ms1 ms2
    :
      add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
  Proof.
    unfold add. ss. f_equal.
    { apply List.app_assoc. }
    { apply List.app_assoc. }
  Qed.

  Theorem add_assoc_arg arg
          ms0 ms1 ms2 P
    :
      <<COMM: Beh.of_program (compile_arg (add ms0 (add ms1 ms2)) P arg) <1=
              Beh.of_program (compile_arg (add (add ms0 ms1) ms2) P arg)>>
  .
  Proof.
    rewrite add_assoc_eq. ss.
  Qed.

  Theorem add_assoc
          ms0 ms1 ms2 P
    :
      <<COMM: Beh.of_program (compile (add ms0 (add ms1 ms2)) P) <1=
              Beh.of_program (compile (add (add ms0 ms1) ms2) P)>>
  .
  Proof.
    rewrite add_assoc_eq. ss.
  Qed.

  Theorem add_assoc_rev_arg arg
          ms0 ms1 ms2 P
    :
      <<COMM: Beh.of_program (compile_arg (add ms0 (add ms1 ms2)) P arg) <1=
              Beh.of_program (compile_arg (add (add ms0 ms1) ms2) P arg)>>
  .
  Proof.
    rewrite add_assoc_eq. ss.
  Qed.

  Theorem add_assoc_rev
          ms0 ms1 ms2 P
    :
      <<COMM: Beh.of_program (compile (add ms0 (add ms1 ms2)) P) <1=
              Beh.of_program (compile (add (add ms0 ms1) ms2) P)>>
  .
  Proof.
    rewrite add_assoc_eq. ss.
  Qed.
End MODSEML.
End ModSemL.
















(* Module Events. *)
Section EVENTS.

  Inductive callE: Type -> Type :=
  | Call (fn: gname) (args: Any.t): callE Any.t
  .

  Inductive pE: Type -> Type :=
  | PPut (p: Any.t): pE unit
  | PGet: pE Any.t
  .

  Definition Es: Type -> Type := (callE +' pE+' eventE).

  Definition handle_pE (mn: mname): pE ~> EventsL.pE :=
    fun _ pe =>
      match pe with
      | PPut a0 => (EventsL.PPut mn a0)
      | PGet => (EventsL.PGet mn)
      end
  .

  Definition handle_callE (mn: mname) `{EventsL.callE -< E}: callE ~> itree E :=
    fun _ '(Call fn args) =>
      r <- trigger (EventsL.Call (Some mn) fn args);;
      Ret r
  .

  Definition handle_all (mn: mname): Es ~> itree EventsL.Es.
    i. destruct X.
    { apply (handle_callE mn); assumption. }
    destruct s.
    { exact (trigger (handle_pE mn p)). }
    exact (trigger e).
  Defined.

  Definition transl_all (mn: mname): itree Es ~> itree EventsL.Es := interp (handle_all mn).






  Lemma transl_all_bind
        A B
        (itr: itree Es A) (ktr: A -> itree Es B)
        mn
    :
      transl_all mn (itr >>= ktr) = a <- (transl_all mn itr);; (transl_all mn (ktr a))
  .
  Proof. unfold transl_all. grind. Qed.

  Lemma transl_all_tau
        mn
        A
        (itr: itree Es A)
    :
      transl_all mn (tau;; itr) = tau;; (transl_all mn itr)
  .
  Proof. unfold transl_all. grind. Qed.

  Lemma transl_all_ret
        mn
        A
        (a: A)
    :
      transl_all mn (Ret a) = Ret a
  .
  Proof. unfold transl_all. grind. Qed.

  Lemma transl_all_callE
        mn
        fn args
    :
      transl_all mn (trigger (Call fn args)) =
      r <- (trigger (EventsL.Call (Some mn) fn args));;
      tau;; Ret r
  .
  Proof. unfold transl_all. rewrite unfold_interp. ss. grind. Qed.

  Lemma transl_all_pE
        mn
        T (e: pE T)
    :
      transl_all mn (trigger e) = r <- trigger (handle_pE mn e);; tau;; Ret r
  .
  Proof. dependent destruction e; ss; unfold transl_all; rewrite unfold_interp; ss; grind. Qed.

  Lemma transl_all_eventE
        mn
        T (e: eventE T)
    :
      transl_all mn (trigger e) = r <- trigger e;; tau;; Ret r
  .
  Proof. dependent destruction e; ss; unfold transl_all; rewrite unfold_interp; ss; grind. Qed.

  Lemma transl_all_triggerUB
        mn T
    :
      transl_all mn (triggerUB: itree _ T) = triggerUB
  .
  Proof. unfold triggerUB. unfold transl_all; rewrite unfold_interp; ss; grind. Qed.

  Lemma transl_all_triggerNB
        mn T
    :
      transl_all mn (triggerNB: itree _ T) = triggerNB
  .
  Proof. unfold triggerNB. unfold transl_all; rewrite unfold_interp; ss; grind. Qed.

End EVENTS.
(* End Events. *)

Section EVENTSCOMMON.

(*** casting call, fun ***)
(* Definition ccallN {X Y} (fn: gname) (varg: X): itree Es Y := vret <- trigger (Call fn varg↑);; vret <- vret↓ǃ;; Ret vret. *)
(* Definition ccallU {X Y} (fn: gname) (varg: X): itree Es Y := vret <- trigger (Call fn varg↑);; vret <- vret↓?;; Ret vret. *)
(* Definition cfunN {X Y} (body: X -> itree Es Y): Any.t -> itree Es Any.t := *)
(*   fun varg => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑. *)
(* Definition cfunU {X Y} (body: X -> itree Es Y): Any.t -> itree Es Any.t := *)
(*   fun varg => varg <- varg↓?;; vret <- body varg;; Ret vret↑. *)

  (* Definition ccall {X Y} (fn: gname) (varg: X): itree Es Y := vret <- trigger (Call fn varg↑);; vret <- vret↓ǃ;; Ret vret. *)
  (* Definition cfun {X Y} (body: X -> itree Es Y): Any.t -> itree Es Any.t := *)
  (*   fun varg => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑. *)
  Context `{HasCallE: callE -< E}.
  Context `{HasEventE: eventE -< E}.

  Definition ccallN {X Y} (fn: gname) (varg: X): itree E Y := vret <- trigger (Call fn varg↑);; vret <- vret↓ǃ;; Ret vret.
  Definition ccallU {X Y} (fn: gname) (varg: X): itree E Y := vret <- trigger (Call fn varg↑);; vret <- vret↓?;; Ret vret.

  Definition cfunN {X Y} (body: X -> itree E Y): (option mname * Any.t) -> itree E Any.t :=
    fun '(_, varg) => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑.
  Definition cfunU {X Y} (body: X -> itree E Y): (option mname * Any.t) -> itree E Any.t :=
    fun '(_, varg) => varg <- varg↓?;; vret <- body varg;; Ret vret↑.

End EVENTSCOMMON.



Module ModSem.
(* Import Events. *)
Section MODSEM.
  Record t: Type := mk {
    fnsems: list (gname * ((option mname * Any.t) -> itree Es Any.t));
    mn: mname;
    initial_st: Any.t;
  }
  .

  Definition prog (ms: t): callE ~> itree Es :=
    fun _ '(Call fn args) =>
      sem <- (alist_find fn ms.(fnsems))?;;
      '(mn, args) <- (Any.split args)ǃ;; mn <- mn↓ǃ;;
      (sem (mn, args))
  .

  (*** TODO: move to CoqlibC ***)
  (*** ss, cbn does not work as expected (in both version) ***)
  Definition map_fst A0 A1 B (f: A0 -> A1): (A0 * B) -> (A1 * B) := fun '(a, b) => (f a, b).
  Definition map_snd A B0 B1 (f: B0 -> B1): (A * B0) -> (A * B1) := fun '(a, b) => (a, f b).
  (* Definition map_fst A0 A1 B (f: A0 -> A1): (A0 * B) -> (A1 * B) := fun ab => match ab with (a, b) => (f a, b) end. *)
  (* Definition map_snd A B0 B1 (f: B0 -> B1): (A * B0) -> (A * B1) := fun ab => match ab with (a, b) => (a, f b) end. *)

  Definition lift (ms: t): ModSemL.t := {|
    ModSemL.fnsems := List.map (map_snd (fun sem args => transl_all ms.(mn) (sem args))) ms.(fnsems);
    ModSemL.initial_mrs := [(ms.(mn), ms.(initial_st))];
  |}
  .
  Coercion lift: t >-> ModSemL.t.

  Definition wf (ms: t): Prop := ModSemL.wf (lift ms).

  Context {BCONF: BehConfig}.
  Definition compile (ms: t) P: semantics := ModSemL.compile (lift ms) P.

End MODSEM.
End ModSem.

Coercion ModSem.lift: ModSem.t >-> ModSemL.t.




Module ModL.
Section MODL.

  Record t: Type := mk {
    get_modsem: Sk.t -> ModSemL.t;
    sk: Sk.t;
    enclose: ModSemL.t := (get_modsem (Sk.sort sk));
  }
  .

  Definition wf (md: t): Prop := (<<WF: ModSemL.wf md.(enclose)>> /\ <<SK: Sk.wf md.(sk)>>).

  Section BEH.

  Context {BCONF: BehConfig}.

  Definition compile (md: t): semantics :=
      ModSemL.compile (enclose md)
                      (Some (<<WF: ModSemL.wf (enclose md)>> /\ <<SK: Sk.wf md.(sk)>>)).
  Definition compile_arg (md: t) (arg: Any.t): semantics :=
    ModSemL.compile_itree (ModSemL.initial_itr_arg md.(enclose) (Some (wf md)) arg).

  Lemma compile_compile_arg_nil md:
    compile md = compile_arg md (tt)↑.
  Proof.
    refl.
  Qed.

  (* Record wf (md: t): Prop := mk_wf { *)
  (*   wf_sk: Sk.wf md.(sk); *)
  (* } *)
  (* . *)
  (*** wf about modsem is enforced in the semantics ***)

  Definition add (md0 md1: t): t := {|
    get_modsem := fun sk =>
                    ModSemL.add (md0.(get_modsem) sk) (md1.(get_modsem) sk);
    sk := Sk.add md0.(sk) md1.(sk);
  |}
  .

  Theorem add_comm_arg arg
          md0 md1
    :
      <<COMM: Beh.of_program (compile_arg (add md0 md1) arg) <1= Beh.of_program (compile_arg (add md1 md0) arg)>>
  .
  Proof.
    ii. unfold compile_arg in *.
    destruct (classic (ModSemL.wf (enclose (add md1 md0)) /\ Sk.wf (sk (add md1 md0)))).
    2: { eapply ModSemL.initial_itr_arg_not_wf. ss. }
    ss. des. assert (SK: Sk.wf (Sk.add (sk md0) (sk md1))).
    { unfold Sk.wf, Sk.add. rewrite List.map_app.
      eapply nodup_comm; et. rewrite <- List.map_app. auto. }
    rewrite Sk.sort_add_comm; et.
    eapply ModSemL.add_comm_arg; [| |et].
    { i. split; auto. unfold enclose. ss. rewrite Sk.sort_add_comm; et.
      inv H. econs; ss.
      { rewrite List.map_app in *. eapply nodup_comm; et. }
      { rewrite List.map_app in *. eapply nodup_comm; et. }
    }
    { rewrite Sk.sort_add_comm; et. }
  Qed.

  Theorem add_comm
          md0 md1
    :
      <<COMM: Beh.of_program (compile (add md0 md1)) <1= Beh.of_program (compile (add md1 md0))>>
  .
  Proof.
    rewrite ! compile_compile_arg_nil. eapply add_comm_arg.
  Qed.

  Lemma add_assoc' ms0 ms1 ms2:
    add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
  Proof.
    unfold add. f_equal.
    { extensionality skenv_link. ss. apply ModSemL.add_assoc'. }
    { eapply app_assoc. }
  Qed.

  Theorem add_assoc_arg arg
          md0 md1 md2
    :
      <<COMM: Beh.of_program (compile_arg (add md0 (add md1 md2)) arg) =
              Beh.of_program (compile_arg (add (add md0 md1) md2) arg)>>
  .
  Proof.
    rewrite add_assoc'. ss.
  Qed.

  Theorem add_assoc_rev_arg arg
          md0 md1 md2
    :
      <<COMM: Beh.of_program (compile_arg (add (add md0 md1) md2) arg) =
              Beh.of_program (compile_arg (add md0 (add md1 md2)) arg)>>
  .
  Proof.
    rewrite add_assoc'. ss.
  Qed.

  Theorem add_assoc
          md0 md1 md2
    :
      <<COMM: Beh.of_program (compile (add md0 (add md1 md2))) =
              Beh.of_program (compile (add (add md0 md1) md2))>>
  .
  Proof.
    rewrite add_assoc'. ss.
  Qed.

  Theorem add_assoc_rev
          md0 md1 md2
    :
      <<COMM: Beh.of_program (compile (add (add md0 md1) md2)) =
              Beh.of_program (compile (add md0 (add md1 md2)))>>
  .
  Proof.
    rewrite add_assoc'. ss.
  Qed.

  Definition empty: t := {|
    get_modsem := fun _ => ModSemL.mk [] [];
    sk := Sk.unit;
  |}
  .

  Lemma add_empty_r md: add md empty = md.
  Proof.
    destruct md; ss.
    unfold add, ModSemL.add. f_equal; ss.
    - extensionality skenv. destruct (get_modsem0 skenv); ss.
      repeat rewrite app_nil_r. auto.
    - unfold Sk.add. rewrite app_nil_r. auto.
  Qed.

  Lemma add_empty_l md: add empty md = md.
  Proof.
    destruct md; ss.
    unfold add, ModSemL.add. f_equal; ss.
    extensionality skenv. destruct (get_modsem0 skenv); ss.
  Qed.

  End BEH.

End MODL.
End ModL.



Module Mod.
Section MOD.

  Record t: Type := mk {
    get_modsem: Sk.t -> ModSem.t;
    sk: Sk.t;
  }
  .

  Definition lift (md: t): ModL.t := {|
    ModL.get_modsem := fun sk => md.(get_modsem) sk;
    ModL.sk := md.(sk);
  |}
  .

  Coercion lift: t >-> ModL.t.

  Definition wf (md: t): Prop := <<WF: ModL.wf (lift md)>>.

   Definition add_list (xs: list t): ModL.t :=
     fold_right ModL.add ModL.empty (List.map lift xs)
   .

   Lemma add_list_single: forall (x: t), add_list [x] = x.
   Proof. ii; cbn. rewrite ModL.add_empty_r. refl. Qed.

   Lemma add_list_cons
         x xs
     :
       (add_list (x :: xs)) = (ModL.add x (add_list xs))
   .
   Proof. ss. Qed.

   Lemma add_list_snoc
         x xs
     :
       (add_list (snoc xs x)) = (ModL.add (add_list xs) x)
   .
   Proof.
     ginduction xs; ii; ss.
     { cbn. rewrite ModL.add_empty_l. rewrite ModL.add_empty_r. refl. }
     { cbn. rewrite <- ModL.add_assoc'. f_equal. rewrite <- IHxs. refl. }
   Qed.

   Lemma add_list_app
         xs ys
     :
       add_list (xs ++ ys) = ModL.add (add_list xs) (add_list ys)
   .
   Proof.
     (* unfold add_list. rewrite map_app. rewrite fold_right_app. *)
     ginduction xs; ii; ss.
     - cbn. rewrite ModL.add_empty_l. refl.
     - rewrite ! add_list_cons. rewrite <- ModL.add_assoc'. f_equal. eapply IHxs; ss.
   Qed.

   Lemma add_list_sk (mdl: list t)
     :
       ModL.sk (add_list mdl)
       =
       fold_right Sk.add Sk.unit (List.map sk mdl).
   Proof.
     induction mdl; ss. rewrite <- IHmdl. auto.
   Qed.

   Lemma add_list_initial_mrs (mdl: list t) (ske: Sk.t)
     :
       ModSemL.initial_mrs (ModL.get_modsem (add_list mdl) ske)
       =
       fold_right (@app _) [] (List.map (fun md => ModSemL.initial_mrs (get_modsem md ske)) mdl).
   Proof.
     induction mdl; ss. rewrite <- IHmdl. auto.
   Qed.

   Lemma add_list_fns (mdl: list t) (ske: Sk.t)
     :
       List.map fst (ModSemL.fnsems (ModL.get_modsem (add_list mdl) ske))
       =
       fold_right (@app _) [] (List.map (fun md => List.map fst (ModSemL.fnsems (get_modsem md ske))) mdl).
   Proof.
     induction mdl.
     { auto. }
     transitivity ((List.map fst (ModSemL.fnsems (get_modsem a ske)))++(fold_right (@app _) [] (List.map (fun md => List.map fst (ModSemL.fnsems (get_modsem md ske))) mdl))); auto.
     rewrite <- IHmdl. clear.
     ss. rewrite map_app. auto.
   Qed.

End MOD.
End Mod.

Coercion Mod.lift: Mod.t >-> ModL.t.













Module Equisatisfiability.
  Inductive pred: Type :=
  | true
  | false
  | meta (P: Prop)

  | disj: pred -> pred -> pred
  | conj: pred -> pred -> pred
  | neg: pred -> pred
  | impl: pred -> pred -> pred

  | univ (X: Type): (X -> pred) -> pred
  | exst (X: Type): (X -> pred) -> pred
  .

  (*** https://en.wikipedia.org/wiki/Negation_normal_form ***)
  Fixpoint embed (p: pred): itree eventE unit :=
    match p with
    | true => triggerUB
    | false => triggerNB
    | meta P => guarantee P

    | disj p0 p1 => b <- trigger (Choose _);; if (b: bool) then embed p0 else embed p1
    | conj p0 p1 => b <- trigger (Take _);; if (b: bool) then embed p0 else embed p1
    | neg p =>
      match p with
      | meta P => assume P
      | _ => triggerNB (*** we are assuming negation normal form ***)
      end
    | impl _ _ => triggerNB (*** we are assuming negation normal form ***)

    | @univ X k => x <- trigger (Take X);; embed (k x)
    | @exst X k => x <- trigger (Choose X);; embed (k x)
    end
  .

  (*** TODO: implication --> function call? ***)
  (***
P -> Q
~=
pname :=
  embed P

pqname :=
  (call pname) (finite times);;
  embed Q




(P -> Q) -> R
~=
pname :=
  embed P

pqname :=
  (call pname) (finite times);;
  embed Q

pqrname :=
  (call pqname) (finite times);;
  embed R
   ***)

  (* Fixpoint embed (p: pred) (is_pos: bool): itree eventE unit := *)
  (*   match p with *)
  (*   | true => triggerUB *)
  (*   | false => triggerNB *)
  (*   | meta P => guarantee P *)
  (*   | disj p0 p1 => b <- trigger (Choose _);; if (b: bool) then embed p0 is_pos else embed p1 is_pos *)
  (*   | conj p0 p1 => b <- trigger (Take _);; if (b: bool) then embed p0 is_pos else embed p1 is_pos *)
  (*   | @univ X k => x <- trigger (Take X);; embed (k x) is_pos *)
  (*   | @exst X k => x <- trigger (Choose X);; embed (k x) is_pos *)
  (*   | _ => triggerNB *)
  (*   end *)
  (* . *)
End Equisatisfiability.


Section REFINE.
   Context {BCONF: BehConfig}.
   Definition refines_arg (arg: Any.t) (md_tgt md_src: ModL.t): Prop :=
     (* forall (ctx: list Mod.t), Beh.of_program (ModL.compile (add_list (md_tgt :: ctx))) <1= *)
     (*                           Beh.of_program (ModL.compile (add_list (md_src :: ctx))) *)
     forall (ctx: list Mod.t), Beh.of_program (ModL.compile_arg (ModL.add (Mod.add_list ctx) md_tgt) arg) <1=
                               Beh.of_program (ModL.compile_arg (ModL.add (Mod.add_list ctx) md_src) arg)
   .

   Definition refines_strong (md_tgt md_src: ModL.t): Prop :=
     forall arg, refines_arg arg md_tgt md_src.

   Definition refines (md_tgt md_src: ModL.t): Prop :=
     (* forall (ctx: list Mod.t), Beh.of_program (ModL.compile (add_list (md_tgt :: ctx))) <1= *)
     (*                           Beh.of_program (ModL.compile (add_list (md_src :: ctx))) *)
     forall (ctx: list Mod.t), Beh.of_program (ModL.compile (ModL.add (Mod.add_list ctx) md_tgt)) <1=
                               Beh.of_program (ModL.compile (ModL.add (Mod.add_list ctx) md_src))
   .

   (*** vertical composition ***)
   Global Program Instance refines_PreOrder: PreOrder refines.
   Next Obligation. ii. ss. Qed.
   Next Obligation. ii. eapply H0. eapply H. ss. Qed.

   Global Program Instance refines_arg_PreOrder arg: PreOrder (refines_arg arg).
   Next Obligation. ii. ss. Qed.
   Next Obligation. ii. eapply H0. eapply H. ss. Qed.

   Global Program Instance refines_strong_PreOrder: PreOrder refines_strong.
   Next Obligation. ii. ss. Qed.
   Next Obligation. ii. eapply H0. eapply H. ss. Qed.

   Lemma refines_refines_arg_nil md_tgt md_src
     :
       refines_arg (tt)↑ md_tgt md_src
       <->
       refines md_tgt md_src.
   Proof.
     auto.
   Qed.


   (*** horizontal composition ***)
   Theorem refines_add_arg arg
         (md0_src md0_tgt md1_src md1_tgt: Mod.t)
         (SIM0: refines_arg arg md0_tgt md0_src)
         (SIM1: refines_arg arg md1_tgt md1_src)
     :
       <<SIM: refines_arg arg (ModL.add md0_tgt md1_tgt) (ModL.add md0_src md1_src)>>
   .
   Proof.
     ii. r in SIM0. r in SIM1.
     (***
ctx (a0 b0)
(ctx a0) b0
(ctx a0) b1
      ***)
     rewrite ModL.add_assoc_arg in PR.
     specialize (SIM1 (snoc ctx md0_tgt)). spc SIM1. rewrite Mod.add_list_snoc in SIM1. eapply SIM1 in PR.
     (***
ctx (a0 b1)
(a0 b1) ctx
a0 (b1 ctx)
(b1 ctx) a0
      ***)
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm_arg in PR.
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm_arg in PR.
     (***
(b1 ctx) a1
a1 (b1 ctx)
(a1 b1) ctx
ctx (a1 b1)
      ***)
     specialize (SIM0 (cons md1_src ctx)). spc SIM0. rewrite Mod.add_list_cons in SIM0. eapply SIM0 in PR.
     eapply ModL.add_comm_arg in PR.
     rewrite ModL.add_assoc' in PR.
     eapply ModL.add_comm_arg in PR.
     ss.
   Qed.

   Theorem refines_proper_r_arg arg
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines_arg arg (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines_arg arg (ModL.add (Mod.add_list mds0_tgt) (Mod.add_list ctx)) (ModL.add (Mod.add_list mds0_src) (Mod.add_list ctx))>>
   .
   Proof.
     ii. r in SIM0. rename ctx into xs. rename ctx0 into ys.
     (***
ys + (tgt + xs)
(tgt + xs) + ys
tgt + (xs + ys)
(xs + ys) + tgt
      ***)
     eapply ModL.add_comm_arg in PR.
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm_arg in PR.
     (***
(xs + ys) + src
src + (xs + ys)
(src + xs) + ys
ys + (src + xs)
      ***)
     specialize (SIM0 (xs ++ ys)). spc SIM0. rewrite Mod.add_list_app in SIM0. eapply SIM0 in PR.
     eapply ModL.add_comm_arg in PR.
     rewrite ModL.add_assoc' in PR.
     eapply ModL.add_comm_arg in PR.
     ss.
   Qed.

   Theorem refines_proper_l_arg arg
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines_arg arg (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines_arg arg (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_tgt)) (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_src))>>
   .
   Proof.
     ii. r in SIM0. rename ctx into xs. rename ctx0 into ys.
     (***
ys + (xs + tgt)
(ys + xs) + tgt
(ys + xs) + src
ys + (xs + src)
      ***)
     rewrite ModL.add_assoc' in PR.
     specialize (SIM0 (ys ++ xs)). spc SIM0. rewrite Mod.add_list_app in SIM0. eapply SIM0 in PR.
     rewrite <- ModL.add_assoc' in PR.
     ss.
   Qed.


   (*** horizontal composition ***)
   Theorem refines_add
         (md0_src md0_tgt md1_src md1_tgt: Mod.t)
         (SIM0: refines md0_tgt md0_src)
         (SIM1: refines md1_tgt md1_src)
     :
       <<SIM: refines (ModL.add md0_tgt md1_tgt) (ModL.add md0_src md1_src)>>
   .
   Proof.
     eapply (@refines_add_arg (tt)↑); et.
   Qed.

   Theorem refines_proper_r
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines (ModL.add (Mod.add_list mds0_tgt) (Mod.add_list ctx)) (ModL.add (Mod.add_list mds0_src) (Mod.add_list ctx))>>
   .
   Proof.
     eapply (@refines_proper_r_arg (tt)↑); et.
   Qed.

   Theorem refines_proper_l
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_tgt)) (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_src))>>
   .
   Proof.
     eapply (@refines_proper_l_arg (tt)↑); et.
   Qed.

   (*** horizontal composition ***)
   Theorem refines_strong_add
         (md0_src md0_tgt md1_src md1_tgt: Mod.t)
         (SIM0: refines_strong md0_tgt md0_src)
         (SIM1: refines_strong md1_tgt md1_src)
     :
       <<SIM: refines_strong (ModL.add md0_tgt md1_tgt) (ModL.add md0_src md1_src)>>
   .
   Proof.
     intros arg. eapply (@refines_add_arg arg); et.
   Qed.

   Theorem refines_strong_proper_r
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines_strong (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines_strong (ModL.add (Mod.add_list mds0_tgt) (Mod.add_list ctx)) (ModL.add (Mod.add_list mds0_src) (Mod.add_list ctx))>>
   .
   Proof.
     intros arg. eapply (@refines_proper_r_arg arg); et.
   Qed.

   Theorem refines_strong_proper_l
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines_strong (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines_strong (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_tgt)) (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_src))>>
   .
   Proof.
     intros arg. eapply (@refines_proper_l_arg arg); et.
   Qed.



   Definition refines_closed (md_tgt md_src: ModL.t): Prop :=
     Beh.of_program (ModL.compile md_tgt) <1= Beh.of_program (ModL.compile md_src)
   .

   Global Program Instance refines_closed_PreOrder: PreOrder refines_closed.
   Next Obligation. ii; ss. Qed.
   Next Obligation. ii; ss. r in H. r in H0. eauto. Qed.

   Lemma refines_close: refines <2= refines_closed.
   Proof. ii. specialize (PR nil). ss. unfold Mod.add_list in *. ss. rewrite ! ModL.add_empty_l in PR. eauto. Qed.


   Definition refines_closed_arg arg (md_tgt md_src: ModL.t): Prop :=
     Beh.of_program (ModL.compile_arg md_tgt arg) <1= Beh.of_program (ModL.compile_arg md_src arg)
   .
   Global Program Instance refines_closed_arg_PreOrder arg: PreOrder (refines_closed_arg arg).
   Next Obligation. ii; ss. Qed.
   Next Obligation. ii; ss. r in H. r in H0. eauto. Qed.

   Lemma refines_close_arg arg: refines_arg arg <2= refines_closed_arg arg.
   Proof. ii. specialize (PR nil). ss. unfold Mod.add_list in *. ss. rewrite ! ModL.add_empty_l in PR. eauto. Qed.

   Lemma refines_strong_refines: refines_strong <2= refines.
   Proof. ii. rewrite ModL.compile_compile_arg_nil in *. eapply PR. et. Qed.
End REFINE.

Class gnames := mk_gnames { gnames_contents :> gname -> Prop }.
Coercion gnames_contents: gnames >-> Funclass.

Definition top_gnames := mk_gnames top1.

Class sk_gnames := mk_sk_gnames { sk_gnames_contents :> Sk.t -> gnames }.
Coercion sk_gnames_contents: Sk.t >-> gnames.

Definition top_sk_gnames := mk_sk_gnames (fun _ => top_gnames).
