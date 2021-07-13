Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export ModSemE.
Require Export AList.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Permutation.

Set Implicit Arguments.



Class EMSConfig := { finalize: Any.t -> option Any.t; initial_arg: Any.t }.

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

  Context `{CONF: EMSConfig}.
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
      fn args rv (rvs: Any.t -> Prop) k
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

  Lemma step_trigger_syscall fn args (rvs: Any.t -> Prop) k rv
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

  Context {CONF: EMSConfig}.

  Let add_comm_aux
      ms0 ms1 stl0 str0
      P
      (SIM: stl0 = str0)
    :
      <<COMM: Beh.of_state (compile (add ms0 ms1) P) stl0
              <1=
              Beh.of_state (compile (add ms1 ms0) P) str0>>
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

  Theorem add_comm
          ms0 ms1 (P0 P1: Prop) (IMPL: P1 -> P0)
          (WF: wf (add ms1 ms0))
    :
      <<COMM: Beh.of_program (compile (add ms0 ms1) (Some P0)) <1= Beh.of_program (compile (add ms1 ms0) (Some P1))>>
  .
  Proof.
    destruct (classic (P1)); cycle 1.
    { ii. eapply initial_itr_not_wf; et. }
    replace P0 with P1.
    2: { eapply prop_ext. split; auto. }
    ii. ss. r in PR. r. eapply add_comm_aux; et.
    rp; et. clear PR. ss. cbn. unfold initial_itr. f_equal.
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

  Theorem add_assoc
          ms0 ms1 ms2 P
    :
      <<COMM: Beh.of_program (compile (add ms0 (add ms1 ms2)) P) <1=
              Beh.of_program (compile (add (add ms0 ms1) ms2) P)>>
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
  (* Definition map_fst A0 A1 B (f: A0 -> A1): (A0 * B) -> (A1 * B) := fun '(a, b) => (f a, b). *)
  (* Definition map_snd A B0 B1 (f: B0 -> B1): (A * B0) -> (A * B1) := fun '(a, b) => (a, f b). *)
  (* Definition map_fst A0 A1 B (f: A0 -> A1): (A0 * B) -> (A1 * B) := fun ab => match ab with (a, b) => (f a, b) end. *)
  (* Definition map_snd A B0 B1 (f: B0 -> B1): (A * B0) -> (A * B1) := fun ab => match ab with (a, b) => (a, f b) end. *)

  Definition lift (ms: t): ModSemL.t := {|
    ModSemL.fnsems := List.map (map_snd (fun sem args => transl_all ms.(mn) (sem args))) ms.(fnsems);
    ModSemL.initial_mrs := [(ms.(mn), ms.(initial_st))];
  |}
  .
  Coercion lift: t >-> ModSemL.t.

  Definition wf (ms: t): Prop := ModSemL.wf (lift ms).

  Context {CONF: EMSConfig}.
  Definition compile (ms: t) P: semantics := ModSemL.compile (lift ms) P.

End MODSEM.
End ModSem.

Coercion ModSem.lift: ModSem.t >-> ModSemL.t.




Module ModL.
Section MODL.
  Context `{Sk.ld}.

  Record t: Type := mk {
    get_modsem: Sk.t -> ModSemL.t;
    sk: Sk.t;
    enclose: ModSemL.t := (get_modsem (Sk.canon sk));
  }
  .

  Definition wf (md: t): Prop := (<<WF: ModSemL.wf md.(enclose)>> /\ <<SK: Sk.wf (md.(sk))>>).

  Section BEH.

  Context {CONF: EMSConfig}.

  Definition compile (md: t): semantics :=
    ModSemL.compile_itree (ModSemL.initial_itr md.(enclose) (Some (wf md))).

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

  Theorem add_comm
          md0 md1
    :
      <<COMM: Beh.of_program (compile (add md0 md1)) <1= Beh.of_program (compile (add md1 md0))>>
  .
  Proof.
    ii. unfold compile in *.
    destruct (classic (ModSemL.wf (enclose (add md1 md0)) /\ Sk.wf (sk (add md1 md0)))).
    2: { eapply ModSemL.initial_itr_not_wf. ss. }
    ss. des. assert (SK: Sk.wf (Sk.add (sk md0) (sk md1))).
    { apply Sk.wf_comm. auto. }
    rewrite Sk.add_comm; et.
    eapply ModSemL.add_comm; [| |et].
    { i. split; auto. unfold enclose. ss. rewrite Sk.add_comm; et.
      inv H2. inv H3. econs; ss.
      { rewrite List.map_app in *. eapply nodup_comm; et. }
      { rewrite List.map_app in *. eapply nodup_comm; et. }
    }
    { rewrite Sk.add_comm; et. }
  Qed.

  Lemma add_assoc' ms0 ms1 ms2:
    add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
  Proof.
    unfold add. f_equal.
    { extensionality skenv_link. ss. apply ModSemL.add_assoc'. }
    { ss. rewrite Sk.add_assoc. auto. }
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
    - eapply Sk.add_unit_r.
  Qed.

  Lemma add_empty_l md: add empty md = md.
  Proof.
    destruct md; ss.
    unfold add, ModSemL.add. f_equal; ss.
    { extensionality skenv. destruct (get_modsem0 skenv); ss. }
    { apply Sk.add_unit_l. }
  Qed.

  End BEH.

End MODL.
End ModL.



Module Mod.
Section MOD.
  Context `{Sk.ld}.

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

   Lemma add_list_fnsems (mdl: list t) (ske: Sk.t)
     :
       (ModSemL.fnsems (ModL.get_modsem (add_list mdl) ske))
       =
       fold_right (@app _) [] (List.map (fun md => (ModSemL.fnsems (get_modsem md ske))) mdl).
   Proof.
     induction mdl.
     { auto. }
     transitivity ((ModSemL.fnsems (get_modsem a ske))++(fold_right (@app _) [] (List.map (fun md => ModSemL.fnsems (get_modsem md ske)) mdl))); auto.
     rewrite <- IHmdl. clear. ss.
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
  Context `{Sk.ld}.

   Definition refines {CONF: EMSConfig} (md_tgt md_src: ModL.t): Prop :=
     (* forall (ctx: list Mod.t), Beh.of_program (ModL.compile (add_list (md_tgt :: ctx))) <1= *)
     (*                           Beh.of_program (ModL.compile (add_list (md_src :: ctx))) *)
     forall (ctx: list Mod.t), Beh.of_program (ModL.compile (ModL.add (Mod.add_list ctx) md_tgt)) <1=
                               Beh.of_program (ModL.compile (ModL.add (Mod.add_list ctx) md_src))
   .

   Definition refines_strong (md_tgt md_src: ModL.t): Prop :=
     forall {CONF: EMSConfig}, refines md_tgt md_src.

   Section CONF.
   Context {CONF: EMSConfig}.

   Definition refines2 (md_tgt md_src: list Mod.t): Prop :=
     forall (ctx: list Mod.t), Beh.of_program (ModL.compile (ModL.add (Mod.add_list ctx) (Mod.add_list md_tgt))) <1=
                               Beh.of_program (ModL.compile (ModL.add (Mod.add_list ctx) (Mod.add_list md_src)))
   .

   Global Program Instance refines2_PreOrder: PreOrder refines2.
   Next Obligation.
     ii. ss.
   Qed.
   Next Obligation.
     ii. eapply H0 in PR. eapply H1 in PR. eapply PR.
   Qed.

   (*** vertical composition ***)
   Global Program Instance refines_PreOrder: PreOrder refines.
   Next Obligation. ii. ss. Qed.
   Next Obligation. ii. eapply H1. eapply H0. ss. Qed.

   Global Program Instance refines_strong_PreOrder: PreOrder refines_strong.
   Next Obligation. ii. ss. Qed.
   Next Obligation. ii. eapply H1. eapply H0. ss. Qed.



   (*** horizontal composition ***)
   Theorem refines_add
         (md0_src md0_tgt md1_src md1_tgt: Mod.t)
         (SIM0: refines md0_tgt md0_src)
         (SIM1: refines md1_tgt md1_src)
     :
       <<SIM: refines (ModL.add md0_tgt md1_tgt) (ModL.add md0_src md1_src)>>
   .
   Proof.
     ii. r in SIM0. r in SIM1.
     (***
ctx (a0 b0)
(ctx a0) b0
(ctx a0) b1
      ***)
     rewrite ModL.add_assoc in PR.
     specialize (SIM1 (snoc ctx md0_tgt)). spc SIM1. rewrite Mod.add_list_snoc in SIM1. eapply SIM1 in PR.
     (***
ctx (a0 b1)
(a0 b1) ctx
a0 (b1 ctx)
(b1 ctx) a0
      ***)
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     (***
(b1 ctx) a1
a1 (b1 ctx)
(a1 b1) ctx
ctx (a1 b1)
      ***)
     specialize (SIM0 (cons md1_src ctx)). spc SIM0. rewrite Mod.add_list_cons in SIM0. eapply SIM0 in PR.
     eapply ModL.add_comm in PR.
     rewrite ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     ss.
   Qed.

   Theorem refines_proper_r
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines (ModL.add (Mod.add_list mds0_tgt) (Mod.add_list ctx)) (ModL.add (Mod.add_list mds0_src) (Mod.add_list ctx))>>
   .
   Proof.
     ii. r in SIM0. rename ctx into xs. rename ctx0 into ys.
     (***
ys + (tgt + xs)
(tgt + xs) + ys
tgt + (xs + ys)
(xs + ys) + tgt
      ***)
     eapply ModL.add_comm in PR.
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     (***
(xs + ys) + src
src + (xs + ys)
(src + xs) + ys
ys + (src + xs)
      ***)
     specialize (SIM0 (xs ++ ys)). spc SIM0. rewrite Mod.add_list_app in SIM0. eapply SIM0 in PR.
     eapply ModL.add_comm in PR.
     rewrite ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     ss.
   Qed.

   Theorem refines_proper_l
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_tgt)) (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_src))>>
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

   Definition refines_closed (md_tgt md_src: ModL.t): Prop :=
     Beh.of_program (ModL.compile md_tgt) <1= Beh.of_program (ModL.compile md_src)
   .

   Global Program Instance refines_closed_PreOrder: PreOrder refines_closed.
   Next Obligation. ii; ss. Qed.
   Next Obligation. ii; ss. eapply H1. eapply H0. eauto. Qed.

   Lemma refines_close: refines <2= refines_closed.
   Proof. ii. specialize (PR nil). ss. unfold Mod.add_list in *. ss. rewrite ! ModL.add_empty_l in PR. eauto. Qed.

   (*** horizontal composition ***)
   Theorem refines2_add
         (s0 s1 t0 t1: list Mod.t)
         (SIM0: refines2 t0 s0)
         (SIM1: refines2 t1 s1)
     :
       <<SIM: refines2 (t0 ++ t1) (s0 ++ s1)>>
   .
   Proof.
     ii. r in SIM0. r in SIM1.
     (***
ctx (a0 b0)
(ctx a0) b0
(ctx a0) b1
      ***)
     rewrite Mod.add_list_app in PR.
     rewrite ModL.add_assoc in PR.
     specialize (SIM1 (ctx ++ t0)). spc SIM1. rewrite Mod.add_list_app in SIM1. eapply SIM1 in PR.
     (***
ctx (a0 b1)
(a0 b1) ctx
a0 (b1 ctx)
(b1 ctx) a0
      ***)
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     (***
(b1 ctx) a1
a1 (b1 ctx)
(a1 b1) ctx
ctx (a1 b1)
      ***)
     specialize (SIM0 (s1 ++ ctx)). spc SIM0. rewrite Mod.add_list_app in SIM0. eapply SIM0 in PR.
     eapply ModL.add_comm in PR.
     rewrite ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     rewrite ! Mod.add_list_app in *.
     assumption.
   Qed.


   Corollary refines2_pairwise
             (mds0_src mds0_tgt: list Mod.t)
             (FORALL: List.Forall2 (fun md_src md_tgt => refines2 [md_src] [md_tgt]) mds0_src mds0_tgt)
     :
       refines2 mds0_src mds0_tgt.
   Proof.
     induction FORALL; ss.
     hexploit refines2_add.
     { eapply H0. }
     { eapply IHFORALL. }
     i. ss.
   Qed.

   Lemma refines2_eq (mds0 mds1: list Mod.t)
     :
       refines2 mds0 mds1 <-> refines (Mod.add_list mds0) (Mod.add_list mds1).
   Proof.
     split.
     { ii. eapply H0. auto. }
     { ii. eapply H0. auto. }
   Qed.

   Lemma refines2_app mhd0 mhd1 mtl0 mtl1
         (HD: refines2 mhd0 mhd1)
         (TL: refines2 mtl0 mtl1)
     :
       refines2 (mhd0++mtl0) (mhd1++mtl1).
   Proof.
     eapply refines2_eq. rewrite ! Mod.add_list_app. etrans.
     { eapply refines_proper_l. eapply refines2_eq. et. }
     { eapply refines_proper_r. eapply refines2_eq. et. }
   Qed.

   Lemma refines2_cons mhd0 mhd1 mtl0 mtl1
         (HD: refines2 [mhd0] [mhd1])
         (TL: refines2 mtl0 mtl1)
     :
       refines2 (mhd0::mtl0) (mhd1::mtl1).
   Proof.
     eapply (refines2_app HD TL).
   Qed.

   End CONF.



   (*** horizontal composition ***)
   Theorem refines_strong_add
         (md0_src md0_tgt md1_src md1_tgt: Mod.t)
         (SIM0: refines_strong md0_tgt md0_src)
         (SIM1: refines_strong md1_tgt md1_src)
     :
       <<SIM: refines_strong (ModL.add md0_tgt md1_tgt) (ModL.add md0_src md1_src)>>
   .
   Proof.
     intros CONF. eapply (@refines_add CONF); et.
   Qed.

   Theorem refines_strong_proper_r
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines_strong (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines_strong (ModL.add (Mod.add_list mds0_tgt) (Mod.add_list ctx)) (ModL.add (Mod.add_list mds0_src) (Mod.add_list ctx))>>
   .
   Proof.
     intros CONF. eapply (@refines_proper_r CONF); et.
   Qed.

   Theorem refines_strong_proper_l
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines_strong (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines_strong (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_tgt)) (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_src))>>
   .
   Proof.
     intros CONF. eapply (@refines_proper_l CONF); et.
   Qed.

   Lemma refines_strong_refines {CONF: EMSConfig}: refines_strong <2= refines.
   Proof. ii. eapply PR; et. Qed.
End REFINE.


Global Existing Instance Sk.gdefs.
Arguments Sk.unit: simpl never.
Arguments Sk.add: simpl never.
Arguments Sk.wf: simpl never.
Coercion Sk.load_skenv: Sk.t >-> SkEnv.t.
Global Opaque Sk.load_skenv.


(*** TODO: Move to ModSem.v ***)
Lemma interp_Es_unwrapU
      prog R st0 (r: option R)
  :
    EventsL.interp_Es prog (unwrapU r) st0 = r <- unwrapU r;; Ret (st0, r)
.
Proof.
  unfold unwrapU. des_ifs.
  - rewrite EventsL.interp_Es_ret. grind.
  - rewrite EventsL.interp_Es_triggerUB. unfold triggerUB. grind.
Qed.

Lemma interp_Es_unwrapN
      prog R st0 (r: option R)
  :
    EventsL.interp_Es prog (unwrapN r) st0 = r <- unwrapN r;; Ret (st0, r)
.
Proof.
  unfold unwrapN. des_ifs.
  - rewrite EventsL.interp_Es_ret. grind.
  - rewrite EventsL.interp_Es_triggerNB. unfold triggerNB. grind.
Qed.

Lemma interp_Es_assume
      prog st0 (P: Prop)
  :
    EventsL.interp_Es prog (assume P) st0 = assume P;;; tau;; tau;; Ret (st0, tt)
.
Proof.
  unfold assume.
  repeat (try rewrite EventsL.interp_Es_bind; try rewrite bind_bind). grind.
  rewrite EventsL.interp_Es_eventE.
  repeat (try rewrite EventsL.interp_Es_bind; try rewrite bind_bind). grind.
  rewrite EventsL.interp_Es_ret.
  refl.
Qed.

Lemma interp_Es_guarantee
      prog st0 (P: Prop)
  :
    EventsL.interp_Es prog (guarantee P) st0 = guarantee P;;; tau;; tau;; Ret (st0, tt)
.
Proof.
  unfold guarantee.
  repeat (try rewrite EventsL.interp_Es_bind; try rewrite bind_bind). grind.
  rewrite EventsL.interp_Es_eventE.
  repeat (try rewrite EventsL.interp_Es_bind; try rewrite bind_bind). grind.
  rewrite EventsL.interp_Es_ret.
  refl.
Qed.





Require Import Red IRed.
Section AUX.
  Lemma interp_Es_ext
        prog R (itr0 itr1: itree _ R) st0
    :
      itr0 = itr1 -> EventsL.interp_Es prog itr0 st0 = EventsL.interp_Es prog itr1 st0
  .
  Proof. i; subst; refl. Qed.

  Global Program Instance interp_Es_rdb: red_database (mk_box (@EventsL.interp_Es)) :=
    mk_rdb
      1
      (mk_box EventsL.interp_Es_bind)
      (mk_box EventsL.interp_Es_tau)
      (mk_box EventsL.interp_Es_ret)
      (mk_box EventsL.interp_Es_pE)
      (mk_box EventsL.interp_Es_pE)
      (mk_box EventsL.interp_Es_callE)
      (mk_box EventsL.interp_Es_eventE)
      (mk_box EventsL.interp_Es_triggerUB)
      (mk_box EventsL.interp_Es_triggerNB)
      (mk_box interp_Es_unwrapU)
      (mk_box interp_Es_unwrapN)
      (mk_box interp_Es_assume)
      (mk_box interp_Es_guarantee)
      (mk_box interp_Es_ext)
  .

  Lemma transl_all_unwrapU
        mn R (r: option R)
    :
      transl_all mn (unwrapU r) = unwrapU r
  .
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite transl_all_ret. grind.
    - rewrite transl_all_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma transl_all_unwrapN
        mn R (r: option R)
    :
      transl_all mn (unwrapN r) = unwrapN r
  .
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite transl_all_ret. grind.
    - rewrite transl_all_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma transl_all_assume
        mn (P: Prop)
    :
      transl_all mn (assume P) = assume P;;; tau;; Ret (tt)
  .
  Proof.
    unfold assume.
    repeat (try rewrite transl_all_bind; try rewrite bind_bind). grind.
    rewrite transl_all_eventE.
    repeat (try rewrite transl_all_bind; try rewrite bind_bind). grind.
    rewrite transl_all_ret.
    refl.
  Qed.

  Lemma transl_all_guarantee
        mn (P: Prop)
    :
      transl_all mn (guarantee P) = guarantee P;;; tau;; Ret (tt)
  .
  Proof.
    unfold guarantee.
    repeat (try rewrite transl_all_bind; try rewrite bind_bind). grind.
    rewrite transl_all_eventE.
    repeat (try rewrite transl_all_bind; try rewrite bind_bind). grind.
    rewrite transl_all_ret.
    refl.
  Qed.

  Lemma transl_all_ext
        mn R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      transl_all mn itr0 = transl_all mn itr1
  .
  Proof. subst; refl. Qed.

  Global Program Instance transl_all_rdb: red_database (mk_box (@transl_all)) :=
    mk_rdb
      0
      (mk_box transl_all_bind)
      (mk_box transl_all_tau)
      (mk_box transl_all_ret)
      (mk_box transl_all_pE)
      (mk_box transl_all_pE)
      (mk_box transl_all_callE)
      (mk_box transl_all_eventE)
      (mk_box transl_all_triggerUB)
      (mk_box transl_all_triggerNB)
      (mk_box transl_all_unwrapU)
      (mk_box transl_all_unwrapN)
      (mk_box transl_all_assume)
      (mk_box transl_all_guarantee)
      (mk_box transl_all_ext)
  .
End AUX.
