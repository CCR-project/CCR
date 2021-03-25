Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.




Section EVENTS.

  Variant eventE: Type -> Type :=
  | Choose (X: Type): eventE X
  | Take X: eventE X
  | Syscall (fn: gname) (args: list val): eventE val
  .

  Inductive callE: Type -> Type :=
  | Call (fn: gname) (args: Any.t): callE Any.t
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

  Definition assume {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Take P) ;; Ret tt.
  Definition guarantee {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Choose P) ;; Ret tt.

  (* Notation "'unint?'" := (unwrapA <*> unint) (at level 57, only parsing). *)
  (* Notation "'unint﹗'" := (unwrapG <*> unint) (at level 57, only parsing). *)
  (* Notation "'Ret!' f" := (RetG f) (at level 57, only parsing). *)
  (* Notation "'Ret?' f" := (RetA f) (at level 57, only parsing). *)

  Context `{Σ: GRA.t}.

  Inductive pE: Type -> Type :=
  | PPut (mn: mname) (p: Any.t): pE unit
  | PGet (mn: mname): pE Any.t
  .

  Inductive rE: Type -> Type :=
  (* | MPut (mn: mname) (r: GRA): rE unit *)
  (* | MGet (mn: mname): rE GRA *)
  (* | FPut (r: GRA): rE unit *)
  (* | FGet: rE GRA *)
  | MPut (mn: mname) (mr: Σ): rE unit
  | FPut (fr: Σ): rE unit
  | MGet (mn: mname): rE Σ
  | FGet: rE Σ
  (* | Get (mn: mname): rE (GRA * GRA) *)

  | PushFrame: rE unit
  | PopFrame: rE unit
  .

  Definition put E `{rE -< E} `{eventE -< E} (mn: mname) (mr1: Σ) (fr1: Σ): itree E unit :=
    mr0 <- trigger (MGet mn);; fr0 <- trigger FGet;;
    guarantee(URA.updatable (URA.add mr0 fr0) (URA.add mr1 fr1));;
    trigger (FPut fr1);; trigger (MPut mn mr1)
  .

  Definition forge E `{rE -< E} `{eventE -< E} (delta: Σ): itree E unit :=
    fr0 <- trigger FGet;;
    trigger (FPut (URA.add fr0 delta))
  .

  Definition discard E `{rE -< E} `{eventE -< E} (fr1: Σ): itree E unit :=
    fr0 <- trigger FGet;;
    rest <- trigger (Choose _);;
    guarantee(fr0 = URA.add fr1 rest);;
    trigger (FPut rest)
  .

  Definition checkWf E `{rE -< E} `{eventE -< E} (mn: mname): itree E unit :=
    mr0 <- trigger (MGet mn);; fr0 <- trigger FGet;;
    assume(URA.wf (URA.add mr0 fr0))
  .

  (*** TODO: we don't want to require "mname" here ***)
  (*** use dummy mname? ***)
  (* Definition FPut E `{rE -< E} (mn: mname) (fr: GRA): itree E unit := *)

  Definition Es: Type -> Type := (callE +' rE +' pE+' eventE).

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
  Definition r_state: Type := ((mname -> Σ) * list Σ).
  Definition handle_rE `{eventE -< E}: rE ~> stateT r_state (itree E) :=
    fun _ e '(mrs, frs) =>
      match frs with
      | hd :: tl =>
        match e with
        (* | Put mn mr fr => Ret (((update mrs mn mr), fr :: tl), tt) *)
        | MPut mn mr => Ret (((update mrs mn mr), hd :: tl), tt)
        | FPut fr => Ret ((mrs, fr :: tl), tt)
        | MGet mn => Ret ((mrs, frs), mrs mn)
        | FGet => Ret ((mrs, frs), hd)
        | PushFrame =>
          Ret ((mrs, ε :: frs), tt)
        | PopFrame =>
          Ret ((mrs, tl), tt)
        end
      | _ => triggerNB
      end.

  (*** Same as State.pure_state, but does not use "Vis" directly ***)
  Definition pure_state {S E}: E ~> stateT S (itree E) := fun _ e s => x <- trigger e;; Ret (s, x).

  (* Definition compose2 A B C R: (C -> R) -> (A -> B -> C) -> A -> B -> R := fun f g a b => f (g a b). *)
  Definition interp_rE `{eventE -< E}: itree (rE +' E) ~> stateT r_state (itree E) :=
    State.interp_state (case_ handle_rE pure_state).
    (* State.interp_state (case_ ((fun _ e s0 => resum_itr (handle_rE e s0)): _ ~> stateT _ _) State.pure_state). *)
    (* State.interp_state (case_ ((fun _ => compose2 (@resum_itr _ _ _ _) (@handle_rE _)): rE ~> stateT r_state (itree E)) State.pure_state). *)

  Definition p_state: Type := (mname -> Any.t).
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
  Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (st0: r_state * p_state): itree eventE ((r_state * p_state) * _)%type :=
    let (rst0, pst0) := st0 in
    '(pst1, (rst1, v)) <- interp_pE (interp_rE (interp_mrec prog itr0) rst0) pst0;;
    Ret ((rst1, pst1), v)
  .



  Lemma interp_Es_bind
        (prog: callE ~> itree Es)
        A B
        (itr: itree Es A) (ktr: A -> itree Es B)
        st0
    :
      interp_Es prog (v <- itr ;; ktr v) st0 =
      '(st1, v) <- interp_Es prog (itr) st0 ;; interp_Es prog (ktr v) st1
  .
  Proof. unfold interp_Es, interp_rE, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_tau
        (prog: callE ~> itree Es)
        A
        (itr: itree Es A)
        st0
    :
      interp_Es prog (tau;; itr) st0 = tau;; interp_Es prog itr st0
  .
  Proof. unfold interp_Es, interp_rE, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_ret
        T
        prog st0 (v: T)
    :
      interp_Es prog (Ret v) st0 = Ret (st0, v)
  .
  Proof. unfold interp_Es, interp_rE, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_callE
        p st0
        (* (e: Es Σ) *)
        (e: callE Any.t)
    :
      interp_Es p (trigger e) st0 = tau;; (interp_Es p (p _ e) st0)
  .
  Proof. unfold interp_Es, interp_rE, interp_pE. des_ifs. grind. Qed.

  Lemma unfold_interp_state: forall {E F} {S R} (h: E ~> stateT S (itree F)) (t: itree E R) (s: S),
      interp_state h t s = _interp_state h (observe t) s.
  Proof. i. f. apply unfold_interp_state. Qed.

  Lemma interp_Es_rE
        p rst0 pst0
        (* (e: Es Σ) *)
        T
        (e: rE T)
    :
      interp_Es p (trigger e) (rst0, pst0) =
      '(rst1, r) <- handle_rE e rst0;;
      tau;; tau;;
      Ret ((rst1, pst0), r)
  .
  Proof.
    unfold interp_Es, interp_rE, interp_pE. grind.
    destruct rst0; ss. unfold triggerNB, pure_state. destruct e; ss; des_ifs; grind.
  Qed.

  Lemma interp_Es_pE
        p rst0 pst0
        (* (e: Es Σ) *)
        T
        (e: pE T)
    :
      interp_Es p (trigger e) (rst0, pst0) =
      '(pst1, r) <- handle_pE e pst0;;
      tau;; tau;; tau;;
      Ret ((rst0, pst1), r)
  .
  Proof.
    unfold interp_Es, interp_rE, interp_pE. grind.
    (* Ltac grind := repeat (ired; f; repeat (f_equiv; ii; des_ifs_safe); f). *)
    destruct rst0; ss. unfold triggerNB, pure_state. destruct e; ss; des_ifs; grind.
  Qed.

  Lemma interp_Es_eventE
        p st0
        (* (e: Es Σ) *)
        T
        (e: eventE T)
    :
      interp_Es p (trigger e) st0 = r <- trigger e;; tau;; tau;; tau;; Ret (st0, r)
  .
  Proof.
    unfold interp_Es, interp_rE, interp_pE. grind.
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
    unfold interp_Es, interp_rE, interp_pE, pure_state, triggerUB. grind.
  Qed.

  Lemma interp_Es_triggerNB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (interp_Es prog (triggerNB) st0: itree eventE (_ * A)) = triggerNB
  .
  Proof.
    unfold interp_Es, interp_rE, interp_pE, pure_state, triggerNB. grind.
  Qed.

End EVENTS.

Notation "f '?'" := (unwrapU f) (at level 9, only parsing).
Notation "f 'ǃ'" := (unwrapN f) (at level 9, only parsing).
Notation "(?)" := (unwrapU) (only parsing).
Notation "(ǃ)" := (unwrapN) (only parsing).
Goal (tt ↑↓?) = Ret tt. rewrite Any.upcast_downcast. ss. Qed.
Goal (tt ↑↓ǃ) = Ret tt. rewrite Any.upcast_downcast. ss. Qed.





Section AUX.

  Context `{Σ: GRA.t}.
(*** casting call, fun ***)
(* Definition ccallN {X Y} (fn: gname) (varg: X): itree Es Y := vret <- trigger (Call fn varg↑);; vret <- vret↓ǃ;; Ret vret. *)
(* Definition ccallU {X Y} (fn: gname) (varg: X): itree Es Y := vret <- trigger (Call fn varg↑);; vret <- vret↓?;; Ret vret. *)
(* Definition cfunN {X Y} (body: X -> itree Es Y): Any.t -> itree Es Any.t := *)
(*   fun varg => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑. *)
(* Definition cfunU {X Y} (body: X -> itree Es Y): Any.t -> itree Es Any.t := *)
(*   fun varg => varg <- varg↓?;; vret <- body varg;; Ret vret↑. *)
Definition ccall {X Y} (fn: gname) (varg: X): itree Es Y := vret <- trigger (Call fn varg↑);; vret <- vret↓ǃ;; Ret vret.
Definition cfun {X Y} (body: X -> itree Es Y): Any.t -> itree Es Any.t :=
  fun varg => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑.

End AUX.





Module ModSem.
Section MODSEM.

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

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    (* initial_ld: mname -> GRA; *)
    fnsems: list (gname * (Any.t -> itree Es Any.t));
    initial_mrs: list (mname * (Σ * Any.t));
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
    fun _ '(Call fn args) =>
      '(_, sem) <- (List.find (fun fnsem => dec fn (fst fnsem)) ms.(fnsems))?;;
      trigger PushFrame;;
      rv <- (sem args);;
      trigger PopFrame;;
      Ret rv
  .



  Definition initial_r_state: r_state :=
    (fun mn => match List.find (fun mnr => dec mn (fst mnr)) ms.(initial_mrs) with
               | Some r => fst (snd r)
               | None => ε
               end, [ε]). (*** we have a dummy-stack here ***)
  Definition initial_p_state: p_state :=
    (fun mn => match List.find (fun mnr => dec mn (fst mnr)) ms.(initial_mrs) with
               | Some r => (snd (snd r))
               | None => tt↑
               end).
  Definition initial_itr: itree (eventE) Any.t :=
    assume(<<WF: wf ms>>);;
    snd <$> interp_Es prog (prog (Call "main" (([]: list val)↑))) (initial_r_state, initial_p_state).

  Definition initial_itr_no_check: itree (eventE) Any.t :=
    snd <$> interp_Es prog (prog (Call "main" (([]: list val)↑))) (initial_r_state, initial_p_state).


  Let state: Type := itree eventE Any.t.

  Definition state_sort (st0: state): sort :=
    match (observe st0) with
    | TauF _ => demonic
    | RetF rv =>
      match rv↓ with
      | Some (Vint rv) => final rv
      | _ => angelic
      end
    | VisF (Choose X) k => demonic
    | VisF (Take X) k => angelic
    | VisF (Syscall fn args) k => vis
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
      (* fn args k ev rv *)
      (* (SYSCALL: syscall_sem fn args = (ev, rv)) *)
      fn args rv k
      (SYSCALL: syscall_sem (event_sys fn args rv))
    :
      step (Vis (subevent _ (Syscall fn args)) k) (Some (event_sys fn args rv)) (k rv)
  .

  Program Definition interp: semantics := {|
    STS.state := state;
    STS.step := step;
    STS.initial_state := initial_itr;
    STS.state_sort := state_sort;
  |}
  .
  Next Obligation. inv STEP; inv STEP0; ss. csc. Qed.
  (* Next Obligation. inv STEP; inv STEP0; ss. csc. rewrite SYSCALL in *. csc. Qed. *)
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.

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

  (*** TODO: probably we can make ModSem.t as an RA too. (together with Sk.t) ***)
  (*** However, I am not sure what would be the gain; and there might be universe problem. ***)

  Let add_comm_aux
      ms0 ms1 stl0 str0
      (SIM: stl0 = str0)
    :
      <<COMM: Beh.of_state (interp (add ms0 ms1)) stl0 <1= Beh.of_state (interp (add ms1 ms0)) str0>>
  .
  Proof.
    revert_until ms1.
    pcofix CIH. i. pfold.
    clarify.
    punfold PR. induction PR using Beh.of_state_ind; ss.
    - econs 1; et.
    - econs 2; et.
      clear CIH. clear_tac. revert_until ms1.
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
    r. eapply prop_ext. split; i.
    - admit "ez".
    - admit "ez".
  Qed.

  Theorem add_comm
          ms0 ms1
          (* (WF: wf (add ms0 ms1)) *)
    :
      <<COMM: Beh.of_program (interp (add ms0 ms1)) <1= Beh.of_program (interp (add ms1 ms0))>>
  .
  Proof.
    destruct (classic (wf (add ms1 ms0))); cycle 1.
    { ii. clear PR. eapply Beh.ub_top. pfold. econsr; ss; et. rr. ii; ss. unfold initial_itr, assume in *.
      inv STEP; ss; irw in H1; (* clarify <- TODO: BUG, runs infloop. *) inv H1; simpl_depind; subst.
      clarify.
    }
    rename H into WF.
    (* ii. ss. r in PR. r. eapply add_comm_aux; et. *)
    (* rp; et. clear PR. cbn. do 1 f_equal; cycle 1. *)
    (* { unfold assume. rewrite wf_comm. ss. } *)
    (* apply func_ext; ii. *)
    (* f_equiv. *)
    (* f_equal; cycle 1. *)
    (* - unfold initial_r_state. f_equal. apply func_ext. intros fn. ss. des_ifs. *)
    (*   + admit "ez: wf". *)
    (*   + admit "ez: wf". *)
    (*   + admit "ez: wf". *)
    (* - repeat f_equal. apply func_ext_dep. intro T. apply func_ext. intro c. destruct c. *)
    (*   repeat f_equal. apply func_ext. i. f_equal. ss. do 2 f_equal. *)
    (*   admit "ez: wf". *)
    admit "TODO".
  Qed.

  Lemma add_assoc' ms0 ms1 ms2:
    add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
  Proof.
    induction ms2; ss. unfold add. f_equal; ss.
    { eapply app_assoc. }
    { eapply app_assoc. }
  Qed.

  Theorem add_assoc
          ms0 ms1 ms2
          (WF: wf (add ms0 (add ms1 ms2)))
    :
      <<COMM: Beh.of_program (interp (add ms0 (add ms1 ms2))) <1=
              Beh.of_program (interp (add (add ms0 ms1) ms2))>>
  .
  Proof.
    admit "TODO".
  Qed.

  Theorem add_assoc_rev
          ms0 ms1 ms2
          (WF: wf (add ms0 (add ms1 ms2)))
    :
      <<COMM: Beh.of_program (interp (add ms0 (add ms1 ms2))) <1=
              Beh.of_program (interp (add (add ms0 ms1) ms2))>>
  .
  Proof.
    admit "TODO".
  Qed.

End MODSEM.
End ModSem.



Module Mod.
Section MOD.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    get_modsem: SkEnv.t -> ModSem.t;
    sk: Sk.t;
    enclose: ModSem.t := (get_modsem (Sk.load_skenv sk));
    interp: semantics := ModSem.interp enclose;
  }
  .

  (* Record wf (md: t): Prop := mk_wf { *)
  (*   wf_sk: Sk.wf md.(sk); *)
  (* } *)
  (* . *)
  Definition wf (md: t): Prop := <<WF: Sk.wf md.(sk)>>.
  (*** wf about modsem is enforced in the semantics ***)

  Definition add (md0 md1: t): t := {|
    get_modsem := fun skenv_link =>
                    ModSem.add (md0.(get_modsem) skenv_link) (md1.(get_modsem) skenv_link);
    sk := Sk.add md0.(sk) md1.(sk);
  |}
  .

  Theorem add_comm
          md0 md1
    :
      <<COMM: Beh.of_program (interp (add md0 md1)) <1= Beh.of_program (interp (add md1 md0))>>
  .
  Proof.
    ii.
    unfold interp in *. ss.
    eapply ModSem.add_comm; et.
    rp; et. do 4 f_equal.
    - admit "TODO: maybe the easy way is to 'canonicalize' the list by sorting.".
    - admit "TODO: maybe the easy way is to 'canonicalize' the list by sorting.".
  Qed.

  Lemma add_assoc' ms0 ms1 ms2:
    add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
  Proof.
    unfold add. f_equal.
    { extensionality skenv_link. ss. apply ModSem.add_assoc'. }
    { eapply app_assoc. }
  Qed.

  Theorem add_assoc
          md0 md1 md2
    :
      <<COMM: Beh.of_program (interp (add md0 (add md1 md2))) =
              Beh.of_program (interp (add (add md0 md1) md2))>>
  .
  Proof.
    admit "ez".
  Qed.

  Definition empty: t := {|
    get_modsem := fun _ => ModSem.mk [] [];
    sk := Sk.unit;
  |}
  .

  Lemma add_empty_r md: add md empty = md.
  Proof.
    destruct md; ss.
    unfold add, ModSem.add. f_equal; ss.
    - extensionality skenv. destruct (get_modsem0 skenv); ss.
      repeat rewrite app_nil_r. auto.
    - unfold Sk.add. rewrite app_nil_r. auto.
  Qed.

  Lemma add_empty_l md: add empty md = md.
  Proof.
    destruct md; ss.
    unfold add, ModSem.add. f_equal; ss.
    extensionality skenv. destruct (get_modsem0 skenv); ss.
  Qed.

  Fixpoint add_list (mds: list t): t :=
    match mds with
    | hd::tl => add hd (add_list tl)
    | [] => empty
    end.

End MOD.
End Mod.


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
