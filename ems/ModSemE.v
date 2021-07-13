Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Any.

Set Implicit Arguments.


Notation gname := string (only parsing). (*** convention: not capitalized ***)
Notation mname := string (only parsing). (*** convention: capitalized ***)

Section EVENTSCOMMON.

  Variant eventE: Type -> Type :=
  | Choose (X: Type): eventE X
  | Take X: eventE X
  | Syscall (fn: gname) (args: Any.t) (rvs: Any.t -> Prop): eventE Any.t
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

  Definition unleftU {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerUB
    end.

  Definition unleftN {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerNB
    end.

  Definition unrightU {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
    match xy with
    | inl x => triggerUB
    | inr y => Ret y
    end.

  Definition unrightN {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
    match xy with
    | inl x => triggerNB
    | inr y => Ret y
    end.

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
