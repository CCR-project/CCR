Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.

Set Implicit Arguments.

(** 
Any state st & given step relation step (transition system)
st0 -(step A)-> st1/st2/st3/...
->
itree trigger Choose {states which satisfy (st0 -(step A)->) | all state}

f(st0) = Vis (Choose X) (cont: f(st1/st2/st3/...))

interp: ModSem.t -> semantics
semantics -> ModSem.t
 **)

Section CONV.

(**

function f (sm: semantics) (st0: semantics.state) 
: itree Es Any.t :=
stepA <- trigger (Choose sm.step);;
_ <- trigger (stepA st0);;
st1 <- trigger (Choose {states st' that satisfy (st0 -(stepA)-> st') | sm.state});;
f sm st1

 **)

  Context `{Σ: GRA.t}.
  CoFixpoint interpSTS
             (state: Type)
             (step: state -> option event -> state -> Prop)
             (state_sort: state -> sort):
    state -> itree eventE Any.t :=
    fun st0 =>
      match (state_sort st0) with
      | angelic =>
        Vis (Take {st': state | @step st0 None st' })
            (fun st1 => interpSTS step state_sort (proj1_sig st1))
      | demonic =>
        Vis (Choose {st': state | @step st0 None st' })
            (fun st1 => interpSTS step state_sort (proj1_sig st1))
      | final z =>
        Ret z↑
      | vis =>
        '(exist _ (event_sys fn args) _) <-
        trigger (Choose {ev': event | exists st', @step st0 (Some ev') st' });;
        v <- trigger (Syscall fn args);;
        Vis (Choose {st': state | @step st0 (Some (event_sys fn args)) st' })
            (fun st1 => interpSTS step state_sort (proj1_sig st1))
      end
  .

  Lemma observe_eta E R (itr0 itr1: itree E R)
        (EQ: _observe itr0 = _observe itr1)
    :
      itr0 = itr1.
  Proof.
    erewrite (itree_eta_ itr0).
    erewrite (itree_eta_ itr1).
    f_equal. auto.
  Qed.

  Lemma interpSTS_red
        (state: Type)
        (step: state -> option event -> state -> Prop)
        (state_sort: state -> sort)
        (st0: state):
    interpSTS step state_sort st0
    =
    match (state_sort st0) with
    | angelic =>
      Vis (Take {st': state | @step st0 None st' })
          (fun st1 => interpSTS step state_sort (proj1_sig st1))
    | demonic =>
      Vis (Choose {st': state | @step st0 None st' })
          (fun st1 => interpSTS step state_sort (proj1_sig st1))
    | final z =>
      Ret z↑
    | vis =>
      '(exist _ (event_sys fn args) _) <-
      trigger (Choose {ev': event | exists st', @step st0 (Some ev') st' });;
      v <- trigger (Syscall fn args);;
      Vis (Choose {st': state | @step st0 (Some (event_sys fn args)) st' })
          (fun st1 => interpSTS step state_sort (proj1_sig st1))
    end
  .
  Proof.
    eapply observe_eta. reflexivity.
  Qed.

  (* Set Primitive Projections.  *)
  
  (* Lemma interpSTS_final: *)
  (*   forall state step state_sort (st1 : state) retv, *)
  (*     (state_sort st1 = final retv) -> *)
  (*     (interpSTS step state_sort st1) = Ret retv↑. *)
  (* Proof. *)
  (*   intros. erewrite interpSTS_red. rewrite H. reflexivity. *)
  (* Qed. *)

End CONV.

Section INV.

  Import ModSem.ModSem.
  
  Program Definition interpITree:
    (itree eventE Any.t) -> semantics :=
    fun itr =>
      {|
        STS.state := (itree eventE Any.t);
        STS.step := step;
        STS.initial_state := itr;
        STS.state_sort := state_sort;
      |}
  .
  Next Obligation. inv STEP; inv STEP0; ss. csc. rewrite SYSCALL in *. csc. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.

End INV.

Section PROOF.

  Import Behavior.Beh.

  Variable
    (state: Type)
    (step: state -> option event -> state -> Prop)
    (state_sort: state -> sort).

  Hypothesis wf_vis :
    forall (st0 : state) (ev0 ev1 : option event) (st1 st2 : state),
      state_sort st0 = vis ->
      step st0 ev0 st1 -> step st0 ev1 st2 -> ev0 = ev1 /\ st1 = st2.

  Hypothesis wf_angelic :
    forall (st0 : state) (ev : option event) (st1 : state),
      state_sort st0 = angelic -> step st0 ev st1 -> ev = None.

  Hypothesis wf_demonic :
    forall (st0 : state) (ev : option event) (st1 : state),
      state_sort st0 = demonic -> step st0 ev st1 -> ev = None.
  
  Theorem beh_preserved:
    forall (st0: state) (tr: Tr.t),
      of_state
        {|
          STS.state := state;
          STS.step := step;
          STS.initial_state := st0;
          STS.state_sort := state_sort;
          STS.wf_vis := wf_vis;
          STS.wf_angelic := wf_angelic;
          STS.wf_demonic := wf_demonic;
        |}
        st0
        tr
      ->
      of_state
        (interpITree (interpSTS step state_sort st0))
        (initial_state (interpITree (interpSTS step state_sort st0)))
        tr.
  Proof.
    intros st0. pcofix CIH. i. punfold H0.
    induction H0 using of_state_ind; ss; clarify.
    - pfold. econs. ss.
      erewrite interpSTS_red. rewrite H.
      unfold ModSem.state_sort. ss.
      (** type mismatch:
          ModSem.state_sort assumes return type = val,
          but
          state of 'final' sort returns only Z. *)
      admit "TODO: fix the return type".
    - pfold. econs. clear CIH.
      (* revert st1 H.  *)
      pcofix CIH. punfold H. ss. inv H.
      + pfold. econs 1.
        * ss. erewrite interpSTS_red. rewrite SRT. ss.
        * i. ss. rewrite interpSTS_red in STEP0. rewrite SRT in STEP0.
          dependent destruction STEP0. destruct x as [st2 STEP0].
          right. admit "paco bug".
      + pfold. econs 2.
          

      

    Abort.
  (* paco gf r = gfp (fun x => r \/ gf (paco gf r)) *)
   
  (* Theorem beh_preserved: *)
  (*   forall (sm: semantics) (st0: state sm) (tr: Tr.t), *)
  (*     of_state *)
  (*       sm *)
  (*       st0 tr *)
  (*     -> *)
  (*     of_state *)
  (*       (interpITree (interpSTS (step sm) (state_sort sm) st0)) *)
  (*       st0 tr. *)
                      


End PROOF.
