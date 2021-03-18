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
  
  (* Let state: Type := itree eventE Any.t. *)
  
  (* Inductive step: state -> option event -> state -> Prop := *)
  (* | step_tau *)
  (*     itr *)
  (*   : *)
  (*     step (Tau itr) None itr *)
  (* | step_choose *)
  (*     X k (x: X) *)
  (*   : *)
  (*     step (Vis (Choose X) k) None (k x) *)
  (* | step_take *)
  (*     X k (x: X) *)
  (*   : *)
  (*     step (Vis (Take X) k) None (k x) *)
  (* | step_syscall *)
  (*     fn args k ev rv *)
  (*     (SYSCALL: syscall_sem fn args = (ev, rv)) *)
  (*   : *)
  (*     step (Vis (Syscall fn args) k) (Some ev) (k rv) *)
  (* . *)
  
  Program Definition interpITree:
    (itree eventE Any.t) -> semantics :=
    fun itr =>
      {|
        STS.state := itree eventE Any.t;
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

(**
of_state = 
fun L : semantics => paco2 (_of_state L) bot2
     : forall L : semantics, STS.state L -> Tr.t -> Prop

paco2 has 'fixed' semantics -> needs fixed semantics to do pcofix
So, fix semantics with st_init, later let st_init = st0 in the main thm.
 **)
  Theorem beh_preserved st_init :
    forall (st0: state) (tr: Tr.t),
      of_state
        {|
          STS.state := state;
          STS.step := step;
          STS.initial_state := st_init;
          STS.state_sort := state_sort;
          STS.wf_vis := wf_vis;
          STS.wf_angelic := wf_angelic;
          STS.wf_demonic := wf_demonic;
        |}
        st0
        tr
      ->
      of_state
        (interpITree (interpSTS step state_sort st_init))
        (initial_state (interpITree (interpSTS step state_sort st0)))
        tr.
  Proof.
    revert_until st_init.
    pcofix CIH.
    i. punfold H0.
    induction H0 using of_state_ind; ss; clarify.
    - pfold. econs. ss.
      erewrite interpSTS_red. rewrite H.
      unfold ModSem.state_sort. ss.
      (** type mismatch:
          ModSem.state_sort assumes return type = val,
          but
          state of 'final' sort returns only Z. *)
      admit "TODO: fix the return type".
    - pfold. econs. clear CIH r.
      revert_until wf_demonic.
      pcofix CIH. i. punfold H0. inv H0.
      + pfold. econs 1.
        * ss. erewrite interpSTS_red. rewrite SRT. ss.
        * i. ss. rewrite interpSTS_red in STEP0. rewrite SRT in STEP0.
          (* inv STEP0. *)
          dependent destruction STEP0. destruct x as [st1 STEP0].
          remember STEP0 as ST. clear HeqST.
          apply STEP in STEP0. destruct STEP0; clarify.
          right. apply CIH. apply H.
      + pfold. econs 2.
        * ss. erewrite interpSTS_red. rewrite SRT. ss.
        * ss. des. destruct TL.
          { exists None. do 2 eexists.
            2:{ right. apply CIH. apply H. }
            rewrite interpSTS_red in *; rewrite SRT in *.
            remember STEP0 as ST. clear HeqST.
            apply (wf_demonic SRT) in STEP0. clarify.
            (* apply (step_choose (fun st2 : {st' : state | step st0 None st'} => interpSTS step state_sort (st2 $)) (exist _ st1 ST)). } *)
            apply (ModSem.step_choose (fun st2 : {st' : state | step st0 None st'} => interpSTS step state_sort (st2 $)) (exist _ st1 ST)). }
          { clarify. }
    - pfold. econs.
    - pfold. econs. ss.
      rewrite interpSTS_red. rewrite SRT.
      unfold ModSem.state_sort.
      
      destruct TL; clarify.
      
            
          
          

      

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
