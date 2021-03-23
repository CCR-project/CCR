Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import SimSTS.

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
        '(exist _ ((event_sys fn args, st1)) _) <-
        trigger (Choose {'(ev', st'): event * state | @step st0 (Some ev') st' });;
        Vis (Syscall fn args) (fun _ => interpSTS step state_sort st1)
        (* '(exist _ (event_sys fn args) _) <- *)
        (* trigger (Choose {ev': event | exists st', @step st0 (Some ev') st' });; *)
        (* v <- trigger (Syscall fn args);; *)
        (* Vis (Choose {st': state | @step st0 (Some (event_sys fn args)) st' }) *)
        (*     (fun st1 => interpSTS step state_sort (proj1_sig st1)) *)
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
      '(exist _ ((event_sys fn args, st1)) _) <-
      trigger (Choose {'(ev', st'): event * state | @step st0 (Some ev') st' });;
      Vis (Syscall fn args) (fun _ => interpSTS step state_sort st1)
    end
  .
  Proof.
    eapply observe_eta. reflexivity.
  Qed.

  (* Set Primitive Projections.  *)

End CONV.

Section INV.

  Import ModSem.ModSem.

  Let state: Type := itree eventE Any.t.

  Definition itr_state_sort (st0: state): sort :=
    match (observe st0) with
    | TauF _ => demonic
    | RetF rv =>
      match rv↓ with
      | Some z => final z
      | _ => angelic
      end
    | VisF (Choose X) k => demonic
    | VisF (Take X) k => angelic
    | VisF (Syscall fn args) k => vis
    end
  .
  
  Program Definition interpITree:
    (itree eventE Any.t) -> semantics :=
    fun itr =>
      {|
        STS.state := itree eventE Any.t;
        STS.step := step;
        STS.initial_state := itr;
        STS.state_sort := itr_state_sort;
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
  Theorem beh_preserved_inv st_init :
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
    intros st0. eapply adequacy_aux with (i0:=10).
    { apply Nat.lt_wf_0. }
    revert st0.
    pcofix CIH. i. pfold.
    destruct (state_sort st0) eqn:SRT.
    - eapply sim_angelic_both; ss; clarify.
      + rewrite interpSTS_red. rewrite SRT. ss.
      + i. rewrite interpSTS_red in STEP. rewrite SRT in STEP.
        dependent destruction STEP. destruct x.
        exists x. exists s. exists 10. right. apply CIH.
    - eapply sim_demonic_both; ss; clarify.
      + rewrite interpSTS_red. rewrite SRT. ss.
      + i. exists (interpSTS step state_sort st_tgt1).
        eexists.
        { rewrite interpSTS_red in *. rewrite SRT in *.
          apply (ModSem.step_choose (fun st1 : {st' : state | step st0 None st'} => interpSTS step state_sort (st1 $)) (exist _ st_tgt1 STEP)). }
        exists 10. right. apply CIH.
    - econs; ss.
      + rewrite interpSTS_red. rewrite SRT.
        unfold itr_state_sort. ss.
        rewrite Any.upcast_downcast. reflexivity.
        (* ModSem.state_sort do not match type (Z, val) *)
      + auto.
    - assert (CASE: (forall ev st1, not (step st0 (Some ev) st1)) \/ (exists ev st1, (step st0 (Some ev) st1))).
      { destruct (classic (exists ev st1, step st0 (Some ev) st1)); eauto.
        left. ii. apply H. eauto. }
      destruct CASE.
      + eapply sim_vis_stuck_tgt; eauto.
      + set (cont :=
               (fun x_ : {'(ev', st') : event * state | step st0 (Some ev') st'}
                => let (x, _) := x_ in
                  let (y0, st1) := x in
                  match y0 with
                  | event_sys fn args =>
                    Vis (Syscall fn args) (fun _ : val => interpSTS step state_sort st1)
                  end)).
        des.
        eapply sim_demonic_src; ss; clarify.
        * rewrite interpSTS_red. rewrite SRT. ss.
        * exists (cont (exist (fun '(ev, st) => step st0 (Some ev) st) (ev, st1) H)).
          eexists.
          { rewrite interpSTS_red. rewrite SRT. rewrite bind_trigger.
            eapply (ModSem.step_choose cont). }
          exists 9. split; auto.
          left. pfold. destruct ev. eapply sim_vis; eauto.
          ss. eapply ModSem.step_syscall with (k := (fun _ : val => interpSTS step state_sort st1)) (ev := event_sys fn args).
          admit "TODO: syscall_sem is an axiom".
  Admitted.
  

         (** ver. behavior proof **) 
    (* revert_until st_init. *)
    (* pcofix CIH. *)
    (* i. punfold H0. *)
    (* induction H0 using of_state_ind; ss; clarify. *)
    (* - pfold. econs. ss. *)
    (*   erewrite interpSTS_red. rewrite H. *)
    (*   unfold ModSem.state_sort. ss. *)
    (*   (** type mismatch: *)
    (*       ModSem.state_sort assumes return type = val, *)
    (*       but *)
    (*       state of 'final' sort returns only Z. *) *)
    (*   admit "TODO: fix the return type". *)
    (* - pfold. econs. clear CIH r. *)
    (*   revert_until wf_demonic. *)
    (*   pcofix CIH. i. punfold H0. inv H0. *)
    (*   + pfold. econs 1. *)
    (*     * ss. erewrite interpSTS_red. rewrite SRT. ss. *)
    (*     * i. ss. rewrite interpSTS_red in STEP0. rewrite SRT in STEP0. *)
    (*       (* inv STEP0. *) *)
    (*       dependent destruction STEP0. destruct x as [st1 STEP0]. *)
    (*       remember STEP0 as ST. clear HeqST. *)
    (*       apply STEP in STEP0. destruct STEP0; clarify. *)
    (*       right. apply CIH. apply H. *)
    (*   + pfold. econs 2. *)
    (*     * ss. erewrite interpSTS_red. rewrite SRT. ss. *)
    (*     * ss. des. destruct TL. *)
    (*       { exists None. do 2 eexists. *)
    (*         2:{ right. apply CIH. apply H. } *)
    (*         rewrite interpSTS_red in *; rewrite SRT in *. *)
    (*         remember STEP0 as ST. clear HeqST. *)
    (*         apply (wf_demonic SRT) in STEP0. clarify. *)
    (*         (* apply (step_choose (fun st2 : {st' : state | step st0 None st'} => interpSTS step state_sort (st2 $)) (exist _ st1 ST)). } *) *)
    (*         apply (ModSem.step_choose (fun st2 : {st' : state | step st0 None st'} => interpSTS step state_sort (st2 $)) (exist _ st1 ST)). } *)
    (*       { clarify. } *)
    (* - pfold. econs. *)
    (* - pfold. eapply sb_demonic. *)
    (*   { ss. rewrite interpSTS_red. rewrite SRT. ired. ss. } *)
    (*   set (p := exist (fun '(ev', st') => step st0 (Some ev') st') (ev, st1) STEP). *)
    (*   set (cont :=  *)
    (*          (fun x : {'(ev', st') : event * state | step st0 (Some ev') st'} => *)
    (*             let (x0, _) := x in *)
    (*             let (y0, st2) := x0 in *)
    (*             match y0 with *)
    (*             | event_sys fn args => *)
    (*               Vis (Syscall fn args) (fun _ : val => interpSTS step state_sort st2) *)
    (*             end)). *)
    (*   set (next := cont p). *)
    (*   exists None. exists next. split. *)
    (*   { ss. rewrite interpSTS_red. rewrite SRT. *)
    (*     rewrite bind_trigger. *)
    (*     apply (ModSem.step_choose cont p). } *)
    (*   split; auto. ss; clarify. destruct ev. ss; clarify. *)
    (*   econs; ss. *)
    (*   { instantiate (1:= interpSTS step state_sort st1). *)
    (*     set (sys_cont := (fun _ : val => interpSTS step state_sort st1)). *)
    (*     apply (ModSem.step_syscall sys_cont (rv:= snd (syscall_sem fn args))). *)
    (*     admit "TODO: syscall_sem axiom?". } *)
    (*   clear p cont next. right. apply CIH. *)
    (*   destruct TL; clarify. *)
    (* - pfold. unfold union in STEP. des. *)
    (*   econs; ss; clarify. *)
    (*   { rewrite interpSTS_red. rewrite SRT. ss. } *)
    (*   set (cont := (fun st2 : {st' : state | step st0 None st'} => interpSTS step state_sort (st2 $))). *)
    (*   set (p := exist (fun st' => step st0 None st') st1 STEP0). *)
    (*   exists None. exists (cont p). split. *)
    (*   { ss. rewrite interpSTS_red. rewrite SRT. econs. } *)
    (*   split; auto. econs; ss; clarify. *)
        

End PROOF.
