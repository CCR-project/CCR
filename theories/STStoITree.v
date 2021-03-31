Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import SimSTS.
Require Import STS_vis.

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
        Ret (Vint z)↑
      | vis =>
        '(exist _ (event_sys fn args _) _) <-
        trigger (Choose {ev': event | exists st1, @step st0 (Some ev') st1 });;
        rv <- trigger (Syscall fn args (fun rv => exists st1, (@step st0 (Some (event_sys fn args rv)) st1)));;
        Vis (Choose {st1: state | @step st0 (Some (event_sys fn args rv)) st1 })
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
      Ret (Vint z)↑
    | vis =>
      '(exist _ (event_sys fn args _) _) <-
      trigger (Choose {ev': event | exists st1, @step st0 (Some ev') st1 });;
      rv <- trigger (Syscall fn args (fun rv => exists st1, (@step st0 (Some (event_sys fn args rv)) st1)));;
      Vis (Choose {st1: state | @step st0 (Some (event_sys fn args rv)) st1 })
          (fun st1 => interpSTS step state_sort (proj1_sig st1))
    end
  .
  Proof.
    eapply observe_eta. reflexivity.
  Qed.

  (* Set Primitive Projections.  *)

End CONV.

(* Section INV. *)

(*   Let state: Type := itree eventE Any.t. *)

(*   Definition itr_state_sort (st0: state): sort := *)
(*     match (observe st0) with *)
(*     | TauF _ => demonic *)
(*     | RetF rv => *)
(*       match rv↓ with *)
(*       | Some z => final z *)
(*       | _ => angelic *)
(*       end *)
(*     | VisF (Choose X) k => demonic *)
(*     | VisF (Take X) k => angelic *)
(*     | VisF (Syscall fn args rvs) k => vis *)
(*     end *)
(*   . *)
  
(*   Program Definition interpITree: *)
(*     (itree eventE Any.t) -> semantics := *)
(*     fun itr => *)
(*       {| *)
(*         STS.state := itree eventE Any.t; *)
(*         STS.step := step; *)
(*         STS.initial_state := itr; *)
(*         STS.state_sort := state_sort; *)
(*       |} *)
(*   . *)
(*   Next Obligation. inv STEP; inv STEP0; ss. csc. Qed. *)
(*   Next Obligation. inv STEP; ss. Qed. *)
(*   Next Obligation. inv STEP; ss. Qed. *)

(* End INV. *)

Module PROOF.
Section BEH_PROOF.

  Import Behavior.Beh.

  Variable
    (state: Type)
    (st_init0: state)
    (step0: state -> option event -> state -> Prop)
    (state_sort0: state -> sort).
  
  Hypothesis wf_vis0 :
    forall (st0 : state) (ev0 ev1 : option event) (st1 st2 : state),
      state_sort0 st0 = vis ->
      step0 st0 ev0 st1 -> step0 st0 ev1 st2 -> ev0 = ev1 -> st1 = st2.

  Hypothesis wf_angelic0 :
    forall (st0 : state) (ev : option event) (st1 : state),
      state_sort0 st0 = angelic -> step0 st0 ev st1 -> ev = None.

  Hypothesis wf_demonic0 :
    forall (st0 : state) (ev : option event) (st1 : state),
      state_sort0 st0 = demonic -> step0 st0 ev st1 -> ev = None.

  Definition L0 :=
    {|
    STS.state := state;
    STS.step := step0;
    STS.initial_state := st_init0;
    STS.state_sort := state_sort0;
    STS.wf_vis := wf_vis0;
    STS.wf_angelic := wf_angelic0;
    STS.wf_demonic := wf_demonic0;
    |}
  .

  Definition L := vis_normalize L0.

  Definition step := norm_step state_sort0 step0.
  Definition state_sort := norm_state_sort state_sort0.
  Definition st_init := norm_state st_init0.

  Definition wf_vis := L.(wf_vis).
  Definition wf_angelic := L.(wf_angelic).
  Definition wf_demonic := L.(wf_demonic).

  Definition STS_itree := interpSTS step state_sort st_init.
  (* Definition L_itree := interpITree STS_itree. *)
  Definition L_itree := ModSem.interp_itree STS_itree.
  
  Hypothesis wf_syscall0 :
    forall ev,
      (exists st0 st1, (state_sort0 st0 = vis) /\ (step0 st0 (Some ev) st1)) ->
      syscall_sem ev.

  Lemma wf_syscall :
    forall ev,
      (exists st0 st1, (state_sort st0 = vis) /\ (step st0 (Some ev) st1)) ->
      syscall_sem ev.
  Proof.
    i. des. unfold step in *. unfold state_sort in *.
    destruct st0. destruct st1. ss; clarify.
    destruct o; ss; clarify.
    2:{ destruct (state_sort0 s); ss; clarify. }
    inv H0. eapply wf_syscall0; eauto.
  Qed.

(**
of_state = 
fun L : semantics => paco2 (_of_state L) bot2
     : forall L : semantics, STS.state L -> Tr.t -> Prop

paco2 has 'fixed' semantics -> needs fixed semantics to do pcofix
So, fix semantics with st_init, later let st_init = st0 in the main thm.
 **)
  Theorem beh_preserved_vis_norm_dir :
    forall st0 (tr: Tr.t),
      of_state
        L_itree
        (initial_state (ModSem.interp_itree (interpSTS step state_sort st0)))
        tr
      ->
      of_state
        L
        st0
        tr.
  Proof.
    intros st0. eapply adequacy_aux with (i0 := 10).
    { apply Nat.lt_wf_0. }
    revert st0.
    pcofix CIH. i. pfold.
    destruct (state_sort st0) eqn:SRT.
    - eapply sim_angelic_both; ss; clarify.
      + rewrite interpSTS_red. rewrite SRT. ss.
      + i.
        set (cont:= (fun st1 : {st' | step st0 None st'} => interpSTS step state_sort (st1 $))).
        exists (cont (exist (fun st => step st0 None st) st_src1 STEP)). eexists.
        { rewrite interpSTS_red. rewrite SRT. econs 3. }
        exists 10. right. eapply CIH.
    - eapply sim_demonic_both; ss; clarify.
      + rewrite interpSTS_red. rewrite SRT. ss.
      + i. rewrite interpSTS_red in STEP. rewrite SRT in STEP.
        dependent destruction STEP.
        destruct x. rename x into st1.
        exists st1. eexists; auto.
        exists 10. right. apply CIH.
    - eapply sim_fin; eauto.
      ss. rewrite interpSTS_red. rewrite SRT.
      unfold ModSem.state_sort. ss.
      rewrite Any.upcast_downcast. reflexivity.
    - eapply sim_demonic_tgt; ss; clarify.
      + rewrite interpSTS_red. rewrite SRT. ss.
      + i. rewrite interpSTS_red in STEP. rewrite SRT in STEP.
        rewrite bind_trigger in STEP.
        dependent destruction STEP.
        destruct x. des. destruct x.
        exists 9. split; auto.
        left. pfold. eapply sim_vis; i; ss; clarify.
        rewrite bind_trigger in STEP.
        dependent destruction STEP.
        destruct SYSCALL. des. rename H0 into STEP.
        exists st2. eexists.
        { auto. }
        exists 11. left. pfold. eapply sim_demonic_tgt; ss; clarify.
        i. dependent destruction STEP0.
        destruct x.
        exists 10. split; auto. right.
        assert (st2 = x).
        { eapply wf_vis. apply SRT. apply STEP. apply s. reflexivity. }
        clarify.
  Qed.
  
  Theorem beh_preserved_vis_norm_inv :
    forall st0 (tr: Tr.t),
      of_state
        L
        st0
        tr
      ->
      of_state
        L_itree
        (initial_state (ModSem.interp_itree (interpSTS step state_sort st0)))
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
          apply (ModSem.step_choose (fun st1 : {st' | step st0 None st'} => interpSTS step state_sort (st1 $)) (exist _ st_tgt1 STEP)). }
        exists 10. right. apply CIH.
    - econs; ss.
      + rewrite interpSTS_red. rewrite SRT.
        unfold ModSem.state_sort. ss.
        rewrite Any.upcast_downcast. reflexivity.
      + auto.
    - assert (CASE: (forall ev st1, not (step st0 (Some ev) st1)) \/ (exists ev st1, (step st0 (Some ev) st1))).
      { destruct (classic (exists ev st1, step st0 (Some ev) st1)); eauto.
        left. ii. apply H. eauto. }
      destruct CASE.
      + eapply sim_vis_stuck_tgt; eauto.
      + set (cont := fun x_ : {ev' : event | exists st1, step st0 (Some ev') st1} =>
                       (let (x, _) := x_ in
                        match x with
                        | event_sys fn args _ =>
                          ` rv0 : val <-
                                  trigger
                                    (Syscall fn args
                                             (fun rv0 : val =>
                                                exists st1, step st0 (Some (event_sys fn args rv0)) st1));;
                                  Vis
                                    (Choose {st1 | step st0 (Some (event_sys fn args rv0)) st1})
                                    (fun
                                        st1 : {st1 | step st0 (Some (event_sys fn args rv0)) st1}
                                      => interpSTS step state_sort (st1 $))
                        end)).
        destruct H.
        eapply sim_demonic_src; ss; clarify.
        { rewrite interpSTS_red. rewrite SRT. ss. }
        exists (cont (exist (fun 'ev => exists st1, step st0 (Some ev) st1) x H)).
        destruct x. eexists.
        { rewrite interpSTS_red. rewrite SRT. ss. rewrite bind_trigger.
          eapply (ModSem.step_choose cont (exist (fun 'ev => exists st1, step st0 (Some ev) st1) (event_sys fn args rv) H)). }
        exists 9. split; auto.
        left. pfold. destruct H. rename s into STEP. subst cont.
        set (cont := fun rv0 =>
                       Vis
                         (Choose
                            {st1 | step st0 (Some (event_sys fn args rv0)) st1})
                         (fun
                             st1 : {st1 | step st0 (Some (event_sys fn args rv0)) st1} =>
                             interpSTS step state_sort (st1 $))).
        eapply sim_vis; eauto.
        i. ss. 
        exploit wf_vis_norm.
        { instantiate (1:= L). exists L0. reflexivity. }
        { ss. apply SRT. }
        { apply STEP. }
        { apply STEP0. }
        i. des. clarify.
        exists (cont rv). eexists.
        { ss. rewrite bind_trigger. subst cont. ss.
          apply (@ModSem.step_syscall fn args rv (fun rv0 : val => exists st1, step st0 (Some (event_sys fn args rv0)) st1) (fun x : val => Vis (Choose {st1 | step st0 (Some (event_sys fn args x)) st1}) (fun st1 : {st1 | step st0 (Some (event_sys fn args x)) st1} => interpSTS step state_sort (st1 $)))).
          split.
          2:{ exists st_tgt1. auto. }
          apply wf_syscall.
          exists st0, st_tgt1. auto. }
        exists 11. left. pfold. eapply sim_demonic_src; ss; clarify.
        subst cont. ss. 
        set (cont :=
               (fun
                   st1 : 
                     {st1 | step st0
                                 (Some (event_sys fn args rv))
                                 st1} =>
                   interpSTS step state_sort (st1 $))).
        exists (cont (exist (fun st1 => step st0 (Some (event_sys fn args rv)) st1) st_tgt1 STEP)).
        eexists.
        { econs. }
        exists 10. split; eauto.
  Qed.
  
  Theorem beh_preserved_vis_norm :
    forall st0 (tr: Tr.t),
      of_state
        L
        st0
        tr
      <->
      of_state
        L_itree
        (initial_state (ModSem.interp_itree (interpSTS step state_sort st0)))
        tr.
  Proof.
    split.
    - apply beh_preserved_vis_norm_inv.
    - apply beh_preserved_vis_norm_dir.
  Qed.

  Theorem beh_preserved :
    exists itr, forall tr,
        of_state
          L0
          st_init0
          tr
        <->
        of_state
          (ModSem.interp_itree itr)
          itr
          tr.
  Proof.
    exists STS_itree. i.
    rewrite <- (beh_preserved_vis_norm st_init).
    rewrite STS_vis.beh_preserved. eauto.
  Qed.
  
End BEH_PROOF.
End PROOF.

(* Import Behavior.Beh. *)

(* Theorem exists_itree : *)
(*   forall (L: semantics), *)
(*     (forall ev, *)
(*         (exists st0 st1, (state_sort L st0 = vis) /\ (step L st0 (Some ev) st1)) -> *)
(*         syscall_sem ev) -> *)
(*     exists itr, forall tr, *)
(*         of_state L L.(initial_state) tr *)
(*         <-> *)
(*         of_state (interpITree itr) itr tr. *)
(* Proof. *)
(*   i. destruct L. ss. *)
(*   revert state initial_state step state_sort wf_vis wf_angelic wf_demonic H. *)
(*   eapply PROOF.beh_preserved. *)

(* (** Universe consistency *) *)
