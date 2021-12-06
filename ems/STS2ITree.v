Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import ModSem.
Require Import SimSTSOld.
Require Import STSNorm.
Require Import STS Behavior.

Set Implicit Arguments.

Section CONV.

  CoFixpoint decompile_STS
             (state: Type)
             (step: state -> option event -> state -> Prop)
             (state_sort: state -> sort):
    state -> itree eventE Any.t :=
    fun st0 =>
      match (state_sort st0) with
      | STS.angelic =>
        Vis (Take {st': state | @step st0 None st' })
            (fun st1 => decompile_STS step state_sort (proj1_sig st1))
      | STS.demonic =>
        Vis (Choose {st': state | @step st0 None st' })
            (fun st1 => decompile_STS step state_sort (proj1_sig st1))
      | STS.final z =>
        Ret (z)
      | STS.vis =>
        '(exist _ (event_sys fn args _) _) <-
        trigger (Choose {ev': event | exists st1, @step st0 (Some ev') st1 });;
        rv <- trigger (Syscall fn args (fun rv => exists st1, (@step st0 (Some (event_sys fn args rv)) st1)));;
        Vis (Choose {st1: state | @step st0 (Some (event_sys fn args rv)) st1 })
            (fun st1 => decompile_STS step state_sort (proj1_sig st1))
      end
  .


  Lemma unfold_decompile_STS
        (state: Type)
        (step: state -> option event -> state -> Prop)
        (state_sort: state -> sort)
        (st0: state):
    decompile_STS step state_sort st0
    =
    match (state_sort st0) with
    | STS.angelic =>
      Vis (Take {st': state | @step st0 None st' })
          (fun st1 => decompile_STS step state_sort (proj1_sig st1))
    | STS.demonic =>
      Vis (Choose {st': state | @step st0 None st' })
          (fun st1 => decompile_STS step state_sort (proj1_sig st1))
    | STS.final z =>
      Ret (z)
    | STS.vis =>
      '(exist _ (event_sys fn args _) _) <-
      trigger (Choose {ev': event | exists st1, @step st0 (Some ev') st1 });;
      rv <- trigger (Syscall fn args (fun rv => exists st1, (@step st0 (Some (event_sys fn args rv)) st1)));;
      Vis (Choose {st1: state | @step st0 (Some (event_sys fn args rv)) st1 })
          (fun st1 => decompile_STS step state_sort (proj1_sig st1))
    end
  .
  Proof.
    eapply observe_eta. reflexivity.
  Qed.

  (* Set Primitive Projections.  *)

End CONV.

Section PROOF.

  Import Behavior.Beh.

  Context {CONF: EMSConfig}.

  Variable
    (state: Type)
    (st_init0: state)
    (step0: state -> option event -> state -> Prop)
    (state_sort0: state -> sort).

  Hypothesis wf_vis0 :
    forall (st0 : state) (ev0 ev1 : option event) (st1 st2 : state),
      state_sort0 st0 = vis ->
      step0 st0 ev0 st1 -> step0 st0 ev1 st2 -> ev0 = ev1 -> st1 = st2.

  Hypothesis wf_vis_event0 :
    forall (st0 : state) (ev0 : option event) (st1 : state),
      state_sort0 st0 = vis ->
      step0 st0 ev0 st1 -> ev0 <> None.

  Hypothesis wf_angelic0 :
    forall (st0 : state) (ev : option event) (st1 : state),
      state_sort0 st0 = angelic -> step0 st0 ev st1 -> ev = None.

  Hypothesis wf_demonic0 :
    forall (st0 : state) (ev : option event) (st1 : state),
      state_sort0 st0 = demonic -> step0 st0 ev st1 -> ev = None.

  Hypothesis wf_final0 :
    forall st0 ev st1 r (FIN: state_sort0 st0 = final r) (STEP: step0 st0 ev st1),
      False.

  Let L0 :=
    {|
    STS.state := state;
    STS.step := step0;
    STS.initial_state := st_init0;
    STS.state_sort := state_sort0;
    STS.wf_vis := wf_vis0;
    STS.wf_vis_event := wf_vis_event0;
    STS.wf_angelic := wf_angelic0;
    STS.wf_demonic := wf_demonic0;
    STS.wf_final := wf_final0;
    |}
  .

  Let L1 := vis_normalize L0.

  Let step := norm_step state_sort0 step0.
  Let state_sort := norm_state_sort state_sort0.
  Let st_init := norm_state st_init0.

  Let wf_vis := L1.(wf_vis).
  Let wf_angelic := L1.(wf_angelic).
  Let wf_demonic := L1.(wf_demonic).

  Let STS_itree := decompile_STS step state_sort st_init.
  Let L1_itree := ModSemL.compile_itree STS_itree.

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

  Hypothesis wf_finalize0:
    forall st0 rv, state_sort0 st0 = final rv -> finalize (rv) = Some rv.

  Lemma wf_finalize:
    forall st0 rv, state_sort st0 = final rv -> finalize (rv) = Some rv.
  Proof.
    i. unfold state_sort, norm_state_sort in H. des_ifs. eapply wf_finalize0; et.
  Qed.

(**
of_state =
fun L1 : semantics => paco2 (_of_state L1) bot2
     : forall L1 : semantics, STS.state L1 -> Tr.t -> Prop

paco2 has 'fixed' semantics -> needs fixed semantics to do pcofix
 **)
  Lemma beh_preserved_L1_dir :
    forall st0 (tr: Tr.t),
      of_state
        L1_itree
        (decompile_STS step state_sort st0)
        tr
      ->
      of_state
        L1
        st0
        tr.
  Proof.
    intros st0. eapply adequacy_aux.
    { apply Nat.lt_wf_0. }
    { apply Nat.lt_wf_0. }
    instantiate (1:=10). instantiate (1:=10).
    revert st0.
    pcofix CIH. i. pfold.
    destruct (state_sort st0) eqn:SRT.
    - eapply sim_angelic_src; ss; clarify. i. esplits; et.
      left. pfold. eapply sim_angelic_tgt; ss; clarify.
      + rewrite unfold_decompile_STS. rewrite SRT. ss.
      + i.
        set (cont:= (fun st1 : {st' | step st0 None st'} => decompile_STS step state_sort (st1 $))).
        exists (cont (exist (fun st => step st0 None st) st_src1 STEP)). eexists.
        { rewrite unfold_decompile_STS. rewrite SRT. econs 3. }
        esplits; et.
    - eapply sim_demonic_tgt; ss; clarify.
      + rewrite unfold_decompile_STS. rewrite SRT. ss.
      + i. rewrite unfold_decompile_STS in STEP. rewrite SRT in STEP.
        dependent destruction STEP.
        destruct x. rename x into st1.
        esplits; et. left. pfold. eapply sim_demonic_src; ss; clarify.
        exists st1. eexists; auto.
        esplits; et.
    - eapply sim_fin; eauto.
      ss. rewrite unfold_decompile_STS. rewrite SRT.
      unfold ModSemL.state_sort. ss.
      erewrite wf_finalize; et.
    - eapply sim_demonic_tgt; ss; clarify.
      + rewrite unfold_decompile_STS. rewrite SRT. ss.
      + i. rewrite unfold_decompile_STS in STEP. rewrite SRT in STEP.
        rewrite bind_trigger in STEP.
        dependent destruction STEP.
        destruct x. des. destruct x.
        esplits; et.
        left. pfold. eapply sim_vis; i; ss; clarify.
        rewrite bind_trigger in STEP.
        dependent destruction STEP.
        des. rename RETURN into STEP.
        exists st2. eexists.
        { auto. }
        esplits. left. pfold. eapply sim_demonic_tgt; ss; clarify.
        i. dependent destruction STEP0.
        destruct x.
        esplits; et. right.
        assert (st2 = x).
        { eapply wf_vis. apply SRT. apply STEP. apply s. reflexivity. }
        clarify.
    Unshelve. all: try exact 0.
  Qed.

  Lemma beh_preserved_L1_inv :
    forall st0 (tr: Tr.t),
      of_state
        L1
        st0
        tr
      ->
      of_state
        L1_itree
        (decompile_STS step state_sort st0)
        tr.
  Proof.
    intros st0. eapply adequacy_aux.
    { apply Nat.lt_wf_0. }
    { apply Nat.lt_wf_0. }
    instantiate (1:=10). instantiate (1:=10).
    revert st0.
    pcofix CIH. i. pfold.
    destruct (state_sort st0) eqn:SRT.
    - eapply sim_angelic_src; ss; clarify.
      + rewrite unfold_decompile_STS. rewrite SRT. ss.
      + i. rewrite unfold_decompile_STS in STEP. rewrite SRT in STEP.
        dependent destruction STEP. destruct x.
        esplits; et. left. pfold. eapply sim_angelic_tgt; ss; clarify.
        exists x. exists s. esplits; et.
    - eapply sim_demonic_tgt; ss; clarify. i.
      esplits; et. left. pfold. eapply sim_demonic_src; ss; clarify.
      + rewrite unfold_decompile_STS. rewrite SRT. ss.
      + i. exists (decompile_STS step state_sort st_tgt1).
        eexists.
        { rewrite unfold_decompile_STS in *. rewrite SRT in *.
          apply (ModSemL.step_choose (fun st1 : {st' | step st0 None st'} => decompile_STS step state_sort (st1 $)) (exist _ st_tgt1 STEP)). }
        esplits; et.
    - econs; ss.
      + rewrite unfold_decompile_STS. rewrite SRT.
        unfold ModSemL.state_sort. ss.
        erewrite wf_finalize; et.
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
                          ` rv0 : Any.t <-
                                  trigger
                                    (Syscall fn args
                                             (fun rv0 : Any.t =>
                                                exists st1, step st0 (Some (event_sys fn args rv0)) st1));;
                                  Vis
                                    (Choose {st1 | step st0 (Some (event_sys fn args rv0)) st1})
                                    (fun
                                        st1 : {st1 | step st0 (Some (event_sys fn args rv0)) st1}
                                      => decompile_STS step state_sort (st1 $))
                        end)).
        destruct H.
        eapply sim_demonic_src; ss; clarify.
        { rewrite unfold_decompile_STS. rewrite SRT. ss. }
        exists (cont (exist (fun 'ev => exists st1, step st0 (Some ev) st1) x H)).
        destruct x. eexists.
        { rewrite unfold_decompile_STS. rewrite SRT. ss. rewrite bind_trigger.
          eapply (ModSemL.step_choose cont (exist (fun 'ev => exists st1, step st0 (Some ev) st1) (event_sys fn args rv) H)). }
        esplits; et.
        left. pfold. destruct H. rename s into STEP. subst cont.
        set (cont := fun rv0 =>
                       Vis
                         (Choose
                            {st1 | step st0 (Some (event_sys fn args rv0)) st1})
                         (fun
                             st1 : {st1 | step st0 (Some (event_sys fn args rv0)) st1} =>
                             decompile_STS step state_sort (st1 $))).
        eapply sim_vis; eauto.
        i. ss.
        exploit wf_vis_norm.
        { instantiate (1:= L1). exists L0. reflexivity. }
        { ss. apply SRT. }
        { apply STEP. }
        { apply STEP0. }
        i. des. clarify.
        exists (cont rv). eexists.
        { ss. rewrite bind_trigger. subst cont. ss.
          apply (@ModSemL.step_syscall fn args rv (fun rv0 : Any.t => exists st1, step st0 (Some (event_sys fn args rv0)) st1) (fun x : Any.t => Vis (Choose {st1 | step st0 (Some (event_sys fn args x)) st1}) (fun st1 : {st1 | step st0 (Some (event_sys fn args x)) st1} => decompile_STS step state_sort (st1 $)))).
          2:{ exists st_tgt1. auto. }
          apply wf_syscall.
          exists st0, st_tgt1. auto. }
        esplits. left. pfold. eapply sim_demonic_src; ss; clarify.
        subst cont. ss.
        set (cont :=
               (fun
                   st1 :
                     {st1 | step st0
                                 (Some (event_sys fn args rv))
                                 st1} =>
                   decompile_STS step state_sort (st1 $))).
        exists (cont (exist (fun st1 => step st0 (Some (event_sys fn args rv)) st1) st_tgt1 STEP)).
        eexists.
        { econs. }
        esplits; et.
    Unshelve. all: try exact 0.
  Qed.

  Lemma beh_preserved_L1 :
    forall st0 (tr: Tr.t),
      of_state L1 st0 tr
      <->
      of_state
        L1_itree
        (decompile_STS step state_sort st0)
        tr.
  Proof.
    split.
    - apply beh_preserved_L1_inv.
    - apply beh_preserved_L1_dir.
  Qed.

  Theorem beh_preserved :
    exists itr, forall tr,
        of_state L0 st_init0 tr
        <->
        of_state (ModSemL.compile_itree itr) itr tr.
  Proof.
    exists STS_itree. i.
    assert (A: of_state (ModSemL.compile_itree STS_itree) STS_itree tr
               =
               of_state L1_itree (decompile_STS step state_sort st_init) tr).
    { ss. }
    rewrite A.
    rewrite <- (beh_preserved_L1 st_init tr).
    rewrite STSNorm.beh_preserved. eauto.
  Qed.

End PROOF.

(* Import Behavior.Beh. *)

(* Theorem exists_itree : *)
(*   forall (L1: semantics), *)
(*     (forall ev, *)
(*         (exists st0 st1, (state_sort L1 st0 = vis) /\ (step L1 st0 (Some ev) st1)) -> *)
(*         syscall_sem ev) -> *)
(*     exists itr, forall tr, *)
(*         of_state L1 L1.(initial_state) tr *)
(*         <-> *)
(*         of_state (interpITree itr) itr tr. *)
(* Proof. *)
(*   i. destruct L1. ss. *)
(*   revert state initial_state step state_sort wf_vis wf_angelic wf_demonic H. *)
(*   eapply PROOF.beh_preserved. *)

(* (** Universe consistency *) *)
