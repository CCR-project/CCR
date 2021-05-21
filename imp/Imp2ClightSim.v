From compcert Require Import Smallstep Clight Integers Events Behaviors Errors.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.
Require Import Imp2Clight.
Require Import ImpProofs.
Require Import Mem0.
(* Require Import HoareDef. *)
Require Import IRed.

Set Implicit Arguments.

Definition single_events_at (L: Smallstep.semantics) (s:L.(Smallstep.state)) : Prop :=
  forall t s', Step L s t s' -> (t = E0).

Record strict_determinate_at (L: Smallstep.semantics) (s:L.(Smallstep.state)) : Prop :=
  Strict_determinate_at {
      ssd_determ_at: forall t1 s1 t2 s2
        (STEP0: Step L s t1 s1)
        (STEP1 :Step L s t2 s2),
        <<EQ: s1 = s2>>;
    ssd_determ_at_final: forall tr s' retv
        (FINAL: Smallstep.final_state L s retv)
        (STEP: Step L s tr s'),
        False;
    ssd_traces_at:
      single_events_at L s
  }.

Section SIM.

  Variable L0: STS.semantics.
  Variable L1: Smallstep.semantics.
  Variable idx: Type.
  Variable ord: idx -> idx -> Prop.

  Local Open Scope smallstep_scope.

  Variant _sim sim (i0 j0: idx) (st_src0: L0.(STS.state)) (st_tgt0: L1.(Smallstep.state)): Prop :=
  | sim_fin
      retv
      (RANGE: (0 <= retv <= Int.max_unsigned)%Z)
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(Smallstep.final_state) st_tgt0 (Int.repr retv))
      (DTM: (* sd_final_determ *)
         forall (s : Smallstep.state L1) (r1 r2 : int),
           Smallstep.final_state L1 s r1 -> Smallstep.final_state L1 s r2 -> r1 = r2)
    :
      _sim sim i0 j0 st_src0 st_tgt0

  | sim_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          exists i1, <<ORD: ord i1 i0>> /\ <<SIM: exists j1, sim i1 j1 st_src1 st_tgt0>>)
    :
      _sim sim i0 j0 st_src0 st_tgt0
  | sim_demonic_tgt_dtm
      (*** WRONG DEF, Note: UB in tgt ***)
      (* (SIM: forall st_tgt1 *)
      (*     (STEP: Step L1 st_tgt0 E0 st_tgt1) *)
      (*   , *)
      (*     exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src0 st_tgt1>>) *)
      (DTM: strict_determinate_at L1 st_tgt0)
      (SIM: exists st_tgt1
          (STEP: Step L1 st_tgt0 E0 st_tgt1)
        ,
          exists j1, <<ORD: ord j1 j0>> /\ <<SIM: exists i1, sim i1 j1 st_src0 st_tgt1>>)
      (*** equivalent def ***)
      (* st_tgt1 *)
      (* (STEP: Step L1 st_tgt0 E0 st_tgt1) *)
      (* i1 *)
      (* (ORD: ord i1 i0) *)
      (* (SIM: sim i1 st_src0 st_tgt1) *)
    :
      _sim sim i0 j0 st_src0 st_tgt0
  | sim_angelic_src
      (SRT: _.(state_sort) st_src0 = angelic)
      (SIM: forall st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          exists i1, <<ORD: ord i1 i0>> /\ <<SIM: exists j1, sim i1 j1 st_src1 st_tgt0>>)
    :
      _sim sim i0 j0 st_src0 st_tgt0

  (* | sim_vis *)
  (*     (SRT: _.(state_sort) st_src0 = vis) *)
  (*     (SRT: _.(state_sort) st_tgt0 = vis) *)
  (*     (SIM: forall ev st_tgt1 *)
  (*         (STEP: _.(step) st_tgt0 (Some ev) st_tgt1) *)
  (*       , *)
  (*         exists st_src1 (STEP: _.(step) st_src0 (Some ev) st_src1), *)
  (*           <<SIM: exists i1, sim i1 st_src1 st_tgt1>>) *)
  (*   : *)
  (*     _sim sim i0 st_src0 st_tgt0 *)

  (* | sim_demonic_both *)
  (*     (SRT: _.(state_sort) st_src0 = demonic) *)
  (*     (DTM: strict_determinate_at L1 st_tgt0) *)
  (*     (SIM: exists st_tgt1 *)
  (*         (STEP: Step L1 st_tgt0 E0 st_tgt1) *)
  (*       , *)
  (*         exists st_src1 (STEP: _.(step) st_src0 None st_src1), *)
  (*           <<SIM: exists i1, sim i1 st_src1 st_tgt1>>) *)
  (*   : *)
  (*     _sim sim i0 st_src0 st_tgt0 *)
  .

  Definition sim: _ -> _ -> _ -> _ -> Prop := paco4 _sim bot4.

  Lemma sim_mon: monotone4 _sim.
  Proof.
    ii. inv IN.

    - econs 1; et.
    - econs 2; et. des. esplits; et.
    - econs 3; et. des. esplits; et.
    - econs 4; et. i. exploit SIM; et. i; des. esplits; et.
  Qed.

  Hint Constructors _sim.
  Hint Unfold sim.
  Hint Resolve sim_mon: paco.

  Record simulation: Prop := mk_simulation {
    sim_wf_ord: <<WF: well_founded ord>>;
    sim_init: forall st_tgt0 (INITT: L1.(Smallstep.initial_state) st_tgt0),
        exists i0 j0, (<<SIM: sim i0 j0 L0.(initial_state) st_tgt0>>);
    (* sim_init: exists i0 st_tgt0, (<<SIM: sim i0 L0.(initial_state) st_tgt0>>) /\ *)
    (*                              (<<INITT: L1.(Smallstep.initial_state) st_tgt0>>); *)
    (* sim_dtm: True; *)
  }
  .

  Hypothesis WF: well_founded ord.

  Ltac pc H := rr in H; desH H; ss.

End SIM.

Lemma unbind_trigger E:
  forall [X0 X1 A : Type] (ktr0 : X0 -> itree E A) (ktr1 : X1 -> itree E A) e0 e1,
    (x <- trigger e0;; ktr0 x = x <- trigger e1;; ktr1 x) -> (X0 = X1 /\ e0 ~= e1 /\ ktr0 ~= ktr1).
Proof.
  i. eapply f_equal with (f:=_observe) in H. cbn in H.
  inv H. split; auto.
  dependent destruction H3. dependent destruction H2.
  cbv in x. subst. split; auto.
  assert (ktr0 = ktr1); clarify.
  extensionality x. eapply equal_f in x0.
  irw in x0. eauto.
Qed.

Lemma angelic_step :
  forall X (ktr next : itree eventE Any.t),
    ModSemL.step (trigger (Take X);; ktr) None next -> next = ktr.
Proof.
  i. dependent destruction H; try (irw in x; clarify; fail).
  rewrite <- bind_trigger in x. apply unbind_trigger in x.
  des. clarify.
Qed.

(* Lemma idK_spec2: forall [E : Type -> Type] [R : Type] (i0 : itree E R), i0 = ` x : _ <- i0;; idK x *)
Section PROOF.

  Import ModSemL.

  Context `{Σ: GRA.t}.

  Ltac sim_red := Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau i j := (try sim_red); econs 2; ss; clarify; eexists; exists (step_tau _); exists i; split; auto; exists j.

  Lemma step_expr
        e te
        tcode tf tcont tge tle tm (src: ModL.t) (tgt: Clight.program)
        r ms mn ge le rstate pstate ktr i1 j1
        (MLE: match_le le tle)
        (CEXP: compile_expr e = Some te)
        (SIM:
           forall rv trv,
             eval_expr tge empty_env tle tm te trv ->
             trv = map_val rv ->
             _sim (ModL.compile src) (semantics2 tgt) lt
                  (upaco4 (_sim (ModL.compile src) (semantics2 tgt) lt) r) i1 j1
                  (ktr (rstate, pstate, (le, rv)))
                  (State tf tcode tcont empty_env tle tm))
    :
      _sim (ModL.compile src) (semantics2 tgt) lt
           (upaco4 (_sim (ModL.compile src) (semantics2 tgt) lt) r) (20+i1) (20+j1)
           (r0 <- EventsL.interp_Es (prog ms) (transl_all mn (interp_imp ge le (denote_expr e))) (rstate, pstate);; ktr r0)
           (State tf tcode tcont empty_env tle tm).
  Proof.
    generalize dependent ktr. generalize dependent te.
    (* generalize dependent rv. generalize dependent trv. *)
    (* generalize dependent i0. generalize dependent j0. *)
    generalize dependent e. Local Opaque Init.Nat.add. induction e; i; ss; des; clarify.
    - rewrite interp_imp_expr_Var. sim_red.
      destruct (alist_find v le) eqn:AFIND; try sim_red.
      + sim_tau (19 + i1) (21 + j1). left. pfold.
        sim_tau (18 + i1) (22 + j1). left. pfold.
        sim_red. econs 4; auto. unfold assume. grind. eapply angelic_step in STEP. clarify.
        exists (17 + i1); split; auto. exists (23 + j1). left. pfold.
        sim_tau (16 + i1) (24 + j1). left. pfold.
        sim_tau (15 + i1) (25 + j1). left. pfold.
        sim_tau (14 + i1) (26 + j1). left. pfold.
        sim_tau (13 + i1) (27 + j1). left. pfold.
        sim_tau (12 + i1) (28 + j1). left. pfold.
        sim_red. econs 2; ss; clarify. eexists; exists (step_tau _). exists i1; split; auto.
        { unfold NW. nia. }
        exists j1. left. pfold. sim_red.
        eapply SIM; eauto. econs. inv MLE. specialize ML with (x:=v). specialize ML with (sv:=(Some v0)).
        hexploit ML; auto. i. des. clarify.
      + ss. unfold triggerUB. sim_red. econs 4; i; ss; auto.
        dependent destruction STEP; try (irw in x; clarify; fail).
    - admit "ez: Lit".
    - rewrite interp_imp_expr_Plus. sim_red.
      destruct (compile_expr e1) eqn:EXP1; destruct (compile_expr e2) eqn:EXP2; ss; clarify.
      eapply IHe1; eauto; clear IHe1.
      i. sim_red.
      admit "ez?: Add, index".

  Admitted.



  Variable mmem : Mem.t -> Memory.Mem.mem -> Prop.

  (* Variable src : Imp.program. *)
  (* Let src_mod := ImpMod.get_mod src. *)
  (* Variable tgt : Ctypes.program Clight.function. *)

  (* Let src_sem := ModL.compile (Mod.add_list ([src_mod] ++ [Mem])). *)
  (* Let tgt_sem := semantics2 tgt. *)


  Theorem match_states_sim
          (src: Imp.program) tgt ist cst
          (COMP: Imp2Clight.compile src = OK tgt)
          (MS: match_states mmem ist cst)
    :
      <<SIM: sim (ModL.compile (Mod.add_list ([Mem] ++ [ImpMod.get_mod src]))) (semantics2 tgt) lt 100 100 ist cst>>.
  Proof.
    move COMP before tgt.
    revert_until COMP.
    pcofix CIH. i. pfold.
    inv MS. destruct code.
    (* 12:{ ss.  destruct (compile_expr p) eqn:EXP1; destruct (compile_expr v) eqn:EXP2; ss. uo. *)
    (*      unfold itree_of_cont_stmt, itree_of_imp_cont, itree_of_imp_pop. rewrite interp_imp_Store. *)
    (*      sim_red. *)
    - admit "mid: skip".
    - ss. unfold itree_of_cont_stmt, itree_of_imp_cont.
      rewrite interp_imp_Assign. sim_red. grind.
      replace 100 with (20 + 80); auto.
      destruct (compile_expr e) eqn:EXP; uo; ss. destruct rp. grind.
      eapply step_expr; eauto. i.
      sim_tau 79 81; left; pfold. sim_tau 78 110; left; pfold.
      rewrite transl_all_ret. rewrite EventsL.interp_Es_ret. grind.
      econs 3.
      + admit "ez? strict_determinate_at".
      + eexists. eexists.
        { eapply step_set. eapply H. }
        exists 100; split; eauto.
        { unfold NW; nia. }
        eexists. right. apply CIH.
        eapply match_states_intro with (le0:= alist_add x rv le) (gm0:= gm) (ge0:= ge) (rp:= (r0, p)) (code:= Skip); eauto.
        { econs. i. destruct (classic (x = x0)).
          - clarify. exists (Some (map_val rv)). ss. split.
            2:{ des_ifs.
                assert (A: x0 ?[ eq ] x0 = true).
                { unfold rel_dec. ss. apply String.string_dec_sound. auto. }
                clarify. }
            rewrite Maps.PTree.gss. auto.
          - inv ML. specialize ML0 with (x:=x0).
            admit "ez: alist_find & alist_add". }
        unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind.
    -

  Admitted.

End PROOF.
