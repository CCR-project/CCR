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

Section PROOF.

  Import ModSemL.

  Context `{Σ: GRA.t}.

  Variable mmem : Mem.t -> Memory.Mem.mem -> Prop.

  (* Variable src : Imp.program. *)
  (* Let src_mod := ImpMod.get_mod src. *)
  (* Variable tgt : Ctypes.program Clight.function. *)

  (* Let src_sem := ModL.compile (Mod.add_list ([src_mod] ++ [Mem])). *)
  (* Let tgt_sem := semantics2 tgt. *)

  Ltac sim_red := Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau i j := sim_red; econs 2; ss; clarify; eexists; exists (step_tau _); exists i; split; auto; exists j.

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
    - ss. unfold itree_of_cont_stmt, itree_of_imp_cont, itree_of_imp_pop.
      rewrite interp_imp_Assign. destruct e.
      + rewrite interp_imp_expr_Var. grind. sim_red.
        destruct (alist_find v le) eqn:AFIND; ss.
        * sim_tau 99 101. left. pfold. sim_tau 98 102. left. pfold.
          sim_red. destruct (classic (wf_val v0)).
          { unfold assume. grind. econs 4; ss; clarify.
            i. dependent destruction STEP; ss; clarify.
            unfold trigger in STEP. ss. inv STEP; clarify. 
          


      clarify. grind.
      Red.prw ltac:(_red_gen) 2 0.
      inv MCS; clarify.
      + 

      
      Red.prw ltac:(_red_gen) 2 1 0.
      admit "ez? needs to handle two cases?".


    - ss. destruct (compile_expr e) as [te|] eqn:CE; uo; clarify.
      clear gm MM m WF_RETF MM.
      unfold itree_of_cont_stmt, itree_of_imp_cont.
      rewrite interp_imp_Assign. destruct e.
      + rewrite interp_imp_expr_Var.
        destruct (alist_find v le) eqn: AFIND; ss.
        * econs 5; clarify.
          { unfold ModL.compile, ModSemL.compile, ModSemL.compile_itree. ss.
            (* ired. rewrite transl_all_tau. *)
            (* Red.prw ltac:(_red_gen) 2 1 1 0. *)
            Red.prw ltac:(_red_gen) 2 1 0. ss. }
          { admit "ez, strict_determinate_at". }
          ss.
          eexists (State tf Sskip tcont empty_env (Maps.PTree.set (s2p x) _ tle) tm).
          eexists.
          { eapply step_set. econs. inv ML. hexploit ML0. apply AFIND.
            i. des. destruct tv; ss; clarify. eauto. }
          eexists ('(_, _, (_, rv)) <- next _;; x <- Ret (rv↑);; stack x).
          eexists.
          { Red.prw ltac:(_red_gen) 3 0. 
            


  Admitted.
  

End PROOF.
