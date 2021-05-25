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
Require Import Imp2Csharpminor.
Require Import ImpProofs.
Require Import Mem0.
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

  | sim_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: exists _ev_tgt _st_tgt1, Step L1 st_tgt0 [_ev_tgt] _st_tgt1)
      (SIM: forall ev_tgt st_tgt1
          (STEP: Step L1 st_tgt0 ev_tgt st_tgt1)
        ,
          exists st_src1 ev_src (STEP: _.(step) st_src0 (Some ev_src) st_src1),
            (<<MATCH: Forall2 match_event ev_tgt [ev_src]>>) /\
            (<<SIM: exists i1 j1, sim i1 j1 st_src1 st_tgt1>>))
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
  .

  Definition sim: _ -> _ -> _ -> _ -> Prop := paco4 _sim bot4.

  Lemma sim_mon: monotone4 _sim.
  Proof.
    ii. inv IN.

    - econs 1; et.
    - econs 2; et. i. exploit SIM; et. i; des. esplits; et.
    - econs 3; et. des. esplits; et.
    - econs 4; et. des. esplits; et.
    - econs 5; et. i. exploit SIM; et. i; des. esplits; et.
  Qed.

End SIM.

Hint Constructors _sim.
Hint Unfold sim.
Hint Resolve sim_mon: paco.

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
  forall (X : Prop) (ktr next : itree eventE Any.t),
    ModSemL.step (trigger (Take X);; ktr) None next -> (next = ktr /\ X).
Proof.
  i. dependent destruction H; try (irw in x; clarify; fail).
  rewrite <- bind_trigger in x. apply unbind_trigger in x.
  des. clarify.
Qed.

Section PROOF.

  From compcert Require Import Csharpminor.
  Import ModSemL.

  Context `{Σ: GRA.t}.

  Definition ordN : nat -> nat -> Prop := fun a b => True.

  Ltac sim_red := Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); econs 3; ss; clarify; eexists; exists (step_tau _); eexists; split; auto; eexists.

  Lemma map_val_vadd_comm
        a b v
        (VADD: vadd a b = Some v)
        (WFA: wf_val a)
        (WFB: wf_val b)
        (WFV: wf_val v)
    :
      Values.Val.addl (map_val a) (map_val b) = map_val v.
  Proof.
    destruct a; destruct b; ss; clarify; unfold to_long; ss.
    - unfold to_long. ss. repeat f_equal. unfold Int64.add. f_equal.
      rewrite! Int64.unsigned_repr_eq.
      unfold intrange_64 in *. unfold modulus_64 in *. unfold Int64.modulus.
      unfold wordsize_64, Int64.wordsize in *. unfold Wordsize_64.wordsize.
      rewrite! Z.mod_small; auto; try nia.
    - des_ifs. unfold Ptrofs.add; ss.
      unfold intrange_64 in *. unfold modulus_64 in *. unfold wordsize_64 in *.
      repeat f_equal; try rewrite Ptrofs.unsigned_repr_eq.
      + unfold Ptrofs.modulus. unfold Ptrofs.wordsize. unfold Wordsize_Ptrofs.wordsize.
        des_ifs. rewrite Z.mod_small; auto. nia.
      + unfold Ptrofs.of_int64.
        rewrite Int64.unsigned_repr_eq. rewrite Ptrofs.unsigned_repr_eq.
        unfold Ptrofs.modulus. unfold Ptrofs.wordsize. unfold Wordsize_Ptrofs.wordsize. des_ifs.
        unfold Int64.modulus. unfold Int64.wordsize. unfold Wordsize_64.wordsize.
        rewrite Z.mod_mod; try nia. rewrite Z.mod_small; try nia.
    - des_ifs. unfold Ptrofs.add; ss.
      unfold intrange_64 in *. unfold modulus_64 in *. unfold wordsize_64 in *.
      repeat f_equal; try rewrite Ptrofs.unsigned_repr_eq.
      + unfold Ptrofs.modulus. unfold Ptrofs.wordsize. unfold Wordsize_Ptrofs.wordsize.
        des_ifs. rewrite Z.mod_small; auto. nia.
      + unfold Ptrofs.of_int64.
        rewrite Int64.unsigned_repr_eq. rewrite Ptrofs.unsigned_repr_eq.
        unfold Ptrofs.modulus. unfold Ptrofs.wordsize. unfold Wordsize_Ptrofs.wordsize. des_ifs.
        unfold Int64.modulus. unfold Int64.wordsize. unfold Wordsize_64.wordsize.
        rewrite Z.mod_mod; try nia. rewrite Z.mod_small; try nia.
  Qed.

  Lemma step_expr
        e te
        tcode tf tcont tge tle tm (src: ModL.t) (tgt: Csharpminor.program)
        r ms mn ge le rstate pstate ktr
        i0 j0 i1 j1
        (MLE: match_le le tle)
        (CEXP: compile_expr e = Some te)
        (SIM:
           forall rv trv,
             wf_val rv ->
             eval_expr tge empty_env tle tm te trv ->
             trv = map_val rv ->
             _sim (ModL.compile src) (semantics tgt) ordN
                  (upaco4 (_sim (ModL.compile src) (semantics tgt) ordN) r) i1 j1
                  (ktr (rstate, pstate, (le, rv)))
                  (State tf tcode tcont empty_env tle tm))
    :
      _sim (ModL.compile src) (semantics tgt) ordN
           (upaco4 (_sim (ModL.compile src) (semantics tgt) ordN) r) i0 j0
           (r0 <- EventsL.interp_Es (prog ms) (transl_all mn (interp_imp ge le (denote_expr e))) (rstate, pstate);; ktr r0)
           (State tf tcode tcont empty_env tle tm).
  Proof.
    unfold ordN in *.
    generalize dependent ktr. generalize dependent te.
    move MLE before pstate. revert_until MLE.
    generalize dependent e. Local Opaque Init.Nat.add. induction e; i; ss; des; clarify.
    - rewrite interp_imp_expr_Var. sim_red.
      destruct (alist_find v le) eqn:AFIND; try sim_red.
      + repeat (sim_tau; left; pfold). sim_red.
        unfold assume. grind. econs 5; ss; auto. i. eapply angelic_step in STEP; des; clarify.
        eexists; split; auto. eexists. left. pfold.
        repeat (sim_tau; left; pfold).
        sim_red. eapply SIM; auto.
        econs. inv MLE. specialize ML with (x:=v) (sv:=(Some v0)).
        hexploit ML; auto. i. des. ss. clarify.
      + ss. unfold triggerUB. sim_red. econs 5; i; ss; auto.
        dependent destruction STEP; try (irw in x; clarify; fail).
    - rewrite interp_imp_expr_Lit.
      sim_red. unfold assume. grind. econs 5; auto. i. eapply angelic_step in STEP; des; clarify.
      eexists; split; auto. eexists. left; pfold.
      repeat (sim_tau; left; pfold).
      sim_red. eapply SIM; eauto. econs. unfold map_val. ss.
    - rewrite interp_imp_expr_Plus.
      sim_red. destruct (compile_expr e1) eqn:EXP1; destruct (compile_expr e2) eqn:EXP2; ss; clarify.
      eapply IHe1; eauto; clear IHe1.
      i. sim_red. eapply IHe2; eauto; clear IHe2.
      i. sim_red.
      unfold unwrapU. destruct (vadd rv rv0) eqn:VADD; ss; clarify.
      + sim_red. unfold assume. grind. econs 5; auto. i. eapply angelic_step in STEP; des; clarify.
        eexists; split; auto. eexists. left; pfold.
        repeat (sim_tau; left; pfold).
        sim_red. specialize SIM with (rv:=v) (trv:= map_val v). apply SIM; auto.
        econs; eauto. ss. f_equal. apply map_val_vadd_comm; auto.
      + ss. unfold triggerUB. sim_red. econs 5; i; ss; auto.
        dependent destruction STEP; try (irw in x; clarify; fail).
    -
  Admitted.

  Variable mmem : Mem.t -> Memory.Mem.mem -> Prop.

  (* Variable src : Imp.program. *)
  (* Let src_mod := ImpMod.get_mod src. *)
  (* Variable tgt : Ctypes.program Clight.function. *)

  (* Let src_sem := ModL.compile (Mod.add_list ([src_mod] ++ [Mem])). *)
  (* Let tgt_sem := semantics2 tgt. *)


  Theorem match_states_sim
          (src: Imp.program) tgt ist cst
          i0 j0
          (COMP: Imp2Clight.compile src = OK tgt)
          (MS: match_states mmem ist cst)
    :
      <<SIM: sim (ModL.compile (Mod.add_list ([Mem] ++ [ImpMod.get_mod src]))) (semantics2 tgt) ordN i0 j0 ist cst>>.
  Proof.
    move COMP before tgt.
    revert_until COMP.
    pcofix CIH. i. pfold.
    inv MS.
    unfold ordN in *.
    destruct code.
    - ss. unfold itree_of_cont_stmt, itree_of_imp_cont.
      rewrite interp_imp_Skip. grind.
      destruct tcont; ss; clarify.
      + inv MCS. inv MCN; ss; clarify. unfold idK. sim_red.
        destruct rp. sim_red.
        econs 4; ss; auto.
        { unfold state_sort. ss. rewrite Any.upcast_downcast. ss. }
        i. dependent destruction STEP.
      + inv MCS.
        admit "mid: skip".
      + admit "mid: skip".
    - ss. unfold itree_of_cont_stmt, itree_of_imp_cont.
      rewrite interp_imp_Assign. sim_red. grind.
      destruct (compile_expr e) eqn:EXP; uo; ss. destruct rp. grind.
      eapply step_expr; eauto. i.
      repeat (sim_tau; left; pfold).
      rewrite transl_all_ret. rewrite EventsL.interp_Es_ret. grind.
      econs 3.
      + admit "ez? strict_determinate_at".
      + eexists. eexists.
        { eapply step_set. eapply H. }
        unfold ordN in *. eexists; split; eauto; auto.
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
    - admit "ez?: Seq".
    - admit "ez?: If".
    - admit "hard: CallFun".
    - admit "hard: CallPtr".
    - admit "mid: CallSys".
    - admit "hard: AddrOf".
    - admit "hard: Malloc".
    - admit "hard: free".
    - admit "hard: Load".
    - admit "hard: Store".
    - admit "hard: Cmp".
  Admitted.

End PROOF.
