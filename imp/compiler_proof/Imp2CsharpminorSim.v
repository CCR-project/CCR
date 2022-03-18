From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.
Require Import Imp2Csharpminor.
Require Import ImpProofs.
Require Import SimSTS2.
Require Import Mem0.
Require Import IRed.
From Ordinal Require Import Ordinal Arithmetic.

Require Import Imp2CsharpminorMatch.
Require Import Imp2CsharpminorArith.
Require Import Imp2CsharpminorGenv.
Require Import Imp2CsharpminorLenv.
Require Import Imp2CsharpminorMem.

From compcert Require Import Csharpminor.

Set Implicit Arguments.

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
  rewrite ! subst_bind in *.
  irw in x0. eauto.
Qed.

Lemma angelic_step :
  forall (X : Prop) (ktr next : itree eventE Any.t),
    ModSemL.step (trigger (Take X);;; ktr) None next -> (next = ktr /\ X).
Proof.
  i. dependent destruction H; try (irw in x; clarify; fail).
  rewrite <- bind_trigger in x. apply unbind_trigger in x.
  des. clarify.
Qed.

Lemma eval_exprlist_length :
  forall a b c d l1 l2
    (EE: eval_exprlist a b c d l1 l2),
    <<EELEN: List.length l1 = List.length l2>>.
Proof.
  i. induction EE; ss; clarify; eauto.
Qed.



Section PROOF.


  Create HintDb ord_step2.
  Hint Resolve Nat.lt_succ_diag_r OrdArith.lt_from_nat OrdArith.lt_add_r: ord_step2.
  Hint Extern 1000 => lia: ord_step2.
  Ltac ord_step2 := eauto with ord_step2.

  Import ModSemL.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  Variable srcprog : Imp.programL.



  Definition compile_val md := @ModL.compile _ EMSConfigImp md.

  Let _sim_mon := Eval simpl in (fun (src: ModL.t) (tgt: Csharpminor.program) => @sim_mon (compile_val src) (semantics tgt)).
  Hint Resolve _sim_mon: paco.

  Let _ordC_spec := Eval simpl in (fun (src: ModL.t) (tgt: Csharpminor.program) => @ordC_spec (compile_val src) (semantics tgt)).

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); econs 3; ss; clarify; eexists; exists (step_tau _); eexists; split; [ord_step2|auto].
  Ltac sim_ord := guclo _ordC_spec; econs.


  Ltac solve_ub := des; irw in H; dependent destruction H; clarify.
  Ltac sim_triggerUB := (try rename H into HH); gstep; ss; unfold triggerUB; try sim_red; econs 5; i; ss; auto;
                        [solve_ub | irw in  STEP; dependent destruction STEP; clarify].

  Ltac dtm H H0 := eapply angelic_step in H; eapply angelic_step in H0; des; rewrite H; rewrite H0; ss.



  Fixpoint expr_ord (e: Imp.expr): Ord.t :=
    match e with
    | Imp.Var _ => 20
    | Imp.Lit _ => 20
    | Imp.Eq e0 e1 => (20 + expr_ord e1 + 20 + expr_ord e0 + 20)%ord
    | Imp.Lt e0 e1 => (20 + expr_ord e1 + 20 + expr_ord e0 + 20)%ord
    | Imp.Plus e0 e1 => (20 + expr_ord e1 + 20 + expr_ord e0 + 20)%ord
    | Imp.Minus e0 e1 => (20 + expr_ord e1 + 20 + expr_ord e0 + 20)%ord
    | Imp.Mult e0 e1 => (20 + expr_ord e1 + 20 + expr_ord e0 + 20)%ord
    end.

  Lemma expr_ord_omega e:
    (expr_ord e < Ord.omega)%ord.
  Proof.
    assert (exists n: nat, (expr_ord e <= n)%ord).
    { induction e; ss.
      { eexists. refl. }
      { eexists. refl. }
      { des. eexists.
        rewrite IHe1. rewrite IHe2.
        rewrite <- ! OrdArith.add_from_nat. refl. }
      { des. eexists.
        rewrite IHe1. rewrite IHe2.
        rewrite <- ! OrdArith.add_from_nat. refl. }
      { des. eexists.
        rewrite IHe1. rewrite IHe2.
        rewrite <- ! OrdArith.add_from_nat. refl. }
      { des. eexists.
        rewrite IHe1. rewrite IHe2.
        rewrite <- ! OrdArith.add_from_nat. refl. }
      { des. eexists.
        rewrite IHe1. rewrite IHe2.
        rewrite <- ! OrdArith.add_from_nat. refl. }
    }
    des. eapply Ord.le_lt_lt; et. eapply Ord.omega_upperbound.
  Qed.

  Definition max_fuel := (Ord.omega * Ord.omega)%ord.

  Lemma max_fuel_spec2 e0 e1 (n: Ord.t) :
    (100 + expr_ord e0 + expr_ord e1 <= 100 + max_fuel + n)%ord.
  Proof.
    rewrite ! OrdArith.add_assoc. eapply OrdArith.le_add_r.
    etrans.
    2: { eapply OrdArith.add_base_l. }
    unfold max_fuel. etrans.
    2: {
      eapply OrdArith.le_mult_r.
      eapply Ord.lt_le. eapply Ord.omega_upperbound.
    }
    instantiate (1:=2). rewrite Ord.from_nat_S. rewrite Ord.from_nat_S.
    rewrite OrdArith.mult_S. rewrite OrdArith.mult_S.
    etrans.
    2:{ rewrite OrdArith.add_assoc. eapply OrdArith.add_base_r. }
    etrans.
    { eapply OrdArith.le_add_l. eapply Ord.lt_le. eapply expr_ord_omega. }
    { eapply OrdArith.le_add_r. eapply Ord.lt_le. eapply expr_ord_omega. }
  Qed.

  Lemma max_fuel_spec2' e0 e1 (n: Ord.t) :
    (100 + expr_ord e0 + expr_ord e1 <= (100 + max_fuel) + 100 + Ord.omega + n)%ord.
  Proof.
    set (temp:=(100 + expr_ord e0 + expr_ord e1)%ord).
    do 2 rewrite OrdArith.add_assoc.
    subst temp. eapply max_fuel_spec2.
  Qed.

  Lemma max_fuel_spec1 e (n: Ord.t) :
    (100 + expr_ord e <= 100 + max_fuel + n)%ord.
  Proof.
    etrans.
    2: { eapply max_fuel_spec2. }
    eapply OrdArith.add_base_l.
    Unshelve. all: exact e.
  Qed.

  Lemma max_fuel_spec1' e (n: Ord.t) :
    (100 + expr_ord e <= (100 + max_fuel) + 100 + Ord.omega + n)%ord.
  Proof.
    do 2 (rewrite OrdArith.add_assoc). eapply max_fuel_spec1.
  Qed.

  Lemma max_fuel_spec3 (args: list Imp.expr) (n: Ord.t) :
    (100 + Ord.omega * Datatypes.length args <= 100 + max_fuel + n)%ord.
  Proof.
    rewrite ! OrdArith.add_assoc. eapply OrdArith.le_add_r.
    etrans.
    2: { eapply OrdArith.add_base_l. }
    unfold max_fuel. eapply OrdArith.le_mult_r.
    eapply Ord.lt_le. eapply Ord.omega_upperbound.
  Qed.

  Lemma max_fuel_spec3' (args: list Imp.expr) (n: Ord.t) :
    (100 + Ord.omega * Datatypes.length args <= (100 + max_fuel) + 100 + Ord.omega + n)%ord.
  Proof.
    do 2 (rewrite OrdArith.add_assoc). eapply max_fuel_spec3.
  Qed.

  Lemma max_fuel_spec4 e (args: list Imp.expr) (n: Ord.t) :
    ((100 + Ord.omega * Datatypes.length args) + 100 + (expr_ord e) <= (100 + max_fuel) + 100 + Ord.omega + n)%ord.
  Proof.
    rewrite ! OrdArith.add_assoc.
    etrans.
    2:{ repeat rewrite <- OrdArith.add_assoc. eapply OrdArith.add_base_l. }
    etrans.
    2:{ instantiate (1:= (100 + (Ord.omega * Datatypes.length args) + (100 + Ord.omega))%ord).
        rewrite <- OrdArith.add_assoc. do 2 eapply OrdArith.le_add_l.
        eapply OrdArith.le_add_r. unfold max_fuel.
        eapply OrdArith.le_mult_r. eapply Ord.lt_le. eapply Ord.omega_upperbound.
    }
    rewrite ! OrdArith.add_assoc.
    do 3 eapply OrdArith.le_add_r. eapply Ord.lt_le. eapply expr_ord_omega.
  Qed.

  Lemma max_fuel_spec4' (args: list Imp.expr) (n: Ord.t) :
    (100 + Ord.omega * Datatypes.length args <= 100 + Ord.omega * Datatypes.length args + n)%ord.
  Proof.
    apply OrdArith.add_base_l.
  Qed.





  Lemma step_expr
        (src: ModL.t) (tgt: Csharpminor.program)
        e te
        tcode tf tcont tge tle tm
        r rg ms mn ge le pstate ktr
        i1
        (MLE: match_le srcprog le tle)
        (CEXP: compile_expr e = te)
        (SIM:
           forall rv trv,
             eval_expr tge empty_env tle tm te trv ->
             trv = map_val srcprog rv ->
             gpaco3 (_sim (compile_val src) (semantics tgt))
                    (cpn3 (_sim (compile_val src) (semantics tgt))) rg rg i1
                    (ktr (pstate, (le, rv)))
                    (State tf tcode tcont empty_env tle tm))
    :
      gpaco3 (_sim (compile_val src) (semantics tgt))
             (cpn3 (_sim (compile_val src) (semantics tgt)))
             r rg (i1 + expr_ord e)%ord
             (r0 <- EventsL.interp_Es (prog ms) (transl_all mn (interp_imp ge (denote_expr e) le)) (pstate);; ktr r0)
             (State tf tcode tcont empty_env tle tm).
  Proof.
    generalize dependent ktr. generalize dependent te.
    move MLE before pstate. revert_until MLE. revert r rg.
    generalize dependent e. Local Opaque Init.Nat.add. induction e; i; ss; des; clarify.
    - rewrite interp_imp_expr_Var. sim_red.
      destruct (alist_find v le) eqn:AFIND; try sim_red.
      + do 2 (gstep; sim_tau). red. sim_red.
        sim_ord.
        { eapply OrdArith.add_base_l. }
        eapply SIM; auto.
        econs. inv MLE. specialize ML with (x:=v) (sv:=v0).
        hexploit ML; auto.
      + sim_triggerUB.
    - rewrite interp_imp_expr_Lit.
      do 1 (gstep; sim_tau). red.
      sim_red.
      sim_ord.
      { eapply OrdArith.add_base_l. }
      eapply SIM; eauto. econs. unfold map_val. ss.

    - rewrite interp_imp_expr_Eq.
      sim_red.
      sim_ord.
      { instantiate (1:=((i1 + 20 + expr_ord e2 + 20) + expr_ord e1)%ord).
        rewrite <- ! OrdArith.add_assoc. eapply OrdArith.add_base_l. }
      eapply IHe1; auto. clear IHe1.
      i. sim_red.
      sim_ord.
      { instantiate (1:=(i1 + 20 + expr_ord e2)%ord).
        eapply OrdArith.add_base_l. }
      eapply IHe2; auto. clear IHe2.
      i. sim_red.
      destruct (wf_val rv && wf_val rv0) eqn:WFVAL.
      2: sim_triggerUB.
      sim_red. destruct rv; destruct rv0; try sim_triggerUB.
      2,3,4: gstep; ss; unfold triggerUB; try sim_red.
      des_ifs; ss; try sim_triggerUB.
      + sim_ord.
        { eapply OrdArith.add_base_l. }
        sim_red.
        eapply SIM; eauto.
        econs; eauto.
        { econs; eauto. }
        ss. f_equal. rewrite Z.eqb_eq in Heq. clarify.
        rewrite Int64.eq_true. ss.
      + sim_ord.
        { eapply OrdArith.add_base_l. }
        sim_red.
        eapply SIM; eauto.
        econs; eauto.
        { econs; eauto. }
        ss. f_equal.
        bsimpl. des. unfold_intrange_64. bsimpl. des.
        apply sumbool_to_bool_true in WFVAL.
        apply sumbool_to_bool_true in WFVAL0.
        apply sumbool_to_bool_true in WFVAL1.
        apply sumbool_to_bool_true in WFVAL2.
        rewrite Int64.signed_eq.
        rewrite ! Int64.signed_repr.
        2,3: unfold_Int64_max_signed; unfold_Int64_min_signed; lia.
        rewrite Z.eqb_neq in Heq. unfold Coqlib.proj_sumbool. des_ifs.
    - rewrite interp_imp_expr_Lt.
      sim_red.
      sim_ord.
      { instantiate (1:=((i1 + 20 + expr_ord e2 + 20) + expr_ord e1)%ord).
        rewrite <- ! OrdArith.add_assoc. eapply OrdArith.add_base_l. }
      eapply IHe1; auto. clear IHe1.
      i. sim_red.
      sim_ord.
      { instantiate (1:=(i1 + 20 + expr_ord e2)%ord).
        eapply OrdArith.add_base_l. }
      eapply IHe2; auto. clear IHe2.
      i. sim_red.
      destruct (wf_val rv && wf_val rv0) eqn:WFVAL.
      2: sim_triggerUB.
      sim_red. destruct rv; destruct rv0; try sim_triggerUB.
      2,3,4: gstep; ss; unfold triggerUB; try sim_red.
      des_ifs; ss; try sim_triggerUB.
      + sim_ord.
        { eapply OrdArith.add_base_l. }
        sim_red.        
        eapply SIM; eauto.
        econs; eauto.
        { econs; eauto. }
        ss. f_equal.
        bsimpl. des. unfold_intrange_64. bsimpl. des.
        apply sumbool_to_bool_true in WFVAL.
        apply sumbool_to_bool_true in WFVAL0.
        apply sumbool_to_bool_true in WFVAL1.
        apply sumbool_to_bool_true in WFVAL2.
        unfold Int64.lt. rewrite ! Int64.signed_repr.
        2,3: unfold_Int64_max_signed; unfold_Int64_min_signed; lia.
        des_ifs.
      + sim_ord.
        { eapply OrdArith.add_base_l. }
        sim_red.        
        eapply SIM; eauto.
        econs; eauto.
        { econs; eauto. }
        ss. f_equal.
        bsimpl. des. unfold_intrange_64. bsimpl. des.
        apply sumbool_to_bool_true in WFVAL.
        apply sumbool_to_bool_true in WFVAL0.
        apply sumbool_to_bool_true in WFVAL1.
        apply sumbool_to_bool_true in WFVAL2.
        unfold Int64.lt. rewrite ! Int64.signed_repr.
        2,3: unfold_Int64_max_signed; unfold_Int64_min_signed; lia.
        des_ifs.

    - rewrite interp_imp_expr_Plus.
      sim_red.
      sim_ord.
      { instantiate (1:=((i1 + 20 + expr_ord e2 + 20) + expr_ord e1)%ord).
        rewrite <- ! OrdArith.add_assoc. eapply OrdArith.add_base_l. }
      eapply IHe1; auto. clear IHe1.
      i. sim_red.
      sim_ord.
      { instantiate (1:=(i1 + 20 + expr_ord e2)%ord).
        eapply OrdArith.add_base_l. }
      eapply IHe2; auto. clear IHe2.
      i. sim_red.
      unfold unwrapU. destruct (vadd rv rv0) eqn:VADD; ss; clarify.
      + sim_red.
        specialize SIM with (rv:=v) (trv:= @map_val builtins srcprog v).
        sim_ord.
        { eapply OrdArith.add_base_l. }
        apply SIM; auto.
        econs; eauto. ss. f_equal. apply map_val_vadd_comm; auto.
      + sim_triggerUB.
    - rewrite interp_imp_expr_Minus.
      sim_red.
      sim_ord.
      { instantiate (1:=((i1 + 20 + expr_ord e2 + 20) + expr_ord e1)%ord).
        rewrite <- ! OrdArith.add_assoc. eapply OrdArith.add_base_l. }
      eapply IHe1; auto. clear IHe1.
      i. sim_red.
      sim_ord.
      { instantiate (1:=(i1 + 20 + expr_ord e2)%ord).
        eapply OrdArith.add_base_l. }
      eapply IHe2; auto. clear IHe2.
      i. sim_red.
      unfold unwrapU. destruct (vsub rv rv0) eqn:VSUB; ss; clarify.
      + sim_red.
        specialize SIM with (rv:=v) (trv:= @map_val builtins srcprog v).
        sim_ord.
        { eapply OrdArith.add_base_l. }
        apply SIM; auto.
        econs; eauto. ss. f_equal. apply map_val_vsub_comm; auto.
      + sim_triggerUB.
    - rewrite interp_imp_expr_Mult.
      sim_red.
      sim_ord.
      { instantiate (1:=((i1 + 20 + expr_ord e2 + 20) + expr_ord e1)%ord).
        rewrite <- ! OrdArith.add_assoc. eapply OrdArith.add_base_l. }
      eapply IHe1; auto. clear IHe1.
      i.
      sim_red.
      sim_ord.
      { instantiate (1:=(i1 + 20 + expr_ord e2)%ord).
        eapply OrdArith.add_base_l. }
      eapply IHe2; auto. clear IHe2.
      i. sim_red.
      unfold unwrapU. destruct (vmul rv rv0) eqn:VMUL; ss; clarify.
      + sim_red.
        specialize SIM with (rv:=v) (trv:= @map_val builtins srcprog v).
        sim_ord.
        { eapply OrdArith.add_base_l. }
        apply SIM; auto.
        econs; eauto. ss. f_equal. apply map_val_vmul_comm; auto.
      + sim_triggerUB.
  Qed.

  Lemma step_exprs
        (src: ModL.t) (tgt: Csharpminor.program)
        es tes
        tcode tf tcont tge tle tm
        r rg ms mn ge le pstate ktr
        i1
        (MLE: match_le srcprog le tle)
        (CEXP: compile_exprs es = tes)
        (SIM:
           forall rvs trvs,
             (* Forall wf_val rvs -> *)
             eval_exprlist tge empty_env tle tm tes trvs ->
             trvs = List.map (map_val srcprog) rvs ->
             gpaco3 (_sim (compile_val src) (semantics tgt)) (cpn3 (_sim (compile_val src) (semantics tgt))) r rg i1
                   (ktr (pstate, (le, rvs)))
                   (State tf tcode tcont empty_env tle tm))
    :
      gpaco3 (_sim (compile_val src) (semantics tgt))
             (cpn3 (_sim (compile_val src) (semantics tgt)))
             r rg (i1 + (Ord.omega * List.length es))%ord
            (r0 <- EventsL.interp_Es (prog ms) (transl_all mn (interp_imp ge (denote_exprs es) le)) (pstate);; ktr r0)
            (State tf tcode tcont empty_env tle tm).
  Proof.
    generalize dependent ktr. generalize dependent tes.
    move MLE before pstate. revert_until MLE.
    generalize dependent es. intros es. revert r rg. induction es; i; ss; des; clarify.
    - rewrite interp_imp_Ret. sim_red. sim_ord.
      { eapply OrdArith.add_base_l. }
      eapply SIM; eauto. econs.
    - eapply gpaco3_gen_guard.
      rewrite interp_imp_bind. sim_red.
      sim_ord.
      { instantiate (1:=((i1 + (Ord.omega * Datatypes.length es)) + expr_ord a)%ord).
        rewrite OrdArith.add_assoc. eapply OrdArith.le_add_r.
        rewrite Ord.from_nat_S. rewrite OrdArith.mult_S.
        eapply OrdArith.le_add_r. eapply Ord.lt_le. eapply expr_ord_omega. }
      eapply step_expr; eauto.
      i. rewrite interp_imp_bind. sim_red.
      eapply IHes; auto.
      i. rewrite interp_imp_Ret. sim_red.
      eapply gpaco3_mon; [eapply SIM|..]; auto.
      unfold compile_exprs in H2. econs; ss; clarify; eauto.
  Qed.

  Lemma compile_stmt_no_Sreturn
        src e
        (CSTMT: compile_stmt src = (Sreturn e))
    :
      False.
  Proof. destruct src; ss; uo; des_ifs; clarify. Qed.





  (**** At the moment, it suffices to support integer IO in our scenario,
        and we simplify all the other aspects.
        e.g., the system calls that we are aware of
        (1) behaves irrelevant from Senv.t,
        (2) does not allow arguments/return values other than integers,
        (3) produces exactly one event (already in CompCert; see: ec_trace_length),
        (4) does not change memory,
        (5) always returns without stuck,
        and (6) we also assume that it refines our notion of system call.
   ****)
  Axiom syscall_exists: forall fn sg se args_tgt m0, exists tr ret_tgt m1,
        <<TGT: external_functions_sem fn sg se args_tgt m0 tr ret_tgt m1>>
  .
  Axiom syscall_refines:
    forall fn sg args_tgt ret_tgt
           se m0 tr m1
           (TGT: external_functions_sem fn sg se args_tgt m0 tr ret_tgt m1)
    ,
      exists args_int ret_int ev,
        (<<ARGS: args_tgt = (List.map Values.Vlong args_int)>>) /\
        (<<RET: ret_tgt = (Values.Vlong ret_int)>>) /\
        let args_src := List.map Int64.signed args_int in
        let ret_src := Int64.signed ret_int in
        (<<EV: tr = [ev] /\ decompile_event ev = Some (event_sys fn args_src↑ ret_src↑)>>)
        /\ (<<SRC: syscall_sem (event_sys fn args_src↑ ret_src↑)>>)
        /\ (<<MEM: m0 = m1>>)
  .





  Hypothesis map_blk_after_init :
    forall src blk
      (COMP : exists tgt, Imp2Csharpminor.compile src = OK tgt)
      (ALLOCED : blk >= (src_init_nb src)),
      (<<ALLOCMAP: (map_blk src blk) = Pos.of_succ_nat (tgt_init_len + (ext_len src) + (int_len src - sk_len src) + blk)>>).

  Hypothesis map_blk_inj :
    forall src b1 b2
      (COMP : exists tgt, Imp2Csharpminor.compile src = OK tgt)
      (WFPROG: incl (name1 src.(defsL)) ((name1 src.(prog_varsL)) ++ (name2 src.(prog_funsL))))
      (WFSK: Sk.wf src.(defsL)),
      <<INJ: map_blk src b1 = map_blk src b2 -> b1 = b2>>.

  (* Context {WFPROG: Permutation.Permutation *)
  (*                    ((List.map fst srcprog.(prog_varsL)) ++ (List.map (compose fst snd) srcprog.(prog_funsL))) *)
  (*                    (List.map fst srcprog.(defsL)) /\ Sk.wf srcprog.(defsL)}. *)

  Theorem match_states_sim
          tgt
          (modl: ModL.t) ge ms
          ist cst
          (MODL: modl = (ModL.add (Mod.lift (Mem (fun _ => false))) (ImpMod.get_modL srcprog)))
          (MODSEML: ms = modl.(ModL.enclose))
          (GENV: ge = Sk.load_skenv (Sk.sort modl.(ModL.sk)))
          (MGENV: match_ge srcprog ge (Genv.globalenv tgt))
          (COMP: Imp2Csharpminor.compile srcprog = OK tgt)
          (MS: match_states ge ms srcprog ist cst)
          (WFPROG: incl (name1 srcprog.(defsL)) ((name1 srcprog.(prog_varsL)) ++ (name2 srcprog.(prog_funsL))))
          (WFPROG2: forall blk name, (ge.(SkEnv.blk2id) blk = Some name) -> call_ban name = false)
          (WFSK: Sk.wf srcprog.(defsL))
    :
      <<SIM: sim (compile_val modl) (semantics tgt) ((100 + max_fuel) + 100 + Ord.omega + 100)%ord ist cst>>.
  Proof.
    red. red. ginit.
    depgen ist. depgen cst. gcofix CIH. i.
    assert (EXISTSCOMP: exists tgt, Imp2Csharpminor.compile srcprog = OK tgt); eauto.
    inv MS. unfold Imp2Csharpminor.compile in COMP. des_ifs_safe.
    match goal with | [ MGENV: match_ge _ _ (Genv.globalenv ?_tgt) |- _ ] => set (tgt:=_tgt) in * end.
    destruct code.
    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. ss; clarify.
      destruct tcont; ss; clarify. inv MCONT; clarify.
      { unfold itree_of_imp_ret, itree_of_imp_cont. unfold exit_stmt in *; ss; clarify.
        destruct tcont; inv MSTACK; ss; clarify. sim_red. gstep. econs 6; clarify.
        eexists. eexists.
        { eapply step_skip_seq. }
        eexists. exists (step_tau _). eexists. sim_red.

        rewrite interp_imp_expr_Var. sim_red. unfold unwrapU. des_ifs.
        2:{ sim_triggerUB. }
        sim_red. gstep. econs 6; clarify.
        eexists. eexists.
        { eapply step_return_1; ss; eauto. econs; ss. econs; ss. inv ML; ss; clarify. hexploit ML0; i; eauto. }
        eexists. exists (step_tau _). eexists.
        do 1 (gstep; sim_tau). red. sim_red.
        unfold itree_of_imp_pop_bottom. sim_red.
        destruct v.
        - destruct ((0 <=? n)%Z && (n <? two_power_nat 32)%Z) eqn:INT32; bsimpl; des.
          + gstep. econs 1; eauto.
            { unfold Int.max_unsigned. unfold_Int_modulus. instantiate (1:=n). lia. }
            { ss. unfold state_sort; ss. rewrite Any.upcast_downcast. des_ifs. }
            ss. unfold Int64.loword. rewrite Int64.unsigned_repr.
            2:{ unfold Int64.max_unsigned. unfold_Int64_modulus. unfold two_power_nat in *. ss. lia. }
            econs.
          + gstep. econs 5; ss; eauto.
            { unfold state_sort; ss. rewrite Any.upcast_downcast. des_ifs. }
            { i. inv H. }
            i. inv STEP.
          + gstep. econs 5; ss; eauto.
            { unfold state_sort; ss. rewrite Any.upcast_downcast. des_ifs. bsimpl. clarify. }
            { i. inv H. }
            i. inv STEP.

        - gstep. econs 5; ss; eauto.
          { unfold state_sort; ss. rewrite Any.upcast_downcast. des_ifs. }
          { i. inv H. }
          i. inv STEP.
        - gstep. econs 5; ss; eauto.
          { unfold state_sort; ss. rewrite Any.upcast_downcast. des_ifs. }
          { i. inv H. }
          i. inv STEP.
      }

      { unfold return_stmt in *; ss; clarify. destruct tcont; inv MSTACK; ss; clarify.
        sim_red. gstep. econs 6; clarify.
        eexists. eexists.
        { eapply step_skip_seq. }
        eexists. exists (step_tau _). eexists. unfold idK. sim_red.

        rewrite interp_imp_expr_Var. sim_red.
        unfold unwrapU. des_ifs.
        2:{ sim_triggerUB. }
        sim_red. gstep. econs 6; clarify.
        eexists. eexists.
        { eapply step_return_1; ss; eauto. econs; ss. inv ML; ss; clarify. hexploit ML0; i; eauto. }
        eexists. exists (step_tau _). eexists.
        do 4 (gstep; sim_tau). red. sim_red.
        rewrite Any.upcast_downcast. sim_red.
        gstep. econs 6; clarify.
        eexists. eexists.
        { eapply step_return. }
        eexists. exists (step_tau _). eexists.
        do 1 (gstep; sim_tau).
        sim_ord.
        { eapply OrdArith.add_base_l. }
        gbase. apply CIH.
        unfold ret_call_cont in TPOP. unfold return_stmt in TPOP. ss; clarify.
        hexploit match_states_intro.
        { instantiate (2:=Skip). ss. }
        2,3,4,5,6: eauto.
        2: clarify.
        2:{ i.
            match goal with
            | [ H : match_states _ _ _ ?i0 _ |- match_states _ _ _ ?i1 _ ] =>
              replace i1 with i0; eauto
            end.
            unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
        econs. i. eapply alist_update_le; eauto. }

      sim_red. gstep. econs 6; clarify.
      eexists. eexists.
      { eapply step_skip_seq. }
      eexists. eexists (step_tau _). eexists. sim_red. gbase. eapply CIH. hexploit match_states_intro; eauto.
      all: (destruct (compile_stmt code) eqn: CST; eauto; apply compile_stmt_no_Sreturn in CST; clarify).

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Assign. sim_red. ss.
      sim_ord.
      { eapply max_fuel_spec1'. }
      eapply step_expr; eauto. i.
      (* tau point *)
      do 1 (gstep; sim_tau). red. sim_red.
      gstep. econs 6; auto.
      eexists. eexists.
      { eapply step_set. eapply H. }
      eexists. eexists.
      { eapply step_tau. }
      eexists. gbase. apply CIH. hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      2,3,4,5,6,7:eauto.
      2:{ unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. eauto. }
      { econs. i. eapply alist_update_le; eauto. }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Seq. sim_red. ss.
      (* tau point *)
      gstep. econs 6; ss; clarify.
      eexists. eexists.
      { eapply step_seq. }
      eexists. exists (step_tau _). eexists. gbase. eapply CIH. hexploit match_states_intro.
      { instantiate (2:=code1). ss. }
      4:{ instantiate (1:=Kseq (compile_stmt code2) tcont). ss. destruct (compile_stmt code2) eqn:CSC2; eauto.
          eapply compile_stmt_no_Sreturn in CSC2; clarify. }
      4:{ econs 3; eauto. }
      all: eauto.
      { ss. destruct (compile_stmt code2) eqn:CSC2; eauto. eapply compile_stmt_no_Sreturn in CSC2; clarify. }
      i.
      match goal with
      | [ H: match_states _ _ _ ?it0 _ |- match_states _ _ _ ?it1 _ ] =>
        replace it1 with it0; eauto
      end.
      unfold itree_of_cont_stmt, itree_of_imp_cont. Red.prw ltac:(_red_gen) 1 0. grind.

    - unfold itree_of_cont_stmt in *; unfold itree_of_imp_cont in *. rewrite interp_imp_If. sim_red. ss.
      sim_ord.
      { eapply max_fuel_spec1'. }
      eapply step_expr; eauto.
      i. des_ifs.
      2:{ sim_triggerUB. }

      sim_red. destruct (is_true rv) eqn:COND; ss; clarify.
      2:{ sim_triggerUB. }
      sim_red. destruct rv; clarify. ss. destruct (n =? 0)%Z eqn:CZERO; ss; clarify.
      { rewrite Z.eqb_eq in CZERO. clarify.
        (* tau point *)
        gstep. econs 6; ss.
        eexists. eexists.
        { eapply step_ifthenelse; ss. econs; eauto.
          + econs. ss.
          + ss. }
        eexists. eexists.
        { eapply step_tau. }
        eexists. des_ifs. gbase. eapply CIH. hexploit match_states_intro; eauto. }
      { rewrite Z.eqb_neq in CZERO.
        (* tau point *)
        gstep. econs 6; ss.
        eexists. eexists.
        { eapply step_ifthenelse.
          - econs; eauto.
            + econs. ss.
            + ss.
          - ss. destruct (negb (Int64.eq (Int64.repr n) Int64.zero)) eqn:CONTRA; ss; clarify.
            rewrite negb_false_iff in CONTRA. apply Int64.same_if_eq in CONTRA.
            unfold Int64.zero in CONTRA. unfold_intrange_64. bsimpl. des.
            apply sumbool_to_bool_true in Heq.
            apply sumbool_to_bool_true in Heq0.
            hexploit Int64.signed_repr.
            { unfold_Int64_max_signed. unfold_Int64_min_signed. instantiate (1:=n). nia. }
            i. rewrite CONTRA in H0. rewrite Int64.signed_repr_eq in H0. des_ifs. }
        eexists. exists (step_tau _).
        eexists. des_ifs. gbase. eapply CIH. hexploit match_states_intro; eauto. }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_CallFun.
      ss. des_ifs; sim_red.
      { sim_triggerUB. }
      assert (COMP2: Imp2Csharpminor.compile srcprog = OK tgt).
      { unfold Imp2Csharpminor.compile. des_ifs; auto. }
      sim_ord.
      { eapply max_fuel_spec3'. }
      eapply step_exprs; eauto.
      i. sim_red.
      grind. do 1 (gstep; sim_tau). sim_red.
      match goal with
      | [ |- gpaco3 _ _ _ _ _ (r0 <- unwrapU (?f);; _) _ ] => destruct f eqn:FSEM; ss
      end.
      2:{ sim_triggerUB. }
      unfold call_ban in Heq. bsimpl; des. des_ifs; clarify.
      rename Heq0 into NOTMAIN. apply neg_rel_dec_correct in NOTMAIN.
      repeat match goal with | [ Heq: _ = false |- _ ] => clear Heq end.

      grind. rewrite alist_find_find_some in FSEM. rewrite find_map in FSEM.
      match goal with
      | [ FSEM: o_map (?a) _ = _ |- _ ] => destruct a eqn:FOUND; ss; clarify
      end.
      destruct p. destruct p. clarify. 
      rewrite Sk.add_unit_l in FOUND.
      eapply found_imp_function in FOUND. des; clarify.
      hexploit in_tgt_prog_defs_ifuns; eauto. i.
      des. rename H0 into COMPF.
      (* assert (INTGT: In (s2p f, Gfun (Internal tf0)) (prog_defs tgtp)); auto. *)
      rename s into mn2, f into fn, f0 into impf.
      assert (COMPF2: In (compile_iFun (mn2, (fn, impf))) (prog_defs tgt)); auto.
      eapply Globalenvs.Genv.find_symbol_exists in COMPF.
      destruct COMPF as [b TGTFG].
      assert (TGTGFIND: Globalenvs.Genv.find_def (Globalenvs.Genv.globalenv tgt) b = Some (snd (compile_iFun (mn2, (fn, impf))))).
      { hexploit tgt_genv_find_def_by_blk; eauto. }

      unfold cfunU. sim_red.
      rewrite unfold_eval_imp_only.
      grind. des_ifs.
      2,3,4: sim_triggerUB.
      rename n into WFFUN, Heq into ARGS. sim_red.
      rewrite interp_imp_tau. sim_red.

      gstep. econs 6; auto.
      eexists. eexists.
      { eapply step_call; eauto.
        - econs. econs 2.
          { apply Maps.PTree.gempty. }
          eapply TGTFG.
        - rewrite Globalenvs.Genv.find_funct_find_funct_ptr.
          rewrite Globalenvs.Genv.find_funct_ptr_iff. ss. eapply TGTGFIND.
        - ss. apply init_args_prop in ARGS. rewrite map_length. des. setoid_rewrite ARGS.
          des_ifs; eauto.
          { rewrite eq_rel_dec_correct in Heq. des_ifs. }
          depgen H. clear. i.
          apply eval_exprlist_length in H. des. unfold compile_exprs in H. rewrite ! map_length in H.
          rewrite H. ss.
      }
      eexists. exists (step_tau _). eexists.

      hexploit initial_lenv_match; eauto. i. des; ss; clarify. instantiate (1:=srcprog) in MLINIT.
      gstep. econs 4.
      eexists. eexists.
      { rewrite <- NoDup_norepeat in WFFUN. apply Coqlib.list_norepet_app in WFFUN. des.
        eapply step_internal_function; ss; eauto; try econs.
        { apply Coqlib.list_map_norepet; eauto. i. ii. apply H2. apply s2p_inj; auto. }
        { unfold Coqlib.list_disjoint in *. depgen WFFUN1. clear. i.
          apply Coqlib.list_in_map_inv in H. apply in_app_or in H0. des.
          - apply Coqlib.list_in_map_inv in H0. des. clarify.
            ii. apply s2p_inj in H. hexploit WFFUN1; eauto. apply in_or_app. left; auto.
          - ii. clarify. hexploit WFFUN1; eauto. apply in_or_app. right; auto.
            match goal with
            | [ H0: In _ ?ml |- In _ ?ll ] => replace ml with (List.map s2p ll) end; ss; des; eauto.
            apply s2p_inj in H0; auto. apply s2p_inj in H0; auto.
        }
        rewrite map_app in BIND. ss. eapply BIND.
      }
      eexists; split; [ord_step2|].

      des_ifs.
      { rewrite rel_dec_correct in Heq; clarify. }
      clear Heq.

      gstep. econs 4.
      eexists. eexists.
      { eapply step_seq. }
      eexists; split; [ord_step2|].
      sim_ord.
      { eapply OrdArith.add_base_l. }
      gbase. eapply CIH.
      match goal with
      | [ |- match_states ?_ge _ _ _ _ ] =>
        set (ge:=_ge) in *
      end.
      match goal with
      | [ |- match_states _ ?_ms _ _ _ ] =>
        set (ms:=_ms) in *
      end.
      match goal with
      | [ |- match_states _ _ _ (?i) _] =>
        replace i with
    (` r0 : p_state * (lenv * val) <-
     EventsL.interp_Es (prog ms)
                       (transl_all mn2 (interp_imp ge (denote_stmt (Imp.fn_body impf)) l0))
       (pstate);; x4 <- itree_of_imp_pop ge ms mn2 mn x le r0;; ` x : _ <- next x4;; stack x)
      end.
      2:{ rewrite interp_imp_bind. Red.prw ltac:(_red_gen) 1 0. grind.
          Red.prw ltac:(_red_gen) 2 0. grind.
          Red.prw ltac:(_red_gen) 2 0. Red.prw ltac:(_red_gen) 1 0. grind. }

      hexploit match_states_intro.
      5:{ instantiate (1:=Kseq (Sreturn (Some (Evar (s2p "return")))) (Kcall (Some (s2p x)) tf empty_env tle tcont)). ss. }
      6:{ instantiate (1:= fun r0 =>
                             ` x4 : p_state * (lenv * val) <- itree_of_imp_pop ge ms mn2 mn x le r0;;
                                    ` x0 : p_state * (lenv * val) <- next x4;; stack x0).
          instantiate (1:=mn2). instantiate (1:=srcprog). instantiate (1:=ms). instantiate (1:=ge).
          econs 2; ss; eauto. }
      3,4: eauto.
      1:{ instantiate (2:= (Imp.fn_body impf)). ss. }
      2:{ ss. econs 2. }
      2:{ clarify. }
      2:{ i.
          match goal with
          | [ H1: match_states _ _ _ ?i0 _ |- match_states _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. unfold idK. grind. }
      { eauto. }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_CallPtr.
      des_ifs.
      2,3,4,5,6,7: sim_triggerUB.
      clear Heq.
      sim_red.
      sim_ord.
      { eapply max_fuel_spec4. }
      grind. eapply step_expr; eauto. i. rename H0 into TGTEXPR. clarify.
      des_ifs.
      1,3,4,5,6: try sim_triggerUB.
      gstep; sim_tau.

      assert (COMP2: Imp2Csharpminor.compile srcprog = OK tgt).
      { unfold Imp2Csharpminor.compile. des_ifs; auto. }
      sim_ord.
      { eapply max_fuel_spec4'. }
      sim_red. eapply step_exprs; eauto.
      i. sim_red.
      grind. do 1 (gstep; sim_tau). sim_red.
      match goal with
      | [ |- gpaco3 _ _ _ _ _ (r0 <- unwrapU (?f);; _) _ ] => destruct f eqn:FSEM; ss
      end.
      2:{ sim_triggerUB. }

      des_ifs; ss; clarify.
      { apply rel_dec_correct in Heq0. unfold call_ban in WFPROG2. apply WFPROG2 in Heq. bsimpl. des.
        apply neg_rel_dec_correct in Heq. clarify. }
      { apply rel_dec_correct in Heq1. unfold call_ban in WFPROG2. apply WFPROG2 in Heq. bsimpl. des.
        apply neg_rel_dec_correct in Heq6. clarify. }
      { apply rel_dec_correct in Heq2. unfold call_ban in WFPROG2. apply WFPROG2 in Heq. bsimpl. des.
        apply neg_rel_dec_correct in Heq6. clarify. }
      { apply rel_dec_correct in Heq3. unfold call_ban in WFPROG2. apply WFPROG2 in Heq. bsimpl. des.
        apply neg_rel_dec_correct in Heq6. clarify. }
      { apply rel_dec_correct in Heq4. unfold call_ban in WFPROG2. apply WFPROG2 in Heq. bsimpl. des.
        apply neg_rel_dec_correct in Heq6. clarify. }
      repeat match goal with | [ Heq: _ = false |- _ ] => clear Heq end.

      assert (NOTMAIN: s <> "main").
      { depgen WFPROG2. depgen Heq. clear; i. apply WFPROG2 in Heq.
        unfold call_ban in Heq. bsimpl; des.  apply neg_rel_dec_correct in Heq0. ss. }

      grind. rewrite alist_find_find_some in FSEM. rewrite find_map in FSEM.
      match goal with
      | [ FSEM: o_map (?a) _ = _ |- _ ] => destruct a eqn:FOUND; ss; clarify
      end.
      destruct p. destruct p. clarify. 
      rewrite Sk.add_unit_l in FOUND.
      eapply found_imp_function in FOUND. des; clarify.
      hexploit in_tgt_prog_defs_ifuns; eauto. i.
      des. rename H1 into COMPF. clear FOUND.
      rename s0 into mn2, s into fn, f into impf.
      assert (COMPF2: In (compile_iFun (mn2, (fn, impf))) (prog_defs tgt)); auto.
      eapply Globalenvs.Genv.find_symbol_exists in COMPF.
      destruct COMPF as [b TGTFG].
      assert (TGTGFIND: Globalenvs.Genv.find_def (Globalenvs.Genv.globalenv tgt) b = Some (snd (compile_iFun (mn2, (fn, impf))))).
      { hexploit tgt_genv_find_def_by_blk; eauto. }

      unfold cfunU. sim_red.
      rewrite unfold_eval_imp_only.
      grind. des_ifs.
      2,3,4: sim_triggerUB.
      sim_red.
      rename n into WFFUN. grind.
      inv MGENV. apply Sk.sort_wf in WFSK.
      assert (BBLK: (map_blk srcprog blk) = b).
      { apply Sk.load_skenv_wf in WFSK. apply WFSK in Heq. apply MG in Heq. clarify. }
      clarify.

      rename Heq0 into ARGS.
      rewrite interp_imp_tau. sim_red.
      gstep. econs 6; auto.
      eexists. eexists.
      { eapply step_call; eauto.
        - rewrite Globalenvs.Genv.find_funct_find_funct_ptr.
          rewrite Globalenvs.Genv.find_funct_ptr_iff. ss. eapply TGTGFIND.
        - ss. apply init_args_prop in ARGS. rewrite map_length. des. setoid_rewrite ARGS.
          des_ifs.
          { rewrite rel_dec_correct in Heq0; clarify. }
          depgen H0. clear. i.
          apply eval_exprlist_length in H0. des. unfold compile_exprs in H0. rewrite ! map_length in H0.
          rewrite H0. ss.
      }
      eexists. exists (step_tau _). eexists.

      hexploit initial_lenv_match; eauto. i. des; ss; clarify. instantiate (1:=srcprog) in MLINIT.
      gstep. econs 4.
      eexists. eexists.
      { rewrite <- NoDup_norepeat in WFFUN. apply Coqlib.list_norepet_app in WFFUN. des.
        eapply step_internal_function; ss; eauto; try econs.
        { apply Coqlib.list_map_norepet; eauto. i. ii. apply H3. apply s2p_inj; auto. }
        { unfold Coqlib.list_disjoint in *. depgen WFFUN1. clear. i.
          apply Coqlib.list_in_map_inv in H. apply in_app_or in H0. des.
          - apply Coqlib.list_in_map_inv in H0. des. clarify.
            ii. apply s2p_inj in H. hexploit WFFUN1; eauto. apply in_or_app. left; auto.
          - ii. clarify. hexploit WFFUN1; eauto. apply in_or_app. right; auto.
            match goal with
            | [ H0: In _ ?ml |- In _ ?ll ] => replace ml with (List.map s2p ll) end; ss; des; eauto.
            apply s2p_inj in H0; auto. apply s2p_inj in H0; auto.
        }
        rewrite map_app in BIND. ss. eapply BIND.
      }
      eexists; split; [ord_step2|].

      des_ifs.
      { rewrite rel_dec_correct in Heq0; clarify. }
      gstep. econs 4.
      eexists. eexists.
      { eapply step_seq. }
      eexists; split; [ord_step2|].
      sim_ord.
      { eapply OrdArith.add_base_l. }
      gbase. eapply CIH.
      match goal with
      | [ |- match_states ?_ge _ _ _ _ ] =>
        set (ge:=_ge) in *
      end.
      match goal with
      | [ |- match_states _ ?_ms _ _ _ ] =>
        set (ms:=_ms) in *
      end.
      match goal with
      | [ |- match_states _ _ _ (?i) _] =>
        replace i with
    (` r0 : p_state * (lenv * val) <-
     EventsL.interp_Es (prog ms)
                       (transl_all mn2 (interp_imp ge (denote_stmt (Imp.fn_body impf)) l0))
       (pstate);; x4 <- itree_of_imp_pop ge ms mn2 mn x le r0;; ` x : _ <- next x4;; stack x)
      end.
      2:{ rewrite interp_imp_bind. Red.prw ltac:(_red_gen) 1 0. grind.
          Red.prw ltac:(_red_gen) 2 0. grind.
          Red.prw ltac:(_red_gen) 2 0. Red.prw ltac:(_red_gen) 1 0. grind. }

      hexploit match_states_intro.
      5:{ instantiate (1:=Kseq (Sreturn (Some (Evar (s2p "return")))) (Kcall (Some (s2p x)) tf empty_env tle tcont)). ss. }
      6:{ instantiate (1:= fun r0 =>
                             ` x4 : p_state * (lenv * val) <- itree_of_imp_pop ge ms mn2 mn x le r0;;
                                    ` x0 : p_state * (lenv * val) <- next x4;; stack x0).
          instantiate (1:=mn2). instantiate (1:=srcprog). instantiate (1:=ms). instantiate (1:=ge).
          econs 2; ss; eauto. }
      3,4: eauto.
      1:{ instantiate (2:= (Imp.fn_body impf)). ss. }
      2:{ ss. econs 2. }
      2:{ clarify. }
      2:{ i.
          match goal with
          | [ H1: match_states _ _ _ ?i0 _ |- match_states _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. unfold idK. grind. }
      { eauto. }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_CallSys.
      ss. sim_red. unfold unwrapU. des_ifs.
      2:{ sim_triggerUB. }
      rename Heq into FOUND.
      sim_red.

      apply alist_find_some in FOUND.
      assert (COMP2: Imp2Csharpminor.compile srcprog = OK tgt).
      { unfold Imp2Csharpminor.compile. des_ifs; ss; auto. }
      hexploit in_tgt_prog_defs_c_sys; eauto. i. rename H into INTGT.
      hexploit Genv.find_symbol_exists; eauto. i. des. rename H into FINDSYM.
      hexploit tgt_genv_find_def_by_blk; eauto. i. rename H into FINDDEF.

      des_ifs.
      2: sim_triggerUB.
      rewrite Nat.eqb_eq in Heq. clarify.
      sim_red.
      sim_ord.
      { eapply max_fuel_spec3'. }
      eapply step_exprs; eauto.
      i.
      des_ifs.
      2,3,4: sim_triggerUB.
      rename Heq0 into WFARGS.
      sim_red.
      gstep. econs 4.
      eexists. eexists.
      { eapply step_call; eauto.
        - econs. econs 2.
          { eapply Maps.PTree.gempty. }
          simpl. apply FINDSYM.
        - simpl. des_ifs. unfold Genv.find_funct_ptr.
          rewrite FINDDEF. ss.
        - ss. }
      eexists; split; [ord_step2|].

      (* System call semantics *)
      set (trvs:= List.map (map_val srcprog) rvs) in *.
      pose (syscall_exists f (make_signature (List.length args)) (Genv.globalenv tgt) trvs tm) as TGTSYSSEM. des.
      hexploit syscall_refines; eauto. i. ss. des. clarify.

      gstep. econs 2; auto.
      { eexists. eexists. eapply step_external_function. ss. eauto. }
      clear TGT EV0 SRC ARGS ev ret_int args_int.
      (* rename H into WFARGS. *)
      rename H into TGTARGS.
      i. inv STEP. ss. rename H5 into TGT.
      hexploit syscall_refines; eauto. i; ss; des; clarify.

      assert (SRCARGS: rvs = (List.map (Vint ∘ Int64.signed) args_int)).
      { depgen ARGS. depgen WFARGS. subst trvs. clear. depgen rvs. induction args_int; i; ss; clarify.
        - apply map_eq_nil in ARGS. auto.
        - destruct rvs; ss; clarify. bsimpl. des.
          f_equal; ss; eauto.
          unfold map_val in H1. des_ifs.
          f_equal. hexploit Int64.signed_repr; eauto.
          ss. unfold_intrange_64. bsimpl. des.
          apply sumbool_to_bool_true in WFARGS.
          apply sumbool_to_bool_true in WFARGS1.
          unfold_Int64_max_signed; unfold_Int64_min_signed; lia.
      }

      eexists. eexists. eexists.
      { hexploit step_syscall.
        (* { eauto. } *)
        (* { instantiate (1:=top1). ss. } *)
        3:{ i. rename H into SYSSTEP.
            match goal with
            | [ SYSSTEP: step ?i0 _ _ |- step ?i1 _ _ ] =>
              replace i1 with i0; eauto
            end.
            rewrite bind_trigger. ss. }
        { match goal with
          | [ SRC: syscall_sem (event_sys _ ?args0 _) |- syscall_sem (event_sys _ ?args1 _) ] =>
            replace args1 with args0; eauto
          end.
          rewrite SRCARGS. rewrite List.map_map. ss. }
        ss.
      }

      split.
      { unfold decompile_event in EV0. des_ifs. uo; des_ifs; ss; clarify.
        unfold decompile_eval in Heq2. des_ifs; ss; clarify. econs; auto.
        apply Any.upcast_inj in H0. des; ss.
        apply Any.upcast_inj in H1. des; ss.
        econs.
        2:{ rewrite <- EQ0. econs. }
        generalize dependent Heq1. depgen EQ2. clear. generalize dependent args_int. depgen l1.
        induction l0; i; ss; clarify.
        { destruct args_int; ss; clarify. }
        des_ifs. uo; des_ifs; ss. destruct args_int; ss; clarify.
        econs; eauto. unfold decompile_eval in Heq. des_ifs. rewrite <- H0. econs. }

      eexists.
      do 5 (gstep; sim_tau).
      sim_red. rewrite Any.upcast_downcast. sim_red.
      do 2 (gstep; sim_tau).
      gstep. econs 4.
      eexists. eexists.
      { eapply step_return. }
      eexists; split; [ord_step2|].
      sim_ord.
      { eapply OrdArith.add_base_l. }
      gbase. eapply CIH.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      2,3,4,5,6: eauto.
      2: clarify.
      2:{ i.
          match goal with
          | [ H1: match_states _ _ _ ?i0 _ |- match_states _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { econs. i. simpl. set (vv:=Vint (Int64.signed ret_int)) in *.
        replace (Values.Vlong ret_int) with (map_val srcprog vv).
        2:{ ss. rewrite Int64.repr_signed; ss. }
        eapply alist_update_le; eauto. }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_AddrOf.
      ss. unfold unwrapU. des_ifs.
      2:{ sim_triggerUB. }
      rename n into blk, Heq into SRCBLK.
      do 2 (gstep; sim_tau). sim_red.
      gstep. econs 6; ss.
      eexists. eexists.
      { eapply step_set. econs. econs 2.
        { apply Maps.PTree.gempty. }
        inv MGENV. specialize MG with (symb:=X) (blk:=blk). apply MG. auto. }
      eexists. exists (step_tau _). eexists. gbase. apply CIH.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      2,3,4,5,6: eauto.
      2: clarify.
      2:{ i.
          match goal with
          | [ H: match_states _ _ _ ?i0 _ |- match_states _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { econs. i. set (vv:=Vptr blk 0) in *.
        replace (Values.Vptr (map_blk srcprog blk) Ptrofs.zero) with (map_val srcprog vv).
        2:{ ss. }
        eapply alist_update_le; eauto. }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Malloc. sim_red.
      ss.
      sim_ord.
      { eapply max_fuel_spec1'. }
      eapply step_expr; eauto. i. rename H0 into MAPRV. sim_red.
      do 1 (gstep; sim_tau). sim_red.
      match goal with
      | [ MCONT: match_code ?_ge _ _ _ _ |- _ ] =>
        set (ge:=_ge) in *
      end.
      match goal with
      | [ MCONT: match_code _ ?_ms _ _ _ |- _ ] =>
        set (ms:=_ms) in *
      end.
      unfold cfunU.
      unfold allocF. sim_red.
      do 3 (gstep; sim_tau). sim_red.
      rewrite PSTATE. rewrite Any.upcast_downcast. grind. unfold unint. des_ifs; sim_red.
      2,3: sim_triggerUB.
      des_ifs.
      2: sim_triggerUB.
      bsimpl. des. sim_red.
      rename Heq into NRANGE1. apply sumbool_to_bool_true in NRANGE1.
      rename Heq0 into NRANGE2. apply sumbool_to_bool_true in NRANGE2.

      assert (COMP2: Imp2Csharpminor.compile srcprog = OK tgt).
      { unfold Imp2Csharpminor.compile. des_ifs; ss; auto. }
      assert (TGTDEFS: In (s2p "malloc", Gfun (External EF_malloc)) (prog_defs tgt)).
      { eapply in_tgt_prog_defs_init_g; eauto.
        Local Transparent init_g. Local Transparent init_g0.
        unfold init_g, init_g0. rewrite map_app. rewrite in_app_iff. right. ss. eauto.
        Local Opaque init_g. Local Opaque init_g0. }

      assert (TGTMALLOC: exists blk, Genv.find_symbol (globalenv (semantics tgt)) (s2p "malloc") = Some blk).
      { hexploit Genv.find_symbol_exists; eauto. }
      des.
      hexploit tgt_genv_find_def_by_blk; eauto. i. rename H0 into TGTFINDDEF.

      gstep. econs 6; clarify.
      eexists. eexists.
      { eapply step_call.
        - econs. econs 2.
          { eapply Maps.PTree.gempty. }
          apply TGTMALLOC.
        - econs 2; eauto.
          + econs 5; try econs; eauto.
          + econs 1.
        - ss. des_ifs. unfold Genv.find_funct_ptr. rewrite TGTFINDDEF. ss.
        - ss. }
      eexists. eexists.
      { rewrite bind_trigger. eapply (step_choose _ 0). }
      eexists.
      do 9 (gstep; sim_tau). sim_red.
      do 2 (gstep; sim_tau).

      unfold Int64.mul. rewrite! Int64.unsigned_repr; ss.
      2:{ split; ss. unfold_modrange_64. unfold Int64.max_unsigned. unfold_Int64_modulus. lia. }

      assert (TGTALLOC: forall tm ch sz, Memory.Mem.alloc tm ch sz = (fst (Memory.Mem.alloc tm ch sz), snd (Memory.Mem.alloc tm ch sz))).
      { clear. i. ss. }

      pose (Mem.valid_access_store (fst (Memory.Mem.alloc tm (- size_chunk Mptr) (8 * n))) Mptr
                                   (snd (Memory.Mem.alloc tm (- size_chunk Mptr) (8 * n))) (- size_chunk Mptr)
                                   (Values.Vlong (Int64.repr (8 * n)))) as TGTM2.
      match goal with
      | [ TGTM2 := _ : ?_VACCESS -> _ |- _ ] => assert (VACCESS: _VACCESS)
      end.
      { eapply Mem.valid_access_freeable_any. unfold_modrange_64. unfold scale_ofs in *.
        eapply Mem.valid_access_alloc_same; eauto; try nia. unfold align_chunk, size_chunk. des_ifs. exists (- 1)%Z. lia. }
      apply TGTM2 in VACCESS. clear TGTM2. dependent destruction VACCESS. rename x0 into tm2. rename e into TGTM2.

      gstep. econs 4.
      eexists. eexists.
      { eapply step_external_function. ss.
        assert (POSSIZE: Ptrofs.unsigned (Ptrofs.repr (8 * n)) = (8 * n)%Z).
        { unfold_modrange_64. rewrite Ptrofs.unsigned_repr; auto. unfold Ptrofs.max_unsigned. unfold_Ptrofs_modulus.
          unfold scale_ofs in *. des_ifs. nia. }
        hexploit extcall_malloc_sem_intro.
        3:{ unfold Values.Vptrofs. des_ifs. unfold Ptrofs.to_int64.
            i. instantiate (4:= Ptrofs.repr (8 * n)) in H0. rewrite POSSIZE in H0. eapply H0. }
        { rewrite POSSIZE. apply TGTALLOC. }
        unfold Values.Vptrofs. des_ifs. unfold Ptrofs.to_int64. rewrite POSSIZE. eauto. }

      eexists; split; [ord_step2|].
      gstep. econs 4.
      eexists. eexists.
      { eapply step_return. }
      eexists; split; [ord_step2|].
      sim_ord.
      { eapply OrdArith.add_base_l. }
      gbase. apply CIH.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      4,5,6: eauto.
      4:{ clarify. }
      4:{ i.
          match goal with
          | [ H1: match_states _ _ _ ?i0 _ |- match_states _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { econs. i.  specialize TGTALLOC with tm (- size_chunk Mptr)%Z (8 * n)%Z. apply Mem.alloc_result in TGTALLOC.
        rewrite TGTALLOC. inv MM. rewrite NBLK. rename H0 into LENV. depgen LENV. depgen ML. clear; i.

        set (vv:=Vptr (Mem.nb m + 0) 0) in *. simpl.
        replace (Values.Vptr (map_blk srcprog (Mem.nb m)) Ptrofs.zero) with (map_val srcprog vv).
        2:{ ss. repeat f_equal. lia. }
        eapply alist_update_le; eauto. }
      { clarify. }
      eapply match_mem_malloc; eauto. unfold Mem.alloc; ss. f_equal. rewrite! Nat.add_0_r. ss.

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Free. sim_red.
      ss.
      sim_ord.
      { eapply max_fuel_spec1'. }
      eapply step_expr; eauto.
      i. sim_red.
      grind. do 1 (gstep; sim_tau). sim_red.
      match goal with
      | [ MCONT: match_code ?_ge _ _ _ _ |- _ ] =>
        set (ge:=_ge) in *
      end.
      match goal with
      | [ MCONT: match_code _ ?_ms _ _ _ |- _ ] =>
        set (ms:=_ms) in *
      end.
      unfold cfunU. grind. unfold freeF. sim_red.
      do 3 (gstep; sim_tau). sim_red.
      rewrite PSTATE. rewrite Any.upcast_downcast. grind. unfold unptr. des_ifs; sim_red.
      1,3: sim_triggerUB.
      unfold Mem.free. destruct (Mem.cnts m blk ofs) eqn:MEMCNT; ss.
      2:{ sim_triggerUB. }
      sim_red.
      gstep. econs 6; clarify.
      eexists. eexists.
      { econs. }
      eexists. exists (step_tau _).
      eexists. do 4 (gstep; sim_tau). sim_red.
      gstep. econs 6; clarify.
      eexists. eexists.
      { econs. }
      eexists. exists (step_tau _). eexists. gbase. eapply CIH.
      rewrite Any.upcast_downcast. grind.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      1,4,5,6: eauto.
      3:{ clarify. }
      3:{ i.
          match goal with
          | [ H1: match_states _ _ _ ?i0 _ |- match_states _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { ss. }
      eapply match_mem_free; eauto.
      instantiate (1:=ofs). instantiate (1:=blk). unfold Mem.free. rewrite MEMCNT. ss.

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Load. sim_red.
      ss.
      sim_ord.
      { eapply max_fuel_spec1'. }
      eapply step_expr; eauto.
      i.
      des_ifs.
      2: sim_triggerUB.
      sim_red.
      grind. do 1 (gstep; sim_tau). sim_red.
      match goal with
      | [ MCONT: match_code ?_ge _ _ _ _ |- _ ] =>
        set (ge:=_ge) in *
      end.
      match goal with
      | [ MCONT: match_code _ ?_ms _ _ _ |- _ ] =>
        set (ms:=_ms) in *
      end.
      unfold cfunU.
      grind. unfold loadF. sim_red.
      do 3 (gstep; sim_tau). sim_red.
      rewrite PSTATE. rewrite Any.upcast_downcast. grind. unfold unptr. des_ifs; sim_red.
      1: sim_triggerUB.
      unfold Mem.load. destruct (Mem.cnts m blk ofs) eqn:MEMCNT; ss.
      2:{ sim_triggerUB. }
      sim_red.
      gstep. econs 6; clarify.
      eexists. eexists.
      { eapply step_set. econs; eauto. ss. inv MM. apply MMEM in MEMCNT. des.
        unfold scale_ofs in *. unfold map_ofs in *. rewrite unwrap_Ptrofs_repr_z; try nia; eauto. }
      eexists. exists (step_tau _).
      eexists.
      do 2 (gstep; sim_tau). sim_red. grind.
      do 1 (gstep; sim_tau). gstep; sim_tau.
      sim_ord.
      { eapply OrdArith.add_base_l. }
      gbase. eapply CIH.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      2,3,4,5,6: eauto.
      2: clarify.
      2:{ i.
          match goal with
          | [ H1: match_states _ _ _ ?i0 _ |- match_states _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { econs. i. eapply alist_update_le; eauto. }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Store. sim_red.
      match goal with
      | [ MCONT: match_code ?_ge _ _ _ _ |- _ ] =>
        set (ge:=_ge) in *
      end.
      match goal with
      | [ MCONT: match_code _ ?_ms _ _ _ |- _ ] =>
        set (ms:=_ms) in *
      end.
      ss.
      sim_ord.
      { eapply max_fuel_spec2'. }
      eapply step_expr; eauto. i.
      des_ifs.
      2: sim_triggerUB.
      sim_red.
      eapply step_expr; eauto. i. sim_red.
      grind. do 1 (gstep; sim_tau). sim_red.
      unfold cfunU.
      grind. unfold storeF. sim_red.
      do 3 (gstep; sim_tau). sim_red.
      rewrite PSTATE. rewrite Any.upcast_downcast. grind. unfold unptr. des_ifs; sim_red.
      2:{ sim_triggerUB. }
      unfold Mem.store. destruct (Mem.cnts m blk ofs) eqn:MEMCNT; ss.
      2:{ sim_triggerUB. }
      sim_red.

      hexploit match_mem_store; eauto.
      { instantiate (2:=rv0); instantiate (2:=ofs); instantiate (2:=blk). unfold Mem.store. des_ifs. }
      i. des.

      gstep. econs 6; clarify.
      eexists. eexists.
      { eapply step_store; eauto. ss. inv MM. unfold scale_ofs in *; unfold map_ofs in *.
        hexploit MMEM; eauto. i; des. rewrite unwrap_Ptrofs_repr_z; try nia; eauto. }
      eexists. exists (step_tau _). eexists.
      do 4 (gstep; sim_tau). sim_red. gstep; sim_tau.
      sim_ord.
      { eapply OrdArith.add_base_l. }
      gbase. eapply CIH. rewrite Any.upcast_downcast. grind.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      1,4,5,6: eauto.
      3: clarify.
      3:{ i.
          match goal with
          | [ H1: match_states _ _ _ ?i0 _ |- match_states _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { ss. }
      eauto.

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Cmp. sim_red.
      match goal with
      | [ MCONT: match_code ?_ge _ _ _ _ |- _ ] =>
        set (ge:=_ge) in *
      end.
      match goal with
      | [ MCONT: match_code _ ?_ms _ _ _ |- _ ] =>
        set (ms:=_ms) in *
      end.
      ss.
      sim_ord.
      { eapply max_fuel_spec2'. }
      eapply step_expr; eauto. i. sim_red.
      eapply step_expr; eauto. i.
      des_ifs.
      2: sim_triggerUB.
      bsimpl. des. rename Heq into WFA, Heq0 into WFB.
      sim_red.
      (* destruct rstate. ss. destruct l0; clarify. *)
      grind. do 1 (gstep; sim_tau). sim_red.
      (* unfold cfunU. *)
      grind. unfold cmpF. sim_red.
      do 3 (gstep; sim_tau). sim_red.
      rewrite PSTATE. rewrite Any.upcast_downcast. grind.
      destruct (vcmp m rv rv0) eqn:VCMP; sim_red.
      2:{ sim_triggerUB. }
      des_ifs.
      + sim_red.
        gstep. econs 6; clarify.
        eexists. eexists.
        { eapply step_set. econs; eauto. econs; eauto; ss. eapply match_mem_cmp in VCMP; eauto. }
        eexists. exists (step_tau _).
        eexists.
        do 2 (gstep; sim_tau). sim_red. grind.
        do 1 (gstep; sim_tau). gstep; sim_tau.
        sim_ord.
        { eapply OrdArith.add_base_l. }
        gbase. eapply CIH.
        hexploit match_states_intro.
        { instantiate (2:=Skip). ss. }
        2,3,4,5,6: eauto.
        2: clarify.
        2:{ i.
            match goal with
            | [ H1: match_states _ _ _ ?i0 _ |- match_states _ _ _ ?i1 _ ] =>
              replace i1 with i0; eauto
            end.
            unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
        { econs. i. unfold Int.one. rewrite Int.signed_repr.
          2:{ unfold_Int_max_signed; unfold_Int_min_signed. ss. }
          set (vv:=Vint 1) in *.
          replace (Values.Vlong (Int64.repr 1)) with (map_val srcprog vv).
          2:{ ss. }
          eapply alist_update_le; eauto. }
    + sim_red.
        gstep. econs 6; clarify.
        eexists. eexists.
        { eapply step_set. econs; eauto. econs; eauto; ss. eapply match_mem_cmp in VCMP; eauto. }
        eexists. exists (step_tau _).
        eexists.
        do 2 (gstep; sim_tau). sim_red. grind.
        do 1 (gstep; sim_tau). gstep; sim_tau.
        sim_ord.
        { eapply OrdArith.add_base_l. } gbase. eapply CIH.
        hexploit match_states_intro.
        { instantiate (2:=Skip). ss. }
        2,3,4,5,6: eauto.
        2: clarify.
        2:{ i.
            match goal with
            | [ H1: match_states _ _ _ ?i0 _ |- match_states _ _ _ ?i1 _ ] =>
              replace i1 with i0; eauto
            end.
            unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
        { econs. i. unfold Int.zero. rewrite Int.signed_repr.
          2:{ unfold_Int_max_signed; unfold_Int_min_signed. ss. }
          set (vv:=Vint 0) in *.
          replace (Values.Vlong (Int64.repr 0)) with (map_val srcprog vv).
          2:{ ss. }
          eapply alist_update_le; eauto. }

        Unshelve. all: try (exact Ord.O). all: try (exact 0%nat). all: ss.
        { eapply (Genv.globalenv tgt). }
  Qed.

  Ltac rewriter :=
    try match goal with
        | H: _ = _ |- _ => rewrite H in *; clarify
        end.

  Lemma Csharpminor_eval_expr_determ a
    :
      forall v0 v1 ge e le m
             (EXPR0: eval_expr ge e le m a v0)
             (EXPR1: eval_expr ge e le m a v1),
        v0 = v1.
  Proof.
    induction a; i; inv EXPR0; inv EXPR1; rewriter.
    { inv H0; inv H1; rewriter. }
    { exploit (IHa v2 v3); et. i. subst. rewriter. }
    { exploit (IHa1 v2 v4); et. i. subst.
      exploit (IHa2 v3 v5); et. i. subst. rewriter. }
    { exploit (IHa v2 v3); et. i. subst. rewriter. }
  Qed.

  Lemma Csharpminor_eval_exprlist_determ a
    :
      forall v0 v1 ge e le m
             (EXPR0: eval_exprlist ge e le m a v0)
             (EXPR1: eval_exprlist ge e le m a v1),
        v0 = v1.
  Proof.
    induction a; ss.
    { i. inv EXPR0. inv EXPR1. auto. }
    { i. inv EXPR0. inv EXPR1.
      hexploit (@Csharpminor_eval_expr_determ a v2 v0); et. i.
      hexploit (IHa vl vl0); et. i. clarify. }
  Qed.

  Lemma alloc_variables_determ vars
    :
      forall e0 e1 ee m m0 m1
             (ALLOC0: alloc_variables ee m vars e0 m0)
             (ALLOC1: alloc_variables ee m vars e1 m1),
        e0 = e1 /\ m0 = m1.
  Proof.
    induction vars; et.
    { i. inv ALLOC0; inv ALLOC1; auto. }
    { i. inv ALLOC0; inv ALLOC1; auto. rewriter.
      eapply IHvars; et. }
  Qed.

  Lemma Csharpminor_wf_semantics prog
    :
      wf_semantics (Csharpminor.semantics prog).
  Proof.
    econs.
    { i. inv STEP0; inv STEP1; ss; rewriter.
      { hexploit (@Csharpminor_eval_expr_determ a v v0); et. i. rewriter. }
      { hexploit (@Csharpminor_eval_expr_determ addr vaddr vaddr0); et. i. rewriter.
        hexploit (@Csharpminor_eval_expr_determ a v v0); et. i. rewriter. }
      { hexploit (@Csharpminor_eval_expr_determ a vf vf0); et. i. rewriter.
        hexploit (@Csharpminor_eval_exprlist_determ bl vargs vargs0); et. i. rewriter. }
      { hexploit (@Csharpminor_eval_exprlist_determ bl vargs vargs0); et. i. rewriter.
        hexploit external_call_determ; [eapply H0|eapply H12|..]. i. des.
        inv H1. hexploit H2; et. i. des. clarify. }
      { hexploit (@Csharpminor_eval_expr_determ a v v0); et. i. rewriter.
        inv H0; inv H12; auto. }
      { hexploit (@Csharpminor_eval_expr_determ a v v0); et. i. rewriter.
        inv H0; inv H12; et. }
      { hexploit (@Csharpminor_eval_expr_determ a v v0); et. i. rewriter. }
      { hexploit (@alloc_variables_determ (fn_vars f) e e0); et. i. des; clarify. }
      { hexploit external_call_determ; [eapply H|eapply H6|..]. i. des.
        inv H0. hexploit H1; et. i. des. clarify. }
    }
    { i. inv FINAL. inv STEP. }
    { i. inv FINAL0. inv FINAL1. ss. }
  Qed.

End PROOF.
