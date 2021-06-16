From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
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
Require Import SimSTS2.
Require Import Mem0.
Require Import IRed.

Require Import Imp2CsharpminorMatch.
Require Import Imp2CsharpminorArith.
Require Import Imp2CsharpminorGenv.
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


Section PROOF.

  Import ModSemL.

  Context `{Σ: GRA.t}.

  Variable srcprog : Imp.programL.

  Ltac sim_red := Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); econs 3; ss; clarify; eexists; exists (step_tau _); eexists; split; auto.

  Ltac sim_triggerUB := pfold; ss; unfold triggerUB; (try sim_red); econs 5; i; ss; auto;
                        dependent destruction STEP; try (irw in x; clarify; fail).

  Definition ordN : nat -> nat -> Prop := fun a b => True.

  Lemma step_expr
        e te
        tcode tf tcont tge tle tm (src: ModL.t) (tgt: Csharpminor.program)
        r ms mn ge le rstate pstate ktr
        i0 i1
        (MLE: @match_le srcprog le tle)
        (CEXP: compile_expr e = Some te)
        (SIM:
           forall rv trv,
             wf_val rv ->
             eval_expr tge empty_env tle tm te trv ->
             trv = @map_val srcprog rv ->
             paco3 (_sim (ModL.compile src) (semantics tgt) ordN) r i1
                   (ktr (rstate, pstate, (le, rv)))
                   (State tf tcode tcont empty_env tle tm))
    :
      paco3 (_sim (ModL.compile src) (semantics tgt) ordN) r i0
            (r0 <- EventsL.interp_Es (prog ms) (transl_all mn (interp_imp ge (denote_expr e) le)) (rstate, pstate);; ktr r0)
            (State tf tcode tcont empty_env tle tm).
  Proof.
    unfold ordN in *.
    generalize dependent ktr. generalize dependent te.
    move MLE before pstate. revert_until MLE.
    generalize dependent e. Local Opaque Init.Nat.add. induction e; i; ss; des; clarify.
    - rewrite interp_imp_expr_Var. sim_red.
      destruct (alist_find v le) eqn:AFIND; try sim_red.
      + repeat (pfold; sim_tau; left). sim_red.
        unfold assume. grind.
        pfold. econs 5; ss; auto. i. eapply angelic_step in STEP; des; clarify.
        eexists; split; auto. left.
        do 6 (pfold; sim_tau; left).
        sim_red. eapply SIM; auto.
        econs. inv MLE. specialize ML with (x:=v) (sv:=v0).
        hexploit ML; auto.
      + sim_triggerUB.
    - rewrite interp_imp_expr_Lit.
      sim_red. unfold assume. grind. pfold. econs 5; auto. i. eapply angelic_step in STEP; des; clarify.
      eexists; split; auto. left.
      do 6 (pfold; sim_tau; left).
      sim_red. eapply SIM; eauto. econs. unfold map_val. ss.
    - rewrite interp_imp_expr_Plus.
      sim_red. destruct (compile_expr e1) eqn:EXP1; destruct (compile_expr e2) eqn:EXP2; ss; clarify.
      eapply IHe1; eauto; clear IHe1.
      i. sim_red. eapply IHe2; eauto; clear IHe2.
      i. sim_red.
      unfold unwrapU. destruct (vadd rv rv0) eqn:VADD; ss; clarify.
      + sim_red. unfold assume. grind. pfold. econs 5; auto. i. eapply angelic_step in STEP; des; clarify.
        eexists; split; auto. left.
        do 6 (pfold; sim_tau; left).
        sim_red. specialize SIM with (rv:=v) (trv:= @map_val srcprog v). apply SIM; auto.
        econs; eauto. ss. f_equal. apply map_val_vadd_comm; auto.
      + sim_triggerUB.
    -
  Admitted.

  Variable EMI : nat.

  Lemma step_exprs
        es tes
        tcode tf tcont tge tle tm (src: ModL.t) (tgt: Csharpminor.program)
        r ms mn ge le rstate pstate ktr
        i0 i1
        (IDX: i0 = (List.length es)*EMI + i1)
        (MLE: @match_le srcprog le tle)
        (CEXP: compile_exprs es = Some tes)
        (SIM:
           forall rvs trvs,
             Forall wf_val rvs ->
             eval_exprlist tge empty_env tle tm tes trvs ->
             trvs = List.map (@map_val srcprog) rvs ->
             paco3 (_sim (ModL.compile src) (semantics tgt) ordN) r i1
                   (ktr (rstate, pstate, (le, rvs)))
                   (State tf tcode tcont empty_env tle tm))
    :
      paco3 (_sim (ModL.compile src) (semantics tgt) ordN) r i0
            (r0 <- EventsL.interp_Es (prog ms) (transl_all mn (interp_imp ge (denote_exprs es) le)) (rstate, pstate);; ktr r0)
            (State tf tcode tcont empty_env tle tm).
  Proof.
    unfold ordN in *.
    generalize dependent ktr. generalize dependent tes.
    move MLE before pstate. revert_until MLE.
    generalize dependent es. induction es; i; ss; des; clarify.
    - rewrite interp_imp_Ret. sim_red. eapply SIM; eauto.
      econs.
    - destruct (compile_expr a) eqn:CEA; destruct (compile_exprs es) eqn:CEES; uo; ss; clarify.
      rewrite interp_imp_bind. sim_red. eapply step_expr; eauto.
      i. unfold ordN in *. rewrite interp_imp_bind. sim_red.
      eapply IHes.
      { admit "mid: index". }
      { auto. }
      i. rewrite interp_imp_Ret. sim_red. eapply SIM; eauto.
      econs; ss; clarify; eauto.
  Admitted.

  Lemma compile_stmt_no_Sreturn
        gm src e
        (CSTMT: compile_stmt gm src = Some (Sreturn e))
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
        let args_src := List.map (Vint ∘ Int64.signed) args_int in
        let ret_src := (Vint ∘ Int64.signed) ret_int in
        (<<EV: tr = [ev] /\ decompile_event ev = Some (event_sys fn args_src ret_src)>>)
        /\ (<<SRC: syscall_sem (event_sys fn args_src ret_src)>>)
        /\ (<<MEM: m0 = m1>>)
  .


  Hypothesis map_blk_after_init :
    forall src blk
      (COMP : exists tgt, Imp2Csharpminor.compile src = OK tgt)
      (ALLOCED : blk >= (src_init_nb src)),
      (<<ALLOCMAP: (map_blk src blk) = Pos.of_succ_nat (2 + (ext_len src) + blk)>>).

  Hypothesis map_blk_inj :
    forall src b1 b2
      (COMP : exists tgt, Imp2Csharpminor.compile src = OK tgt)
      (WFPROG: Permutation.Permutation
                 ((List.map fst src.(prog_varsL)) ++ (List.map fst src.(prog_funsL)))
                 (List.map fst src.(defsL))),
      <<INJ: map_blk src b1 = map_blk src b2 -> b1 = b2>>.

  Context {WFPROG: Permutation.Permutation
                     ((List.map fst srcprog.(prog_varsL)) ++ (List.map fst srcprog.(prog_funsL)))
                     (List.map fst srcprog.(defsL))}.


  Theorem match_states_sim
          tgt
          (modl: ModL.t) gm ge ms tlof
          ist cst
          i0
          (TLOF: tlof = 2 + (List.length srcprog.(ext_funsL)) + (List.length srcprog.(ext_varsL)))
          (GMAP: get_gmap srcprog = Some gm)
          (MODL: modl = (ModL.add (Mod.lift Mem) (ImpMod.get_modL srcprog)))
          (MODSEML: ms = modl.(ModL.enclose))
          (GENV: ge = Sk.load_skenv (Sk.sort modl.(ModL.sk)))
          (MGENV: @match_ge srcprog ge (Genv.globalenv tgt))
          (COMP: Imp2Csharpminor.compile srcprog = OK tgt)
          (MS: match_states gm ge ms srcprog ist cst)
    :
      <<SIM: sim (ModL.compile modl) (semantics tgt) ordN i0 ist cst>>.
  Proof.
    (* move GMAP before ms. move MODSEML before GMAP. move GENV before MODSEML. move COMP before GENV. *)
    (* move TLOF before COMP. move MODL before COMP. move MGENV before COMP. *)
    (* revert_until TLOF. *)
    depgen i0. depgen ist. depgen cst. pcofix CIH. i.
    assert (EXISTSCOMP: exists tgt, Imp2Csharpminor.compile srcprog = OK tgt); eauto.
    inv MS. unfold ordN in *. unfold Imp2Csharpminor.compile in COMP. des_ifs. rename Heq into GMAP.
    destruct code.
    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. ss; clarify.
      destruct tcont; ss; clarify. inv MCONT; clarify.
      { unfold exit_stmt in *; ss; clarify. destruct tcont; inv MSTACK; ss; clarify.
        sim_red. pfold. econs 6; clarify.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_skip_seq. }
        eexists. exists (step_tau _). eexists. unfold idK. sim_red. left.

        rewrite interp_imp_expr_Var. sim_red.
        unfold unwrapU. des_ifs.
        2:{ sim_triggerUB. }
        sim_red. pfold. econs 6; clarify.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_return_1; ss; eauto. econs; ss. econs; ss. inv ML; ss; clarify. hexploit ML0; i; eauto. }
        eexists. exists (step_tau _). eexists. left.
        do 1 (pfold; sim_tau; left). sim_red. unfold assume. grind.
        pfold. econs 5; ss; auto. i. eapply angelic_step in STEP; des; clarify.
        eexists; split; auto. left.
        do 6 (pfold; sim_tau; left). sim_red.
        destruct rstate. ss. destruct l.
        { admit "ez: wf_rstate". }
        do 3 (pfold; sim_tau; left). sim_red.
        destruct v.
        - destruct ((0 <=? n)%Z && (n <? two_power_nat 32)%Z) eqn:INT32; bsimpl; des.
          + pfold. econs 1; eauto.
            { unfold Int.max_unsigned. unfold_Int_modulus. instantiate (1:=n). lia. }
            { ss. unfold state_sort; ss. rewrite Any.upcast_downcast. des_ifs. }
            ss. unfold Int64.loword. rewrite Int64.unsigned_repr.
            2:{ unfold Int64.max_unsigned. unfold_Int64_modulus. unfold two_power_nat in *. ss. lia. }
            econs.
          + pfold. econs 5; ss; eauto.
            { unfold state_sort; ss. rewrite Any.upcast_downcast. des_ifs. }
            i. inv STEP.
          + pfold. econs 5; ss; eauto.
            { unfold state_sort; ss. rewrite Any.upcast_downcast. des_ifs. bsimpl. clarify. }
            i. inv STEP.

        - pfold. econs 5; ss; eauto.
          { unfold state_sort; ss. rewrite Any.upcast_downcast. des_ifs. }
          i. inv STEP.
        - pfold. econs 5; ss; eauto. }

      { unfold return_stmt in *; ss; clarify. destruct tcont; inv MSTACK; ss; clarify.
        sim_red. pfold. econs 6; clarify.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_skip_seq. }
        eexists. exists (step_tau _). eexists. unfold idK. sim_red. left.

        rewrite interp_imp_expr_Var. sim_red.
        unfold unwrapU. des_ifs.
        2:{ sim_triggerUB. }
        sim_red. pfold. econs 6; clarify.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_return_1; ss; eauto. econs; ss. inv ML; ss; clarify. hexploit ML0; i; eauto. }
        eexists. exists (step_tau _). eexists. left.
        do 1 (pfold; sim_tau; left). sim_red. unfold assume. grind.
        pfold. econs 5; ss; auto. i. eapply angelic_step in STEP; des; clarify.
        eexists; split; auto. left.
        do 6 (pfold; sim_tau; left). sim_red.
        destruct rstate. ss. destruct l.
        { admit "ez: wf_rstate". }
        do 3 (pfold; sim_tau; left). sim_red.
        pfold. econs 6; clarify.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_return. }
        eexists. exists (step_tau _). eexists. left. do 1 (pfold; sim_tau; left). sim_red.
        rewrite Any.upcast_downcast. grind. do 1 (pfold; sim_tau; left). pfold; sim_tau; right. apply CIH.
        unfold ret_call_cont in TPOP. unfold return_stmt in TPOP. ss; clarify.
        hexploit match_states_intro.
        { instantiate (2:=Skip). ss. }
        2,3,4,5,6: eauto.
        2: clarify.
        2:{ i.
            match goal with
            | [ H : match_states _ _ _ _ ?i0 _ |- match_states _ _ _ _ ?i1 _ ] =>
              replace i1 with i0; eauto
            end.
            unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
        econs. i. ss. admit "ez: find in lenv". }

      sim_red. pfold. econs 6; clarify.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_skip_seq. }
      eexists. eexists (step_tau _). eexists. sim_red. right. eapply CIH. hexploit match_states_intro; eauto.
      all: (destruct s; eauto).
      all: (generalize dependent tcont; induction tcont; i; ss; clarify; eauto).
      all: (eapply compile_stmt_no_Sreturn in CST; clarify).

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Assign. sim_red.
      ss. destruct (compile_expr e) eqn:EXP; uo; ss. eapply step_expr; eauto. i.
      (* tau point *)
      unfold ordN in *. do 1 (pfold; sim_tau; left). sim_red.
      pfold. econs 6; auto.
      { admit "ez? strict_determinate_at". }
      eexists. eexists.
      { eapply step_set. eapply H0. }
      eexists. eexists.
      { eapply step_tau. }
      eexists. right. apply CIH. hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      2,3,4,5,6,7:eauto.
      2:{ unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. eauto. }
      { econs. i. admit "ez? alist & Maps.PTree". }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Seq. sim_red.
      ss. destruct (compile_stmt gm code1) eqn:CSC1; destruct (compile_stmt gm code2) eqn:CSC2; uo; clarify.
      (* tau point *)
      pfold. econs 6; ss; clarify.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_seq. }
      eexists. exists (step_tau _). eexists. right. eapply CIH. hexploit match_states_intro.
      { eapply CSC1. }
      4:{ instantiate (1:=Kseq s0 tcont). ss. destruct s0; eauto. eapply compile_stmt_no_Sreturn in CSC2; clarify. }
      4:{ econs 3; eauto. }
      all: eauto.
      { ss. destruct s0; eauto. eapply compile_stmt_no_Sreturn in CSC2; clarify. }
      i.
      match goal with
      | [ H: match_states _ _ _ _ ?it0 _ |- match_states _ _ _ _ ?it1 _ ] =>
        replace it1 with it0; eauto
      end.
      unfold itree_of_cont_stmt, itree_of_imp_cont. Red.prw ltac:(_red_gen) 1 0. grind.

    - unfold itree_of_cont_stmt in *; unfold itree_of_imp_cont in *. rewrite interp_imp_If. sim_red. ss.
      destruct (compile_expr i) eqn:CEXPR; destruct (compile_stmt gm code1) eqn:CCODE1;
        destruct (compile_stmt gm code2) eqn:CCODE2; uo; clarify.
      eapply step_expr; eauto.
      i. sim_red. destruct (is_true rv) eqn:COND; ss; clarify.
      2:{ sim_triggerUB. }
      sim_red. destruct rv; clarify. ss. destruct (n =? 0)%Z eqn:CZERO; ss; clarify.
      { rewrite Z.eqb_eq in CZERO. clarify.
        (* tau point *)
        pfold. econs 6; ss.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_ifthenelse; ss. econs; eauto.
          + econs. ss.
          + ss. }
        eexists. eexists.
        { eapply step_tau. }
        eexists. des_ifs. right. eapply CIH. hexploit match_states_intro; eauto. }
      { rewrite Z.eqb_neq in CZERO.
        (* tau point *)
        pfold. econs 6; ss.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_ifthenelse.
          - econs; eauto.
            + econs. ss.
            + ss.
          - ss. destruct (negb (Int64.eq (Int64.repr n) Int64.zero)) eqn:CONTRA; ss; clarify.
            rewrite negb_false_iff in CONTRA. apply Int64.same_if_eq in CONTRA.
            unfold Int64.zero in CONTRA. unfold_intrange_64.
            hexploit Int64.signed_repr.
            { unfold_Int64_max_signed. unfold_Int64_min_signed. instantiate (1:=n). nia. }
            i. rewrite CONTRA in H1. rewrite Int64.signed_repr_eq in H1. des_ifs. }
        eexists. exists (step_tau _).
        eexists. des_ifs. right. eapply CIH. hexploit match_states_intro.
        { eapply CCODE1. }
        all: eauto. }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_CallFun.
      ss. uo; des_ifs; sim_red.
      { sim_triggerUB. }
      assert (COMP2: Imp2Csharpminor.compile srcprog = OK tgt).
      { unfold Imp2Csharpminor.compile. rewrite GMAP. auto. }
      unfold _compile in COMP. des_ifs.
      unfold compile_gdefs in Heq0. uo; des_ifs; clarify.
      match goal with
      | [ |- paco3 (_sim _ (semantics ?tp) _) _ _ _ _ ] =>
        set (tgtp:=tp) in *
      end.
      eapply step_exprs; eauto.
      { admit "mid: index". }
      i. sim_red. destruct rstate. destruct l0.
      { ss. admit "mid?: r_state is nil". }
      ss. grind. unfold ordN in *. do 3 (pfold; sim_tau; left). sim_red.
      match goal with
      | [ |- paco3 _ _ _ (r0 <- unwrapU (?f);; _) _ ] => destruct f eqn:FSEM; ss
      end.
      2:{ sim_triggerUB. }
      unfold call_mem in Heq. bsimpl; des. des_ifs; clarify. apply neg_rel_dec_correct in Heq4. rename Heq4 into NOTMAIN.
      repeat match goal with
      | [ Heq: _ = false |- _ ] => clear Heq
      end.
      grind. rewrite alist_find_find_some in FSEM. rewrite find_map in FSEM.
      match goal with
      | [ FSEM: o_map (?a) _ = _ |- _ ] => destruct a eqn:FOUND; ss; clarify
      end.
      destruct p. destruct p. clarify. eapply found_imp_function in FOUND. des; clarify.
      hexploit exists_compiled_function; eauto. i.
      des. rename cf into tf0. rename H1 into COMPF.
      hexploit in_tgt_prog_defs_ifuns; eauto. i.
      (* assert (TGTFG: In (s2p f, Gfun (Internal tf0)) tgtp.(prog_defs)); auto. *)
      assert (INTGT: In (s2p f, Gfun (Internal tf0)) (prog_defs tgtp)); auto.
      eapply Globalenvs.Genv.find_symbol_exists in H1.
      destruct H1 as [b TGTFG].
      unfold ident_key in Heq1.
      hexploit compiled_function_props; eauto. i. des; clarify.
      apply alist_find_some in Heq1. apply in_app_iff in Heq1.
      hexploit gm_funs_disjoint; eauto. i.
      (* hexploit gm_int_fun_exists; eauto. i. *)
      des.
      { apply (in_map fst _ _) in Heq1. apply (in_map fst _ _) in H2.
        unfold Coqlib.list_disjoint in H10. hexploit H10; eauto. i. ss. }
      hexploit gm_unique_intfun.
      { eauto. }
      { eapply Heq1. }
      { eapply H2. }
      i. clarify. ss. clarify.
      (* Coqlib.list_in_map_inv: *)
      assert (TGTGFIND: Globalenvs.Genv.find_def (Globalenvs.Genv.globalenv tgtp) b = Some (Gfun (Internal tf0))).
      { hexploit tgt_genv_find_def_by_blk; eauto. }

      unfold cfun. sim_red. rewrite Any.upcast_downcast. sim_red.
      rewrite unfold_eval_imp_only.
      destruct (init_args (Imp.fn_params f0) rvs []) eqn:ARGS; sim_red.
      2:{ sim_triggerUB. }
      (* tau point?? need a tau BEFORE denote_stmt(fn_body) *)
      rewrite interp_imp_tau. sim_red.
      pfold. econs 6; auto.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_call; eauto.
        - econs. econs 2.
          { apply Maps.PTree.gempty. }
          eapply TGTFG.
        - rewrite Globalenvs.Genv.find_funct_find_funct_ptr.
          rewrite Globalenvs.Genv.find_funct_ptr_iff. ss. eapply TGTGFIND.
        - ss. }

      eexists. exists (step_tau _). eexists. left.
      pfold. econs 4.
      { admit "ez: strict_determinate_at". }

      unfold pre_compile_function in COMPF. des_ifs; clarify; uo; des_ifs; ss.
      { rewrite rel_dec_correct in Heq2. clarify. }
      eexists. eexists.
      { eapply step_internal_function; ss; eauto; try econs.
        match goal with
        | [ |- bind_parameters _ _ ?_tle0 = Some _ ] =>
          set (tle0:=_tle0) in *
        end.
        admit "ez: use induction?". }
      eexists; split; auto. grind. left.

      pfold. econs 4.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_seq. }
      eexists; split; auto. right. eapply CIH.
      match goal with
      | [ |- match_states _ ?_ge _ _ _ _ ] =>
        set (ge:=_ge) in *
      end.
      match goal with
      | [ |- match_states _ _ ?_ms _ _ _ ] =>
        set (ms:=_ms) in *
      end.
      match goal with
      | [ |- match_states _ _ _ _ (?i) _] =>
        replace i with
    (` r0 : r_state * p_state * (lenv * val) <-
     EventsL.interp_Es (prog ms)
       (transl_all s0 (interp_imp ge (denote_stmt (Imp.fn_body f0)) (init_lenv (Imp.fn_vars f0) ++ l3)))
       (c, ε :: c0 :: l0, pstate);; x4 <- itree_of_imp_pop ge ms s0 mn x le r0;; ` x : _ <- next x4;; stack x)
      end.
      2:{ rewrite interp_imp_bind. Red.prw ltac:(_red_gen) 1 0. grind.
          Red.prw ltac:(_red_gen) 2 0. grind.
          Red.prw ltac:(_red_gen) 2 0. Red.prw ltac:(_red_gen) 1 0. grind.
          Red.prw ltac:(_red_gen) 2 0. Red.prw ltac:(_red_gen) 1 0. grind. }

      hexploit match_states_intro.
      5:{ instantiate (1:=Kseq (Sreturn (Some (Evar (s2p "return")))) (Kcall (Some (s2p x)) tf empty_env tle tcont)). ss. }
      6:{ instantiate (1:= fun r0 =>
                             ` x4 : r_state * p_state * (lenv * val) <- itree_of_imp_pop ge ms s0 mn x le r0;;
                                    ` x0 : r_state * p_state * (lenv * val) <- next x4;; stack x0).
          instantiate (1:=s0). instantiate (1:=srcprog). instantiate (1:=ms). instantiate (1:=ge). instantiate (1:=gm).
          econs 2; ss; eauto. }
      3,4: eauto.
      1:{ eapply H5. }
      2:{ ss. econs 2. }
      2:{ clarify. }
      2:{ i.
          match goal with
          | [ H1: match_states _ _ _ _ ?i0 _ |- match_states _ _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. unfold idK. grind. }
      { admit "ez: should follow from above, the initial lenv". }

    - ss. destruct p eqn:PVAR; clarify. 
      admit "ez: CallPtr, similar to CallFun.".

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_CallSys.
      ss. uo; des_ifs; clarify. unfold ident_key in Heq0.
      rename Heq0 into FOUND. apply alist_find_some in FOUND.
      assert (COMP2: Imp2Csharpminor.compile srcprog = OK tgt).
      { unfold Imp2Csharpminor.compile. rewrite GMAP. auto. }
      assert (GMAP2: get_gmap srcprog = Some gm).
      { auto. }
      unfold get_gmap in GMAP. uo; des_ifs; ss.
      match goal with
      | [ COMP: _compile ?_gm _ = OK _ |- _ ] =>
        set (gm:=_gm) in *
      end.
      unfold compile_eFuns in FOUND.
      rewrite in_map_iff in FOUND. des. destruct x0. ss; clarify.
      assert (S2PBI: forall x y, s2p x = s2p y <-> x = y).
      { admit "ez: make such s2p". }
      apply S2PBI in H1. clear S2PBI; clarify.
      unfold get_funsig in Heq1. clarify.

      unfold _compile in COMP. des_ifs; ss; clarify.
      unfold compile_gdefs in Heq. uo; des_ifs; ss; clarify.
      match goal with
      | [ |- paco3 (_sim _ (semantics ?_tgtp) _) _ _ _ _ ] =>
        set (tgtp:=_tgtp) in *
      end.
      hexploit in_tgt_prog_defs_efuns; eauto. i. rename H into INTGT.
      hexploit Genv.find_symbol_exists; eauto. i. des. rename H into FINDSYM.
      hexploit tgt_genv_find_def_by_blk; eauto. i. rename H into FINDDEF.

      sim_red. eapply step_exprs; eauto.
      { admit "ez: index". }
      i. sim_red.
      pfold. econs 4.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_call; eauto.
        - econs. econs 2.
          { eapply Maps.PTree.gempty. }
          simpl. apply FINDSYM.
        - simpl. des_ifs. unfold Genv.find_funct_ptr.
          rewrite FINDDEF. ss.
        - ss. }
      unfold ordN in *. eexists; split; auto. left.

      (* System call semantics *)
      pose (syscall_exists f (make_signature n) (Genv.globalenv tgtp) trvs tm) as TGTSYSSEM. des.
      hexploit syscall_refines; eauto. i. ss. des. clarify.

      pfold. econs 2; auto.
      { eexists. eexists. eapply step_external_function. ss. eauto. }
      clear TGT EV0 SRC ARGS ev ret_int args_int. rename H into WFARGS. rename H0 into TGTARGS.
      i. inv STEP. ss. rename H5 into TGT.
      hexploit syscall_refines; eauto. i; ss; des; clarify.

      assert (SRCARGS: rvs = (List.map (Vint <*> Int64.signed) args_int)).
      { depgen ARGS. depgen WFARGS. clear. depgen rvs. induction args_int; i; ss; clarify.
        - apply map_eq_nil in ARGS. auto.
        - destruct rvs; ss; clarify. inv WFARGS. f_equal; ss; eauto.
          unfold map_val in H1. des_ifs. unfold compose.
          f_equal. hexploit Int64.signed_repr; eauto. }

      eexists. eexists. eexists.
      { hexploit step_syscall.
        { eauto. }
        { instantiate (1:=top1). ss. }
        i. rename H into SYSSTEP.
        match goal with
        | [ SYSSTEP: step ?i0 _ _ |- step ?i1 _ _ ] =>
          replace i1 with i0; eauto
        end.
        rewrite bind_trigger. ss. grind. }

      split.
      { unfold decompile_event in EV0. des_ifs. uo; des_ifs; ss; clarify.
        unfold decompile_eval in Heq4. des_ifs; ss; clarify. econs; auto. econs.
        2:{ unfold compose. rewrite <- H0. econs. }
        generalize dependent Heq3. clear. generalize dependent args_int. unfold compose.
        induction l2; i; ss; clarify.
        { destruct args_int; ss; clarify. }
        des_ifs. uo; des_ifs; ss. destruct args_int; ss; clarify.
        econs; eauto. unfold decompile_eval in Heq. des_ifs. rewrite <- H0. econs. }

      eexists. left.
      do 8 (pfold; sim_tau; left).
      pfold. econs 4.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_return. }
      eexists; split; auto. right. eapply CIH.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      2,3,4,5,6: eauto.
      2: clarify.
      2:{ i.
          match goal with
          | [ H1: match_states _ _ _ _ ?i0 _ |- match_states _ _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { econs. i. ss. admit "ez: find from local env". }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_AddrOf.
      ss. uo; des_ifs. rename Heq0 into FOUND. unfold ident_key in FOUND.
      apply alist_find_some in FOUND.
      unfold unwrapU. des_ifs.
      2:{ sim_triggerUB. }
      rename n into blk. rename Heq into SRCBLK.
      do 2 (pfold; sim_tau; left). sim_red.
      pfold. econs 6; ss.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_set. econs. econs 2.
        { apply Maps.PTree.gempty. }
        inv MGENV. specialize MG with (symb:=X) (blk:=blk). apply MG. auto. }
      eexists. exists (step_tau _). eexists. right. apply CIH.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      2,3,4,5,6: eauto.
      2: clarify.
      2:{ i.
          match goal with
          | [ H: match_states _ _ _ _ ?i0 _ |- match_states _ _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { econs. i. ss. admit "ez: alist, PTree". }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Malloc. sim_red.
      ss. uo; des_ifs. eapply step_expr; eauto. i. rename H0 into TGTEXPR. rename H1 into MAPRV. sim_red.
      destruct rstate. ss. destruct l.
      { admit "ez: wf_r_state". }
      unfold ordN in *. do 3 (pfold; sim_tau; left). sim_red.
      match goal with
      | [ MCONT: match_code _ ?_ge _ _ _ _ |- _ ] =>
        set (ge:=_ge) in *
      end.
      match goal with
      | [ MCONT: match_code _ _ ?_ms _ _ _ |- _ ] =>
        set (ms:=_ms) in *
      end.
      unfold cfun. rewrite Any.upcast_downcast. grind. unfold allocF. sim_red.
      do 4 (pfold; sim_tau; left). sim_red.
      rewrite PSTATE. rewrite Any.upcast_downcast. grind. unfold unint. des_ifs; sim_red.
      des_ifs; sim_red.
      2,3: sim_triggerUB.
      bsimpl. des. rename Heq into NRANGE1. apply sumbool_to_bool_true in NRANGE1.
      rename Heq1 into NRANGE2. apply sumbool_to_bool_true in NRANGE2.

      assert (TGTDEFS: In (s2p "malloc", Gfun (External EF_malloc)) (prog_defs tgt)).
      { unfold _compile in COMP. des_ifs; ss. rename Heq into CGDEFS.
        unfold compile_gdefs in CGDEFS. uo; des_ifs; ss; clarify.
        rename l1 into NOREPET. eapply Maps.PTree_Properties.of_list_norepet in NOREPET.
        { eapply Maps.PTree.elements_correct. eapply NOREPET. }
        rewrite app_assoc. apply in_or_app. right. econs. ss. }

      assert (TGTMALLOC: exists blk, Genv.find_symbol (globalenv (semantics tgt)) (s2p "malloc") = Some blk).
      { unfold _compile in COMP. des_ifs; ss. rename Heq into CGDEFS.
        unfold compile_gdefs in CGDEFS. uo; des_ifs; ss; clarify.
        hexploit Genv.find_symbol_exists; eauto. ss. eauto. }
      des.

      assert (COMP2: Imp2Csharpminor.compile srcprog = OK tgt).
      { unfold Imp2Csharpminor.compile. rewrite GMAP. auto. }
      hexploit tgt_genv_find_def_by_blk; eauto. i. rename H0 into TGTFINDDEF.

      pfold. econs 6; clarify.
      { admit "ez: strict_determinate_at". }
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
      eexists. left.
      do 13 (pfold; sim_tau; left). sim_red.
      rewrite Any.upcast_downcast. sim_red.
      do 2 (pfold; sim_tau; left).

      rewrite Int64.mul_signed. rewrite! Int64.signed_repr; ss.

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
      apply TGTM2 in VACCESS. clear TGTM2. dependent destruction VACCESS. rename x0 into tm2. rename e0 into TGTM2.

      pfold. econs 4.
      { admit "ez: strict_determinate_at". }
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

      eexists; split; auto. left.
      pfold. econs 4.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_return. }
      eexists; split; auto. right. eapply CIH.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      4,5,6: eauto.
      4:{ clarify. }
      4:{ i.
          match goal with
          | [ H1: match_states _ _ _ _ ?i0 _ |- match_states _ _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { econs. i. ss. admit "ez: local env". }
      { clarify. }
      eapply match_mem_malloc; eauto. unfold Mem.alloc; ss. f_equal. rewrite! Nat.add_0_r. ss.

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Free. sim_red.
      ss. uo; des_ifs. eapply step_expr; eauto.
      i. sim_red. destruct rstate. ss. destruct l.
      { admit "ez: wf_r_state". }
      grind. unfold ordN in *. do 3 (pfold; sim_tau; left). sim_red.
      match goal with
      | [ MCONT: match_code _ ?_ge _ _ _ _ |- _ ] =>
        set (ge:=_ge) in *
      end.
      match goal with
      | [ MCONT: match_code _ _ ?_ms _ _ _ |- _ ] =>
        set (ms:=_ms) in *
      end.
      unfold cfun. rewrite Any.upcast_downcast. grind. unfold freeF. sim_red.
      do 4 (pfold; sim_tau; left). sim_red.
      rewrite PSTATE. rewrite Any.upcast_downcast. grind. unfold unptr. des_ifs; sim_red.
      1:{ sim_triggerUB. }
      unfold Mem.free. destruct (Mem.cnts m blk ofs) eqn:MEMCNT; ss.
      2:{ sim_triggerUB. }
      sim_red.
      pfold. econs 6; clarify.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { econs. }
      eexists. exists (step_tau _).
      eexists. left. do 7 (pfold; sim_tau; left). sim_red.
      pfold. econs 6; clarify.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { econs. }
      eexists. exists (step_tau _). eexists. right. eapply CIH.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      1,4,5,6: eauto.
      3:{ clarify. }
      3:{ i.
          match goal with
          | [ H1: match_states _ _ _ _ ?i0 _ |- match_states _ _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { ss. }
      eapply match_mem_free; eauto.
      instantiate (1:=ofs). instantiate (1:=blk). unfold Mem.free. rewrite MEMCNT. ss.

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Load. sim_red.
      ss. uo; des_ifs. eapply step_expr; eauto.
      i. sim_red. destruct rstate. ss. destruct l.
      { admit "ez: wf_r_state". }
      grind. unfold ordN in *. do 3 (pfold; sim_tau; left). sim_red.
      match goal with
      | [ MCONT: match_code _ ?_ge _ _ _ _ |- _ ] =>
        set (ge:=_ge) in *
      end.
      match goal with
      | [ MCONT: match_code _ _ ?_ms _ _ _ |- _ ] =>
        set (ms:=_ms) in *
      end.
      unfold cfun. rewrite Any.upcast_downcast. grind. unfold loadF. sim_red.
      do 4 (pfold; sim_tau; left). sim_red.
      rewrite PSTATE. rewrite Any.upcast_downcast. grind. unfold unptr. des_ifs; sim_red.
      1:{ sim_triggerUB. }
      unfold Mem.load. destruct (Mem.cnts m blk ofs) eqn:MEMCNT; ss.
      2:{ sim_triggerUB. }
      sim_red.
      pfold. econs 6; clarify.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_set. econs; eauto. ss. inv MM. apply MMEM in MEMCNT. des.
        unfold scale_ofs in *. unfold map_ofs in *. rewrite unwrap_Ptrofs_Int64_z; try nia; eauto. }
      eexists. exists (step_tau _).
      eexists. left.
      do 4 (pfold; sim_tau; left). sim_red. rewrite Any.upcast_downcast. grind.
      do 1 (pfold; sim_tau; left). pfold; sim_tau; right. eapply CIH.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      2,3,4,5,6: eauto.
      2: clarify.
      2:{ i.
          match goal with
          | [ H1: match_states _ _ _ _ ?i0 _ |- match_states _ _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { econs. i. admit "ez: match lenv". }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Store. sim_red.
      match goal with
      | [ MCONT: match_code _ ?_ge _ _ _ _ |- _ ] =>
        set (ge:=_ge) in *
      end.
      match goal with
      | [ MCONT: match_code _ _ ?_ms _ _ _ |- _ ] =>
        set (ms:=_ms) in *
      end.
      ss. uo; des_ifs. eapply step_expr; eauto. i. sim_red.
      eapply step_expr; eauto. i. sim_red.
      destruct rstate. ss. destruct l.
      { admit "ez: wf_r_state". }
      grind. unfold ordN in *. do 3 (pfold; sim_tau; left). sim_red.
      unfold cfun. rewrite Any.upcast_downcast. grind. unfold storeF. sim_red.
      do 4 (pfold; sim_tau; left). sim_red.
      rewrite PSTATE. rewrite Any.upcast_downcast. grind. unfold unptr. des_ifs; sim_red.
      2:{ sim_triggerUB. }
      unfold Mem.store. destruct (Mem.cnts m blk ofs) eqn:MEMCNT; ss.
      2:{ sim_triggerUB. }
      sim_red.

      hexploit match_mem_store; eauto.
      { instantiate (2:=rv0); instantiate (2:=ofs); instantiate (2:=blk). unfold Mem.store. des_ifs. }
      i. des.

      pfold. econs 6; clarify.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_store; eauto. ss. inv MM. unfold scale_ofs in *; unfold map_ofs in *.
        hexploit MMEM; eauto. i; des. rewrite unwrap_Ptrofs_Int64_z; try nia; eauto. }
      eexists. exists (step_tau _). eexists. left.
      do 7 (pfold; sim_tau; left). sim_red. pfold; sim_tau; right. eapply CIH.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      1,4,5,6: eauto.
      3: clarify.
      3:{ i.
          match goal with
          | [ H1: match_states _ _ _ _ ?i0 _ |- match_states _ _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { ss. }
      eauto.

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Cmp. sim_red.
      match goal with
      | [ MCONT: match_code _ ?_ge _ _ _ _ |- _ ] =>
        set (ge:=_ge) in *
      end.
      match goal with
      | [ MCONT: match_code _ _ ?_ms _ _ _ |- _ ] =>
        set (ms:=_ms) in *
      end.
      ss. uo; des_ifs. eapply step_expr; eauto. i. sim_red.
      eapply step_expr; eauto. i. sim_red.
      destruct rstate. ss. destruct l.
      { admit "ez: wf_r_state". }
      grind. unfold ordN in *. do 3 (pfold; sim_tau; left). sim_red.
      unfold cfun. rewrite Any.upcast_downcast. grind. unfold cmpF. sim_red.
      do 4 (pfold; sim_tau; left). sim_red.
      rewrite PSTATE. rewrite Any.upcast_downcast. grind.
      destruct (vcmp m rv rv0) eqn:VCMP; sim_red.
      2:{ sim_triggerUB. }
      des_ifs.
      + sim_red.
        pfold. econs 6; clarify.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_set. econs; eauto. econs; eauto; ss. eapply match_mem_cmp in VCMP; eauto. }
        eexists. exists (step_tau _).
        eexists. left.
        do 4 (pfold; sim_tau; left). sim_red. rewrite Any.upcast_downcast. grind.
        do 1 (pfold; sim_tau; left). pfold; sim_tau; right. eapply CIH.
        hexploit match_states_intro.
        { instantiate (2:=Skip). ss. }
        2,3,4,5,6: eauto.
        2: clarify.
        2:{ i.
            match goal with
            | [ H1: match_states _ _ _ _ ?i0 _ |- match_states _ _ _ _ ?i1 _ ] =>
              replace i1 with i0; eauto
            end.
            unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
        { econs. i. unfold Int.one. rewrite Int.signed_repr.
          2:{ unfold_Int_max_signed; unfold_Int_min_signed. ss. }
          admit "ez: match le". }
      + sim_red.
        pfold. econs 6; clarify.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_set. econs; eauto. econs; eauto; ss. eapply match_mem_cmp in VCMP; eauto. }
        eexists. exists (step_tau _).
        eexists. left.
        do 4 (pfold; sim_tau; left). sim_red. rewrite Any.upcast_downcast. grind.
        do 1 (pfold; sim_tau; left). pfold; sim_tau; right. eapply CIH.
        hexploit match_states_intro.
        { instantiate (2:=Skip). ss. }
        2,3,4,5,6: eauto.
        2: clarify.
        2:{ i.
            match goal with
            | [ H1: match_states _ _ _ _ ?i0 _ |- match_states _ _ _ _ ?i1 _ ] =>
              replace i1 with i0; eauto
            end.
            unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
        { econs. i. unfold Int.zero. rewrite Int.signed_repr.
          2:{ unfold_Int_max_signed; unfold_Int_min_signed. ss. }
          admit "ez: match le". }

  Admitted.

End PROOF.
