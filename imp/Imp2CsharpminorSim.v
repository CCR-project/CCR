From compcert Require Import Smallstep AST Integers Events Behaviors Errors.
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

Set Implicit Arguments.

(* Section SIM. *)

(*   Variable L0: STS.semantics. *)
(*   Variable L1: Smallstep.semantics. *)
(*   Variable idx: Type. *)
(*   Variable ord: idx -> idx -> Prop. *)

(*   Local Open Scope smallstep_scope. *)

(*   Variant _sim sim (i0 j0: idx) (st_src0: L0.(STS.state)) (st_tgt0: L1.(Smallstep.state)): Prop := *)
(*   | sim_fin *)
(*       retv *)
(*       (RANGE: (0 <= retv <= Int.max_unsigned)%Z) *)
(*       (SRT: _.(state_sort) st_src0 = final retv) *)
(*       (SRT: _.(Smallstep.final_state) st_tgt0 (Int.repr retv)) *)
(*       (DTM: (* sd_final_determ *) *)
(*          forall (s : Smallstep.state L1) (r1 r2 : int), *)
(*            Smallstep.final_state L1 s r1 -> Smallstep.final_state L1 s r2 -> r1 = r2) *)
(*     : *)
(*       _sim sim i0 j0 st_src0 st_tgt0 *)

(*   | sim_vis *)
(*       (SRT: _.(state_sort) st_src0 = vis) *)
(*       (SRT: exists _ev_tgt _st_tgt1, Step L1 st_tgt0 [_ev_tgt] _st_tgt1) *)
(*       (SIM: forall ev_tgt st_tgt1 *)
(*           (STEP: Step L1 st_tgt0 ev_tgt st_tgt1) *)
(*         , *)
(*           exists st_src1 ev_src (STEP: _.(step) st_src0 (Some ev_src) st_src1), *)
(*             (<<MATCH: Forall2 match_event ev_tgt [ev_src]>>) /\ *)
(*             (<<SIM: exists i1 j1, sim i1 j1 st_src1 st_tgt1>>)) *)
(*     : *)
(*       _sim sim i0 j0 st_src0 st_tgt0 *)

(*   | sim_demonic_src *)
(*       (SRT: _.(state_sort) st_src0 = demonic) *)
(*       (SIM: exists st_src1 *)
(*           (STEP: _.(step) st_src0 None st_src1) *)
(*         , *)
(*           exists i1, <<ORD: ord i1 i0>> /\ <<SIM: exists j1, sim i1 j1 st_src1 st_tgt0>>) *)
(*     : *)
(*       _sim sim i0 j0 st_src0 st_tgt0 *)

(*   | sim_demonic_tgt_dtm *)
(*       (*** WRONG DEF, Note: UB in tgt ***) *)
(*       (* (SIM: forall st_tgt1 *) *)
(*       (*     (STEP: Step L1 st_tgt0 E0 st_tgt1) *) *)
(*       (*   , *) *)
(*       (*     exists i1, <<ORD: ord i1 i0>> /\ <<SIM: sim i1 st_src0 st_tgt1>>) *) *)
(*       (DTM: strict_determinate_at L1 st_tgt0) *)
(*       (SIM: exists st_tgt1 *)
(*           (STEP: Step L1 st_tgt0 E0 st_tgt1) *)
(*         , *)
(*           exists j1, <<ORD: ord j1 j0>> /\ <<SIM: exists i1, sim i1 j1 st_src0 st_tgt1>>) *)
(*       (*** equivalent def ***) *)
(*       (* st_tgt1 *) *)
(*       (* (STEP: Step L1 st_tgt0 E0 st_tgt1) *) *)
(*       (* i1 *) *)
(*       (* (ORD: ord i1 i0) *) *)
(*       (* (SIM: sim i1 st_src0 st_tgt1) *) *)
(*     : *)
(*       _sim sim i0 j0 st_src0 st_tgt0 *)

(*   | sim_angelic_src *)
(*       (SRT: _.(state_sort) st_src0 = angelic) *)
(*       (SIM: forall st_src1 *)
(*           (STEP: _.(step) st_src0 None st_src1) *)
(*         , *)
(*           exists i1, <<ORD: ord i1 i0>> /\ <<SIM: exists j1, sim i1 j1 st_src1 st_tgt0>>) *)
(*     : *)
(*       _sim sim i0 j0 st_src0 st_tgt0 *)
(*   . *)

(*   Definition sim: _ -> _ -> _ -> _ -> Prop := paco4 _sim bot4. *)

(*   Lemma sim_mon: monotone4 _sim. *)
(*   Proof. *)
(*     ii. inv IN. *)

(*     - econs 1; et. *)
(*     - econs 2; et. i. exploit SIM; et. i; des. esplits; et. *)
(*     - econs 3; et. des. esplits; et. *)
(*     - econs 4; et. des. esplits; et. *)
(*     - econs 5; et. i. exploit SIM; et. i; des. esplits; et. *)
(*   Qed. *)

(* End SIM. *)

(* Hint Constructors _sim. *)
(* Hint Unfold sim. *)
(* Hint Resolve sim_mon: paco. *)

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

From compcert Require Import Csharpminor.

Section PROOF.

  Import ModSemL.

  Context `{Σ: GRA.t}.

  Definition ordN : nat -> nat -> Prop := fun a b => True.

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

  Ltac sim_red := Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); econs 3; ss; clarify; eexists; exists (step_tau _); eexists; split; auto.

  Ltac sim_triggerUB := pfold; ss; unfold triggerUB; (try sim_red); econs 5; i; ss; auto;
                        dependent destruction STEP; try (irw in x; clarify; fail).

  Lemma step_expr
        e te
        tcode tf tcont tge tle tm (src: ModL.t) (tgt: Csharpminor.program)
        r ms mn ge le rstate pstate ktr
        i0 i1
        (MLE: match_le le tle)
        (CEXP: compile_expr e = Some te)
        (SIM:
           forall rv trv,
             wf_val rv ->
             eval_expr tge empty_env tle tm te trv ->
             trv = map_val rv ->
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
        econs. inv MLE. specialize ML with (x:=v) (sv:=(Some v0)).
        hexploit ML; auto. i. des. ss. clarify.
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
        sim_red. specialize SIM with (rv:=v) (trv:= map_val v). apply SIM; auto.
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
        (MLE: match_le le tle)
        (CEXP: compile_exprs es = Some tes)
        (SIM:
           forall rvs trvs,
             Forall wf_val rvs ->
             eval_exprlist tge empty_env tle tm tes trvs ->
             trvs = List.map map_val rvs ->
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

  Variable mmem : Mem.t -> Memory.Mem.mem -> Prop.

  (* Variable src : Imp.program. *)
  (* Let src_mod := ImpMod.get_mod src. *)
  (* Variable tgt : Ctypes.program Clight.function. *)

  (* Let src_sem := ModL.compile (Mod.add_list ([src_mod] ++ [Mem])). *)
  (* Let tgt_sem := semantics2 tgt. *)

  Lemma compile_stmt_no_Sreturn
        gm src e
        (CSTMT: compile_stmt gm src = Some (Sreturn e))
    :
      False.
  Proof. destruct src; ss; uo; des_ifs; clarify. Qed.

  Theorem match_states_sim
          (src: Imp.program) tgt
          gm ge ms mn
          ist cst
          i0
          (MODNAME: mn = src.(name))
          (GMAP: gm = get_gmap src)
          (MODSEML: ms = (ImpMod.get_modL src).(ModL.enclose))
          (GENV: ge = Sk.load_skenv (ImpMod.get_modL src).(ModL.sk))
          (COMP: Imp2Csharpminor.compile src = OK tgt)
          (MS: match_states mmem gm ge ms mn ist cst)
    :
      <<SIM: sim (ModL.compile (Mod.add_list ([Mem] ++ [ImpMod.get_mod src]))) (semantics tgt) ordN i0 ist cst>>.
  Proof.
    move GMAP before ms. move MODSEML before GMAP. move GENV before MODSEML. move COMP before GENV.
    move MODNAME before COMP.
    revert_until MODNAME.
    pcofix CIH. i.
    inv MS.
    unfold ordN in *.
    destruct code.
    (* generalize dependent i0. generalize dependent j0. *)
    (* generalize dependent stack. generalize dependent next. generalize dependent CST. *)
    (* generalize dependent tcont. generalize dependent tcode. *)
    (* generalize dependent code. *)
    (* induction code; i. *)
    - ss. unfold itree_of_cont_stmt, itree_of_imp_cont.
      rewrite interp_imp_Skip. ss; clarify.
      (* move MM before tm. move ML before MM. move tcont before ML. *)
      (* revert_until ML. *)
      destruct tcont; ss; clarify.
      inv MCONT; clarify.
      { destruct s; ss; clarify.
        destruct tcont; clarify.
        - inv MSTACK.
          + 


        sim_red. pfold. econs 6; clarify.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_skip_seq. }


        }
      sim_red. pfold. econs 6; clarify.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_skip_seq. }
      eexists. eexists (step_tau _). eexists. sim_red. right.
      destruct rp. eapply CIH.
      hexploit match_states_intro; eauto.
      all: (destruct s; eauto).
      all: (generalize dependent tcont; induction tcont; i; ss; clarify; eauto).
      all: (eapply compile_stmt_no_Sreturn in CST; clarify).

    - ss. unfold itree_of_cont_stmt, itree_of_imp_cont.
      rewrite interp_imp_Assign. sim_red. grind.
      destruct (compile_expr e) eqn:EXP; uo; ss. destruct rp. grind.
      eapply step_expr; eauto. i.
      (* tau point *)
      unfold ordN in *.
      do 1 (pfold; sim_tau; left). sim_red.
      pfold. econs 6; auto.
      { admit "ez? strict_determinate_at". }
      eexists. eexists.
      { eapply step_set. eapply H0. }
      eexists. eexists.
      { eapply step_tau. }
      eexists. right. apply CIH.
      hexploit match_states_intro.
      { instantiate (2:=Skip). instantiate (2:=get_gmap src). ss. }
      2,3,4,5,7:eauto.
      2:{ unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. ss. }
      { econs. i. exists (map_val_opt sv); split; auto.
        admit "ez? alist & Maps.PTree". }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Seq. sim_red.
      ss. destruct (compile_stmt (get_gmap src) code1) eqn:CSC1; destruct (compile_stmt (get_gmap src) code2) eqn:CSC2; uo; clarify.

      set (next_seq:= 
    (fun r0 : r_state * p_state * (lenv * val) =>
     ` x : r_state * p_state * (lenv * val) <-
     (let (st1, v) := r0 in
      EventsL.interp_Es (prog (ImpMod.modsemL src (Sk.load_skenv (defs src))))
        (transl_all (name src) (let (le1, _) := v in interp_imp (Sk.load_skenv (defs src)) (denote_stmt code2) le1)) st1);; next x)).

      (* tau point *)
      pfold. econs 6; ss; clarify.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_seq. }
      eexists. eexists.
      { eapply step_tau. }
      eexists. right. eapply CIH.
      hexploit match_states_intro.
      { eapply CSC1. }
      3:{ instantiate (1:=Kseq s0 tcont). ss. destruct s0; eauto. eapply compile_stmt_no_Sreturn in CSC2; clarify. }
      3:{ econs 2; eauto. clarify. }
      all: eauto.
      { ss. destruct s0; eauto. eapply compile_stmt_no_Sreturn in CSC2; clarify. }
      i.
      match goal with
      | [ H: match_states _ _ _ _ _ ?it0 _ |- match_states _ _ _ _ _ ?it1 _ ] =>
        replace it1 with it0; eauto
      end.
      unfold itree_of_cont_stmt, itree_of_imp_cont.
      Red.prw ltac:(_red_gen) 1 0. grind.

    - unfold itree_of_cont_stmt in *; unfold itree_of_imp_cont in *. rewrite interp_imp_If. sim_red. ss.
      destruct (compile_expr i) eqn:CEXPR; destruct (compile_stmt (get_gmap src) code1) eqn:CCODE1;
        destruct (compile_stmt (get_gmap src) code2) eqn:CCODE2; uo; clarify.
      destruct rp. eapply step_expr; eauto.
      i. sim_red. destruct (is_true rv) eqn:COND; ss; clarify.
      2:{ sim_triggerUB. }
      sim_red. destruct rv; clarify. ss. destruct (n =? 0)%Z eqn:CZERO; ss; clarify.
      { rewrite Z.eqb_eq in CZERO. clarify.
        (* tau point *)
        pfold. econs 6; ss.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_ifthenelse; ss.
          econs; eauto.
          + econs. ss.
          + ss. }
        eexists. eexists.
        { eapply step_tau. }
        eexists. des_ifs. right. eapply CIH.
        hexploit match_states_intro; eauto. }
      { rewrite Z.eqb_neq in CZERO.
        (* tau point *)
        pfold. econs 6; ss.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_ifthenelse.
          - econs; eauto.
            + econs. ss.
            + ss.
          - ss. destruct (negb (Int64.eq (to_long n) Int64.zero)) eqn:CONTRA; ss; clarify.
            rewrite negb_false_iff in CONTRA. apply Int64.same_if_eq in CONTRA.
            unfold to_long in CONTRA. unfold Int64.zero in CONTRA.
            admit "ez: int64 extenttionality with wf-ed values". }
        eexists. eexists.
        { eapply step_tau. }
        eexists. des_ifs. right. eapply CIH.
        hexploit match_states_intro.
        { eapply CCODE1. }
        all: eauto. }

    - ss. uo; des_ifs.
      unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_CallFun.
      des_ifs; sim_red.
      { sim_triggerUB. }
      unfold Imp2Csharpminor.compile in COMP. unfold _compile in COMP. des_ifs.
      unfold compile_gdefs in Heq2. uo; des_ifs; clarify.
      match goal with
      | [ |- paco3 (_sim _ (semantics ?tp) _) _ _ _ _ ] =>
        set (tgtp:=tp)
      end.
      destruct rp. eapply step_exprs; eauto.
      { admit "mid: index". }
      i. sim_red. destruct r0. destruct l0.
      { ss. admit "mid?: r_state is nil". }
      ss. grind. unfold ordN in *.
      do 3 (pfold; sim_tau; left). sim_red.
      match goal with
      | [ |- paco3 _ _ _ (r0 <- unwrapU (?f);; _) _ ] => destruct f eqn:FSEM; ss
      end.
      2:{ sim_triggerUB. }
      grind.
      rewrite find_map in FSEM.
      match goal with
      | [ FSEM: o_map (?a) _ = _ |- _ ] => destruct a eqn:FOUND; ss; clarify
      end.
      destruct p0. destruct p0. clarify.
      rewrite find_map in FOUND.
      match goal with
      | [ FOUND: o_map (?a) _ = _ |- _ ] => destruct a eqn:FOUND2; ss; clarify
      end.

      (* make lemma *)
      assert (COMPF: exists tf0, compile_function (get_gmap src) f0 = Some tf0).
      { admit "ez: use FOUND2". }
      destruct COMPF as [tf0 COMPF].
      assert (SRCF: In (f, f0) (prog_funs src)).
      { admit "ez: trivial, use FOUND2". }
      assert (TGTF: In (s2p f, AST.Gfun (AST.Internal tf0)) l1).
      { admit "ez: by definition". }
      assert (TGTFG: In (s2p f, AST.Gfun (AST.Internal tf0)) tgtp.(AST.prog_defs)).
      { admit "mid?: need to construct tgt's genv". }
      eapply Globalenvs.Genv.find_symbol_exists in TGTFG.
      destruct TGTFG as [b TGTFG].
      assert (TGTGFIND: Globalenvs.Genv.find_def (Globalenvs.Genv.globalenv tgtp) b = Some (Gfun (Internal tf0))).
      { admit "mid? from construction of tgt's genv". }

      unfold ident_key in Heq0.
      assert (SIG: s = make_signature (Datatypes.length (Imp.fn_params f0))).
      { admit "ez: trivial, use FOUND2". }
      clarify.

      unfold compile_function in COMPF. uo; des_ifs. rename s into bodytf0.
      assert (COMPFRET: forall tfd0 tf0, In tfd0 l1 -> snd tfd0 = AST.Gfun (AST.Internal tf0) ->
                                    tf0.(fn_body) = Sseq (bodytf0) (Sreturn (Some (Evar (s2p "return"))))).
      { admit "ez: trivial by definition". }

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

      eexists. exists (step_tau _).
      eexists. left.
      pfold. econs 4.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_internal_function; ss; eauto.
        - econs.
        - admit "ez: need wf condition for a Imp.program & lemmas".
        - admit "ez: need wf condition for a Imp.program & lemmas".
        - econs.
        - admit "ez: need wf condition for a Imp.program & lemmas". }
      eexists; split; auto. grind. left.

      pfold. econs 4.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_seq. }
      eexists; split; auto. right.
      eapply CIH.
      set (ge:= Sk.load_skenv (defs src)).
      set (ms:=ImpMod.modsemL src ge).
      set (mn:=name src).
      match goal with
      | [ |- match_states _ _ _ _ _ (?i) _] =>
        replace i with
    (` r0 : r_state * p_state * (lenv * val) <-
     EventsL.interp_Es (prog ms)
       (transl_all mn (interp_imp ge (denote_stmt (Imp.fn_body f0)) (init_lenv (Imp.fn_vars f0) ++ l2)))
       (c, ε :: c0 :: l0, p);; x4 <- itree_of_imp_pop ge ms mn mn x le r0;; ` x : _ <- next x4;; stack x)
      end.
      2:{ rewrite interp_imp_bind. Red.prw ltac:(_red_gen) 1 0. grind.
          Red.prw ltac:(_red_gen) 2 0. grind.
          Red.prw ltac:(_red_gen) 2 0. Red.prw ltac:(_red_gen) 1 0. grind.
          Red.prw ltac:(_red_gen) 2 0. Red.prw ltac:(_red_gen) 1 0. grind. }

      hexploit match_states_intro.
      4:{ instantiate (1:=Kseq (Sreturn (Some (Evar (s2p "return")))) (Kcall (Some (s2p x)) tf empty_env tle tcont)). ss. }
      5:{ instantiate (1:= fun r0 =>
                             ` x4 : r_state * p_state * (lenv * val) <- itree_of_imp_pop ge ms mn mn x le r0;;
                                    ` x0 : r_state * p_state * (lenv * val) <- next x4;; stack x0).
          instantiate (1:=mn). instantiate (1:=ms). instantiate (1:=ge). instantiate (1:=get_gmap src).
          econs 2; ss; eauto. }
      3: eauto.
      1:{ eapply Heq5. }
      4:{ instantiate (9:= EventsL.interp_Es (prog ms) (transl_all mn (interp_imp ge (denote_stmt (Imp.fn_body f0)) (init_lenv (Imp.fn_vars f0) ++ l1))) (c, ε :: c0 :: l0, p)). i.
          match goal with
          | [ H1: match_states _ _ _ _ _ ?i0 _ |- match_states _ _ _ _ _ ?i1 _] =>
            replace i1 with i0; eauto
          end.
          unfold idK. grind. }
      { instantiate (2:=f0.(Imp.fn_body)). admit "ez: fn_body is THE stmt we get by compiling". }
      { instantiate (2:=(init_lenv (Imp.fn_vars f0) ++ l1)). admit "ez?: the initial lenv of function". }
      { unfold itree_of_cont_stmt, itree_of_imp_cont. ss. }
    - ss. destruct p eqn:PVAR; clarify. 
      admit "ez: CallPtr, similar to CallFun.".
    - admit "mid: CallSys".
    - admit "hard: AddrOf".
    - admit "hard: Malloc".
    - admit "hard: free".
    - admit "hard: Load".
    - admit "hard: Store".
    - admit "hard: Cmp".
  Admitted.

End PROOF.
