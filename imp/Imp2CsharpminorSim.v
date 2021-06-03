From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors.
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

From compcert Require Import Csharpminor.

Section MATCH.

  Fixpoint get_cont_stmts (cc: cont) : list Csharpminor.stmt :=
    match cc with
    | Kseq s k => s :: (get_cont_stmts k)
    | _ => []
    end
  .

  Fixpoint wf_ccont (k: cont) : Prop :=
    match k with
    | Kseq s k2 =>
      match s with
      | Sreturn _ =>
        match k2 with
        | Kstop => True
        | Kcall _ _ env _ k3 => (env = empty_env /\ wf_ccont k3)
        | _ => False
        end
      | _ => wf_ccont k2
      end
    | _ => False
    end
  .

  Fixpoint get_cont_stack k : option cont :=
    match k with
    | Kseq s k2 =>
      match s with
      | Sreturn _ =>
        match k2 with
        | Kstop | Kcall _ _ _ _ _ => Some k
        | _ => None
        end
      | _ => get_cont_stack k2
      end
    | _ => None
    end
  .

  Lemma wf_cont_has_stack
        k
        (WFCCONT: wf_ccont k)
    :
      exists ks, get_cont_stack k = Some ks.
  Proof.
    revert_until k.
    induction k; i; ss; clarify.
    destruct s; ss; clarify; eauto.
    destruct k; ss; clarify; eauto.
  Qed.

  Context `{Σ: GRA.t}.

  Definition itree_of_imp_cont {T} (itr: itree _ T) :=
    fun ge le ms mn rp =>
      EventsL.interp_Es (ModSemL.prog ms) (transl_all mn (interp_imp ge itr le)) rp.

  Definition itree_of_imp_ret :=
    fun ge le ms mn rp =>
      itree_of_imp_cont (denote_expr (Var "return"%string)) ge le ms mn rp.

  Lemma itree_of_imp_cont_bind
        T R ge le ms mn rp (itr: itree _ T) (ktr: T -> itree _ R)
    :
      itree_of_imp_cont (x <- itr;; ktr x) ge le ms mn rp
      =
      '(r, p, (le2, v)) <- (itree_of_imp_cont itr ge le ms mn rp);; (itree_of_imp_cont (ktr v) ge le2 ms mn (r, p)).
  Proof.
    unfold itree_of_imp_cont. rewrite interp_imp_bind. grind.    
    rewrite! transl_all_bind; rewrite! EventsL.interp_Es_bind.
    grind. destruct p0. grind.
  Qed.

  Definition itree_of_imp_pop :=
    fun ge ms mn retmn (retx: var) (retle: lenv) (x: _ * _ * (lenv * val)) =>
      let '(r, p, (le0, _)) := x in
      '(r2, p2, rv) <- EventsL.interp_Es (ModSemL.prog ms) (transl_all mn ('(_, v) <- interp_imp ge (denote_expr (Var "return"%string)) le0;; Ret (v↑))) (r, p);;
      '(r3, p3, rv) <- EventsL.interp_Es (ModSemL.prog ms) (trigger EventsL.PopFrame;; (tau;; Ret rv)) (r2, p2);;
      pop <- EventsL.interp_Es (ModSemL.prog ms) (transl_all retmn (tau;; tau;; v0 <- unwrapN (rv↓);; (tau;; tau;; tau;; Ret (alist_add retx v0  retle, Vundef)))) (r3, p3);;
      Ret pop.

  Definition itree_of_imp_pop_bottom :=
    fun ge ms mn (x: _ * _ * (lenv * val)) =>
      let '(r, p, (le0, _)) := x in
      '(r2, p2, rv) <- EventsL.interp_Es (ModSemL.prog ms) (transl_all mn ('(_, v) <- interp_imp ge (denote_expr (Var "return"%string)) le0;; Ret (v↑))) (r, p);;
      '(_, _, rv) <- EventsL.interp_Es (ModSemL.prog ms) (trigger EventsL.PopFrame;; (tau;; Ret rv)) (r2, p2);;
      Ret rv.

  Definition itree_of_cont_stmt (s : Imp.stmt) :=
    fun ge le ms mn rp => itree_of_imp_cont (denote_stmt s) ge le ms mn rp.

  Definition imp_state := itree eventE Any.t.
  Definition imp_cont {T} {R} := (r_state * p_state * (lenv * T)) -> itree eventE (r_state * p_state * (lenv * R)).
  Definition imp_stack := (r_state * p_state * (lenv * val)) -> imp_state.

  (* tlof will be 1 + number of external symbols *)
  (* Hypothesis archi_ptr64 : Archi.ptr64 = true. *)

  Variable tlof : nat.

  Definition map_val (v : Universe.val) : Values.val :=
    match v with
    | Vint z => Values.Vlong (to_long z)
    | Vptr blk ofs =>
      Values.Vptr (Pos.of_nat (tlof + blk)) (Ptrofs.repr ofs)
    | Vundef => Values.Vundef
    end.

  (* Definition map_val_opt (optv : option Universe.val) : option Values.val := *)
  (*   match optv with *)
  (*   | Some v => Some (map_val v) *)
  (*   | None => None *)
  (*   end. *)

  Variant match_le : lenv -> temp_env -> Prop :=
  | match_le_intro
      sle tle
      (ML: forall x sv,
          (alist_find x sle = Some sv) ->
          (Maps.PTree.get (s2p x) tle = Some (map_val sv)))
    :
      match_le sle tle.

  (* prog_defs has offset of 1 + length(efuns ++ evars ++ init_g) = tlof then Imp.defs *)
  Variant match_ge : SkEnv.t -> (Genv.t fundef ()) -> Prop :=
  | match_ge_intro
      sge tge
      (MG: forall symb blk,
          (sge.(SkEnv.id2blk) symb = Some blk) ->
          (Maps.PTree.get (s2p symb) tge.(Genv.genv_symb) = Some (Pos.of_nat (tlof + blk))))
    :
      match_ge sge tge.

  Definition id2blk_cgenv (src: Imp.program) (id: string) : option positive :=
    match compile src with
    | Error _ => None
    | OK tgt =>
      let tgenv := Genv.globalenv tgt in
      Genv.find_symbol tgenv (s2p id)
    end.

  Lemma id2blk_cgenv_correct
        (src: Imp.program) tgt tgenv id
        (COMP: compile src = OK tgt)
        (TGE: tgenv = Genv.globalenv tgt)
    :
      Genv.find_symbol tgenv (s2p id) = id2blk_cgenv src id.
  Proof.
    unfold id2blk_cgenv. clarify. rewrite COMP. auto.
  Qed.

  Definition ret_call_cont k :=
    (Kseq (Sreturn (Some (Evar (s2p "return")))) (call_cont k)).
  (* global env is fixed when src program is fixed *)
  Variable gm : gmap.
  Variable ge : SkEnv.t.
  (* ModSem should be fixed with src too *)
  Variable ms : ModSemL.t.
  (* (* Current function's module name *) *)
  (* Variable mn : mname. *)

  Inductive match_code (mn: mname) : imp_cont -> (list Csharpminor.stmt) -> Prop :=
  | match_code_return
    :
      match_code mn idK [Sreturn (Some (Evar (s2p "return")))]
  | match_code_cont
      code itr ktr chead ctail
      (CST: compile_stmt gm code = Some chead)
      (ITR: itr = fun '(r, p, (le, _)) => itree_of_cont_stmt code ge le ms mn (r, p))
      (MCONT: match_code mn ktr ctail)
    :
      match_code mn (fun x => (itr x >>= ktr)) (chead :: ctail)
  .

  Inductive match_stack (mn: mname) : imp_stack -> option Csharpminor.cont -> Prop :=
  | match_stack_bottom
    :
      match_stack mn (fun x => itree_of_imp_pop_bottom ge ms mn x) (Some (ret_call_cont Kstop))

  | match_stack_cret
      tf le tle next stack tcont id tid tpop retmn
      (MLE: match_le le tle)
      (MID: s2p id = tid)

      (WFCONT: wf_ccont tcont)
      (MCONT: match_code retmn next (get_cont_stmts tcont))
      (MSTACK: match_stack retmn stack (get_cont_stack tcont))

      (TPOP: tpop = ret_call_cont (Kcall (Some tid) tf empty_env tle tcont))
    :
      match_stack mn (fun x => (y <- (itree_of_imp_pop ge ms mn retmn id le x);; next y >>= stack)) (Some tpop)
  .

  Variable match_mem : Mem.t -> Memory.Mem.mem -> Prop.

  Variant match_states : imp_state -> Csharpminor.state -> Prop :=
  | match_states_intro
      tf rstate pstate le tle code itr tcode m tm next stack tcont mn
      (CST: compile_stmt gm code = Some tcode)
      (ML: match_le le tle)

      (PSTATE: pstate "Mem"%string = m↑)
      (MM: match_mem m tm)
      (* (MG: match_ge ge tge) *)
      (WFCONT: wf_ccont tcont)
      (MCONT: match_code mn next (get_cont_stmts tcont))
      (MSTACK: match_stack mn stack (get_cont_stack tcont))
      (ITR: itr = itree_of_cont_stmt code ge le ms mn (rstate, pstate))
    :
      match_states (x <- itr;; next x >>= stack) (State tf tcode tcont empty_env tle tm)
  .

  (* Definition alist_add_option optid v (le : lenv) := *)
  (*   match optid with *)
  (*   | None => le *)
  (*   | Some id => alist_add id v le *)
  (*   end. *)

  (* Variant match_id : option var -> option ident -> Prop := *)
  (* | match_id_None *)
  (*   : *)
  (*     match_id None None *)
  (* | match_id_Some *)
  (*     v *)
  (*   : *)
  (*     match_id (Some v) (Some (s2p v)). *)

End MATCH.

Section GENV.

  Context `{Σ: GRA.t}.

  Variable src : Imp.programL.
  (* Let m : ModL.t := ImpMod.get_modL src. *)
  (* Let ms := ModL.enclose m. *)

  Lemma found_imp_function
        f mn fn impf
        (FOUND : find
                   (((fun fnsem : string * (Any.t -> itree EventsL.Es Any.t) => dec f (fst fnsem)) : _ -> bool) <*>
                    (fun '(mn0, (fn0, f0)) => (fn0, fun a : Any.t => transl_all mn0 (cfun (eval_imp (Sk.load_skenv (defsL src)) f0) a)))) 
                   (prog_funsL src) = Some (mn, (fn, impf)))
    :
      (fn = f) /\ (In (mn, (fn, impf)) (prog_funsL src)).
  Proof.
    apply find_some in FOUND. des. split; auto.
    unfold compose in FOUND0. ss. des_sumbool. auto.
  Qed.

  Lemma gm_int_fun_exists
        gm mn fn impf
        (GMAP: get_gmap src = Some gm)
        (INSRC: In (mn, (fn, impf)) (prog_funsL src))
    :
      exists g, In (s2p fn, Gfun (Internal g)) (_int_funs gm).
  Proof.
    unfold get_gmap in GMAP. uo; des_ifs. ss. clear l0.
    unfold pre_compile_iFuns in Heq0. des_ifs.
    rewrite List.map_map in f.
    rewrite Forall_forall in f.
    do 2 (rewrite List.map_map).
    match goal with
    | [ |- exists _, In _ (List.map ?_mapf _) ] =>
      set (mapf:=_mapf) in *
    end.
    assert (SAVED: In (mn, (fn, impf)) (prog_funsL src)); auto.
    apply (in_map mapf _ _) in INSRC.
    subst mapf. ss. des_ifs.
    - exists f0. apply INSRC.
    - specialize f with (x:=None). ss.
      match goal with
      | [ f : In _ (List.map ?_mapf _) -> _ |- _ ] =>
        set (mapf:=_mapf) in *
      end.
      apply (in_map mapf _ _) in SAVED. subst mapf.
      ss. rewrite Heq0 in SAVED. ss.
  Qed.

  Lemma exists_compiled_function
        gm cfs mn fn impf
        (GMAP: get_gmap src = Some gm)
        (COMP: get_iFuns gm (_int_funs gm) = Some cfs)
        (INSRC: In (mn, (fn, impf)) (prog_funsL src))
    :
      exists precf cf,
        (pre_compile_function impf = Some precf /\
         In (s2p fn, Gfun (Internal precf)) (_int_funs gm) /\
         get_function gm (Gfun (Internal precf)) = Some (Gfun (Internal cf)) /\
         In (s2p fn, Gfun (Internal cf)) cfs).
  Proof.
    Local Opaque get_function.
    unfold get_gmap in GMAP. uo; des_ifs. ss.
    match goal with
    | [ COMP: get_iFuns ?_gm _ = Some _ |- _ ] =>
      set (gm:=_gm) in *
    end.
    unfold pre_compile_iFuns in Heq0. des_ifs; ss.
    rewrite List.Forall_map in f. rewrite List.Forall_map in f.
    rewrite Forall_forall in f. hexploit f.
    { apply INSRC. }
    i. ss. des_ifs; ss; clarify. exists f0.
    unfold get_iFuns in COMP. des_ifs; ss.
    do 4 (rewrite List.Forall_map in f1). rewrite Forall_forall in f1.
    hexploit f1.
    { apply INSRC. }
    i. ss. des_ifs; ss; clarify.
    Local Transparent get_function.
    assert (SAVED: get_function gm (Gfun (Internal f0)) = Some g0); auto.
    unfold get_function in Heq2. uo. destruct (compile_stmt gm (fn_body2 f0)) eqn:CSF0.
    2:{ clarify. }
    match goal with
    | [ Heq2: Some (Gfun (Internal ?_cf)) = Some _ |- _ ] =>
      set (cf:=_cf)
    end.
    clarify.
    Local Opaque get_function.
    exists cf.
    split; auto. split; auto.
    { do 2 (rewrite List.map_map).
      match goal with
      | [ |- In _ (List.map ?_mapf _) ] =>
        set (mapf:=_mapf) in *
      end.
      apply (in_map mapf _ _) in INSRC.
      subst mapf. ss. des_ifs. }

    split; auto.
    do 4 (rewrite List.map_map).
    match goal with
    | [ |- In _ (List.map ?_mapf _) ] =>
      set (mapf:=_mapf) in *
    end.
    apply (in_map mapf _ _) in INSRC.
    assert (mapf (mn, (fn, impf)) = (s2p fn, Gfun (Internal cf))).
    { subst mapf. ss. rewrite Heq1. rewrite SAVED. ss. }
    rewrite <- H1. auto.
    Local Transparent get_function.
  Qed.

  Lemma in_tgt_prog_defs_ifuns
        gm tgt mn fn impf precf cf
        (GMAP: get_gmap src = Some gm)
        (COMP: compile2 src = OK tgt)
        (INSRC: In (mn, (fn, impf)) (prog_funsL src))
        (PRECF: pre_compile_function impf = Some precf)
        (COMPF: get_function gm (Gfun (Internal precf)) = Some (Gfun (Internal cf)))
    :
      In (s2p fn, Gfun (Internal cf)) tgt.(prog_defs).
  Proof.
    unfold compile2 in COMP. unfold _compile2 in COMP. des_ifs.
    unfold compile_gdefs in Heq0. uo; des_ifs.
    hexploit exists_compiled_function; eauto.
    i. des. clarify. ss. do 2 (apply in_or_app; right).
    ss. do 2 right. apply in_or_app; left. auto.
  Qed.

  Lemma in_tgt_prog_defs_efuns
        gm tgt fn sig
        (GMAP: get_gmap src = Some gm)
        (COMP: compile2 src = OK tgt)
        (INSRC: In (fn, sig) (ext_funsL src))
    :
      In (s2p fn, Gfun (External (EF_external fn (make_signature sig)))) tgt.(prog_defs).
  Proof.
    unfold compile2 in COMP. unfold _compile2 in COMP. des_ifs.
    unfold compile_gdefs in Heq0. uo; des_ifs. ss.
    apply in_or_app. left. 
    clear Heq0 l0 l1.
    unfold get_gmap in Heq. uo; des_ifs; ss; clarify.
    unfold compile_eFuns. rewrite List.map_map.
    match goal with
    | [ |- In _ (List.map ?_mapf _) ] =>
      set (mapf:=_mapf) in *
    end.
    apply (in_map mapf _ _) in INSRC.
    match goal with
    | [ INSRC: In ?p0 _ |- In ?p1 _ ] =>
      replace p1 with p0; auto
    end.
  Qed.

  Lemma compiled_function_props
        gm impf precf cf
        (GMAP: get_gmap src = Some gm)
        (PRECF: pre_compile_function impf = Some precf)
        (COMPF: get_function gm (Gfun (Internal precf)) = Some (Gfun (Internal cf)))
    :
      (cf.(fn_sig) = precf.(fn_sig2)) /\
      (exists tfbody, compile_stmt gm impf.(Imp.fn_body) = Some tfbody /\
                 cf.(fn_body) = Sseq tfbody (Sreturn (Some (Evar (s2p "return"))))) /\
      (cf.(fn_vars) = [] ) /\
      (Coqlib.list_norepet (fn_params cf)) /\
      (Coqlib.list_disjoint (fn_params cf) (fn_temps cf)).
  Proof.
    unfold pre_compile_function in PRECF. uo; des_ifs. ss.
    uo; des_ifs. ss.
    split; auto.
    split; auto.
    { exists s; split; auto. }
    split; auto. split; auto.
    { apply Coqlib.list_norepet_append_left in l. auto. }
    apply Coqlib.list_norepet_app in l. des; auto.
  Qed.

  Lemma gm_funs_disjoint
        gm
        (GMAP: get_gmap src = Some gm)
    :
      Coqlib.list_disjoint (List.map fst (_int_funs gm)) (List.map fst (_ext_funs gm)).
  Proof.
    unfold get_gmap in GMAP. uo; des_ifs. ss.
    rewrite map_app in l0. rewrite map_app in l0.
    rewrite app_assoc in l0.
    apply Coqlib.list_norepet_append_left in l0.
    rewrite Coqlib.list_norepet_app in l0. des.
    clear Heq0 l0 l1. clarify.
  Qed.

  Lemma gm_unique
        gm fn f g
        (GMAP: get_gmap src = Some gm)
        (IN1: In (s2p fn, f) (gm.(_int_funs) ++ gm.(_ext_funs) ++ gm.(_int_vars) ++ gm.(_ext_vars)))
        (IN2: In (s2p fn, g) (gm.(_int_funs) ++ gm.(_ext_funs) ++ gm.(_int_vars) ++ gm.(_ext_vars)))
    :
      f = g.
  Proof.
    unfold get_gmap in GMAP. uo; des_ifs. ss.
    match goal with
    | [ IN1: In _ ?_ll |- _ ] =>
      remember _ll as ll
    end.
    clear Heq0 Heqll l. move ll before src. revert_until src. induction ll; i; clarify; ss.
    inv l0. des; clarify; ss.
    - apply (in_map fst _ _) in IN2. ss.
    - apply (in_map fst _ _) in IN1. ss.
    - hexploit IHll; eauto.
  Qed.

  Lemma gm_unique_intfun
        gm fn f g
        (GMAP: get_gmap src = Some gm)
        (IN1: In (s2p fn, f) (_int_funs gm))
        (IN2: In (s2p fn, g) (_int_funs gm))
    :
      f = g.
  Proof.
    hexploit gm_unique.
    { eauto. }
    { eapply in_or_app. left. eapply IN1. }
    { eapply in_or_app. left. eapply IN2. }
    auto.
  Qed.

  Lemma tgt_genv_match_symb_def
        tgt name b gd1 gd2
        (COMP: compile2 src = OK tgt)
        (GFSYM: Genv.find_symbol (Genv.globalenv tgt) (s2p name) = Some b)
        (GFDEF: Genv.find_def (Genv.globalenv tgt) b = Some gd1)
        (INTGT: In (s2p name, gd2) (prog_defs tgt))
    :
      gd1 = gd2.
  Proof.
    unfold compile2 in COMP. des_ifs. rename Heq into GMAP. rename g into gm.
    unfold _compile2 in COMP. des_ifs. rename Heq into CGDEFS. rename l into cgdefs.
    rename l0 into WFCGDEFS.
    match goal with
    | [ INTGT: In _ (prog_defs ?_tgt) |- _ ] =>
      remember _tgt as tgt
    end.
    hexploit prog_defmap_norepet.
    { unfold prog_defs_names. instantiate (1:=tgt). rewrite Heqtgt. ss. }
    { eapply INTGT. }
    i. apply Genv.find_def_symbol in H. des. clarify.
  Qed.

  Lemma tgt_genv_find_def_by_blk
        tgt name b gd
        (COMP: compile2 src = OK tgt)
        (GFSYM: Genv.find_symbol (Genv.globalenv tgt) (s2p name) = Some b)
        (INTGT: In (s2p name, gd) (prog_defs tgt))
    :
      Genv.find_def (Genv.globalenv tgt) b = Some gd.
  Proof.
    unfold compile2 in COMP. des_ifs. rename Heq into GMAP. rename g into gm.
    unfold _compile2 in COMP. des_ifs. rename Heq into CGDEFS. rename l into cgdefs.
    rename l0 into WFCGDEFS.
    match goal with
    | [ INTGT: In _ (prog_defs ?_tgt) |- _ ] =>
      remember _tgt as tgt
    end.
    hexploit prog_defmap_norepet.
    { unfold prog_defs_names. instantiate (1:=tgt). rewrite Heqtgt. ss. }
    { eapply INTGT. }
    i. apply Genv.find_def_symbol in H. des. clarify.
  Qed.

End GENV.

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

  Import ModSemL.

  Context `{Σ: GRA.t}.

  Definition ordN : nat -> nat -> Prop := fun a b => True.

  Lemma map_val_vadd_comm
        tlof a b v
        (VADD: vadd a b = Some v)
        (WFA: wf_val a)
        (WFB: wf_val b)
        (WFV: wf_val v)
    :
      Values.Val.addl (map_val tlof a) (map_val tlof b) = map_val tlof v.
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
        e te tlof
        tcode tf tcont tge tle tm (src: ModL.t) (tgt: Csharpminor.program)
        r ms mn ge le rstate pstate ktr
        i0 i1
        (MLE: match_le tlof le tle)
        (CEXP: compile_expr e = Some te)
        (SIM:
           forall rv trv,
             wf_val rv ->
             eval_expr tge empty_env tle tm te trv ->
             trv = map_val tlof rv ->
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
        sim_red. specialize SIM with (rv:=v) (trv:= map_val tlof v). apply SIM; auto.
        econs; eauto. ss. f_equal. apply map_val_vadd_comm; auto.
      + sim_triggerUB.
    -
  Admitted.

  Variable EMI : nat.

  Lemma step_exprs
        es tes tlof
        tcode tf tcont tge tle tm (src: ModL.t) (tgt: Csharpminor.program)
        r ms mn ge le rstate pstate ktr
        i0 i1
        (IDX: i0 = (List.length es)*EMI + i1)
        (MLE: match_le tlof le tle)
        (CEXP: compile_exprs es = Some tes)
        (SIM:
           forall rvs trvs,
             Forall wf_val rvs ->
             eval_exprlist tge empty_env tle tm tes trvs ->
             trvs = List.map (map_val tlof) rvs ->
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
          (src: Imp.programL) tgt
          (modl: ModL.t) gm ge ms tlof
          ist cst
          i0
          (TLOF: tlof = 3 + (List.length src.(ext_funsL)) + (List.length src.(ext_varsL)))
          (GMAP: get_gmap src = Some gm)
          (MODL: modl = (ModL.add (Mod.lift Mem) (ImpMod.get_modL src)))
          (MODSEML: ms = modl.(ModL.enclose))
          (GENV: ge = Sk.load_skenv modl.(ModL.sk))
          (COMP: Imp2Csharpminor.compile2 src = OK tgt)
          (MS: match_states tlof gm ge ms mmem ist cst)
    :
      <<SIM: sim (ModL.compile modl) (semantics tgt) ordN i0 ist cst>>.
  Proof.
    move GMAP before ms. move MODSEML before GMAP. move GENV before MODSEML. move COMP before GENV.
    move TLOF before COMP. move MODL before COMP.
    revert_until TLOF.
    pcofix CIH. i.
    inv MS.
    unfold ordN in *.
    unfold compile2 in COMP. des_ifs. rename Heq into GMAP.
    set (tlof := 3 + (List.length src.(ext_funsL)) + (List.length src.(ext_varsL))) in *.
    destruct code.
    - unfold itree_of_cont_stmt, itree_of_imp_cont.
      rewrite interp_imp_Skip. ss; clarify.
      destruct tcont; ss; clarify.
      inv MCONT; clarify.
      { destruct tcont; inv MSTACK; ss; clarify.
        - sim_red. pfold. econs 6; clarify.
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
          { eapply step_return_1; ss; eauto.
            econs. inv ML; ss; clarify. hexploit ML0; i; eauto. }
          eexists. exists (step_tau _). eexists. left.
          do 1 (pfold; sim_tau; left).
          sim_red. unfold assume. grind.
          pfold. econs 5; ss; auto. i. eapply angelic_step in STEP; des; clarify.
          eexists; split; auto. left.
          do 6 (pfold; sim_tau; left). sim_red.
          destruct rstate. ss. destruct l.
          { admit "ez: wf_rstate". }
          do 3 (pfold; sim_tau; left). sim_red.
          pfold. econs 1; eauto.
          { admit "ez: main's wf_retval". }
          { ss. unfold state_sort. ss. rewrite Any.upcast_downcast.
            admit "ez: main's wf_retval". }
          { ss. admit "ez: tgt main's wf_retval". }

        - destruct WFCONT as [ENV WFCONT]; clarify.
          unfold ret_call_cont in TPOP. clarify.
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
          { eapply step_return_1; ss; eauto.
            econs. inv ML; ss; clarify. hexploit ML0; i; eauto. }
          eexists. exists (step_tau _). eexists. left.
          do 1 (pfold; sim_tau; left).
          sim_red. unfold assume. grind.
          pfold. econs 5; ss; auto. i. eapply angelic_step in STEP; des; clarify.
          eexists; split; auto. left.
          do 6 (pfold; sim_tau; left). sim_red.
          destruct rstate. ss. destruct l.
          { admit "ez: wf_rstate". }
          do 5 (pfold; sim_tau; left).
          rewrite Any.upcast_downcast. ss.
          do 2 (pfold; sim_tau; left).
          pfold. econs 4; eauto.
          { admit "ez: strict_determinate_at". }
          eexists. eexists.
          { eapply step_return. }
          eexists; split; auto. right. eapply CIH.
          hexploit match_states_intro.
          { instantiate (2:=Skip). ss. }
          4:{ eapply WFCONT0. }
          4:{ eapply MCONT. }
          4:{ eapply MSTACK0. }
          4:{ clarify. }
          4:{ i.
              match goal with
              | [ H: match_states _ _ _ _ _ ?i0 _ |- match_states _ _ _ _ _ ?i1 _ ] =>
                replace i1 with i0; eauto
              end.
              unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
          2,3: eauto.
          econs. i.
          admit "ez: local env match, use MLE and alist_find". }

      sim_red. pfold. econs 6; clarify.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_skip_seq. }
      eexists. eexists (step_tau _). eexists. sim_red. right. eapply CIH.
      hexploit match_states_intro; eauto.
      all: (destruct s; eauto).
      all: (generalize dependent tcont; induction tcont; i; ss; clarify; eauto).
      all: (eapply compile_stmt_no_Sreturn in CST; clarify).

    - unfold itree_of_cont_stmt, itree_of_imp_cont.
      rewrite interp_imp_Assign. sim_red.
      ss. destruct (compile_expr e) eqn:EXP; uo; ss.
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
      eexists. eexists.
      { eapply step_tau. }
      eexists. right. eapply CIH.
      hexploit match_states_intro.
      { eapply CSC1. }
      4:{ instantiate (1:=Kseq s0 tcont). ss. destruct s0; eauto. eapply compile_stmt_no_Sreturn in CSC2; clarify. }
      4:{ econs 2; eauto. clarify. }
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

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_CallFun.
      ss. uo; des_ifs.
      des_ifs; sim_red.
      { sim_triggerUB. }
      assert (COMP2: compile2 src = OK tgt).
      { unfold compile2. rewrite GMAP. auto. }
      unfold _compile2 in COMP. des_ifs.
      unfold compile_gdefs in Heq0. uo; des_ifs; clarify.
      match goal with
      | [ |- paco3 (_sim _ (semantics ?tp) _) _ _ _ _ ] =>
        set (tgtp:=tp) in *
      end.
      sim_red. eapply step_exprs; eauto.
      { admit "mid: index". }
      i. sim_red. destruct rstate. destruct l0.
      { ss. admit "mid?: r_state is nil". }
      ss. grind. unfold ordN in *.
      do 3 (pfold; sim_tau; left). sim_red.
      match goal with
      | [ |- paco3 _ _ _ (r0 <- unwrapU (?f);; _) _ ] => destruct f eqn:FSEM; ss
      end.
      2:{ sim_triggerUB. }
      unfold call_mem in Heq. des_ifs; clarify.
      repeat match goal with
      | [ H: _ = false |- _ ] =>
        clear H
      end.
      grind. rewrite find_map in FSEM.
      match goal with
      | [ FSEM: o_map (?a) _ = _ |- _ ] => destruct a eqn:FOUND; ss; clarify
      end.
      destruct p. destruct p. clarify.

      eapply found_imp_function in FOUND. des; clarify.
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

      eexists. exists (step_tau _).
      eexists. left.
      pfold. econs 4.
      { admit "ez: strict_determinate_at". }

      unfold pre_compile_function in COMPF. des_ifs. uo; des_ifs. ss.
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
      eexists; split; auto. right.
      eapply CIH.
      match goal with
      | [ |- match_states _ _ ?_ge _ _ _ _ ] =>
        set (ge:=_ge) in *
      end.
      match goal with
      | [ |- match_states _ _ _ ?_ms _ _ _ ] =>
        set (ms:=_ms) in *
      end.
      match goal with
      | [ |- match_states _ _ _ _ _ (?i) _] =>
        replace i with
    (` r0 : r_state * p_state * (lenv * val) <-
     EventsL.interp_Es (prog ms)
       (transl_all s1 (interp_imp ge (denote_stmt (Imp.fn_body f0)) (init_lenv (Imp.fn_vars f0) ++ l3)))
       (c, ε :: c0 :: l0, pstate);; x4 <- itree_of_imp_pop ge ms s1 mn x le r0;; ` x : _ <- next x4;; stack x)
      end.
      2:{ rewrite interp_imp_bind. Red.prw ltac:(_red_gen) 1 0. grind.
          Red.prw ltac:(_red_gen) 2 0. grind.
          Red.prw ltac:(_red_gen) 2 0. Red.prw ltac:(_red_gen) 1 0. grind.
          Red.prw ltac:(_red_gen) 2 0. Red.prw ltac:(_red_gen) 1 0. grind. }

      hexploit match_states_intro.
      5:{ instantiate (1:=Kseq (Sreturn (Some (Evar (s2p "return")))) (Kcall (Some (s2p x)) tf empty_env tle tcont)). ss. }
      6:{ instantiate (1:= fun r0 =>
                             ` x4 : r_state * p_state * (lenv * val) <- itree_of_imp_pop ge ms s1 mn x le r0;;
                                    ` x0 : r_state * p_state * (lenv * val) <- next x4;; stack x0).
          instantiate (1:=s1). instantiate (1:=ms). instantiate (1:=ge). instantiate (1:=gm).
          econs 2; ss; eauto. }
      3,4: eauto.
      1:{ eapply H5. }
      2:{ ss. econs 1. }
      2:{ clarify. }
      2:{ i.
          match goal with
          | [ H1: match_states _ _ _ _ _ ?i0 _ |- match_states _ _ _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. unfold idK. grind. }
      { admit "ez: should follow from above, the initial lenv". }

    - ss. destruct p eqn:PVAR; clarify. 
      admit "ez: CallPtr, similar to CallFun.".

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_CallSys.
      ss. uo; des_ifs; clarify. unfold ident_key in Heq0.
      rename Heq0 into FOUND. apply alist_find_some in FOUND.
      assert (COMP2: compile2 src = OK tgt).
      { unfold compile2. rewrite GMAP. auto. }
      assert (GMAP2: get_gmap src = Some gm).
      { auto. }
      unfold get_gmap in GMAP. uo; des_ifs; ss.
      match goal with
      | [ COMP: _compile2 ?_gm _ = OK _ |- _ ] =>
        set (gm:=_gm) in *
      end.
      unfold compile_eFuns in FOUND.
      rewrite in_map_iff in FOUND. des. destruct x0. ss; clarify.
      assert (S2PBI: forall x y, s2p x = s2p y <-> x = y).
      { admit "ez: make such s2p". }
      apply S2PBI in H1. clear S2PBI; clarify.
      unfold get_funsig in Heq1. clarify.

      unfold _compile2 in COMP. des_ifs; ss; clarify.
      unfold compile_gdefs in Heq. uo; des_ifs; ss; clarify.
      match goal with
      | [ |- paco3 (_sim _ (semantics ?_tgtp) _) _ _ _ _ ] =>
        set (tgtp:=_tgtp) in *
      end.
      hexploit in_tgt_prog_defs_efuns; eauto.
      i. rename H into INTGT.
      hexploit Genv.find_symbol_exists; eauto.
      i. des. rename H into FINDSYM.
      hexploit tgt_genv_find_def_by_blk; eauto.
      i. rename H into FINDDEF.

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
      assert (TGTSYSSEM: exists tgt_ev tgt_rv,
                 external_functions_sem f (make_signature n) (Genv.globalenv tgtp) trvs tm [tgt_ev] tgt_rv tm).
      { admit "ez: tgt syscall sem". }
      des.
      assert (SRCSYSSEM: exists sysrv, syscall_sem (event_sys f rvs sysrv)).
      { admit "ez: src syscall sem". }
      des.
      assert (MATCHSYSSEM: match_event tgt_ev (event_sys f rvs sysrv)).
      { admit "ez: src syscall sem matching tgt". }
      inv MATCHSYSSEM.

      pfold. econs 2; auto.
      { eexists. eexists.
        eapply step_external_function. ss.
        apply TGTSYSSEM. }
      i. eexists. eexists. eexists.
      { hexploit step_syscall.
        { apply SRCSYSSEM. }
        { instantiate (1:=top1). ss. }
        i. ss. rename H1 into SYSSTEP.
        match goal with
        | [ SYSSTEP: step ?i0 _ _ |- step ?i1 _ _ ] =>
          replace i1 with i0; eauto
        end.
        rewrite bind_trigger. grind. }

      inv STEP. ss. rename H7 into TGTSYSSEM2.
      assert (TGTSYSSEM_UNIQUE: forall tfn tfsig tgenv targs tm tev1 trv1 tm1 tev2 trv2 tm2,
                 external_functions_sem tfn tfsig tgenv targs tm tev1 trv1 tm1 ->
                 external_functions_sem tfn tfsig tgenv targs tm tev2 trv2 tm2 ->
                 (tev1 = tev2) /\ (trv1 = trv2) /\ (tm1 = tm2)).
      { admit "ez?: tgt syscall determinate". }
      hexploit TGTSYSSEM_UNIQUE.
      { apply TGTSYSSEM. }
      { apply TGTSYSSEM2. }
      i. des. clarify. clear TGTSYSSEM_UNIQUE.

      split.
      { unfold NW. econs; auto. econs; eauto. }
      eexists. left.
      do 8 (pfold; sim_tau; left).
      pfold. econs 4.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_return. }
      eexists; split; auto. right. eapply CIH.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      4,5,6: eauto.
      4: clarify.
      4:{ i.
          match goal with
          | [ H1: match_states _ _ _ _ _ ?i0 _ |- match_states _ _ _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { econs. i. ss.
        admit "ez: find from local env". }
      all: eauto.

      (*** TODO: ADDR, MEM ***)

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_AddrOf.
      ss. des_ifs.
      + unfold unwrapU. des_ifs.
        2:{ sim_triggerUB. }
        do 2 (pfold; sim_tau; left). sim_red.
        pfold. econs 6; ss.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_set. econs. econs 2.
          { eapply Maps.PTree.gempty. }
          admit "ez? genv, use the fact that src already found". }
        eexists. exists (step_tau _). eexists. right. eapply CIH.
        hexploit match_states_intro.
        { instantiate (2:=Skip). ss. }
        2,3,4,5,6: eauto.
        2:{ clarify. }
        2:{ i.
            match goal with
            | [ H: match_states _ _ _ _ _ ?i0 _ |- match_states _ _ _ _ _ ?i1 _ ] =>
              replace i1 with i0; eauto
            end.
            unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
        { econs. i. admit "ez?: need a translation of genv". }
      + uo; des_ifs. unfold ident_key in Heq1.
        unfold unwrapU. des_ifs.
        2:{ sim_triggerUB. }
        do 2 (pfold; sim_tau; left). sim_red.
        pfold. econs 6; ss.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_set. econs. econs 2.
          { eapply Maps.PTree.gempty. }
          admit "ez? genv, use the fact that src already found". }
        eexists. exists (step_tau _). eexists. right. eapply CIH.
        hexploit match_states_intro.
        { instantiate (2:=Skip). ss. }
        2,3,4,5,6: eauto.
        2:{ clarify. }
        2:{ i.
            match goal with
            | [ H: match_states _ _ _ _ _ ?i0 _ |- match_states _ _ _ _ _ ?i1 _ ] =>
              replace i1 with i0; eauto
            end.
            unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
        { econs. i. admit "ez?: need a translation of genv". }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Malloc. sim_red.
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
      unfold cfun. rewrite Any.upcast_downcast. grind. unfold allocF. sim_red.
      do 4 (pfold; sim_tau; left). sim_red.
      rewrite PSTATE. rewrite Any.upcast_downcast. grind. unfold unint. des_ifs; sim_red.
      2:{ sim_triggerUB. }
      pfold. econs 6; clarify.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_call.
        - econs. econs 2.
          { eapply Maps.PTree.gempty. }
          admit "ez: genv lookup".
        - econs 2; eauto. econs 1.
        - ss. des_ifs. admit "ez: genv lookup".
        - admit "ez: genv lookup". }
      eexists. eexists.
      { rewrite bind_trigger. eapply (step_choose _ 0). }
      eexists. left.
      do 13 (pfold; sim_tau; left). sim_red.
      rewrite Any.upcast_downcast. sim_red.
      do 2 (pfold; sim_tau; left).
      pfold. econs 4.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_external_function.
        admit "ez: genv lookup & get malloc". }
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
          | [ H1: match_states _ _ _ _ _ ?i0 _ |- match_states _ _ _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { econs. i. admit "ez: local env". }
      { clarify. }
      { admit "mid: match memory". }

    - unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Free. sim_red.
      admit "hard: free".

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
      { eapply step_set. econs; eauto. ss.
        admit "mid: match_memory's contents". }
      eexists. eexists.
      { eapply (step_tau _). }
      eexists. left.
      do 4 (pfold; sim_tau; left). sim_red. rewrite Any.upcast_downcast. grind.
      do 1 (pfold; sim_tau; left). pfold; sim_tau; right. eapply CIH.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      2,3,4,5,6: eauto.
      2: clarify.
      2:{ i.
          match goal with
          | [ H1: match_states _ _ _ _ _ ?i0 _ |- match_states _ _ _ _ _ ?i1 _ ] =>
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
      pfold. econs 6; clarify.
      { admit "ez: strict_determinate_at". }
      eexists. eexists.
      { eapply step_store; eauto. ss.
        admit "mid: match_memory's contents". }
      eexists. eexists.
      { eapply (step_tau _). }
      eexists. left.
      do 7 (pfold; sim_tau; left). sim_red. pfold; sim_tau; right. eapply CIH.
      hexploit match_states_intro.
      { instantiate (2:=Skip). ss. }
      1,4,5,6: eauto.
      3: clarify.
      3:{ i.
          match goal with
          | [ H1: match_states _ _ _ _ _ ?i0 _ |- match_states _ _ _ _ _ ?i1 _ ] =>
            replace i1 with i0; eauto
          end.
          unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
      { ss. }
      admit "mid: match memory".

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
        { eapply step_set. econs; eauto. ss.
          admit "ez?: match value & comparison". }
        eexists. eexists.
        { eapply (step_tau _). }
        eexists. left.
        do 4 (pfold; sim_tau; left). sim_red. rewrite Any.upcast_downcast. grind.
        do 1 (pfold; sim_tau; left). pfold; sim_tau; right. eapply CIH.
        hexploit match_states_intro.
        { instantiate (2:=Skip). ss. }
        2,3,4,5,6: eauto.
        2: clarify.
        2:{ i.
            match goal with
            | [ H1: match_states _ _ _ _ _ ?i0 _ |- match_states _ _ _ _ _ ?i1 _ ] =>
              replace i1 with i0; eauto
            end.
            unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
        { econs. i. admit "ez: match lenv". }
      + sim_red.
        pfold. econs 6; clarify.
        { admit "ez: strict_determinate_at". }
        eexists. eexists.
        { eapply step_set. econs; eauto. ss.
          admit "ez?: match value & comparison". }
        eexists. eexists.
        { eapply (step_tau _). }
        eexists. left.
        do 4 (pfold; sim_tau; left). sim_red. rewrite Any.upcast_downcast. grind.
        do 1 (pfold; sim_tau; left). pfold; sim_tau; right. eapply CIH.
        hexploit match_states_intro.
        { instantiate (2:=Skip). ss. }
        2,3,4,5,6: eauto.
        2: clarify.
        2:{ i.
            match goal with
            | [ H1: match_states _ _ _ _ _ ?i0 _ |- match_states _ _ _ _ _ ?i1 _ ] =>
              replace i1 with i0; eauto
            end.
            unfold itree_of_cont_stmt, itree_of_imp_cont. rewrite interp_imp_Skip. grind. }
        { econs. i. admit "ez: match lenv". }


  Admitted.

End PROOF.

Section PROOFALL.

  From compcert Require Import Linking.
  Import Maps.PTree.

  Lemma list_norepet_NoDupB {K} {decK} :
    forall l, Coqlib.list_norepet l <-> @NoDupB K decK l = true.
  Proof.
    split; i.
    - induction H; ss.
      clarify.
      destruct (in_dec decK hd tl); clarify.
    - induction l; ss; clarify. constructor.
      des_ifs. econs 2; auto.
  Qed.

  (* Definition wf_imp_prog (src : Imp.programL) := *)
  (*   Coqlib.list_norepet (compile_gdefs (get_gmap src) src). *)

  (* Lemma compile_then_wf : forall src tgt, *)
  (*     compile src = OK tgt *)
  (*     -> *)
  (*     wf_imp_prog src. *)
  (* Proof. *)
  (*   unfold compile, _compile. i. *)
  (*   destruct (compile_gdefs (get_gmap src) src) eqn:EQ; clarify. *)
  (*   eauto using compile_gdefs_then_wf. *)
  (* Qed. *)

  (* Maps.PTree.elements_extensional 
     we will rely on above theorem for commutation lemmas *)
  Lemma _comm_link_imp_compile :
    forall src1 src2 srcl tgt1 tgt2 tgtl,
      compile src1 = OK tgt1 -> compile src2 = OK tgt2 ->
      link_imp src1 src2 = Some srcl ->
      link_prog tgt1 tgt2 = Some tgtl ->
      compile srcl = OK tgtl.
  Proof.
  Admitted.

  Definition wf_link {T} (program_list : list T) :=
    exists h t, program_list = h :: t.

  Inductive compile_list :
    list programL -> list (Csharpminor.program) -> Prop :=
  | compile_nil :
      compile_list [] []
  | compile_head :
      forall src_h src_t tgt_h tgt_t,
        compile src_h = OK tgt_h ->
        compile_list src_t tgt_t ->
        compile_list (src_h :: src_t) (tgt_h :: tgt_t).

  Definition fold_left_option {T} f (t : list T) (opth : option T) :=
    fold_left
      (fun opt s2 => match opt with | Some s1 => f s1 s2 | None => None end)
      t opth.

  Lemma fold_left_option_None {T} :
    forall f (l : list T), fold_left_option f l None = None.
  Proof.
    intros f. induction l; ss; clarify.
  Qed.

  Definition link_imp_list src_list :=
    match src_list with
    | [] => None
    | src_h :: src_t =>
      fold_left_option link_imp src_t (Some src_h)
    end.

  Definition link_clight_list (tgt_list : list (Csharpminor.program)) :=
    match tgt_list with
    | [] => None
    | tgt_h :: tgt_t =>
      fold_left_option link_prog tgt_t (Some tgt_h)
    end.

  Lemma comm_link_imp_compile :
    forall src_list srcl tgt_list tgtl,
      compile_list src_list tgt_list ->
      link_imp_list src_list = Some srcl ->
      link_clight_list tgt_list = Some tgtl
      ->
      compile srcl = OK tgtl.
  Proof.
    i. destruct src_list; destruct tgt_list; ss; clarify.
    inv H; clarify.
    generalize dependent srcl. generalize dependent tgtl.
    generalize dependent p. generalize dependent p0.
    induction H7; i; ss; clarify.
    destruct (link_prog p0 tgt_h) eqn:LPt; ss; clarify.
    2:{ rewrite fold_left_option_None in H1; clarify. }
    destruct (link_imp p src_h) eqn:LPs; ss; clarify.
    2:{ rewrite fold_left_option_None in H0; clarify. }
    eapply IHcompile_list.
    2: apply H1.
    2: apply H0.
    eapply _comm_link_imp_compile.
    3: apply LPs.
    3: apply LPt.
    auto. auto.
  Qed.

  Context `{Σ: GRA.t}.

  Lemma _comm_link_imp_link_mod :
    forall src1 src2 srcl tgt1 tgt2 tgtl (ctx : ModL.t),
      ImpMod.get_modL src1 = tgt1 ->
      ImpMod.get_modL src2 = tgt2 ->
      link_imp src1 src2 = Some srcl ->
      ImpMod.get_modL srcl = tgtl ->
      ModL.add (ModL.add ctx tgt1) tgt2
      =
      ModL.add ctx tgtl.
  Proof.
  Admitted.

  Lemma comm_link_imp_link_mod :
    forall src_list srcl tgt_list tgtl ctx,
      List.map (fun src => ImpMod.get_modL src) src_list = tgt_list ->
      link_imp_list src_list = Some srcl ->
      ImpMod.get_modL srcl = tgtl ->
      fold_left ModL.add tgt_list ctx
      =
      ModL.add ctx tgtl.
  Proof.
    destruct src_list eqn:SL; i; ss; clarify.
    move p after l.
    revert_until Σ.
    induction l; i; ss; clarify.
    destruct (link_imp p a) eqn:LI; ss; clarify.
    2:{ rewrite fold_left_option_None in H0; clarify. }
    erewrite _comm_link_imp_link_mod; eauto.
  Qed.

  Lemma single_compile_behavior_improves :
    forall (src: Imp.program) tgt (beh: program_behavior),
      compile src = OK tgt ->
      program_behaves (Csharpminor.semantics tgt) beh ->
      let srcM := ModL.add Mem (ImpMod.get_mod src) in
      exists mbeh,
        match_beh beh mbeh /\ Beh.of_program (ModL.compile srcM) mbeh.
  Proof.
  Admitted.

  Theorem compile_behavior_improves :
    forall (src_list : list Imp.program) srclM tgt_list tgtl (beh : program_behavior),
      let src_list_lift := List.map Imp.lift src_list in
      compile_list src_list_lift tgt_list ->
      let src_list_mod := List.map (fun src => ImpMod.get_mod src) src_list in
      Mod.add_list (Mem :: src_list_mod) = srclM ->
      link_clight_list tgt_list = Some tgtl ->
      program_behaves (Csharpminor.semantics tgtl) beh ->
      exists mbeh,
        match_beh beh mbeh /\ Beh.of_program (ModL.compile srclM) mbeh.
  Proof.
  Admitted.

End PROOFALL.
