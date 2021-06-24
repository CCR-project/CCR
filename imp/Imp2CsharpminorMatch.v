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
Require Import Mem0.

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
      '(r3, p3, rv) <- EventsL.interp_Es (ModSemL.prog ms) (trigger EventsL.PopFrame;;; (tau;; Ret rv)) (r2, p2);;
      pop <- EventsL.interp_Es (ModSemL.prog ms) (transl_all retmn (tau;; tau;; v0 <- unwrapN (rv↓);; (tau;; tau;; tau;; Ret (alist_add retx v0  retle, Vundef)))) (r3, p3);;
      Ret pop.

  Definition itree_of_imp_pop_bottom :=
    fun ms mn (x : r_state * p_state * (lenv * val)) =>
      ` x0 : r_state * p_state * Any.t <-
      (let (st1, v) := x in
      EventsL.interp_Es (ModSemL.prog ms)
                        (transl_all mn (` x0 : val <- (let (_, retv) := v in Ret retv);; Ret (Any.upcast x0))) st1);; Ret (snd x0).

  Definition itree_of_cont_stmt (s : Imp.stmt) :=
    fun ge le ms mn rp => itree_of_imp_cont (denote_stmt s) ge le ms mn rp.

  Definition imp_state := itree eventE Any.t.
  Definition imp_cont {T} {R} := (r_state * p_state * (lenv * T)) -> itree eventE (r_state * p_state * (lenv * R)).
  Definition imp_stack := (r_state * p_state * (lenv * val)) -> imp_state.

  (* Hypothesis archi_ptr64 : Archi.ptr64 = true. *)
  Definition ext_len : Imp.programL -> nat := fun src => List.length (src.(ext_varsL)) + List.length (src.(ext_funsL)).
  Definition int_len : Imp.programL -> nat := fun src => List.length src.(defsL).
  (* next block of src's initialized genv *)
  Definition src_init_nb : Imp.programL -> nat := fun src => int_len src.
  (* next block of tgt's initialized genv *)
  Definition tgt_init_len := List.length (init_g ++ c_sys).
  Definition tgt_init_nb : Imp.programL -> Values.block := fun src => Pos.of_succ_nat (tgt_init_len + (ext_len src) + (int_len src)).

  Definition get_sge (src : Imp.programL) := Sk.load_skenv (Sk.sort (ImpMod.get_modL src).(ModL.sk)).
  Definition get_tge (tgt : Csharpminor.program) := Genv.globalenv tgt.

  (* should never appear *)
  Definition dummy_blk : positive := 1%positive.

  Definition map_blk : programL -> nat -> Values.block :=
    fun src blk =>
      match (compile src) with
      | OK tgt =>
        if (ge_dec blk (src_init_nb src)) then Pos.of_succ_nat (tgt_init_len + (ext_len src) + blk)
        else
          let sg := get_sge src in
          let tg := get_tge tgt in
          match sg.(SkEnv.blk2id) blk with
          | Some name =>
            match Genv.find_symbol tg (s2p name) with
            | Some tblk => tblk
            | None => dummy_blk
            end
          | None => dummy_blk
          end
      | _ => dummy_blk
      end
  .

  Definition map_ofs (ofs : Z) : Z := 8 * ofs.

  Definition map_val (src : Imp.programL) (v : Universe.val) : Values.val :=
    match v with
    | Vint z => Values.Vlong (Int64.repr z)
    | Vptr blk ofs =>
      Values.Vptr (map_blk src blk) (Ptrofs.of_int64 (Int64.repr (map_ofs ofs)))
    | Vundef => Values.Vundef
    end.

  Variant match_le (src : Imp.programL) : lenv -> temp_env -> Prop :=
  | match_le_intro
      sle tle
      (ML: forall x sv,
          (alist_find x sle = Some sv) ->
          (Maps.PTree.get (s2p x) tle = Some (@map_val src sv)))
    :
      match_le src sle tle.

  Variant match_ge (src : Imp.programL) : SkEnv.t -> (Genv.t fundef ()) -> Prop :=
  | match_ge_intro
      sge tge
      (MG: forall symb blk,
          (sge.(SkEnv.id2blk) symb = Some blk) ->
          (Genv.find_symbol tge (s2p symb) = Some (map_blk src blk)))
    :
      match_ge src sge tge.

  Definition return_stmt := Sreturn (Some (Evar (s2p "return"))).
  Definition ret_call_cont k := Kseq return_stmt (call_cont k).

  Definition exit_stmt := Sreturn (Some (Eunop Cminor.Ointoflong (Evar (s2p "return")))).
  Definition ret_call_main := Kseq exit_stmt Kstop.

  (* global env is fixed when src program is fixed *)
  Variable ge : SkEnv.t.
  (* ModSem should be fixed with src too *)
  Variable ms : ModSemL.t.

  Inductive match_code (mn: mname) : imp_cont -> (list Csharpminor.stmt) -> Prop :=
  | match_code_exit
    :
      match_code mn (fun '(r, p, (le, _)) => itree_of_imp_ret ge le ms mn (r, p)) [exit_stmt]
  | match_code_return
    :
      match_code mn idK [return_stmt]
  | match_code_cont
      code itr ktr chead ctail
      (CST: compile_stmt code = chead)
      (ITR: itr = fun '(r, p, (le, _)) => itree_of_cont_stmt code ge le ms mn (r, p))
      (MCONT: match_code mn ktr ctail)
    :
      match_code mn (fun x => (itr x >>= ktr)) (chead :: ctail)
  .

  Inductive match_stack (size: nat) (src: Imp.programL) (mn: mname) : imp_stack -> option Csharpminor.cont -> Prop :=
  | match_stack_bottom
      (SIZEEND: size = 1)
    :
      match_stack size src mn (itree_of_imp_pop_bottom ms mn) (Some ret_call_main)

  | match_stack_cret
      tf le tle next stack tcont id tid tpop retmn sz
      (MLE: @match_le src le tle)
      (MID: s2p id = tid)

      (WFCONT: wf_ccont tcont)
      (MCONT: match_code retmn next (get_cont_stmts tcont))
      (MSTACK: match_stack sz src retmn stack (get_cont_stack tcont))
      (SIZEUP: size = S sz)

      (TPOP: tpop = ret_call_cont (Kcall (Some tid) tf empty_env tle tcont))
    :
      match_stack size src mn (fun x => (y <- (itree_of_imp_pop ge ms mn retmn id le x);; next y >>= stack)) (Some tpop)
  .

  Variant match_mem src : Mem.t -> Memory.Mem.mem -> Prop :=
  | match_mem_intro
      m tm
      (INITIALIZED: m.(Mem.nb) >= (src_init_nb src))
      (NBLK: tm.(Mem.nextblock) = map_blk src (m.(Mem.nb)))
      (MMEM: forall blk ofs v,
          (<<SMCNT: m.(Mem.cnts) blk ofs = Some v>>) ->
          ((<<TMCNT: Memory.Mem.load Mint64 tm (map_blk src blk) (map_ofs ofs) = Some (@map_val src v)>>) /\
           (<<TVALID: Mem.valid_access tm Mint64 (map_blk src blk) (map_ofs ofs) Writable>>) /\
           (<<WFOFS: (0 <= ofs)%Z>>)))
    :
      match_mem src m tm
  .

  Variant match_states src : imp_state -> Csharpminor.state -> Prop :=
  | match_states_intro
      tf rstate pstate le tle code itr tcode m tm next stack tcont mn sz
      (CST: compile_stmt code = tcode)
      (WFRSTATE: List.length (snd rstate) = S sz)
      (ML: @match_le src le tle)
      (PSTATE: pstate "Mem"%string = m↑)
      (MM: @match_mem src m tm)
      (WFCONT: wf_ccont tcont)
      (MCONT: match_code mn next (get_cont_stmts tcont))
      (MSTACK: @match_stack sz src mn stack (get_cont_stack tcont))
      (ITR: itr = itree_of_cont_stmt code ge le ms mn (rstate, pstate))
    :
      match_states src (x <- itr;; next x >>= stack) (State tf tcode tcont empty_env tle tm)
  .

End MATCH.
