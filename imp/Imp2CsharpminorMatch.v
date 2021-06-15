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
    fun ge ms mn (x: _ * _ * (lenv * val)) =>
      let '(r, p, (le0, _)) := x in
      '(r2, p2, rv) <- EventsL.interp_Es (ModSemL.prog ms) (transl_all mn ('(_, v) <- interp_imp ge (denote_expr (Var "return"%string)) le0;; Ret (v↑))) (r, p);;
      '(_, _, rv) <- EventsL.interp_Es (ModSemL.prog ms) (trigger EventsL.PopFrame;;; (tau;; Ret rv)) (r2, p2);;
      Ret rv.

  Definition itree_of_cont_stmt (s : Imp.stmt) :=
    fun ge le ms mn rp => itree_of_imp_cont (denote_stmt s) ge le ms mn rp.

  Definition imp_state := itree eventE Any.t.
  Definition imp_cont {T} {R} := (r_state * p_state * (lenv * T)) -> itree eventE (r_state * p_state * (lenv * R)).
  Definition imp_stack := (r_state * p_state * (lenv * val)) -> imp_state.

  (* tlof will be the number of external symbols *)
  (* Hypothesis archi_ptr64 : Archi.ptr64 = true. *)
  Variable tlof : nat.

  Definition map_blk (blk : nat) : Values.block := Pos.of_nat (S(tlof + blk)).
  Definition map_ofs (ofs : Z) : Z := 8*ofs.

  Definition map_val (v : Universe.val) : Values.val :=
    match v with
    | Vint z => Values.Vlong (Int64.repr z)
    | Vptr blk ofs =>
      Values.Vptr (map_blk blk) (Ptrofs.of_int64 (Int64.repr (map_ofs ofs)))
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

  (* prog_defs has offset of 1 + length(efuns ++ evars ++ init_g) = 1 + tlof than Imp.defs *)
  Variant match_ge : SkEnv.t -> (Genv.t fundef ()) -> Prop :=
  | match_ge_intro
      sge tge
      (MG: forall symb blk,
          (sge.(SkEnv.id2blk) symb = Some blk) ->
          (Genv.find_symbol tge (s2p symb) = Some (Pos.of_nat (S(tlof + blk)))))
    :
      match_ge sge tge.

  Definition return_stmt := Sreturn (Some (Evar (s2p "return"))).
  Definition ret_call_cont k := Kseq return_stmt (call_cont k).

  Definition exit_stmt := Sreturn (Some (Eunop Cminor.Ointoflong (Evar (s2p "return")))).
  Definition ret_call_main := Kseq exit_stmt Kstop.

  (* global env is fixed when src program is fixed *)
  Variable gm : gmap.
  Variable ge : SkEnv.t.
  (* ModSem should be fixed with src too *)
  Variable ms : ModSemL.t.

  Inductive match_code (mn: mname) : imp_cont -> (list Csharpminor.stmt) -> Prop :=
  | match_code_exit
    :
      match_code mn idK [exit_stmt]
  | match_code_return
    :
      match_code mn idK [return_stmt]
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
      match_stack mn (fun x => itree_of_imp_pop_bottom ge ms mn x) (Some ret_call_main)

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

  Variant match_mem : Mem.t -> Memory.Mem.mem -> Prop :=
  | match_mem_intro
      m tm
      (NBLK: tm.(Mem.nextblock) = map_blk (m.(Mem.nb)))
      (MMEM: forall blk ofs v,
          (<<SMCNT: m.(Mem.cnts) blk ofs = Some v>>) ->
          ((<<TMCNT: Memory.Mem.load Mint64 tm (map_blk blk) (map_ofs ofs) = Some (map_val v)>>) /\
           (<<TVALID: Mem.valid_access tm Mint64 (map_blk blk) (map_ofs ofs) Writable>>) /\
           (<<WFOFS: (0 <= ofs)%Z>>)))
    :
      match_mem m tm
  .

  Variant match_states : imp_state -> Csharpminor.state -> Prop :=
  | match_states_intro
      tf rstate pstate le tle code itr tcode m tm next stack tcont mn
      (CST: compile_stmt gm code = Some tcode)
      (ML: match_le le tle)
      (PSTATE: pstate "Mem"%string = m↑)
      (MM: match_mem m tm)
      (WFCONT: wf_ccont tcont)
      (MCONT: match_code mn next (get_cont_stmts tcont))
      (MSTACK: match_stack mn stack (get_cont_stack tcont))
      (ITR: itr = itree_of_cont_stmt code ge le ms mn (rstate, pstate))
    :
      match_states (x <- itr;; next x >>= stack) (State tf tcode tcont empty_env tle tm)
  .

End MATCH.
