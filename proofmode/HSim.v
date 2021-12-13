Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef OpenDef STB SimModSem.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import ProofMode Invariant.
Require Import HTactics.

Set Implicit Arguments.

Ltac ired_l := try (prw _red_gen 2 1 0).
Ltac ired_r := try (prw _red_gen 1 1 0).

Ltac ired_both := ired_l; ired_r.



(* "safe" simulation constructors *)
Section SIM.
  Context `{Σ: GRA.t}.
  Variable world: Type.
  Variable le: relation world.
  Variable I: world -> Any.t -> Any.t -> iProp.

  Variable mn: mname.
  Variable stb: gname -> option fspec.
  Variable o: ord.

  Definition option_Ord_lt (o0 o1: option Ord.t): Prop :=
    match o0, o1 with
    | None, Some _ => True
    | Some o0, Some o1 => Ord.lt o0 o1
    | _, _ => False
    end.

  Lemma option_Ord_lt_well_founded: well_founded option_Ord_lt.
  Proof.
    ii. destruct a.
    { induction (Ord.lt_well_founded t). econs.
      i. destruct y; ss.
      { eapply H0; eauto. }
      { econs. ii. destruct y; ss. }
    }
    { econs; ii. destruct y; ss. }
  Qed.

  Definition option_Ord_le (o0 o1: option Ord.t): Prop :=
    match o0, o1 with
    | None, _ => True
    | Some o0, Some o1 => Ord.le o0 o1
    | _, _ => False
    end.

  Global Program Instance option_Ord_le_PreOrder: PreOrder option_Ord_le.
  Next Obligation.
  Proof.
    ii. destruct x; ss. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. destruct x, y, z; ss. etrans; eauto.
  Qed.

  Lemma option_Ord_lt_le o0 o1
        (LT: option_Ord_lt o0 o1)
    :
      option_Ord_le o0 o1.
  Proof.
    destruct o0, o1; ss. apply Ord.lt_le; auto.
  Qed.

  Lemma option_Ord_lt_le_lt o0 o1 o2
        (LT: option_Ord_lt o0 o1)
        (LE: option_Ord_le o1 o2)
    :
      option_Ord_lt o0 o2.
  Proof.
    destruct o0, o1, o2; ss. eapply Ord.lt_le_lt; eauto.
  Qed.

  Lemma option_Ord_le_lt_lt o0 o1 o2
        (LE: option_Ord_le o0 o1)
        (LT: option_Ord_lt o1 o2)
    :
      option_Ord_lt o0 o2.
  Proof.
    destruct o0, o1, o2; ss. eapply Ord.le_lt_lt; eauto.
  Qed.

  Inductive _hsim
            (hsim: forall R_src R_tgt
                          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                          (ctx: Σ),
                option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree Es R_tgt -> Prop)
            {R_src R_tgt}
            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
            (ctx: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree Es R_tgt -> Prop :=
  | hsim_ret
      v_src v_tgt
      st_src st_tgt
      fuel f_src f_tgt
      (RET: current_iProp ctx (Q st_src st_tgt v_src v_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt))
  | hsim_call
      fsp (x: fsp.(meta)) w0 FR
      fn arg_src arg_tgt
      st_src0 st_tgt0 ktr_src ktr_tgt
      fuel f_src f_tgt
      (SPEC: stb fn = Some fsp)
      (PRE: current_iProp ctx (FR ** I w0 st_src0 st_tgt0 ** fsp.(precond) (Some mn) x arg_src arg_tgt))
      (MEASURE: o = ord_top)
      (NPURE: fsp.(measure) x = ord_top)
      (POST: forall ctx1 w1 st_src1 st_tgt1 ret_src ret_tgt
                    (ACC: current_iProp ctx1 (FR ** I w1 st_src1 st_tgt1 ** fsp.(postcond) (Some mn) x ret_src ret_tgt)),
          hsim _ _ Q ctx1 None true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt)
  | hsim_apc_start
      fuel1
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim Q ctx (fuel1) true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, trigger (hAPC) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_apc_step
      fsp (x: fsp.(meta)) w0 FR arg_src
      fn arg_tgt
      st_src0 st_tgt0 itr_src ktr_tgt
      fuel0 f_src f_tgt
      (SPEC: stb fn = Some fsp)
      (PRE: current_iProp ctx (FR ** I w0 st_src0 st_tgt0 ** fsp.(precond) (Some mn) x arg_src arg_tgt))
      (MEASURE: ord_lt (fsp.(measure) x) o)
      (PURE: is_pure (fsp.(measure) x))
      (POST: exists fuel1,
          (<<FUEL: Ord.lt fuel1 fuel0>>) /\
          (<<SIM: forall ctx1 w1 st_src1 st_tgt1 ret_src ret_tgt
                         (ACC: current_iProp ctx1 (FR ** I w1 st_src1 st_tgt1 ** fsp.(postcond) (Some mn) x ret_src ret_tgt)),
              hsim _ _ Q ctx1 (Some fuel1) true true (st_src1, itr_src) (st_tgt1, ktr_tgt ret_tgt)>>))
    :
      _hsim hsim Q ctx (Some fuel0) f_src f_tgt (st_src0, itr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt)
  | hsim_syscall
      fn arg rvs
      st_src st_tgt ktr_src ktr_tgt
      fuel f_src f_tgt
      (POST: forall ret,
          hsim _ _ Q ctx None true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt)
  | hsim_tau_src
      st_src st_tgt itr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim Q ctx None true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt)
  | hsim_tau_tgt
      st_src st_tgt itr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt)
  | hsim_choose_src
      X
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: exists x, _hsim hsim Q ctx None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_choose_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: forall x, _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt)
  | hsim_take_src
      X
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: forall x, _hsim hsim Q ctx None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_take_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: exists x, _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt)
  | hsim_pput_src
      st_src1
      st_src0 st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim Q ctx None true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_pput_tgt
      st_tgt1
      st_src st_tgt0 itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt)
  | hsim_pget_src
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim Q ctx None true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_pget_tgt
      st_src st_tgt itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt)
  | hsim_progress
      st_src st_tgt itr_src itr_tgt
      fuel
      (SIM: hsim _ _ Q ctx fuel false false (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel true true (st_src, itr_src) (st_tgt, itr_tgt)
  .

  Inductive _hsim
            (hsim: forall R_src R_tgt
                          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                          (ctx: Σ),
                option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree Es R_tgt -> Prop)
            {R_src R_tgt}
            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
            (ctx: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree Es R_tgt -> Prop :=
  | hsim_ret
      v_src v_tgt
      st_src st_tgt
      fuel f_src f_tgt
      (RET: current_iProp ctx (Q st_src st_tgt v_src v_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt))
  | hsim_call
      fsp (x: fsp.(meta)) w0 FR
      fn arg_src arg_tgt
      st_src0 st_tgt0 ktr_src ktr_tgt
      fuel f_src f_tgt
      (SPEC: stb fn = Some fsp)
      (PRE: current_iProp ctx (FR ** I w0 st_src0 st_tgt0 ** fsp.(precond) (Some mn) x arg_src arg_tgt))
      (MEASURE: o = ord_top)
      (NPURE: fsp.(measure) x = ord_top)
      (POST: forall ctx1 w1 st_src1 st_tgt1 ret_src ret_tgt
                    (ACC: current_iProp ctx1 (FR ** I w1 st_src1 st_tgt1 ** fsp.(postcond) (Some mn) x ret_src ret_tgt)),
          hsim _ _ Q ctx1 None true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt)
  | hsim_apc_start
      fuel1
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim Q ctx (fuel1) true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, trigger (hAPC) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_apc_step
      fsp (x: fsp.(meta)) w0 FR arg_src
      fn arg_tgt
      st_src0 st_tgt0 itr_src ktr_tgt
      fuel0 f_src f_tgt
      (SPEC: stb fn = Some fsp)
      (PRE: current_iProp ctx (FR ** I w0 st_src0 st_tgt0 ** fsp.(precond) (Some mn) x arg_src arg_tgt))
      (MEASURE: ord_lt (fsp.(measure) x) o)
      (PURE: is_pure (fsp.(measure) x))
      (POST: exists fuel1,
          (<<FUEL: Ord.lt fuel1 fuel0>>) /\
          (<<SIM: forall ctx1 w1 st_src1 st_tgt1 ret_src ret_tgt
                         (ACC: current_iProp ctx1 (FR ** I w1 st_src1 st_tgt1 ** fsp.(postcond) (Some mn) x ret_src ret_tgt)),
              hsim _ _ Q ctx1 (Some fuel1) true true (st_src1, itr_src) (st_tgt1, ktr_tgt ret_tgt)>>))
    :
      _hsim hsim Q ctx (Some fuel0) f_src f_tgt (st_src0, itr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt)
  | hsim_syscall
      fn arg rvs
      st_src st_tgt ktr_src ktr_tgt
      fuel f_src f_tgt
      (POST: forall ret,
          hsim _ _ Q ctx None true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt)
  | hsim_tau_src
      st_src st_tgt itr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim Q ctx None true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt)
  | hsim_tau_tgt
      st_src st_tgt itr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt)
  | hsim_choose_src
      X
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: exists x, _hsim hsim Q ctx None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_choose_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: forall x, _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt)
  | hsim_take_src
      X
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: forall x, _hsim hsim Q ctx None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_take_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: exists x, _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt)
  | hsim_pput_src
      st_src1
      st_src0 st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim Q ctx None true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_pput_tgt
      st_tgt1
      st_src st_tgt0 itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt)
  | hsim_pget_src
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim Q ctx None true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_pget_tgt
      st_src st_tgt itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
    :
      _hsim hsim Q ctx fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt)
  | hsim_progress
      st_src st_tgt itr_src itr_tgt
      fuel
      (SIM: hsim _ _ Q ctx fuel false false (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim Q ctx fuel true true (st_src, itr_src) (st_tgt, itr_tgt)
  .

  Lemma _hsim_ind2
        (hsim: forall R_src R_tgt
                      (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                      (ctx: Σ),
            option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree Es R_tgt -> Prop)
        R_src R_tgt Q ctx
        (P: option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree Es R_tgt -> Prop)
        (RET: forall
            v_src v_tgt
            st_src st_tgt
            fuel f_src f_tgt
            (RET: current_iProp ctx (Q st_src st_tgt v_src v_tgt)),
            P fuel f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt)))
        (CALL: forall
            fsp (x: fsp.(meta)) w0 FR
            fn arg_src arg_tgt
            st_src0 st_tgt0 ktr_src ktr_tgt
            fuel f_src f_tgt
            (SPEC: stb fn = Some fsp)
            (PRE: current_iProp ctx (FR ** I w0 st_src0 st_tgt0 ** fsp.(precond) (Some mn) x arg_src arg_tgt))
            (MEASURE: o = ord_top)
            (NPURE: fsp.(measure) x = ord_top)
            (POST: forall ctx1 w1 st_src1 st_tgt1 ret_src ret_tgt
                          (ACC: current_iProp ctx1 (FR ** I w1 st_src1 st_tgt1 ** fsp.(postcond) (Some mn) x ret_src ret_tgt)),
                hsim _ _ Q ctx1 None true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt)),
            P fuel f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt))
        (APCSTART: forall
            fuel1
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: _hsim hsim Q ctx (fuel1) true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
            (IH: P (fuel1) true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src, trigger (hAPC) >>= ktr_src) (st_tgt, itr_tgt))
        (APCSTEP: forall
            fsp (x: fsp.(meta)) w0 FR arg_src
            fn arg_tgt
            st_src0 st_tgt0 itr_src ktr_tgt
            fuel0 f_src f_tgt
            (SPEC: stb fn = Some fsp)
            (PRE: current_iProp ctx (FR ** I w0 st_src0 st_tgt0 ** fsp.(precond) (Some mn) x arg_src arg_tgt))
            (MEASURE: ord_lt (fsp.(measure) x) o)
            (PURE: is_pure (fsp.(measure) x))
            (POST: exists fuel1,
                (<<FUEL: Ord.lt fuel1 fuel0>>) /\
                (<<SIM: forall ctx1 w1 st_src1 st_tgt1 ret_src ret_tgt
                               (ACC: current_iProp ctx1 (FR ** I w1 st_src1 st_tgt1 ** fsp.(postcond) (Some mn) x ret_src ret_tgt)),
                    hsim _ _ Q ctx1 (Some fuel1) true true (st_src1, itr_src) (st_tgt1, ktr_tgt ret_tgt)>>)),
            P (Some fuel0) f_src f_tgt (st_src0, itr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt))
        (SYSCALL: forall
            fn arg rvs
            st_src st_tgt ktr_src ktr_tgt
            fuel f_src f_tgt
            (POST: forall ret,
                hsim _ _ Q ctx None true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret)),
            P fuel f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt))
        (TAUSRC: forall
            st_src st_tgt itr_src itr_tgt
            fuel f_src f_tgt
            (SIM: _hsim hsim Q ctx None true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P None true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
          ,
            P fuel f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt))
        (TAUTGT: forall
            st_src st_tgt itr_src itr_tgt
            fuel f_src f_tgt
            (SIM: _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P fuel f_src true (st_src, itr_src) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt))
        (CHOOSESRC: forall
            X
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: exists x, (<<SIM: _hsim hsim Q ctx None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P fuel f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt))
        (CHOOSETGT: forall
            X
            st_src st_tgt itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: forall x, (<<SIM: _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt))
        (TAKESRC: forall
            X
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: forall x, (<<SIM: _hsim hsim Q ctx None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P fuel f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt))
        (TAKETGT: forall
            X
            st_src st_tgt itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: exists x, (<<SIM: _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt))
        (PPUTSRC: forall
            st_src1
            st_src0 st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: _hsim hsim Q ctx None true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
            (IH: P None true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt))
        (PPUTTGT: forall
            st_tgt1
            st_src st_tgt0 itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
            (IH: P fuel f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt))
        (PGETSRC: forall
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: _hsim hsim Q ctx None true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
            (IH: P None true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt))
        (PGETTGT: forall
            st_src st_tgt itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: _hsim hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
            (IH: P fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt))
        (PROGRESS: forall
            st_src st_tgt itr_src itr_tgt
            fuel
            (SIM: hsim _ _ Q ctx fuel false false (st_src, itr_src) (st_tgt, itr_tgt)),
            P fuel true true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      forall fuel f_src f_tgt st_src st_tgt
             (SIM: @_hsim hsim _ _ Q ctx fuel f_src f_tgt st_src st_tgt),
        P fuel f_src f_tgt st_src st_tgt.
  Proof.
    fix IH 6. i. inv SIM.
    { eapply RET; eauto. }
    { eapply CALL; eauto. }
    { eapply APCSTART; eauto. }
    { des. eapply APCSTEP; eauto. }
    { eapply SYSCALL; eauto. }
    { eapply TAUSRC; eauto. }
    { eapply TAUTGT; eauto. }
    { des. eapply CHOOSESRC; eauto. }
    { eapply CHOOSETGT; eauto. }
    { eapply TAKESRC; eauto. }
    { des. eapply TAKETGT; eauto. }
    { eapply PPUTSRC; eauto. }
    { eapply PPUTTGT; eauto. }
    { eapply PGETSRC; eauto. }
    { eapply PGETTGT; eauto. }
    { eapply PROGRESS; eauto. }
  Qed.

  Definition hsim := paco9 _hsim bot9.
  Arguments hsim [_ _] _ _ _ _ _ _ _.

  Lemma _hsim_mon: monotone9 _hsim.
  Proof.
    ii. induction IN using _hsim_ind2.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { des. econs 4; eauto. esplits; eauto. }
    { econs 5; eauto. }
    { econs 6; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. des. esplits; eauto. }
    { econs 9; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. }
  Qed.
  Hint Resolve _hsim_mon: paco.

  Lemma hsim_ind
        R_src R_tgt Q ctx
        (P: option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree Es R_tgt -> Prop)
        (RET: forall
            v_src v_tgt
            st_src st_tgt
            fuel f_src f_tgt
            (RET: current_iProp ctx (Q st_src st_tgt v_src v_tgt)),
            P fuel f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt)))
        (CALL: forall
            fsp (x: fsp.(meta)) w0 FR
            fn arg_src arg_tgt
            st_src0 st_tgt0 ktr_src ktr_tgt
            fuel f_src f_tgt
            (SPEC: stb fn = Some fsp)
            (PRE: current_iProp ctx (FR ** I w0 st_src0 st_tgt0 ** fsp.(precond) (Some mn) x arg_src arg_tgt))
            (MEASURE: o = ord_top)
            (NPURE: fsp.(measure) x = ord_top)
            (POST: forall ctx1 w1 st_src1 st_tgt1 ret_src ret_tgt
                          (ACC: current_iProp ctx1 (FR ** I w1 st_src1 st_tgt1 ** fsp.(postcond) (Some mn) x ret_src ret_tgt)),
                hsim Q ctx1 None true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt)),
            P fuel f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt))
        (APCSTART: forall
            fuel1
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: hsim Q ctx (fuel1) true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
            (IH: P (fuel1) true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src, trigger (hAPC) >>= ktr_src) (st_tgt, itr_tgt))
        (APCSTEP: forall
            fsp (x: fsp.(meta)) w0 FR arg_src
            fn arg_tgt
            st_src0 st_tgt0 itr_src ktr_tgt
            fuel0 f_src f_tgt
            (SPEC: stb fn = Some fsp)
            (PRE: current_iProp ctx (FR ** I w0 st_src0 st_tgt0 ** fsp.(precond) (Some mn) x arg_src arg_tgt))
            (MEASURE: ord_lt (fsp.(measure) x) o)
            (PURE: is_pure (fsp.(measure) x))
            (POST: exists fuel1,
                (<<FUEL: Ord.lt fuel1 fuel0>>) /\
                (<<SIM: forall ctx1 w1 st_src1 st_tgt1 ret_src ret_tgt
                               (ACC: current_iProp ctx1 (FR ** I w1 st_src1 st_tgt1 ** fsp.(postcond) (Some mn) x ret_src ret_tgt)),
                    hsim Q ctx1 (Some fuel1) true true (st_src1, itr_src) (st_tgt1, ktr_tgt ret_tgt)>>)),
            P (Some fuel0) f_src f_tgt (st_src0, itr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt))
        (SYSCALL: forall
            fn arg rvs
            st_src st_tgt ktr_src ktr_tgt
            fuel f_src f_tgt
            (POST: forall ret,
                hsim Q ctx None true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret)),
            P fuel f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt))
        (TAUSRC: forall
            st_src st_tgt itr_src itr_tgt
            fuel f_src f_tgt
            (SIM: hsim Q ctx None true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P None true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
          ,
            P fuel f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt))
        (TAUTGT: forall
            st_src st_tgt itr_src itr_tgt
            fuel f_src f_tgt
            (SIM: hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P fuel f_src true (st_src, itr_src) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt))
        (CHOOSESRC: forall
            X
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: exists x, (<<SIM: hsim Q ctx None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P fuel f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt))
        (CHOOSETGT: forall
            X
            st_src st_tgt itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: forall x, (<<SIM: hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt))
        (TAKESRC: forall
            X
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: forall x, (<<SIM: hsim Q ctx None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P fuel f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt))
        (TAKETGT: forall
            X
            st_src st_tgt itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: exists x, (<<SIM: hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt))
        (PPUTSRC: forall
            st_src1
            st_src0 st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: hsim Q ctx None true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
            (IH: P None true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt))
        (PPUTTGT: forall
            st_tgt1
            st_src st_tgt0 itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
            (IH: P fuel f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt))
        (PGETSRC: forall
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: hsim Q ctx None true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
            (IH: P None true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt))
        (PGETTGT: forall
            st_src st_tgt itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: hsim Q ctx fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
            (IH: P fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt))
        (PROGRESS: forall
            st_src st_tgt itr_src itr_tgt
            fuel
            (SIM: hsim Q ctx fuel false false (st_src, itr_src) (st_tgt, itr_tgt)),
            P fuel true true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      forall fuel f_src f_tgt st_src st_tgt
             (SIM: hsim Q ctx fuel f_src f_tgt st_src st_tgt),
        P fuel f_src f_tgt st_src st_tgt.
  Proof.
    i. punfold SIM. induction SIM using _hsim_ind2.
    { eapply RET; eauto. }
    { eapply CALL; eauto. i. hexploit POST; eauto. i. pclearbot. eauto. }
    { eapply APCSTART; eauto. pfold. eauto. }
    { des. eapply APCSTEP; eauto. esplits; eauto. i. hexploit SIM; eauto. i. pclearbot. eauto. }
    { eapply SYSCALL; eauto. i. hexploit POST; eauto. i. pclearbot. eauto. }
    { eapply TAUSRC; eauto. pfold. eauto. }
    { eapply TAUTGT; eauto. pfold. eauto. }
    { des. eapply CHOOSESRC; eauto. esplits; eauto. pfold. eauto. }
    { eapply CHOOSETGT; eauto. i. hexploit SIM; eauto. i. des. pclearbot. splits; eauto. pfold. eauto. }
    { eapply TAKESRC; eauto. i. hexploit SIM; eauto. i. des. pclearbot. splits; eauto. pfold. eauto. }
    { des. eapply TAKETGT; eauto. esplits; eauto. pfold. eauto. }
    { eapply PPUTSRC; eauto. pfold. eauto. }
    { eapply PPUTTGT; eauto. pfold. eauto. }
    { eapply PGETSRC; eauto. pfold. eauto. }
    { eapply PGETTGT; eauto. pfold. eauto. }
    { eapply PROGRESS; eauto. pclearbot. eauto. }
  Qed.

  Definition mylift (fuel: option Ord.t) (mn_caller: option mname) X (x: X)
             ctx
             (Q: option mname -> X -> Any.t -> Any.t -> iProp) (itr_src: itree hEs Any.t): itree Es Any.t :=
    match fuel with
    | None =>
        (interp_hCallE_tgt mn stb o (interp_hEs_tgt itr_src) ctx) >>= (HoareFunRet Q mn_caller x)
    | Some fuel =>
        r0 <- (interp_hCallE_tgt mn stb o (_APC fuel) ctx);;
        r1 <- (interp_hCallE_tgt mn stb o (tau;; Ret (snd r0)) (fst r0));;
        r2 <- (interp_hCallE_tgt mn stb o (interp_hEs_tgt itr_src) (fst r1));;
        (HoareFunRet Q mn_caller x r2)
    end.

  Variant myr w0:
    option Ord.t -> bool -> bool -> world → Any.t * itree Es Any.t → Any.t * itree Es Any.t → Prop :=
  | myr_intro0
      f_src f_tgt st_src st_tgt (itr_src: itree (hAPCE +' Es) Any.t) itr_tgt mr_src ctx X (x: X) Q mn_caller
      (SIM: hsim (fun st_src st_tgt ret_src ret_tgt =>
                    (∃ w1, ⌜le w0 w1⌝ ** I w1 st_src st_tgt) ** (Q mn_caller x ret_src ret_tgt: iProp)) ctx None f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    :
      @myr
        w0
        None f_src f_tgt w0
        (Any.pair st_src mr_src, (interp_hCallE_tgt mn stb o (interp_hEs_tgt itr_src) ctx) >>= (HoareFunRet Q mn_caller x))
        (st_tgt, itr_tgt)
  | myr_intro1
      fuel f_src f_tgt st_src st_tgt (itr_src: itree (hAPCE +' Es) Any.t)  itr_tgt mr_src ctx X (x: X) Q mn_caller at_most
      (SIM: hsim (fun st_src st_tgt ret_src ret_tgt =>
                    (∃ w1, ⌜le w0 w1⌝ ** I w1 st_src st_tgt) ** (Q mn_caller x ret_src ret_tgt: iProp)) ctx (Some (fuel)) f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    :
      @myr
        w0
        (Some (fuel)) f_src f_tgt w0
        (Any.pair st_src mr_src,
         r0 <- (interp_hCallE_tgt mn stb o (_APC (Ord.S at_most)) ctx);;
         r1 <- (interp_hCallE_tgt mn stb o (tau;; Ret (snd r0)) (fst r0));;
         r2 <- (interp_hCallE_tgt mn stb o (interp_hEs_tgt itr_src) (fst r1));;
         (HoareFunRet Q mn_caller x r2))
        (st_tgt, itr_tgt)
  .

  Lemma current_iPropL_convert ctx P
        (CUR: current_iProp ctx P)
    :
      current_iPropL ctx [("H", P)].
  Proof.
    unfold current_iPropL. ss. unfold from_iPropL.
    eapply current_iProp_entail; eauto.
  Qed.

  Lemma AAA P Q
        (EQ: P = Q)
    :
    P -> Q.
  Proof.
    subst. auto.
  Qed.

  Lemma hsim_adequacy_aux:
    forall
      f_src f_tgt st_src st_tgt (itr_src: itree (hAPCE +' Es) Any.t) itr_tgt mr_src ctx X (x: X) Q mn_caller fuel w0
      (SIM: hsim (fun st_src st_tgt ret_src ret_tgt =>
                    (∃ w1, ⌜le w0 w1⌝ ** I w1 st_src st_tgt) ** (Q mn_caller x ret_src ret_tgt: iProp)) ctx fuel f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt)),
      paco8 (_sim_itree (mk_wf I) le) bot8 Any.t Any.t (lift_rel (mk_wf I) le w0 (@eq Any.t))
            f_src f_tgt w0
            (Any.pair st_src mr_src,
              mylift fuel mn_caller x ctx Q itr_src)
            (st_tgt, itr_tgt).
  Proof.
    ginit. gcofix CIH. i.
    remember (st_src, itr_src). remember (st_tgt, itr_tgt).
    revert st_src st_tgt itr_src itr_tgt Heqp Heqp0 CIH.
    induction SIM using hsim_ind; i; clarify.
    { eapply current_iPropL_convert in RET. mDesAll. destruct fuel; steps.
      { astop. steps. hret _; eauto. iModIntro. iSplitL "A1"; auto. }
      { hret _; eauto. iModIntro. iSplitL "A1"; auto. }
    }
    { eapply current_iPropL_convert in PRE. mDesAll. destruct fuel; steps.
      { astop. steps. rewrite SPEC. steps. destruct fsp. ss. hcall _ _ with "A A1".
        { iModIntro. iSplitL "A1"; eauto. iApply "A". }
        { rewrite MEASURE in *. splits; ss. unfold ord_lt. des_ifs. }
        { steps. gbase. hexploit CIH.
          { eapply POST. eapply current_iProp_entail; [eauto|].
            start_ipm_proof. iSplitR "POST".
            { iSplitL "H"; eauto. }
            { iApply "POST". }
          }
          i. ss. eauto.
        }
      }
      { rewrite SPEC. steps. destruct fsp. ss. hcall _ _ with "A A1".
        { iModIntro. iSplitL "A1"; eauto. iApply "A". }
        { rewrite MEASURE in *. splits; ss. unfold ord_lt. des_ifs. }
        { steps. gbase. hexploit CIH.
          { eapply POST. eapply current_iProp_entail; [eauto|].
            start_ipm_proof. iSplitR "POST".
            { iSplitL "H"; eauto. }
            { iApply "POST". }
          }
          i. ss. eauto.
        }
      }
    }
    { destruct fuel; steps.
      { astop. steps. exploit IHSIM; eauto. i. destruct fuel1; ss.
        { astart t0.
          match goal with
          | x0: ?P1 (_, ?itr0) _ |- ?P0 (_, ?itr1) _ =>
              replace itr1 with itr0
          end; auto.
          grind. destruct x1, x2. destruct u, u0. grind.
        }
        { astop. steps. }
      }
      { exploit IHSIM; eauto. i. destruct fuel1; ss.
        { astart t.
          match goal with
          | x0: ?P1 (_, ?itr0) _ |- ?P0 (_, ?itr1) _ =>
              replace itr1 with itr0
          end; auto.
          grind. destruct x1, x2. destruct u, u0. grind.
        }
        { astop. steps. }
      }
    }
    { des. steps. rewrite unfold_APC. steps.
      force_l. exists false. steps.
      force_l. exists fuel1. steps.
      force_l; [eauto|..]. steps.
      force_l. exists (fn, arg_src). steps.
      rewrite SPEC. steps.
      eapply current_iPropL_convert in PRE. mDesAll.
      destruct fsp. ss. hcall _ _ with "A A1".
      { iModIntro. iSplitL "A1"; eauto. iApply "A". }
      { splits; ss. }
      { steps. gbase. hexploit CIH.
        { eapply SIM. eapply current_iProp_entail; [eauto|].
          start_ipm_proof. iSplitR "POST".
          { iSplitL "H"; eauto. }
          { iApply "POST". }
        }
        i. ss. eauto.
      }
    }
    { destruct fuel; steps.
      { astop. steps. gbase. hexploit CIH; eauto. }
      { gbase. hexploit CIH; eauto. }
    }
    { destruct fuel; steps.
      { astop. steps. exploit IHSIM; eauto. }
      { exploit IHSIM; eauto. }
    }
    { steps. exploit IHSIM; eauto. }
    { des. exploit IH; eauto. i. destruct fuel; steps.
      { astop. steps. force_l. eexists. steps. eauto. }
      { force_l. eexists. steps. eauto. }
    }
    { steps. exploit SIM; eauto. i. des. eauto. }
    { destruct fuel; steps.
      { astop. steps. exploit SIM; eauto. i. des. eauto. }
      { exploit SIM; eauto. i. des. eauto. }
    }
    { des. exploit IH; eauto. i. force_r. eexists. eauto. }
    { destruct fuel; steps.
      { astop. steps. exploit IHSIM; eauto. }
      { exploit IHSIM; eauto. }
    }
    { steps. exploit IHSIM; eauto. }
    { destruct fuel; steps.
      { astop. steps. exploit IHSIM; eauto. }
      { exploit IHSIM; eauto. }
    }
    { steps. exploit IHSIM; eauto. }
    { deflag. gbase. eapply CIH; eauto. }
  Qed.

  Lemma hsim_progress_flag R_src R_tgt r g Q ctx fuel st_src st_tgt
        (SIM: gpaco9 _hsim (cpn9 _hsim) g g R_src R_tgt Q ctx fuel false false st_src st_tgt)
    :
      gpaco9 _hsim (cpn9 _hsim) r g _ _ Q ctx fuel true true st_src st_tgt.
  Proof.
    destruct st_src, st_tgt. gstep. eapply hsim_progress; eauto.
  Qed.

  Lemma _hsim_flag_mon
        r
        R_src R_tgt Q ctx
        fuel f_src0 f_tgt0 f_src1 f_tgt1 st_src st_tgt
        (SIM: @_hsim r R_src R_tgt Q ctx fuel f_src0 f_tgt0 st_src st_tgt)
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
    @_hsim r R_src R_tgt Q ctx fuel f_src1 f_tgt1 st_src st_tgt.
  Proof.
    revert f_src1 f_tgt1 SRC TGT.
    induction SIM using _hsim_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3. eapply IHSIM; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. }
    { econs 6. eapply IHSIM; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. des. esplits. eapply IH; eauto. }
    { econs 9; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. eapply IH; eauto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12. eapply IHSIM; auto. }
    { econs 13. eapply IHSIM; auto. }
    { econs 14. eapply IHSIM; auto. }
    { econs 15. eapply IHSIM; auto. }
    { exploit SRC; auto. exploit TGT; auto. i. clarify. econs 16; eauto. }
  Qed.

  Variant fuelC (r: forall R_src R_tgt
                           (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                           (ctx: Σ),
                    option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree Es R_tgt -> Prop)
          {R_src R_tgt}
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (ctx: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree Es R_tgt -> Prop :=
    | fuelC_intro
        f_src f_tgt fuel0 fuel1
        st_src st_tgt
        (SIM: r _ _ Q ctx fuel0 f_src f_tgt st_src st_tgt)
        (ORD: option_Ord_le fuel0 fuel1)
      :
      fuelC r Q ctx fuel1 f_src f_tgt st_src st_tgt
  .

  Lemma fuelC_mon:
    monotone9 fuelC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve fuelC_mon: paco.

  Lemma fuelC_spec: fuelC <10= gupaco9 (_hsim) (cpn9 _hsim).
  Proof.
    eapply wrespect9_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    revert x4 ORD. induction SIM using _hsim_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. i. eapply rclo9_base. eauto. }
    { econs 3; eauto. eapply _hsim_mon; eauto. i. eapply rclo9_base. auto. }
    { destruct x4; ss. econs 4; eauto. des. esplits; eauto.
      { eapply Ord.lt_le_lt; eauto. }
      { i. eapply rclo9_base. eauto. }
    }
    { econs 5; eauto. i. eapply rclo9_base. auto. }
    { econs 6; eauto. eapply _hsim_mon; eauto. i. apply rclo9_base. auto. }
    { econs 7; eauto. }
    { econs 8; eauto. des. esplits; eauto. eapply _hsim_mon; eauto. i. apply rclo9_base. auto. }
    { econs 9; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. eapply _hsim_mon; eauto. i. eapply rclo9_base; auto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12; eauto. eapply _hsim_mon; eauto. i. eapply rclo9_base; eauto. }.
    { econs 13; eauto. }
    { econs 14; eauto. eapply _hsim_mon; eauto. i. eapply rclo9_base; eauto. }.
    { econs 15; eauto. }
    { econs 16; eauto. eapply rclo9_clo_base. econs; eauto. }
  Qed.

  Variant hflagC (r: forall R_src R_tgt
                            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                            (ctx: Σ),
                     option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree Es R_tgt -> Prop)
          {R_src R_tgt}
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (ctx: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree Es R_tgt -> Prop :=
  | hflagC_intro
      f_src0 f_src1 f_tgt0 f_tgt1 fuel0 fuel1
      st_src st_tgt
      (SIM: r _ _ Q ctx fuel0 f_src0 f_tgt0 st_src st_tgt)
      (SRC: f_src0 = true -> f_src1 = true)
      (TGT: f_tgt0 = true -> f_tgt1 = true)
      (ORD: option_Ord_le fuel0 fuel1)
    :
      hflagC r Q ctx fuel1 f_src1 f_tgt1 st_src st_tgt
  .

  Lemma hflagC_mon:
    monotone9 hflagC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hflagC_mon: paco.

  Structure grespectful clo : Prop :=
    grespect_intro {
        grespect_mon: monotone9 clo;
        grespect_respect :
        forall l r
               (LE: l <9= r)
               (GF: l <9= @_hsim r),
          clo l <9= gpaco9 _hsim (cpn9 _hsim) bot9 (rclo9 (clo \10/ gupaco9 _hsim (cpn9 _hsim)) r);
      }.

  Lemma grespect_uclo clo
        (RESPECT: grespectful clo)
    :
    clo <10= gupaco9 (_hsim) (cpn9 _hsim).
  Proof.
    eapply grespect9_uclo; eauto with paco.
    econs.
    { eapply RESPECT. }
    i. hexploit grespect_respect.
    { eauto. }
    { eapply LE. }
    { eapply GF. }
    { eauto. }
    i. inv H. eapply rclo9_mon.
    { eauto. }
    i. ss. des; ss. eapply _paco9_unfold in PR0.
    2:{ ii. eapply _hsim_mon; [eapply PR1|]. i. eapply rclo9_mon; eauto. }
    ss. eapply _hsim_mon.
    { eapply PR0; eauto. }
    i. eapply rclo9_clo. right. econs.
    eapply rclo9_mon; eauto. i. inv PR2.
    { left. eapply paco9_mon; eauto. i. ss. des; ss.
      left. auto. }
    { des; ss. right. auto. }
  Qed.

  Lemma hflagC_spec: hflagC <10= gupaco9 (_hsim) (cpn9 _hsim).
  Proof.
    eapply grespect_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    guclo fuelC_spec. econs; [|eauto]. gstep.
    eapply _hsim_flag_mon; eauto.
    eapply _hsim_mon; eauto. i. gbase. eapply rclo9_base. auto.
  Qed.

  Variant hbindC (r: forall R_src R_tgt
                            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                            (ctx: Σ),
                     option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree Es R_tgt -> Prop)
          {R_src R_tgt}
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (ctx: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree Es R_tgt -> Prop :=
  | hbindC_intro
      S_src S_tgt
      (P: Any.t -> Any.t -> S_src -> S_tgt -> iProp)
      fuel f_src f_tgt st_src0 st_tgt0 itr_src itr_tgt ktr_src ktr_tgt
      (SIM: @r S_src S_tgt P ctx fuel f_src f_tgt (st_src0, itr_src) (st_tgt0, itr_tgt))
      (SIMK: forall ctx1 st_src1 st_tgt1 ret_src ret_tgt
                    (POST: current_iProp ctx1 (P st_src1 st_tgt1 ret_src ret_tgt)),
          @r R_src R_tgt Q ctx1 None false false (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt))
    :
      hbindC r Q ctx fuel f_src f_tgt (st_src0, itr_src >>= ktr_src) (st_tgt0, itr_tgt >>= ktr_tgt)
  .

  Lemma hbindC_mon:
    monotone9 hbindC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hbindC_mon: paco.

  Lemma hsim_clo:

  Lemma hbindC_spec: hbindC <10= gupaco9 (_hsim) (cpn9 _hsim).
  Proof.
    eapply grespect_uclo.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    remember (st_src0, itr_src). remember (st_tgt0, itr_tgt).
    revert st_src0 itr_src st_tgt0 itr_tgt Heqp Heqp0.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { hexploit SIMK; eauto. i.
      eapply GF in H. guclo hflagC_spec. econs.
      2:{ instantiate (1:=false). ss. }
      2:{ instantiate (1:=false). ss. }
      2:{ instantiate (1:=None). destruct fuel; ss. }
      gstep. eapply _hsim_mon; eauto. i. gbase. eapply rclo9_base. auto.
    }
    { gstep. econs 2; eauto. i. hexploit POST; eauto. i.
      gbase. eapply rclo9_clo_base. left. econs; eauto.
    }
    { admit "". }
    { des. gstep. econs 4; eauto. esplits; eauto. i.
      hexploit SIM; eauto. i. gbase. eapply rclo9_clo_base. left. econs; eauto.
    }
    { gstep. econs 5; eauto. i. gbase. eapply rclo9_clo_base. left. econs; eauto. }
    { gstep. econs 6; eauto. }
    { econs 7; eauto. }
    { des. econs 8; eauto. }
    { econs 9; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { des. econs 11; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. eapply rclo9_clo_base. econs; eauto. }
  Qed.

  Lemma hbindC_spec: hbindC <10= gupaco9 (_hsim) (cpn9 _hsim).
  Proof.
    eapply grespect9_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    cut (gpaco9 _hsim (cpn9 _hsim) bot9 (@_hsim (rclo9 (hbindC \10/ gupaco9 _hsim (cpn9 _hsim)) r))
                x0 x1 x2 x3 x4 x5 x6 (st_src0, itr_src >>= ktr_src)
                (st_tgt0, itr_tgt >>= ktr_tgt)).
    { i. inv H. eapply rclo9_mon.
      { eapply IN. }
      { i. ss. des; ss. admit "". }
    }
    remember (st_src0, itr_src). remember (st_tgt0, itr_tgt).
    revert st_src0 itr_src st_tgt0 itr_tgt Heqp Heqp0.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { eapply rclo9_base. hexploit SIMK; eauto. i.
      eapply GF in H. admit "ez".
    }
    { eapply rclo9_base. econs 2; eauto. i. hexploit POST; eauto. i.
      eapply rclo9_clo_base. left. econs; eauto.
    }
    { admit "". }
    { eapply rclo9_base. des. econs 4; eauto. esplits; eauto. i.
      hexploit SIM; eauto. i. eapply rclo9_clo_base. left. econs; eauto.
    }
    { eapply rclo9_base. econs 5; eauto. i. eapply rclo9_clo_base. left. econs; eauto. }
    { eapply rclo9_base. econs 6; eauto. }
    { econs 7; eauto. }
    { des. econs 8; eauto. }
    { econs 9; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { des. econs 11; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. eapply rclo9_clo_base. econs; eauto. }
  Qed.

  Lemma hbindC_spec: hbindC <10= gupaco9 (_hsim) (cpn9 _hsim).
  Proof.
    eapply wrespect9_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    remember (st_src0, itr_src). remember (st_tgt0, itr_tgt).
    revert st_src0 itr_src st_tgt0 itr_tgt Heqp Heqp0.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { hexploit SIMK; eauto. i.
      eapply GF in H. admit "ez".
    }
    { econs 2; eauto. i. hexploit POST; eauto. i.
      eapply rclo9_clo_base. econs; eauto.
    }
    { econs 3; eauto. }
    { des. econs 4; eauto. esplits; eauto. i.
      hexploit SIM; eauto. i. eapply rclo9_clo_base. econs; eauto.
    }
    { econs 5; eauto. i. i. eapply rclo9_clo_base. econs; eauto. }
    { econs 6; eauto. }
    { econs 7; eauto. }
    { des. econs 8; eauto. }
    { econs 9; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { des. econs 11; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. eapply rclo9_clo_base. econs; eauto. }
  Qed.

End SIM.


Section HLEMMAS.
  Context `{Σ: GRA.t}.
  Local Opaque GRA.to_URA.

  Variant mk_wf (A: Type)
          (R: A -> Any.t -> Any.t -> iProp)
    : A -> Any.t * Any.t -> Prop :=
  | mk_wf_intro
      a
      mr_src mp_src mp_tgt
      (RSRC: URA.wf mr_src -> R a mp_src mp_tgt mr_src)
    :
      mk_wf R a ((Any.pair mp_src mr_src↑), mp_tgt)
  .

  Definition inv_wf
             `{@GRA.inG invRA Σ}
             A
             (R: A -> Any.t -> Any.t -> iProp)
    : _ -> (Any.t * Any.t -> Prop) :=
    @mk_wf
      (A + Any.t * Any.t)%type
      (fun a' mp_src mp_tgt =>
         match a' with
         | inl a => R a mp_src mp_tgt
         | inr (mp_src1, mp_tgt1) => inv_closed ** ⌜mp_src1 = mp_src /\ mp_tgt1 = mp_tgt⌝
         end)%I
  .

  Lemma hcall_clo_ord_weaken'
        (fsp1: fspec)
        (x: shelve__ fsp1.(meta))

        A (a0: shelve__ A) FR

        (le: A -> A -> Prop) mn r rg a n m mr_src0 mp_src0
        (fsp0: fspec)
        mp_tgt0 k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)

        (WEAKER: fspec_weaker fsp1 fsp0)

        ctx0 I
        (ACC: current_iProp ctx0 I)

        (UPDATABLE:
           I ⊢ #=> (FR ** R a0 mp_src0 mp_tgt0 ** (fsp1.(precond) (Some mn) x varg_src varg_tgt: iProp)))

        (PURE: ord_lt (fsp1.(measure) x) ord_cur /\
               (tbr = true -> is_pure (fsp1.(measure) x)) /\ (tbr = false -> (fsp1.(measure) x) = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      ctx1
                      (ACC: current_iProp ctx1 (FR ** R a1 mp_src1 mp_tgt1 ** fsp1.(postcond) (Some mn) x vret_src vret_tgt))
          ,
                gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true a
                       (Any.pair mp_src1 mr_src1↑, k_src (ctx1, vret_src)) (mp_tgt1, k_tgt vret_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (Any.pair mp_src0 mr_src0, (HoareCall mn tbr ord_cur fsp0 fn varg_src) ctx0 >>= k_src)
             (mp_tgt0, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    subst. unfold HoareCall, mput, mget, assume, guarantee.
    ired_both. apply sim_itreeC_spec. econs.
    hexploit (WEAKER x). i. des.
    assert (exists mr_src0' rarg_src fr_src0',
               (<<UPDATABLE: URA.wf (ctx0 ⋅ (mr_src0' ⋅ (rarg_src ⋅ fr_src0')))>>) /\
               (<<RSRC: R a0 mp_src0 mp_tgt0 mr_src0'>>) /\
               (<<FRS: FR fr_src0'>>) /\
               (<<PRE: fsp0.(precond) (Some mn) x_tgt varg_src varg_tgt rarg_src>>)).
    { inv ACC. uipropall. hexploit UPDATABLE.
      { eapply URA.wf_mon. eapply GWF. }
      { eapply IPROP. }
      { et. }
      i. des. subst.
      hexploit PRE; et. i. uipropall. hexploit (H0 b); et.
      { eapply URA.wf_mon in H. rewrite URA.add_comm in H. eapply URA.wf_mon in H. auto. }
      { instantiate (1:=a2 ⋅ b0 ⋅ ctx0).
        replace (b ⋅ (a2 ⋅ b0 ⋅ ctx0)) with (a2 ⋅ b0 ⋅ b ⋅ ctx0); auto. r_solve. }
      i. des. esplits; et.
      { replace (ctx0 ⋅ (b0 ⋅ (r1 ⋅ a2))) with (r1 ⋅ (a2 ⋅ b0 ⋅ ctx0)); auto. r_solve. }
    }
    des. exists (rarg_src, fr_src0', mr_src0').
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto.
    { r_wf UPDATABLE0. }
    repeat (ired_both; apply sim_itreeC_spec; econs). exists x_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists varg_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto.
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto.
    { r in MEASURE. des_ifs; ss; des_ifs. eapply Ord.le_lt_lt; et. }
    { i. spc PURE0. r in MEASURE. des_ifs; ss; des_ifs. }
    { i. spc PURE1. r in MEASURE. des_ifs; ss; des_ifs. }
    repeat (ired_both; apply sim_itreeC_spec; econs).
    { econs; eauto. }
    i. repeat (ired_both; apply sim_itreeC_spec; econs). i. destruct x0.
    repeat (ired_both; apply sim_itreeC_spec; econs). inv WF.
    repeat (ired_both; apply sim_itreeC_spec; econs). i.
    repeat (ired_both; apply sim_itreeC_spec; econs). i.
    repeat (ired_both; apply sim_itreeC_spec; econs). i.
    ired_both. eapply POST; eauto. hexploit POST0. i.
    uipropall. hexploit (H c); et.
    { eapply URA.wf_mon. instantiate (1:=fr_src0' ⋅ c0 ⋅ mr_src). r_wf x0. }
    { instantiate (1:=fr_src0' ⋅ c0 ⋅ mr_src). r_wf x0. }
    i. des. econs.
    { instantiate (1:=fr_src0' ⋅ mr_src ⋅ r1). r_wf H0. }
    esplits; et.
    eapply RSRC0.
    eapply URA.wf_mon. instantiate (1:=r1 ⋅ fr_src0' ⋅ c0). r_wf H0.
  Qed.

  Lemma hcall_clo_ord_weaken
        Hns Rn Invn
        (fsp1: fspec)
        (x: shelve__ fsp1.(meta))

        A (a0: shelve__ A)

        (le: A -> A -> Prop) mn r rg a n m mr_src0 mp_src0
        (fsp0: fspec)
        mp_tgt0 k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)

        (WEAKER: fspec_weaker fsp1 fsp0)

        ctx0 l
        (ACC: current_iPropL ctx0 l)

        (UPDATABLE:
           from_iPropL (fst (alist_pops Hns l)) ⊢ #=> (R a0 mp_src0 mp_tgt0 ** (fsp1.(precond) (Some mn) x varg_src varg_tgt: iProp)))

        (PURE: ord_lt (fsp1.(measure) x) ord_cur /\
               (tbr = true -> is_pure (fsp1.(measure) x)) /\ (tbr = false -> (fsp1.(measure) x) = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      ctx1
                      (ACC: current_iPropL ctx1 ((Invn, R a1 mp_src1 mp_tgt1) :: (Rn, fsp1.(postcond) (Some mn) x vret_src vret_tgt) :: snd (alist_pops Hns l)))
          ,
            gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true a
                   (Any.pair mp_src1 mr_src1↑, k_src (ctx1, vret_src)) (mp_tgt1, k_tgt vret_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (Any.pair mp_src0 mr_src0, (HoareCall mn tbr ord_cur fsp0 fn varg_src) ctx0 >>= k_src)
             (mp_tgt0, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    subst. eapply hcall_clo_ord_weaken'; et.
    { instantiate (2:=from_iPropL (snd (alist_pops Hns l))).
      etrans.
      { eapply iPropL_alist_pops. }
      iIntros "[H0 H1]".
      iPoseProof (UPDATABLE with "H0") as "> [H0 H2]".
      iModIntro. iFrame.
    }
    i. eapply POST; et. red. ss.
    eapply current_iProp_entail; et.
    iIntros "[[H0 H1] H2]". iFrame.
  Qed.

  Lemma hcall_clo_weaken
        Hns Rn Invn
        (fsp1: fspec)
        (x: shelve__ fsp1.(meta))

        A (a0: shelve__ A)

        (le: A -> A -> Prop) mn r rg a n m mr_src0 mp_src0
        (fsp0: fspec)
        mp_tgt0 k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)

        (WEAKER: fspec_weaker fsp1 fsp0)

        ctx0 l
        (ACC: current_iPropL ctx0 l)

        (UPDATABLE:
           from_iPropL (fst (alist_pops Hns l)) ⊢ #=> (R a0 mp_src0 mp_tgt0 ** (fsp1.(precond) (Some mn) x varg_src varg_tgt: iProp)))

        (PURE: ord_lt (fsp1.(measure) x) ord_cur /\
               (tbr = true -> is_pure (fsp1.(measure) x)) /\ (tbr = false -> (fsp1.(measure) x) = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      ctx1
                      (ACC: current_iPropL ctx1 (@cons (prod string (bi_car iProp)) (Invn, R a1 mp_src1 mp_tgt1) (@cons (prod string (bi_car iProp)) (Rn, fsp1.(postcond) (Some mn) x vret_src vret_tgt) (snd (alist_pops Hns l)))))
          ,
            gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true a
                   (Any.pair mp_src1 mr_src1↑, k_src (ctx1, vret_src)) (mp_tgt1, k_tgt vret_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (Any.pair mp_src0 mr_src0, (HoareCall mn tbr ord_cur fsp0 fn varg_src) ctx0 >>= k_src)
             (mp_tgt0, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    eapply (@hcall_clo_ord_weaken _ _ _); eauto.
  Qed.

  Lemma hcall_clo
        Hns Rn Invn
        X (x: shelve__ X)
        A (a0: shelve__ A)

        (D: X -> ord)
        (P: option mname -> X -> Any.t -> Any.t -> Σ -> Prop)
        (Q: option mname -> X -> Any.t -> Any.t -> Σ -> Prop)
        (le: A -> A -> Prop) mn r rg a n m mr_src0 mp_src0
        mp_tgt0 k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)

        ctx0 l
        (ACC: current_iPropL ctx0 l)

        (UPDATABLE:
           from_iPropL (fst (alist_pops Hns l)) ⊢ #=> (R a0 mp_src0 mp_tgt0 ** (P (Some mn) x varg_src varg_tgt: iProp)))

        (PURE: ord_lt (D x) ord_cur /\
               (tbr = true -> is_pure (D x)) /\ (tbr = false -> (D x) = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1: Σ) (mp_src1 mp_tgt1 : Any.t) a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      ctx1
                      (ACC: current_iPropL ctx1 (@cons (prod string (bi_car iProp)) (Invn, R a1 mp_src1 mp_tgt1) (@cons (prod string (bi_car iProp)) (Rn, Q (Some mn) x vret_src vret_tgt) (snd (alist_pops Hns l)))))
          ,
                gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true a
                       (Any.pair mp_src1 mr_src1↑, k_src (ctx1, vret_src)) (mp_tgt1, k_tgt vret_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (Any.pair mp_src0 mr_src0, (HoareCall mn tbr ord_cur (mk_fspec D P Q) fn varg_src) ctx0 >>= k_src)
             (mp_tgt0, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    eapply hcall_clo_weaken; eauto.
    { refl. }
    { eauto. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma harg_clo
        A Rn Invn
        mn r rg
        X (P: option mname -> X -> Any.t -> Any.t -> Σ -> Prop) varg
        mpr_src mp_tgt f_tgt k_src
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (WF: mk_wf R a (mpr_src, mp_tgt))
        m n
        (ARG:
           forall x varg_src
                  ctx (mr_src: Σ) mp_src
                  (ACC: current_iPropL ctx (@cons (prod string (bi_car iProp)) (Rn, P mn x varg_src varg) (@cons (prod string (bi_car iProp)) (Invn, R a mp_src mp_tgt) (@nil (prod string (bi_car iProp)))))),
             gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr true n a
                    (Any.pair mp_src mr_src↑, k_src (ctx, ((mn, x), varg_src)))
                    (mp_tgt, f_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (mpr_src, (HoareFunArg P (mn, varg) >>= k_src))
             (mp_tgt, f_tgt)
  .
  Proof.
    inv WF.
    unfold HoareFunArg, mput, mget, assume, guarantee.
    repeat (ired_both; apply sim_itreeC_spec; econs). intro x.
    repeat (ired_both; apply sim_itreeC_spec; econs). intro varg_src.
    repeat (ired_both; apply sim_itreeC_spec; econs). intros (rarg_src, ctx).
    repeat (ired_both; apply sim_itreeC_spec; econs). intros VALID.
    repeat (ired_both; apply sim_itreeC_spec; econs). intro PRE.
    ired_both. eapply ARG; et.
    red. econs.
    { instantiate (1:=rarg_src ⋅ mr_src). r_wf VALID. }
    { ss. red. uipropall. esplits; et.
      { rewrite URA.unit_id. et. }
      { eapply RSRC; et. eapply URA.wf_mon. instantiate (1:=(ctx ⋅ rarg_src)). r_wf VALID. }
      { red. uipropall. }
    }
  Qed.

  Lemma hret_clo
        A (a: shelve__ A)
        mn r rg n m mr_src mp_src a0
        X (Q: option mname -> X -> Any.t -> Any.t -> Σ -> Prop)
        x vret_src vret_tgt
        mp_tgt
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)

        ctx l
        (ACC: current_iPropL ctx l)

        (WLE: le a0 a)

        (UPDATABLE:
           (from_iPropL l) ⊢ #=> (R a mp_src mp_tgt ** (Q mn x vret_src vret_tgt: iProp)))

        (EQ: forall (mr_src1: Σ) (WLE: le a0 a) (WF: mk_wf R a (Any.pair mp_src mr_src1↑, mp_tgt)),
            eqr (Any.pair mp_src mr_src1↑) mp_tgt vret_tgt vret_tgt)
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a0
             (Any.pair mp_src mr_src, (HoareFunRet Q mn x (ctx, vret_src)))
             (mp_tgt, (Ret vret_tgt))
  .
  Proof.
    subst. unfold HoareFunRet, mput, mget, guarantee.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists vret_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs).
    assert (exists mr_src1 rret_src,
               (<<UPDATABLE: URA.wf (ctx ⋅ (mr_src1 ⋅ rret_src))>>) /\
               (<<RSRC: R a mp_src mp_tgt mr_src1>>) /\
               (<<PRE: Q mn x vret_src vret_tgt rret_src>>)).
    { red in ACC. inv ACC. uipropall.
      hexploit (UPDATABLE r0); et.
      { eapply URA.wf_mon; et. }
      i. des. subst. exists a1, b. splits; et.
      replace (ctx ⋅ (a1 ⋅ b)) with (a1 ⋅ b ⋅ ctx); et.
      r_solve.
    }
    des. exists (rret_src, mr_src1).
    repeat (ired_both; apply sim_itreeC_spec; econs).
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits.
    { r_wf UPDATABLE0. }
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto.
    repeat (ired_both; apply sim_itreeC_spec; econs).
    eapply EQ; et. econs; et.
  Qed.

  Lemma APC_start_clo
        (at_most: Ord.t)
        (o: ord)
        A mn r rg a m n mp_src0
        k_src
        (wf: A -> Any.t * Any.t -> Prop)
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx

        (POST: gpaco8 (_sim_itree wf le) (cpn8 (_sim_itree wf le)) r rg _ _ eqr true n a
                      (mp_src0,
                       (interp_hCallE_tgt mn stb o (_APC at_most) ctx)>>= k_src)
                      (itr_tgt))
    :
      gpaco8 (_sim_itree wf le) (cpn8 (_sim_itree wf le)) r rg _ _ eqr m n a
             (mp_src0,
              (interp_hCallE_tgt mn stb o APC ctx) >>= k_src)
             (itr_tgt).
  Proof.
    subst. unfold APC. destruct itr_tgt.
    ired_both. apply sim_itreeC_spec. eapply sim_itreeC_choose_src.
    exists at_most.
    repeat (ired_both; apply sim_itreeC_spec; econs).
    ired_both. et.
    Unshelve. all: ss.
  Qed.

  Lemma APC_stop_clo
        (o: ord)
        A mn r rg a n m mp_src0
        k_src
        (at_most: Ord.t)
        (wf: A -> Any.t * Any.t -> Prop)
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx

        (POST: gpaco8 (_sim_itree wf le) (cpn8 (_sim_itree wf le)) r rg _ _ eqr true n a
                      (mp_src0, k_src (ctx, ()))
                      (itr_tgt))
    :
      gpaco8 (_sim_itree wf le) (cpn8 (_sim_itree wf le)) r rg _ _ eqr m n a
              (mp_src0,
              (interp_hCallE_tgt mn stb o (_APC at_most) ctx) >>= k_src)
             (itr_tgt).
  Proof.
    subst. destruct itr_tgt.
    rewrite unfold_APC. ired_l. apply sim_itreeC_spec. eapply sim_itreeC_choose_src.
    exists true. ired_l. apply sim_itreeC_spec. eapply sim_itreeC_tau_src.
    ired_both. et.
  Qed.

  Lemma APC_step_clo
        (fn: gname) (args: Any.t) (next: Ord.t)

        (o: ord)
        A mn r rg a n m mp_src0
        k_src ctx0
        (at_most: Ord.t)
        (wf: A -> Any.t * Any.t -> Prop)
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        stb itr_tgt

        (fsp: fspec)
        (FIND: stb fn = Some fsp)
        (NEXT: (next < at_most)%ord)

        (POST: gpaco8 (_sim_itree wf le) (cpn8 (_sim_itree wf le)) r rg _ _ eqr true n a
                      (mp_src0,
                       ('(ctx1, _) <- (HoareCall mn true o fsp fn args ctx0);;
                        Tau (ITree.bind (interp_hCallE_tgt mn stb o (_APC next) ctx1) k_src)))
                      (itr_tgt))
    :
      gpaco8 (_sim_itree wf le) (cpn8 (_sim_itree wf le)) r rg _ _ eqr m n a
             (mp_src0, (interp_hCallE_tgt mn stb o (_APC at_most) ctx0) >>= k_src)
             (itr_tgt).
  Proof.
    subst. destruct itr_tgt.
    rewrite unfold_APC. ired_l. apply sim_itreeC_spec. eapply sim_itreeC_choose_src.
    exists false. ired_l. apply sim_itreeC_spec. eapply sim_itreeC_tau_src.
    ired_l. apply sim_itreeC_spec. eapply sim_itreeC_choose_src.
    exists next. ired_l. apply sim_itreeC_spec. eapply sim_itreeC_tau_src.
    ired_l. unfold guarantee. ired_l. apply sim_itreeC_spec. eapply sim_itreeC_choose_src.
    split.
    { auto. }
    ired_l. apply sim_itreeC_spec. eapply sim_itreeC_tau_src.
    ired_l. apply sim_itreeC_spec. eapply sim_itreeC_choose_src.
    exists (fn, args).
    ired_l. apply sim_itreeC_spec. eapply sim_itreeC_tau_src.
    ired_l. ss. rewrite FIND. ss. subst. ired_l.
    ss. ired_l.
    match goal with
    | [SIM: gpaco8 _ _ _ _ _ _ _ _ _ _ ?i0 _ |- gpaco8 _ _ _ _ _ _ _ _ _ _ ?i1 _] =>
      replace i1 with i0; et
    end.
    f_equal. grind.
  Qed.

  Lemma trivial_init_clo
        A wf (le: A -> A -> Prop) r rg w arg mrp_src mp_tgt itr_tgt mn stb body RR
        m n
        (INIT:
           gpaco8 (_sim_itree wf le) (cpn8 (_sim_itree wf le)) r rg Any.t Any.t
                  RR true n w
                  (mrp_src, fun_to_tgt mn stb (mk_specbody fspec_trivial body) arg)
                  (mp_tgt, itr_tgt))
    :
      gpaco8 (_sim_itree wf le) (cpn8 (_sim_itree wf le)) r rg Any.t Any.t
             RR m n w
             (mrp_src, KModSem.disclose_ksb_tgt mn stb (ksb_trivial body) arg)
             (mp_tgt, itr_tgt).
  Proof.
    unfold KModSem.disclose_ksb_tgt.
    apply sim_itreeC_spec. econs; eauto. i. destruct x; et.
  Qed.

End HLEMMAS.


Ltac prep := ired_both.

Ltac _force_l :=
  prep;
  match goal with
  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, guarantee ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_src; [exists name]|contradict name]; cycle 1

  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, ITree.bind' _ (interp _ guarantee ?P) (_, _))) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_src; [exists name]|contradict name]; cycle 1

   (* TODO: handle interp_hCallE_tgt better and remove this case *)
  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, ITree.bind' _ (interp _ (guarantee ?P ))) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_src; [exists name]|contradict name]; cycle 1; clear name

  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_tgt; apply sim_itreeC_spec; econs; unseal i_tgt
  end
.

Ltac _force_r :=
  prep;
  match goal with
  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_take_tgt; [exists name]|contradict name]; cycle 1

  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_src; apply sim_itreeC_spec; econs; unseal i_src
  end
.

Ltac _step :=
  match goal with
  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, trigger (Choose _) >>= _) (_, ?i_tgt)) ] => idtac *)
  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, triggerUB >>= _) (_, _)) ] =>
    unfold triggerUB; ired_l; _step; done
  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_both; _force_l; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    ired_both; apply sim_itreeC_spec; eapply sim_itreeC_take_src; intro name

  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, triggerNB >>= _) (_, _)) ] =>
    unfold triggerNB; ired_r; _step; done
  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_both; _force_r; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_tgt; intro name



  | _ => (*** default ***)
    eapply safe_sim_sim; econs; i
  end;
  match goal with
  | [ |- exists (_: unit), _ ] => esplits; [eauto|..]; i
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end
.
Ltac _steps := repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) simpl).

Ltac steps := repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) simpl; des_ifs_safe).
Ltac force_l := _force_l.
Ltac force_r := _force_r.

Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco8 (_sim_itree wf _) _ _ _ _ _ _ _ _ n ((Any.pair src0 src1), src2) (tgt0, tgt2))
      (at level 60,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco8 (_sim_itree wf _) _ _ _ _ _ _ _ _ n (src0, src2) (tgt0, tgt2))
      (at level 60,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Section TEST.
  Context `{Σ: GRA.t}.
  Let wf := (mk_wf (fun (_ : unit) (_ _ : Any.t) => bi_pure True)).
  Let le := fun (_ _: unit) => True.
  Variable (srcs0 tgts0: Any.t).

  Goal gpaco8 (_sim_itree wf le) (cpn8 (_sim_itree wf le)) bot8 bot8 Any.t Any.t (fun _ _ => eq) false false tt
       (srcs0, triggerUB >>= idK) (tgts0, triggerUB >>= idK).
  Proof.
    steps.
  Qed.

  Goal gpaco8 (_sim_itree wf le) (cpn8 (_sim_itree wf le)) bot8 bot8 Any.t Any.t (fun _ _ => eq) false false tt
       (srcs0, triggerNB >>= idK) (tgts0, triggerNB >>= idK).
  Proof.
    steps.
  Qed.

End TEST.


Ltac astep_full _fn _args _next _n1 :=
  eapply (@APC_step_clo _ _fn _args _next _n1);
  [(try by ((try stb_tac); refl))|
   oauto|
  ].

Ltac astep _fn _args :=
  eapply (@APC_step_clo _ _fn _args);
  [(try by ((try stb_tac); refl))|
   oauto|
  ].

Ltac acatch :=
  match goal with
  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?fn ?args) >>= _)) ] =>
    astep fn args
  end.

Ltac astart _at_most :=
  eapply (@APC_start_clo _ _at_most)
.

Ltac astop :=
  match goal with
  | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, interp_hCallE_tgt _ _ _ APC _ >>= _) (_, _)) ] => astart 0
  | _ => idtac
  end;
  eapply APC_stop_clo.

Ltac init :=
  let varg_src := fresh "varg_src" in
  let mn := fresh "mn" in
  let varg := fresh "varg" in
  let EQ := fresh "EQ" in
  let w := fresh "w" in
  let mrp_src := fresh "mrp_src" in
  let mp_tgt := fresh "mp_tgt" in
  let WF := fresh "WF" in
  split; ss; intros varg_src [mn varg] EQ w mrp_src mp_tgt WF;
  try subst varg_src; cbn; ginit;
  match goal with
  | |- gpaco8 _ _ _ _ _ _ _ _ _ _ (_, KModSem.disclose_ksb_tgt _ _ (ksb_trivial _) _) _ =>
    eapply trivial_init_clo;
    try (unfold fun_to_tgt, cfunN, cfunU, KModSem.disclose_ksb_tgt, fun_to_tgt);
    rewrite HoareFun_parse; simpl
  | |- gpaco8 _ _ _ _ _ _ _ _ _ _ (_, KModSem.disclose_ksb_tgt _ _ _ _) _ =>
    try (unfold fun_to_tgt, cfunN, cfunU, KModSem.disclose_ksb_tgt, fun_to_tgt);
    simpl;
    apply sim_itreeC_spec; apply sim_itreeC_take_src; intros [];rewrite HoareFun_parse; simpl
  | |- _ =>
    try (unfold fun_to_tgt, cfunN, cfunU; rewrite HoareFun_parse); simpl
  end.

Ltac harg :=
  let PRE := constr:("PRE") in
  let INV := constr:("INV") in
  eapply (@harg_clo _ _ PRE INV);
  [eassumption
  |
  ]; i.

Tactic Notation "hret" uconstr(a) :=
  eapply (@hret_clo _ _ a); unshelve_goal;
  [eassumption
  |
  |start_ipm_proof
  |try by (i; (try unfold lift_rel); esplits; et)
  ].

Tactic Notation "hcall" uconstr(x) uconstr(a) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := get_fresh_name_tac "INV" in
  let Hns := select_ihyps Hns in
  eapply (@hcall_clo _ Hns POST INV _ x _ a);
  unshelve_goal;
  [eassumption
  |start_ipm_proof
  |
  |on_current ltac:(fun H => try clear H); i; on_current ltac:(fun H => simpl in H)
  ].

Tactic Notation "hcall_weaken" uconstr(fsp) uconstr(x) uconstr(a) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := get_fresh_name_tac "INV" in
  let Hns := select_ihyps Hns in
  eapply (@hcall_clo_weaken _ Hns POST INV fsp x _ a);
  unshelve_goal;
  [
  |eassumption
  |start_ipm_proof
  |
  |on_current ltac:(fun H => try clear H); i; on_current ltac:(fun H => simpl in H)
  ].

Ltac iarg :=
  let PRE := constr:("PRE") in
  let INV := constr:("INV") in
  let CLOSED := constr:("☃CLOSED") in
  eapply (@harg_clo _ _ PRE INV);
  [eassumption
  |
  ];
  i;
  mDesSep PRE as CLOSED PRE;
  match goal with
  | [ |- (gpaco8 _ _ _ _ _ _ _ _ _ ?w _ _)] =>
    destruct w as [?|[?mp_src ?mp_tgt]]; simpl;
    [
        |mAssertPure False; ss; iDestruct "INV" as "[INV _]"; iApply (inv_closed_unique with "☃CLOSED INV")
    ]
  end.

Tactic Notation "icall_open" uconstr(x) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := constr:("☃CLOSED") in
  let Hns := select_ihyps Hns in
  let Hns := constr:("☃CLOSED"::Hns) in
  eapply (@hcall_clo _ Hns POST INV _ x _ (inr (_, _)));
  unshelve_goal;
  [eassumption
  |start_ipm_proof; iSplitL "☃CLOSED"; [iModIntro; iSplitL "☃CLOSED"; [iExact "☃CLOSED"|ss]|]
  |
  |
  on_current ltac:(fun H => try clear H);
  intros ? ? ? ? [|[?mp_src ?mp_tgt]]; i; simpl;
  on_current ltac:(fun H => simpl in H);
  [exfalso; match goal with | H: inv_le _ _ _ |- _ => cbn in H; inv H end
  |mDesSep "☃CLOSED" as "☃CLOSED" "☃TMP"; mPure "☃TMP" as [[] []]
  ]
  ].

Tactic Notation "icall_weaken" uconstr(ftsp) uconstr(x) uconstr(a) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := get_fresh_name_tac "INV" in
  let CLOSED := constr:("☃CLOSED") in
  let TMP := constr:("☃TMP") in
  let Hns := select_ihyps Hns in
  let Hns := constr:("☃CLOSED"::Hns) in
  eapply (@hcall_clo_weaken _ Hns POST INV ftsp x _ (inl a));
  unshelve_goal;
  [|eassumption
   |start_ipm_proof; iFrame "☃CLOSED"
   |
   |on_current ltac:(fun H => try clear H);
    intros ? ? ? ? [|[?mp_src ?mp_tgt]]; i; simpl;
    on_current ltac:(fun H => simpl in H);
    [
      mDesSep POST as "☃CLOSED" POST
    |
    mDesSep INV as "☃CLOSED" INV;
    mDesSep POST as "☃TMP" POST;
    mAssertPure False; [iApply (inv_closed_unique with "☃TMP ☃CLOSED")|ss]
    ]
  ].

Tactic Notation "iret" uconstr(a) :=
  eapply (@hret_clo _ _ (inl a)); unshelve_goal;
  [eassumption
  |
  |start_ipm_proof; iFrame "☃CLOSED"
  |try by (i; (try unfold lift_rel); esplits; et)
  ].


Global Opaque _APC APC interp interp_hCallE_tgt.

Global Opaque HoareFun HoareFunArg HoareFunRet HoareCall.

Definition __hide_mark A (a : A) : A := a.
Lemma intro_hide_mark: forall A (a: A), a = __hide_mark a. refl. Qed.

Ltac hide_k :=
  match goal with
  | [ |- (gpaco8 _ _ _ _ _ _ _ _ _ _ (_, ?isrc >>= ?ksrc) (_, ?itgt >>= ?ktgt)) ] =>
    erewrite intro_hide_mark with (a:=ksrc);
    erewrite intro_hide_mark with (a:=ktgt);
    let name0 := fresh "__KSRC__" in set (__hide_mark ksrc) as name0; move name0 at top;
    let name0 := fresh "__KTGT__" in set (__hide_mark ktgt) as name0; move name0 at top
  end.

Ltac unhide_k :=
  do 2 match goal with
  | [ H := __hide_mark _ |- _ ] => subst H
  end;
  rewrite <- ! intro_hide_mark
.

Ltac deflag :=
  match goal with
  | [ |- (gpaco8 _ _ _ _ _ _ _ true true _ _ _) ] =>
    eapply sim_itree_progress_flag
  | [ |- (gpaco8 _ _ _ _ _ _ _ _ _ _ _ _) ] =>
    eapply sim_itree_flag_down
  | _ => fail
  end.
