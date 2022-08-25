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
Require Import HTactics2.

Set Implicit Arguments.

Ltac ired_l := try (prw _red_gen 2 1 0).
Ltac ired_r := try (prw _red_gen 1 1 0).

Ltac ired_both := ired_l; ired_r.


Section FSP.

  Context `{Σ: GRA.t}.

  Lemma current_iProp_updatable (res0 res1: Σ) P
        (WF: URA.wf res1)
        (UPD: URA.updatable res1 res0)
        (CUR: current_iProp res0 P)
    :
      current_iProp res1 P.
  Proof.
    inv CUR. econs; try eassumption. etrans; et.
  Qed.

  Lemma current_iProp_frame_own res0 res1 P
        (WF: URA.wf ((res0 ⋅ res1): Σ))
        (CUR: current_iProp (res0) (Own res1 -* P))
    :
      current_iProp (res0 ⋅ res1) P.
  Proof.
    inv CUR. uipropall. hexploit IPROP.
    2:{ refl. }
    { eapply URA.updatable_wf; try apply WF; et. eapply URA.updatable_add; et. refl. }
    i. econs; eauto. eapply URA.updatable_add; et. refl.
  Qed.

  Lemma current_iProp_frame_own_rev res0 res1 P
        (CUR: current_iProp res0 (Own res1 ** P))
    :
      exists res2, URA.wf res0 /\ URA.updatable res0 (res2 ⋅ res1) ∧ current_iProp res2 P.
  Proof.
    inv CUR. uipropall.
    unfold URA.extends in *. des; clarify.
    exists (ctx ⋅ b). esplits; et.
    { etrans; et. replace (ctx ⋅ b ⋅ res1) with (res1 ⋅ ctx ⋅ b) by r_solve; ss. }
    econs; eauto.
    { eapply URA.updatable_wf; et. etrans; et. eapply URA.extends_updatable. exists res1. r_solve. }
    { eapply URA.extends_updatable. exists ctx. r_solve. }
  Qed.

  (* Lemma current_iProp_own_wf ctx res *)
  (*       (CUR: current_iProp ctx (Own res)) *)
  (*   : *)
  (*     URA.wf (ctx ⋅ res). *)
  (* Proof. *)
  (*   inv CUR. uipropall. unfold URA.extends in *. des. clarify. *)
  (*   eapply URA.wf_mon. *)
  (*   instantiate (1:=ctx0). r_wf GWF. *)
  (* Qed. *)

End FSP.



(*** `hsim` is an intermediate step towards `isim`, which is defined in iProp like weakest precondition (wp).
Both `hsim` and `isim` take the postcondition (Q) as an argument like the weakest precondition (wp). ***)

Section SIM.
  Context `{Σ: GRA.t}.
  Variable world: Type.
  Variable le: relation world.
  Variable I: world -> Any.t -> Any.t -> iProp.

  Variable mn: mname.
  Variable stb_src stb_tgt: gname -> option fspec.
  Variable o_src o_tgt: ord.
  Hypothesis OLE: ord_le o_tgt o_src.
  Hypothesis SIMPLTGT: forall fn fsp_tgt (IN: stb_tgt fn = Some fsp_tgt), is_simple fsp_tgt.
  Hypothesis PUREINCL: stb_pure_incl stb_tgt stb_src.

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

  Definition inv_with w0 st_src st_tgt: iProp :=
    (∃ w1, I w1 st_src st_tgt ** ⌜le w0 w1⌝)%I.

  Lemma inv_with_current `{PreOrder _ le} w0 st_src st_tgt
    :
      bi_entails (I w0 st_src st_tgt) (inv_with w0 st_src st_tgt).
  Proof.
    unfold inv_with. iIntros "H". iExists w0. iSplit; auto.
  Qed.

  Lemma inv_with_le `{PreOrder _ le} w0 w1 st_src st_tgt
        (LE: le w0 w1)
    :
      bi_entails (inv_with w1 st_src st_tgt) (inv_with w0 st_src st_tgt).
  Proof.
    unfold inv_with. iIntros "H". iDestruct "H" as (w2) "[H0 %]".
    iExists w2. iSplit; auto. iPureIntro. etrans; eauto.
  Qed.

  Inductive _hsim
            (hsim: forall R_src R_tgt
                          (OwnT: Σ)
                          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                          (fmr: Σ),
                option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop)
            {R_src R_tgt}
            (OwnT: Σ)
            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
            (fmr: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop :=
  | hsim_ret
      v_src v_tgt
      st_src st_tgt
      fuel f_src f_tgt
      (RET: current_iProp fmr (Own OwnT ** Q st_src st_tgt v_src v_tgt))
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt))
  | hsim_call
      fsp_src fsp_tgt w0
      fn arg_src arg_tgt
      st_src0 st_tgt0 ktr_src ktr_tgt
      fuel f_src f_tgt
      (SPEC: stb_src fn = Some fsp_src)
      (SPEC: stb_tgt fn = Some fsp_tgt)
      (PRE: forall (x_tgt: fsp_tgt.(meta)), ∃ x_src FR,
          (<<NPURE: fsp_src.(measure) x_src = ord_top>>)
          /\
          (<<PRE: current_iProp fmr (Own OwnT ** ((fsp_tgt.(precond) (Some mn) x_tgt arg_tgt arg_tgt) ==∗
                                               (FR ** inv_with w0 st_src0 st_tgt0 **
                                                   fsp_src.(precond) (Some mn) x_src arg_src arg_tgt)))>>)
          /\
          (<<POST: forall st_src1 st_tgt1 ret_src ret_tgt,
              exists J,
                (<<UPD: (FR ** inv_with w0 st_src1 st_tgt1 **
                                        fsp_src.(postcond) (Some mn) x_src ret_src ret_tgt)
                         ==∗ (fsp_tgt.(postcond) (Some mn) x_tgt ret_tgt ret_tgt ** J)>>) /\
                  (<<SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** J)),
                      hsim _ _ OwnT Q fmr1 None true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt)>>)>>)
      )
      (MEASURE: o_src = ord_top)
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src)
            (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt)
  | hsim_apc_start
      fuel1
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim OwnT Q fmr (fuel1) true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src, trigger (hAPC) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_apc_step
      fsp_src fsp_tgt w0 arg_src
      fn arg_tgt
      st_src0 st_tgt0 itr_src ktr_tgt
      fuel0 fuel1 f_src f_tgt
      (SPEC: stb_src fn = Some fsp_src)
      (SPEC: stb_tgt fn = Some fsp_tgt)
      (FUEL: Ord.lt fuel1 fuel0)
      (PRE: forall (x_tgt: fsp_tgt.(meta)), ∃ x_src FR,
          (<<MEASURE: ord_lt (fsp_src.(measure) x_src) o_src>>)
          /\
          (<<PURE: is_pure (fsp_src.(measure) x_src)>>)
          /\
          (<<PRE: current_iProp fmr (Own OwnT ** ((fsp_tgt.(precond) (Some mn) x_tgt arg_tgt arg_tgt) ==∗
                                               (FR ** inv_with w0 st_src0 st_tgt0 **
                                                   fsp_src.(precond) (Some mn) x_src arg_src arg_tgt)))>>)
          /\
          (<<POST: forall st_src1 st_tgt1 ret_src ret_tgt,
              exists J,
                (<<UPD: (FR ** inv_with w0 st_src1 st_tgt1 **
                                        fsp_src.(postcond) (Some mn) x_src ret_src ret_tgt)
                         ==∗ (fsp_tgt.(postcond) (Some mn) x_tgt ret_tgt ret_tgt ** J)>>) /\
                  (<<SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** J)),
                      hsim _ _ OwnT Q fmr1 (Some fuel1) true true (st_src1, itr_src) (st_tgt1, ktr_tgt ret_tgt)>>)>>)
      )
    :
      _hsim hsim OwnT Q fmr (Some fuel0) f_src f_tgt (st_src0, itr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt)
  | hsim_apc_both
      st_src st_tgt ktr_src ktr_tgt
      fuel f_src f_tgt w0 FR
      (PRE: current_iProp fmr (Own OwnT ** inv_with w0 st_src st_tgt ** FR))
      (SIM: forall st_src1 st_tgt1 fmr1 OwnT
                   (ACC: current_iProp fmr1 (Own OwnT ** inv_with w0 st_src1 st_tgt1 ** FR)),
        hsim _ _ OwnT Q fmr1 None true true (st_src1, ktr_src tt) (st_tgt1, ktr_tgt tt))
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src, trigger (hAPC) >>= ktr_src) (st_tgt, trigger hAPC >>= ktr_tgt)
  | hsim_syscall
      fn arg rvs
      st_src st_tgt ktr_src ktr_tgt
      fuel f_src f_tgt
      (POST: forall ret,
          hsim _ _ OwnT Q fmr None true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret))
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt)
  | hsim_tau_src
      st_src st_tgt itr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim OwnT Q fmr None true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt)
  | hsim_tau_tgt
      st_src st_tgt itr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt)
  | hsim_choose_src
      X
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: exists x, _hsim hsim OwnT Q fmr None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_choose_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: forall x, _hsim hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt)
  | hsim_take_src
      X
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: forall x, _hsim hsim OwnT Q fmr None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_take_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: exists x, _hsim hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt)
  | hsim_pput_src
      st_src1
      st_src0 st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim OwnT Q fmr None true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_pput_tgt
      st_tgt1
      st_src st_tgt0 itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt)
  | hsim_pget_src
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim OwnT Q fmr None true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_pget_tgt
      st_src st_tgt itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: _hsim hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
    :
      _hsim hsim OwnT Q fmr fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt)
  | hsim_progress
      st_src st_tgt itr_src itr_tgt
      fuel
      (SIM: hsim _ _ OwnT Q fmr fuel false false (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim OwnT Q fmr fuel true true (st_src, itr_src) (st_tgt, itr_tgt)
  .

  Lemma _hsim_ind2
        (hsim: forall R_src R_tgt
                      (OwnT: Σ)
                      (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                      (fmr: Σ),
            option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop)
        R_src R_tgt OwnT Q fmr
        (P: option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop)
        (RET: forall
            v_src v_tgt
            st_src st_tgt
            fuel f_src f_tgt
            (RET: current_iProp fmr (Own OwnT ** Q st_src st_tgt v_src v_tgt)),
            P fuel f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt)))
        (CALL: forall
            fsp_src fsp_tgt w0
            fn arg_src arg_tgt
            st_src0 st_tgt0 ktr_src ktr_tgt
            fuel f_src f_tgt
            (SPEC: stb_src fn = Some fsp_src)
            (SPEC: stb_tgt fn = Some fsp_tgt)
            (PRE: forall (x_tgt: fsp_tgt.(meta)), exists x_src FR,
          (<<NPURE: fsp_src.(measure) x_src = ord_top>>)
          /\
          (<<PRE: current_iProp fmr (Own OwnT ** ((fsp_tgt.(precond) (Some mn) x_tgt arg_tgt arg_tgt) ==∗
                                               (FR ** inv_with w0 st_src0 st_tgt0 **
                                                   fsp_src.(precond) (Some mn) x_src arg_src arg_tgt)))>>)
          /\
          (<<POST: forall st_src1 st_tgt1 ret_src ret_tgt,
              exists J,
                (<<UPD: (FR ** inv_with w0 st_src1 st_tgt1 **
                                        fsp_src.(postcond) (Some mn) x_src ret_src ret_tgt)
                            ==∗ (fsp_tgt.(postcond) (Some mn) x_tgt ret_tgt ret_tgt ** J)>>) /\
                  (<<SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** J)),
                      hsim _ _ OwnT Q fmr1 None true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt)>>)>>)
            )
            (MEASURE: o_src = ord_top),
            P fuel f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt))
        (APCSTART: forall
            fuel1
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: _hsim hsim OwnT Q fmr (fuel1) true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
            (IH: P (fuel1) true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src, trigger (hAPC) >>= ktr_src) (st_tgt, itr_tgt))
        (APCSTEP: forall
            fsp_src fsp_tgt w0 arg_src
            fn arg_tgt
            st_src0 st_tgt0 itr_src ktr_tgt
            fuel1 fuel0 f_src f_tgt
            (SPEC: stb_src fn = Some fsp_src)
            (SPEC: stb_tgt fn = Some fsp_tgt)
            (FUEL: Ord.lt fuel1 fuel0)
            (PRE: forall (x_tgt: fsp_tgt.(meta)), ∃ x_src FR,
          (<<MEASURE: ord_lt (fsp_src.(measure) x_src) o_src>>)
          /\
          (<<PURE: is_pure (fsp_src.(measure) x_src)>>)
          /\
          (<<PRE: current_iProp fmr (Own OwnT ** ((fsp_tgt.(precond) (Some mn) x_tgt arg_tgt arg_tgt) ==∗
                                               (FR ** inv_with w0 st_src0 st_tgt0 **
                                                   fsp_src.(precond) (Some mn) x_src arg_src arg_tgt)))>>)
          /\
          (<<POST: forall st_src1 st_tgt1 ret_src ret_tgt,
              exists J,
                (<<UPD: (FR ** inv_with w0 st_src1 st_tgt1 **
                                        fsp_src.(postcond) (Some mn) x_src ret_src ret_tgt)
                            ==∗ (fsp_tgt.(postcond) (Some mn) x_tgt ret_tgt ret_tgt ** J)>>) /\
                  (<<SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** J)),
                      hsim _ _ OwnT Q fmr1 (Some fuel1) true true (st_src1, itr_src) (st_tgt1, ktr_tgt ret_tgt)>>)>>)
            ),
            P (Some fuel0) f_src f_tgt (st_src0, itr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt))
        (APCBOTH: forall
            st_src st_tgt ktr_src ktr_tgt
            fuel f_src f_tgt w0 FR
            (PRE: current_iProp fmr (Own OwnT ** (inv_with w0 st_src st_tgt) ** FR))
            (SIM: forall st_src1 st_tgt1 fmr1 OwnT
                         (ACC: current_iProp fmr1 (Own OwnT ** inv_with w0 st_src1 st_tgt1 ** FR)),
                hsim _ _ OwnT Q fmr1 None true true (st_src1, ktr_src tt) (st_tgt1, ktr_tgt tt))
            (* (IH: P None true true (st_src, ktr_src tt) (st_tgt, ktr_tgt tt)) *)
          ,
            P fuel f_src f_tgt (st_src, trigger (hAPC) >>= ktr_src) (st_tgt, trigger hAPC >>= ktr_tgt))
        (SYSCALL: forall
            fn arg rvs
            st_src st_tgt ktr_src ktr_tgt
            fuel f_src f_tgt
            (POST: forall ret,
                hsim _ _ OwnT Q fmr None true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret)),
            P fuel f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt))
        (TAUSRC: forall
            st_src st_tgt itr_src itr_tgt
            fuel f_src f_tgt
            (SIM: _hsim hsim OwnT Q fmr None true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P None true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
          ,
            P fuel f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt))
        (TAUTGT: forall
            st_src st_tgt itr_src itr_tgt
            fuel f_src f_tgt
            (SIM: _hsim hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P fuel f_src true (st_src, itr_src) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt))
        (CHOOSESRC: forall
            X
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: exists x, (<<SIM: _hsim hsim OwnT Q fmr None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P fuel f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt))
        (CHOOSETGT: forall
            X
            st_src st_tgt itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: forall x, (<<SIM: _hsim hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt))
        (TAKESRC: forall
            X
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: forall x, (<<SIM: _hsim hsim OwnT Q fmr None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P fuel f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt))
        (TAKETGT: forall
            X
            st_src st_tgt itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: exists x, (<<SIM: _hsim hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt))
        (PPUTSRC: forall
            st_src1
            st_src0 st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: _hsim hsim OwnT Q fmr None true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
            (IH: P None true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt))
        (PPUTTGT: forall
            st_tgt1
            st_src st_tgt0 itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: _hsim hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
            (IH: P fuel f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt))
        (PGETSRC: forall
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: _hsim hsim OwnT Q fmr None true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
            (IH: P None true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt))
        (PGETTGT: forall
            st_src st_tgt itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: _hsim hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
            (IH: P fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt))
        (PROGRESS: forall
            st_src st_tgt itr_src itr_tgt
            fuel
            (SIM: hsim _ _ OwnT Q fmr fuel false false (st_src, itr_src) (st_tgt, itr_tgt)),
            P fuel true true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      forall fuel f_src f_tgt st_src st_tgt
             (SIM: @_hsim hsim _ _ OwnT Q fmr fuel f_src f_tgt st_src st_tgt),
        P fuel f_src f_tgt st_src st_tgt.
  Proof.
    fix IH 6. i. inv SIM.
    { eapply RET; eauto. }
    { eapply CALL; eauto. }
    { eapply APCSTART; eauto. }
    { des. eapply APCSTEP; eauto. }
    { eapply APCBOTH; eauto. }
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

  Definition hsim := paco10 _hsim bot10.
  Arguments hsim [_ _] _ _ _ _ _ _ _.

  Lemma _hsim_mon: monotone10 _hsim.
  Proof.
    ii. induction IN using _hsim_ind2.
    { econs 1; eauto. }
    { econs 2; eauto. i. specialize (PRE x_tgt). des. esplits; et. i. exploit POST; et. i; des. esplits; et.
    }
    { econs 3; eauto. }
    { des. econs 4; eauto. i. spc PRE. des. esplits; eauto. i. exploit POST; et. i; des. esplits; et. }
    { econs 5; eauto. }
    { econs 6; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. des. esplits; eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 11; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 12; eauto. des. esplits; eauto. }
    { econs 13; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. }
    { econs 17; eauto. }
  Qed.
  Hint Resolve _hsim_mon: paco.

  Lemma hsim_ind
        R_src R_tgt Q OwnT fmr
        (P: option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop)
        (RET: forall
            v_src v_tgt
            st_src st_tgt
            fuel f_src f_tgt
            (RET: current_iProp fmr (Own OwnT ** Q st_src st_tgt v_src v_tgt)),
            P fuel f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt)))
        (CALL: forall
            fsp_src fsp_tgt w0
            fn arg_src arg_tgt
            st_src0 st_tgt0 ktr_src ktr_tgt
            fuel f_src f_tgt
            (SPEC: stb_src fn = Some fsp_src)
            (SPEC: stb_tgt fn = Some fsp_tgt)
            (PRE: forall (x_tgt: fsp_tgt.(meta)), exists x_src FR,
          (<<NPURE: fsp_src.(measure) x_src = ord_top>>)
          /\
          (<<PRE: current_iProp fmr (Own OwnT ** ((fsp_tgt.(precond) (Some mn) x_tgt arg_tgt arg_tgt) ==∗
                                               (FR ** inv_with w0 st_src0 st_tgt0 **
                                                   fsp_src.(precond) (Some mn) x_src arg_src arg_tgt)))>>)
          /\
          (<<POST: forall st_src1 st_tgt1 ret_src ret_tgt,
              exists J,
                (<<UPD: (FR ** inv_with w0 st_src1 st_tgt1 **
                                        fsp_src.(postcond) (Some mn) x_src ret_src ret_tgt)
                            ==∗ (fsp_tgt.(postcond) (Some mn) x_tgt ret_tgt ret_tgt ** J)>>) /\
                  (<<SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** J)),
                      hsim OwnT Q fmr1 None true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt)>>)>>)
            )
            (MEASURE: o_src = ord_top),
            P fuel f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src)
                  (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt))
        (APCSTART: forall
            fuel1
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: hsim OwnT Q fmr (fuel1) true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
            (IH: P (fuel1) true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src, trigger (hAPC) >>= ktr_src) (st_tgt, itr_tgt))
        (APCSTEP: forall
            fsp_src fsp_tgt w0 arg_src
            fn arg_tgt
            st_src0 st_tgt0 itr_src ktr_tgt
            fuel1 fuel0 f_src f_tgt
            (SPEC: stb_src fn = Some fsp_src)
            (SPEC: stb_tgt fn = Some fsp_tgt)
            (FUEL: Ord.lt fuel1 fuel0)
            (PRE: forall (x_tgt: fsp_tgt.(meta)), ∃ x_src FR,
          (<<MEASURE: ord_lt (fsp_src.(measure) x_src) o_src>>)
          /\
          (<<PURE: is_pure (fsp_src.(measure) x_src)>>)
          /\
          (<<PRE: current_iProp fmr (Own OwnT ** ((fsp_tgt.(precond) (Some mn) x_tgt arg_tgt arg_tgt) ==∗
                                               (FR ** inv_with w0 st_src0 st_tgt0 **
                                                   fsp_src.(precond) (Some mn) x_src arg_src arg_tgt)))>>)
          /\
          (<<POST: forall st_src1 st_tgt1 ret_src ret_tgt,
              exists J,
                (<<UPD: (FR ** inv_with w0 st_src1 st_tgt1 **
                                        fsp_src.(postcond) (Some mn) x_src ret_src ret_tgt)
                            ==∗ (fsp_tgt.(postcond) (Some mn) x_tgt ret_tgt ret_tgt ** J)>>) /\
                  (<<SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** J)),
                      hsim OwnT Q fmr1 (Some fuel1) true true (st_src1, itr_src) (st_tgt1, ktr_tgt ret_tgt)>>)>>)
            ),
            P (Some fuel0) f_src f_tgt (st_src0, itr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt))
        (APCBOTH: forall
            st_src st_tgt ktr_src ktr_tgt
            fuel f_src f_tgt w0 FR
            (PRE: current_iProp fmr (Own OwnT ** (inv_with w0 st_src st_tgt) ** FR))
            (SIM: forall st_src1 st_tgt1 fmr1 OwnT
                         (ACC: current_iProp fmr1 (Own OwnT ** inv_with w0 st_src1 st_tgt1 ** FR)),
                hsim OwnT Q fmr1 None true true (st_src1, ktr_src tt) (st_tgt1, ktr_tgt tt))
            (* (IH: P None true true (st_src, ktr_src tt) (st_tgt, ktr_tgt tt)) *)
          ,
            P fuel f_src f_tgt (st_src, trigger (hAPC) >>= ktr_src) (st_tgt, trigger hAPC >>= ktr_tgt))
        (SYSCALL: forall
            fn arg rvs
            st_src st_tgt ktr_src ktr_tgt
            fuel f_src f_tgt
            (POST: forall ret,
                hsim OwnT Q fmr None true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret)),
            P fuel f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt))
        (TAUSRC: forall
            st_src st_tgt itr_src itr_tgt
            fuel f_src f_tgt
            (SIM: hsim OwnT Q fmr None true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P None true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
          ,
            P fuel f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt))
        (TAUTGT: forall
            st_src st_tgt itr_src itr_tgt
            fuel f_src f_tgt
            (SIM: hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P fuel f_src true (st_src, itr_src) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt))
        (CHOOSESRC: forall
            X
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: exists x, (<<SIM: hsim OwnT Q fmr None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P fuel f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt))
        (CHOOSETGT: forall
            X
            st_src st_tgt itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: forall x, (<<SIM: hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt))
        (TAKESRC: forall
            X
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: forall x, (<<SIM: hsim OwnT Q fmr None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P fuel f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt))
        (TAKETGT: forall
            X
            st_src st_tgt itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: exists x, (<<SIM: hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt))
        (PPUTSRC: forall
            st_src1
            st_src0 st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: hsim OwnT Q fmr None true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
            (IH: P None true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt))
        (PPUTTGT: forall
            st_tgt1
            st_src st_tgt0 itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
            (IH: P fuel f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt))
        (PGETSRC: forall
            st_src st_tgt ktr_src itr_tgt
            fuel f_src f_tgt
            (SIM: hsim OwnT Q fmr None true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
            (IH: P None true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt)),
            P fuel f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt))
        (PGETTGT: forall
            st_src st_tgt itr_src ktr_tgt
            fuel f_src f_tgt
            (SIM: hsim OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
            (IH: P fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt)),
            P fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt))
        (PROGRESS: forall
            st_src st_tgt itr_src itr_tgt
            fuel
            (SIM: hsim OwnT Q fmr fuel false false (st_src, itr_src) (st_tgt, itr_tgt)),
            P fuel true true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      forall fuel f_src f_tgt st_src st_tgt
             (SIM: hsim OwnT Q fmr fuel f_src f_tgt st_src st_tgt),
        P fuel f_src f_tgt st_src st_tgt.
  Proof.
    i. punfold SIM. induction SIM using _hsim_ind2.
    { eapply RET; eauto. }
    { eapply CALL; eauto. i. hexploit PRE; eauto. i. des. esplits; et. i. exploit POST; et. i; des.
      esplits; et. i. exploit SIM; et. i. des. pclearbot. eauto. }
    { eapply APCSTART; eauto. pfold. eauto. }
    { des. eapply APCSTEP; eauto. i. spc PRE. des. esplits; eauto. i. hexploit POST; eauto. i. des.
      esplits; eauto. i. exploit SIM; eauto. i; des. pclearbot. eauto. }
    { eapply APCBOTH; eauto. i. exploit SIM; eauto. i; des. pclearbot. eauto. }
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

  Definition mylift (stb: string -> option fspec) (o: ord) (fuel: option Ord.t) (mn_caller: option mname) X (x: X)
             fr
             (Q: option mname -> X -> Any.t -> Any.t -> iProp) (itr_src: itree hEs Any.t): itree Es Any.t :=
    match fuel with
    | None =>
      (interp_hCallE_tgt mn stb o (interp_hEs_tgt itr_src) fr) >>= (HoareFunRet Q mn_caller x)
    | Some fuel =>
      r0 <- (interp_hCallE_tgt mn stb o (_APC fuel) fr);;
      r1 <- (interp_hCallE_tgt mn stb o (tau;; Ret (snd r0)) (fst r0));;
      r2 <- (interp_hCallE_tgt mn stb o (interp_hEs_tgt itr_src) (fst r1));;
      (HoareFunRet Q mn_caller x r2)
    end.

  Lemma current_iPropL_convert fmr P
        (CUR: current_iProp fmr P)
    :
      current_iPropL fmr [("H", P)].
  Proof.
    unfold current_iPropL. ss. unfold from_iPropL.
    eapply current_iProp_entail; eauto.
  Qed.

  Lemma hsim_adequacy_aux `{PreOrder _ le}:
    forall
      f_src f_tgt st_src st_tgt (itr_src: itree (hAPCE +' Es) Any.t) itr_tgt (mr_src mr_tgt: Σ) fr_src fr_tgt
      X_src (x_src: X_src) X_tgt (x_tgt: X_tgt) Q_src Q_tgt mn_caller fuel w0
      (SIMPL: forall mn x vret vret_tgt, ⊢ Q_tgt mn x vret vret_tgt -* ⌜vret = vret_tgt⌝)
      (SIM: hsim (fr_tgt ⋅ mr_tgt)
                 (fun st_src st_tgt ret_src ret_tgt =>
                    ((Q_tgt mn_caller x_tgt ret_tgt ret_tgt) ==∗
                     ((inv_with w0 st_src st_tgt) ** (Q_src mn_caller x_src ret_src ret_tgt)))%I)
                 (fr_src ⋅ (mr_tgt ⋅ mr_src))
                 fuel f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt)),
      paco8 (_sim_itree (mk_wf I) le) bot8 Any.t Any.t (lift_rel (mk_wf I) le w0 (@eq Any.t))
            f_src f_tgt w0
            (Any.pair st_src (mr_tgt ⋅ mr_src)↑,
             mylift stb_src o_src fuel mn_caller x_src fr_src Q_src itr_src)
            (Any.pair st_tgt mr_tgt↑,
             mylift stb_tgt o_tgt None mn_caller x_tgt fr_tgt Q_tgt itr_tgt).
  Proof.
    ginit. gcofix CIH. i.
    remember (st_src, itr_src). remember (st_tgt, itr_tgt).
    revert st_src st_tgt itr_src itr_tgt Heqp Heqp0 CIH.
    induction SIM using hsim_ind; i; clarify.
    { eapply current_iPropL_convert in RET. mDesAll. destruct fuel; steps.
      { astop. steps. unfold inv_with in RET. mDesAll. eapply hret_clo2; eauto.
        { mAssert (_ ∗ _ ∗ _)%I with "*".
          { iSplitL "A"; try iAssumption. iDestruct "H" as "[A B]". iSplitL "A"; try iAssumption. }
          eapply current_iPropL_entail_all in RET; et.
          iIntros "[[A [B C]] _]". iFrame. eauto.
        }
        { ii. rr. esplits; et. }
      }
      { unfold inv_with in RET. mDesAll. eapply hret_clo2; eauto.
        { mAssert (_ ∗ _ ∗ _)%I with "*".
          { iSplitL "A"; try iAssumption. iDestruct "H" as "[A B]". iSplitL "A"; try iAssumption. }
          eapply current_iPropL_entail_all in RET; et.
          iIntros "[[A [B C]] _]". iFrame. eauto.
        }
        { ii. rr. esplits; et. }
      }
    }
    { destruct fuel; steps.
      { astop. steps. rewrite SPEC. steps. eapply hcall_clo2; eauto.
        i. des. specialize (PRE x_tgt0). des. esplits; eauto; ss.
        { rewrite NPURE. rewrite MEASURE in *. splits; ss. }
        { eapply current_iPropL_convert in PRE.
          replace (fr_src ⋅ mr_src ⋅ mr_tgt) with (fr_src ⋅ (mr_tgt ⋅ mr_src)) by r_solve. eauto.
          eapply current_iProp_entail in PRE; eauto. iIntros "[[[A B] C] _]". iSplitL; eauto. iFrame.
        }
        { i. ss. exploit POST; eauto. i; des. esplits; eauto.
          i. steps. gbase. hexploit CIH; eauto.
          { eapply SIM; eauto. eapply current_iProp_entail; [eauto|].
            iIntros "[A [B [C _]]]". iSplitL "B C"; eauto. iSplitL "B"; eauto. }
          i. ss.
        }
      }
      { rewrite SPEC. steps. eapply hcall_clo2; eauto.
        i. des. specialize (PRE x_tgt0). des. esplits; eauto; ss.
        { rewrite NPURE. rewrite MEASURE in *. splits; ss. }
        { eapply current_iPropL_convert in PRE.
          replace (fr_src ⋅ mr_src ⋅ mr_tgt) with (fr_src ⋅ (mr_tgt ⋅ mr_src)) by r_solve. eauto.
          eapply current_iProp_entail in PRE; eauto. iIntros "[[[A B] C] _]". iSplitL; eauto. iFrame. }
        { i. ss. exploit POST; eauto. i; des. esplits; eauto.
          i. steps. gbase. hexploit CIH; eauto.
          { eapply SIM; eauto. eapply current_iProp_entail; [eauto|].
            iIntros "[A [B [C _]]]". iSplitL "B C"; eauto. iSplitL "B"; eauto. }
          i. ss.
        }
      }
    }
    { destruct fuel; steps.
      { astop. steps. exploit IHSIM; eauto. i. destruct fuel1; ss.
        { astart t0.
          match goal with
          | |- ?P0 (_, ?itr1) _ =>
            match (type of x0) with
            | ?P1 (_, ?itr0) _ =>
              replace itr1 with itr0
            end
          end; auto.
          grind. destruct x, x1. destruct u, u0. grind.
        }
        { astop. steps. }
      }
      { exploit IHSIM; eauto. i. destruct fuel1; ss.
        { astart t.
          match goal with
          | |- ?P0 (_, ?itr1) _ =>
            match (type of x0) with
            | ?P1 (_, ?itr0) _ =>
              replace itr1 with itr0
            end
          end; auto.
          grind. destruct x, x1. destruct u, u0. grind.
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
      eapply hcall_clo2; eauto. i. des. spc PRE. des. esplits; eauto; ss.
      { replace (fr_src ⋅ mr_src ⋅ mr_tgt) with (fr_src ⋅ (mr_tgt ⋅ mr_src)) by r_solve.
        eapply current_iProp_entail; eauto.
        iIntros "[[A B] C]". iFrame.
      }
      i. exploit POST; eauto. i; des. esplits; eauto. i. steps. gbase. hexploit CIH; eauto.
      { eapply SIM; eauto. eapply current_iProp_entail; [eauto|].
        iIntros "[A [B [C _]]]". iSplitL "B C"; eauto. iSplitL "B"; eauto. }
      i; ss.
    }
    { destruct fuel.
      - ss. steps. rewrite unfold_APC. steps. force_l. exists true. steps. eapply hAPC2; ss.
        + eapply current_iProp_entail; eauto.
          iIntros "[[[A B] C] D]". iDestruct "C" as (w2) "[C %]". iFrame. iSplitL "C".
          { iSplits; eauto. }
          instantiate (1:=FR). iFrame.
        + i. steps.
          gbase.
          hexploit CIH; cycle 1.
          { eapply SIM. eapply current_iProp_entail; try apply ACC.
            iIntros "[A [B [C [D _]]]]". iFrame. iSplitL "B"; iFrame. }
          2:{ eauto. }
          i; ss.
      - ss. steps. eapply hAPC2; ss.
        + eapply current_iProp_entail; eauto.
          iIntros "[[[A B] C] D]". iDestruct "C" as (w2) "[C %]". iFrame. iSplitL "C".
          { iSplits; eauto. }
          instantiate (1:=FR). iFrame.
        + i. steps.
          gbase.
          hexploit CIH; cycle 1.
          { eapply SIM. eapply current_iProp_entail; try apply ACC.
            iIntros "[A [B [C [D _]]]]". iFrame. iSplitL "B"; iFrame. }
          2:{ eauto. }
          i; ss.
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
    { des. exploit IH; eauto. i. force_r. eexists. steps. eauto. }
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

  Lemma hsim_adequacy `{PreOrder _ le}:
    forall
      f_src f_tgt st_src st_tgt (itr_src: itree (hAPCE +' Es) Any.t) itr_tgt
      mr_src mr_tgt fr_src fr_tgt X_src (x_src: X_src) X_tgt (x_tgt: X_tgt) Q_src Q_tgt mn_caller w0
      (SIMPL: forall mn x vret vret_tgt, ⊢ Q_tgt mn x vret vret_tgt -* ⌜vret = vret_tgt⌝)
      (SIM: hsim (fr_tgt ⋅ mr_tgt)
                 (fun st_src st_tgt ret_src ret_tgt =>
                    ((Q_tgt mn_caller x_tgt ret_tgt ret_tgt) ==∗
                     ((inv_with w0 st_src st_tgt) ** (Q_src mn_caller x_src ret_src ret_tgt)))%I)
                 (fr_src ⋅ (mr_tgt ⋅ mr_src))
                 None f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt)),
      paco8 (_sim_itree (mk_wf I) le) bot8 Any.t Any.t (lift_rel (mk_wf I) le w0 (@eq Any.t))
            f_src f_tgt w0
            (Any.pair st_src (mr_tgt ⋅ mr_src)↑,
             (interp_hCallE_tgt mn stb_src o_src (interp_hEs_tgt itr_src) fr_src) >>=
             (HoareFunRet Q_src mn_caller x_src))
            (Any.pair st_tgt mr_tgt↑,
             (interp_hCallE_tgt mn stb_tgt o_tgt (interp_hEs_tgt itr_tgt) fr_tgt) >>=
             (HoareFunRet Q_tgt mn_caller x_tgt)).
  Proof.
    i. hexploit hsim_adequacy_aux; eauto.
  Qed.

  Lemma hsim_progress_flag R_src R_tgt r g Q fmr fuel st_src st_tgt OwnT
        (SIM: gpaco10 _hsim (cpn10 _hsim) g g R_src R_tgt OwnT Q fmr fuel false false st_src st_tgt)
    :
      gpaco10 _hsim (cpn10 _hsim) r g _ _ OwnT Q fmr fuel true true st_src st_tgt.
  Proof.
    destruct st_src, st_tgt. gstep. eapply hsim_progress; eauto.
  Qed.

  Lemma _hsim_flag_mon
        r
        R_src R_tgt OwnT Q fmr
        fuel f_src0 f_tgt0 f_src1 f_tgt1 st_src st_tgt
        (SIM: @_hsim r R_src R_tgt OwnT Q fmr fuel f_src0 f_tgt0 st_src st_tgt)
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      @_hsim r R_src R_tgt OwnT Q fmr fuel f_src1 f_tgt1 st_src st_tgt.
  Proof.
    revert f_src1 f_tgt1 SRC TGT.
    induction SIM using _hsim_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3. eapply IHSIM; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. }
    { econs 6. eauto. }
    { econs 7. eapply IHSIM; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. des. esplits. eapply IH; eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 11; eauto. i. hexploit SIM; eauto. i. des. eapply IH; eauto. }
    { econs 12; eauto. des. esplits; eauto. }
    { econs 13. eapply IHSIM; auto. }
    { econs 14. eapply IHSIM; auto. }
    { econs 15. eapply IHSIM; auto. }
    { econs 16. eapply IHSIM; auto. }
    { exploit SRC; auto. exploit TGT; auto. i. clarify. econs 17; eauto. }
  Qed.

  Variant fuelC (r: forall R_src R_tgt
                           (OwnT: Σ)
                           (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                           (fmr: Σ),
                    option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop)
          {R_src R_tgt}
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop :=
  | fuelC_intro
      f_src f_tgt fuel0 fuel1
      st_src st_tgt
      (SIM: r _ _ OwnT Q fmr fuel0 f_src f_tgt st_src st_tgt)
      (ORD: option_Ord_le fuel0 fuel1)
    :
      fuelC r OwnT Q fmr fuel1 f_src f_tgt st_src st_tgt
  .

  Lemma fuelC_mon:
    monotone10 fuelC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve fuelC_mon: paco.

  Lemma fuelC_spec: fuelC <11= gupaco10 (_hsim) (cpn10 _hsim).
  Proof.
    eapply wrespect10_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    revert x5 ORD. induction SIM using _hsim_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. i. hexploit PRE; eauto. i; des. esplits; eauto.
      i. exploit POST; eauto. i; des. esplits; eauto. i. exploit SIM; eauto. eapply rclo10_base. }
    { econs 3; eauto. eapply _hsim_mon; eauto. i. eapply rclo10_base. auto. }
    { destruct x5; ss. econs 4; eauto. des. esplits; eauto.
      { eapply Ord.lt_le_lt; eauto. }
      { i. hexploit PRE; eauto. i; des. esplits; eauto. i. exploit POST; eauto. i; des. esplits; eauto.
        i. eapply rclo10_base. eauto. }
    }
    { econs 5; eauto. i. eapply rclo10_base. auto. }
    { econs 6; eauto. i. eapply rclo10_base. auto. }
    { econs 7; eauto. eapply _hsim_mon; eauto. i. apply rclo10_base. auto. }
    { econs 8; eauto. }
    { econs 9; eauto. des. esplits; eauto. eapply _hsim_mon; eauto. i. apply rclo10_base. auto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 11; eauto. i. hexploit SIM; eauto. i. des. eapply _hsim_mon; eauto. i. eapply rclo10_base; auto. }
    { econs 12; eauto. des. esplits; eauto. }
    { econs 13; eauto. eapply _hsim_mon; eauto. i. eapply rclo10_base; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. eapply _hsim_mon; eauto. i. eapply rclo10_base; eauto. }
    { econs 16; eauto. }
    { econs 17; eauto. eapply rclo10_clo_base. econs; eauto. }
  Qed.

  Variant hflagC (r: forall R_src R_tgt
                            (OwnT: Σ)
                            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                            (fmr: Σ),
                     option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop)
          {R_src R_tgt}
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop :=
  | hflagC_intro
      f_src0 f_src1 f_tgt0 f_tgt1 fuel0 fuel1
      st_src st_tgt
      (SIM: r _ _ OwnT Q fmr fuel0 f_src0 f_tgt0 st_src st_tgt)
      (SRC: f_src0 = true -> f_src1 = true)
      (TGT: f_tgt0 = true -> f_tgt1 = true)
      (ORD: option_Ord_le fuel0 fuel1)
    :
      hflagC r OwnT Q fmr fuel1 f_src1 f_tgt1 st_src st_tgt
  .

  Lemma hflagC_mon:
    monotone10 hflagC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hflagC_mon: paco.

  Structure grespectful clo : Prop :=
    grespect_intro {
        grespect_mon: monotone10 clo;
        grespect_respect :
          forall l r
                 (LE: l <10= r)
                 (GF: l <10= @_hsim r),
            clo l <10= gpaco10 _hsim (cpn10 _hsim) bot10 (rclo10 (clo \11/ gupaco10 _hsim (cpn10 _hsim)) r);
      }.

  Lemma grespect_uclo clo
        (RESPECT: grespectful clo)
    :
      clo <11= gupaco10 (_hsim) (cpn10 _hsim).
  Proof.
    eapply grespect10_uclo; eauto with paco.
    econs.
    { eapply RESPECT. }
    i. hexploit grespect_respect.
    { eauto. }
    { eapply LE. }
    { eapply GF. }
    { eauto. }
    i. inv H. eapply rclo10_mon.
    { eauto. }
    i. ss. des; ss. eapply _paco10_unfold in PR0.
    2:{ ii. eapply _hsim_mon; [eapply PR1|]. i. eapply rclo10_mon; eauto. }
    ss. eapply _hsim_mon.
    { eapply PR0; eauto. }
    i. eapply rclo10_clo. right. econs.
    eapply rclo10_mon; eauto. i. inv PR2.
    { left. eapply paco10_mon; eauto. i. ss. des; ss.
      left. auto. }
    { des; ss. right. auto. }
  Qed.

  Lemma hflagC_spec: hflagC <11= gupaco10 (_hsim) (cpn10 _hsim).
  Proof.
    eapply grespect_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    guclo fuelC_spec. econs; [|eauto]. gstep.
    eapply _hsim_flag_mon; eauto.
    eapply _hsim_mon; eauto. i. gbase. eapply rclo10_base. auto.
  Qed.

  Variant hsimC
          (r g: forall R_src R_tgt
                       (OwnT: Σ)
                       (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                       (fmr: Σ),
              option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop)
          {R_src R_tgt}
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop :=
  | hsimC_ret
      v_src v_tgt
      st_src st_tgt
      fuel f_src f_tgt
      (RET: current_iProp fmr (Own OwnT ** Q st_src st_tgt v_src v_tgt))
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt))
  | hsimC_call
      fsp_src fsp_tgt (x_src: fsp_src.(meta)) w0 FR
      fn arg_src arg_tgt
      st_src0 st_tgt0 ktr_src ktr_tgt
      fuel f_src f_tgt
      (SPEC: stb_src fn = Some fsp_src)
      (SPEC: stb_tgt fn = Some fsp_tgt)
      (PRE: forall (x_tgt: fsp_tgt.(meta)),
          (<<PRE: current_iProp fmr (Own OwnT ** ((fsp_tgt.(precond) (Some mn) x_tgt arg_tgt arg_tgt) ==∗
                                               (FR ** inv_with w0 st_src0 st_tgt0 **
                                                   fsp_src.(precond) (Some mn) x_src arg_src arg_tgt)))>>)
          /\
          (<<POST: forall st_src1 st_tgt1 ret_src ret_tgt,
              exists J,
                (<<UPD: (FR ** inv_with w0 st_src1 st_tgt1 **
                                        fsp_src.(postcond) (Some mn) x_src ret_src ret_tgt)
                         ==∗ (fsp_tgt.(postcond) (Some mn) x_tgt ret_tgt ret_tgt ** J)>>) /\
                  (<<SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** J)),
                      g _ _ OwnT Q fmr1 None true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt)>>)>>)
      )
      (MEASURE: o_src = ord_top)
      (NPURE: fsp_src.(measure) x_src = ord_top)
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src)
            (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt)
  | hsimC_apc_start
      fuel1
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: r _ _ OwnT Q fmr (fuel1) true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src, trigger (hAPC) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_apc_step
      fsp_src (x_src: fsp_src.(meta)) fsp_tgt w0 FR arg_src
      fn arg_tgt
      st_src0 st_tgt0 itr_src ktr_tgt
      fuel0 fuel1 f_src f_tgt
      (SPEC: stb_src fn = Some fsp_src)
      (SPEC: stb_tgt fn = Some fsp_tgt)
      (MEASURE: ord_lt (fsp_src.(measure) x_src) o_src)
      (PURE: is_pure (fsp_src.(measure) x_src))
      (FUEL: Ord.lt fuel1 fuel0)
      (PRE: forall (x_tgt: fsp_tgt.(meta)),
          (<<PRE: current_iProp fmr (Own OwnT ** ((fsp_tgt.(precond) (Some mn) x_tgt arg_tgt arg_tgt) ==∗
                                               (FR ** inv_with w0 st_src0 st_tgt0 **
                                                   fsp_src.(precond) (Some mn) x_src arg_src arg_tgt)))>>)
          /\
          (<<POST: forall st_src1 st_tgt1 ret_src ret_tgt,
              exists J,
                (<<UPD: (FR ** inv_with w0 st_src1 st_tgt1 **
                                        fsp_src.(postcond) (Some mn) x_src ret_src ret_tgt)
                         ==∗ (fsp_tgt.(postcond) (Some mn) x_tgt ret_tgt ret_tgt ** J)>>) /\
                  (<<SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** J)),
                      g _ _ OwnT Q fmr1 (Some fuel1) true true (st_src1, itr_src) (st_tgt1, ktr_tgt ret_tgt)>>)>>)
      )
    :
      hsimC r g OwnT Q fmr (Some fuel0) f_src f_tgt (st_src0, itr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt)
  | hsimC_apc_both
      st_src st_tgt ktr_src ktr_tgt
      fuel f_src f_tgt w0 FR
      (PRE: current_iProp fmr (Own OwnT ** inv_with w0 st_src st_tgt ** FR))
      (SIM: forall st_src1 st_tgt1 fmr1 OwnT
                   (ACC: current_iProp fmr1 (Own OwnT ** inv_with w0 st_src1 st_tgt1 ** FR)),
        g _ _ OwnT Q fmr1 None true true (st_src1, ktr_src tt) (st_tgt1, ktr_tgt tt))
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src, trigger (hAPC) >>= ktr_src) (st_tgt, trigger hAPC >>= ktr_tgt)
  | hsimC_syscall
      fn arg rvs
      st_src st_tgt ktr_src ktr_tgt
      fuel f_src f_tgt
      (POST: forall ret,
          g _ _ OwnT Q fmr None true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret))
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt)
  | hsimC_tau_src
      st_src st_tgt itr_src itr_tgt
      fuel f_src f_tgt
      (SIM: r _ _ OwnT Q fmr None true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt)
  | hsimC_tau_tgt
      st_src st_tgt itr_src itr_tgt
      fuel f_src f_tgt
      (SIM: r _ _ OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt)
  | hsimC_choose_src
      X
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: exists x, r _ _ OwnT Q fmr None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_choose_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: forall x, r _ _ OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt)
  | hsimC_take_src
      X
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: forall x, r _ _ OwnT Q fmr None true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_take_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: exists x, r _ _ OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt)
  | hsimC_pput_src
      st_src1
      st_src0 st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: r _ _ OwnT Q fmr None true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_pput_tgt
      st_tgt1
      st_src st_tgt0 itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: r _ _ OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt)
  | hsimC_pget_src
      st_src st_tgt ktr_src itr_tgt
      fuel f_src f_tgt
      (SIM: r _ _ OwnT Q fmr None true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_pget_tgt
      st_src st_tgt itr_src ktr_tgt
      fuel f_src f_tgt
      (SIM: r _ _ OwnT Q fmr fuel f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
    :
      hsimC r g OwnT Q fmr fuel f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt)
  | hsimC_progress
      st_src st_tgt itr_src itr_tgt
      fuel
      (SIM: g _ _ OwnT Q fmr fuel false false (st_src, itr_src) (st_tgt, itr_tgt))
    :
      hsimC r g OwnT Q fmr fuel true true (st_src, itr_src) (st_tgt, itr_tgt)
  .

  Lemma hsim_indC_mon_gen r0 r1 g0 g1
        (LE0: r0 <10= r1)
        (LE1: g0 <10= g1)
    :
      @hsimC r0 g0 <10= @hsimC r1 g1.
  Proof.
    ii. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. i. hexploit PRE; eauto. i; des. esplits; eauto.
      i. exploit POST; eauto. i; des. esplits; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. i. hexploit PRE; eauto. i; des. esplits; eauto.
      i. exploit POST; eauto. i; des. esplits; eauto. }
    { econs 5; eauto. }
    { econs 6; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. des. esplits; eauto. }
    { econs 10; eauto. }
    { econs 11; eauto. }
    { econs 12; eauto. des. esplits; eauto. }
    { econs 13; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. }
    { econs 17; eauto. }
  Qed.

  Lemma hsim_indC_mon: monotone10 (fun r => @hsimC r r).
  Proof.
    ii. eapply hsim_indC_mon_gen; eauto.
  Qed.

  Lemma hsim_indC_spec:
    (fun r => @hsimC r r) <11= gupaco10 (_hsim) (cpn10 _hsim).
  Proof.
    eapply wrespect10_uclo; eauto with paco. econs.
    { eapply hsim_indC_mon. }
    i. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. i. hexploit PRE; eauto. i; des. esplits; eauto. i. hexploit POST; eauto. i; des.
      esplits; eauto. i. eapply rclo10_base. eauto. }
    { econs 3; eauto. eapply GF in SIM. eapply _hsim_mon; eauto. i. eapply rclo10_base. eauto. }
    { econs 4; eauto. i. hexploit PRE; eauto. i; des. esplits; eauto. i. hexploit POST; eauto. i; des.
      esplits; eauto. i. eapply rclo10_base. eauto. }
    { econs 5; eauto. i. eapply rclo10_base. eauto. }
    { econs 6; eauto. i. eapply rclo10_base. eauto. }
    { econs 7; eauto. eapply _hsim_mon; eauto. i. eapply rclo10_base. eauto. }
    { econs 8; eauto. eapply _hsim_mon; eauto. i. eapply rclo10_base. eauto. }
    { econs 9; eauto. des. esplits; eauto. eapply _hsim_mon; eauto. i. eapply rclo10_base. eauto. }
    { econs 10; eauto. i. eapply _hsim_mon; eauto. i. eapply rclo10_base. eauto. }
    { econs 11; eauto. i. eapply _hsim_mon; eauto. i. eapply rclo10_base. eauto. }
    { econs 12; eauto. des. esplits; eauto. eapply _hsim_mon; eauto. i. eapply rclo10_base. eauto. }
    { econs 13; eauto. eapply _hsim_mon; eauto. i. eapply rclo10_base. eauto. }
    { econs 14; eauto. eapply _hsim_mon; eauto. i. eapply rclo10_base. eauto. }
    { econs 15; eauto. eapply _hsim_mon; eauto. i. eapply rclo10_base. eauto. }
    { econs 16; eauto. eapply _hsim_mon; eauto. i. eapply rclo10_base. eauto. }
    { econs 17; eauto. eapply rclo10_base. eauto. }
  Qed.

  Lemma hsimC_spec:
    hsimC <12= gpaco10 (_hsim) (cpn10 _hsim).
  Proof.
    i. inv PR.
    { gstep. econs 1; eauto. }
    { gstep. econs 2; eauto. i. hexploit PRE; eauto. i; des. esplits; eauto.
      i. hexploit POST; eauto. i; des. esplits; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 3; eauto. gbase. eauto. }
    { gstep. econs 4; eauto. i. hexploit PRE; eauto. i; des. esplits; eauto.
      i. hexploit POST; eauto. i; des. esplits; eauto. gbase. eauto. }
    { gstep. econs 5; eauto. des. esplits; eauto. i. gbase. eauto. }
    { gstep. econs 6; eauto. i. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 7; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 8; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 9; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 10; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 11; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 12; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 13; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 14; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 15; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 16; eauto. gbase. eauto. }
    { gstep. econs 17; eauto. i. gbase. eauto. }
  Qed.

  Lemma hsimC_uclo r g:
    @hsimC (gpaco10 (_hsim) (cpn10 _hsim) r g) (gupaco10 (_hsim) (cpn10 _hsim) g) <10= gpaco10 (_hsim) (cpn10 _hsim) r g.
  Proof.
    i. eapply hsimC_spec in PR.  ss.
    eapply gpaco10_gpaco; [eauto with paco|].
    eapply gpaco10_mon; eauto. i. eapply gupaco10_mon; eauto.
  Qed.

  Variant hbindC (r: forall R_src R_tgt
                            (OwnT: Σ)
                            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                            (fmr: Σ),
                     option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop)
          {R_src R_tgt}
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop :=
  | hbindC_intro
      S_src S_tgt
      (P: Any.t -> Any.t -> S_src -> S_tgt -> iProp)
      fuel f_src f_tgt st_src0 st_tgt0 itr_src itr_tgt ktr_src ktr_tgt
      (SIM: @r S_src S_tgt OwnT P fmr fuel f_src f_tgt (st_src0, itr_src) (st_tgt0, itr_tgt))
      (SIMK: forall fmr1 st_src1 st_tgt1 ret_src ret_tgt OwnT
                    (POST: current_iProp fmr1 (Own OwnT ** P st_src1 st_tgt1 ret_src ret_tgt)),
          @r R_src R_tgt OwnT Q fmr1 None false false (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt))
    :
      hbindC r OwnT Q fmr fuel f_src f_tgt (st_src0, itr_src >>= ktr_src) (st_tgt0, itr_tgt >>= ktr_tgt)
  .

  Lemma hbindC_mon:
    monotone10 hbindC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hbindC_mon: paco.

  Lemma hbindC_spec: hbindC <11= gupaco10 (_hsim) (cpn10 _hsim).
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
      gstep. eapply _hsim_mon; eauto. i. gbase. eapply rclo10_base. auto.
    }
    { gstep. econs 2; eauto. i. hexploit PRE; eauto. i; des. esplits; eauto. i. hexploit POST; eauto. i; des.
      esplits; eauto. i.
      gbase. eapply rclo10_clo_base. left. econs; eauto.
    }
    { eapply hsimC_uclo. econs 3; eauto. }
    { gstep. econs 4; eauto. i. hexploit PRE; eauto. i; des. esplits; eauto. i. hexploit POST; eauto. i; des.
      esplits; eauto. i.
      gbase. eapply rclo10_clo_base. left. econs; eauto.
    }
    { des. gstep. econs 5; eauto. esplits; eauto. i.
      hexploit SIM; eauto. i. gbase. eapply rclo10_clo_base. left. econs; eauto.
    }
    { gstep. econs 6; eauto. i. gbase. eapply rclo10_clo_base. left. econs; eauto. }
    { eapply hsimC_uclo. econs 7; eauto. }
    { eapply hsimC_uclo. econs 8; eauto. }
    { des. eapply hsimC_uclo. econs 9; eauto. }
    { eapply hsimC_uclo. econs 10; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { eapply hsimC_uclo. econs 11; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { des. eapply hsimC_uclo. econs 12; eauto. }
    { eapply hsimC_uclo. econs 13; eauto. }
    { eapply hsimC_uclo. econs 14; eauto. }
    { eapply hsimC_uclo. econs 15; eauto. }
    { eapply hsimC_uclo. econs 16; eauto. }
    { gstep. econs 17; eauto. gbase. eapply rclo10_clo_base. left. econs; eauto. }
  Qed.

  Variant hbind_rightC (r: forall R_src R_tgt
                                  (OwnT: Σ)
                                  (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                                  (fmr: Σ),
                           option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop)
          {R_src R_tgt}
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop :=
  | hbind_rightC_intro
      S_tgt
      (P: Any.t -> Any.t -> S_tgt -> iProp)
      fuel f_src f_tgt st_src0 st_tgt0 itr_src itr_tgt ktr_tgt
      (SIM: @r unit S_tgt OwnT (fun st_src st_tgt _ ret_tgt => P st_src st_tgt ret_tgt) fmr None f_src f_tgt (st_src0, Ret tt) (st_tgt0, itr_tgt))
      (SIMK: forall fmr1 st_src1 st_tgt1 ret_tgt OwnT
                    (POST: current_iProp fmr1 (Own OwnT ** P st_src1 st_tgt1 ret_tgt)),
          @r R_src R_tgt OwnT Q fmr1 fuel false false (st_src1, itr_src) (st_tgt1, ktr_tgt ret_tgt))
    :
      hbind_rightC r OwnT Q fmr fuel f_src f_tgt (st_src0, itr_src) (st_tgt0, itr_tgt >>= ktr_tgt)
  .

  Lemma hbind_rightC_mon:
    monotone10 hbind_rightC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hbind_rightC_mon: paco.

  Lemma hbind_rightC_spec: hbind_rightC <11= gupaco10 (_hsim) (cpn10 _hsim).
  Proof.
    eapply grespect_uclo.
    econs; eauto with paco. i. inv PR. eapply GF in SIM. remember None in SIM.
    remember (st_src0, Ret tt). remember (st_tgt0, itr_tgt).
    revert st_src0 st_tgt0 itr_tgt Heqp Heqp0 Heqo.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { hexploit SIMK; eauto. i.
      eapply GF in H. guclo hflagC_spec. econs.
      2:{ instantiate (1:=false). ss. }
      2:{ instantiate (1:=false). ss. }
      2:{ refl. }
      gstep. eapply _hsim_mon; eauto. i. gbase. eapply rclo10_base. auto.
    }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { eapply hsimC_uclo. econs 8; eauto. }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { eapply hsimC_uclo. econs 10; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { des. eapply hsimC_uclo. econs 12; eauto. }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { eapply hsimC_uclo. econs 14; eauto. }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { eapply hsimC_uclo. econs 16; eauto. }
    { gstep. econs 17; eauto. gbase. eapply rclo10_clo_base. left. econs; eauto. }
  Qed.

  Variant hsplitC (r: forall R_src R_tgt
                             (OwnT: Σ)
                             (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                             (fmr: Σ),
                      option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop)
          {R_src R_tgt}
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop :=
  | hsplitC_intro
      S_tgt
      (P: Any.t -> Any.t -> S_tgt -> iProp)
      fuel0 fuel1 f_src f_tgt st_src0 st_tgt0 itr_src itr_tgt ktr_tgt
      (SIM: @r unit S_tgt OwnT (fun st_src st_tgt _ ret_tgt => P st_src st_tgt ret_tgt) fmr (Some fuel0) f_src f_tgt (st_src0, Ret tt) (st_tgt0, itr_tgt))
      (SIMK: forall fmr1 st_src1 st_tgt1 ret_tgt OwnT
                    (POST: current_iProp fmr1 (Own OwnT ** P st_src1 st_tgt1 ret_tgt)),
          @r R_src R_tgt OwnT Q fmr1 (Some fuel1) false false (st_src1, itr_src) (st_tgt1, ktr_tgt ret_tgt))
    :
      hsplitC r OwnT Q fmr (Some (fuel1 + fuel0)%ord) f_src f_tgt (st_src0, itr_src) (st_tgt0, itr_tgt >>= ktr_tgt)
  .

  Lemma hsplitC_mon:
    monotone10 hsplitC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hsplitC_mon: paco.

  Lemma hsplitC_spec: hsplitC <11= gupaco10 (_hsim) (cpn10 _hsim).
  Proof.
    eapply grespect_uclo.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    remember (st_src0, Ret tt). remember (st_tgt0, itr_tgt). remember (Some fuel0).
    revert fuel0 st_src0 st_tgt0 itr_tgt Heqp Heqp0 Heqo.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { hexploit SIMK; eauto. i.
      eapply GF in H. guclo hflagC_spec. econs.
      2:{ instantiate (1:=false). ss. }
      2:{ instantiate (1:=false). ss. }
      2:{ instantiate (1:=(Some fuel1)). ss. apply OrdArith.add_base_l. }
      gstep. eapply _hsim_mon; eauto. i. gbase. eapply rclo10_base. auto.
    }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { des. gstep. econs 4; eauto. esplits; eauto.
      { eapply OrdArith.lt_add_r. eauto. }
      i. hexploit PRE; eauto. i. des. esplits; eauto. i. exploit POST; eauto. i; des. esplits; eauto.
      i. gbase. eapply rclo10_clo_base. left. econs; eauto.
    }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { eapply hsimC_uclo. econs 8; eauto. }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { eapply hsimC_uclo. econs 10; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { des. eapply hsimC_uclo. econs 12; eauto. }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { eapply hsimC_uclo. econs 14; eauto. }
    { apply f_equal with (f:=_observe) in H0. ss. }
    { eapply hsimC_uclo. econs 16; eauto. }
    { gstep. econs 17; eauto. gbase. eapply rclo10_clo_base. left. econs; eauto. }
  Qed.

  Variant hmonoC (r: forall R_src R_tgt
                            (OwnT: Σ)
                            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                            (fmr: Σ),
                     option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop)
          {R_src R_tgt}
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop :=
  | hmonoC_intro
      f_src f_tgt fuel Q0
      st_src st_tgt
      (SIM: r _ _ OwnT Q0 fmr fuel f_src f_tgt st_src st_tgt)
      (MONO: forall st_src st_tgt ret_src ret_tgt,
          (bi_entails (Q0 st_src st_tgt ret_src ret_tgt) (#=> Q st_src st_tgt ret_src ret_tgt)))
    :
      hmonoC r OwnT Q fmr fuel f_src f_tgt st_src st_tgt
  .

  Lemma hmonoC_mon:
    monotone10 hmonoC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hmonoC_mon: paco.

  Lemma hmonoC_spec: hmonoC <11= gupaco10 (_hsim) (cpn10 _hsim).
  Proof.
    eapply wrespect10_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { econs 1; eauto. eapply current_iProp_upd.
      eapply current_iProp_entail; eauto.
      iIntros "[A B]". iFrame. iStopProof. eauto.
    }
    { econs 2; eauto. i. hexploit PRE; eauto. i; des. esplits; eauto. i. hexploit POST; eauto.
      i; des. esplits; eauto. i. eapply rclo10_clo_base. econs; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. i. hexploit PRE; eauto. i; des. esplits; eauto. i. hexploit POST; eauto.
      i; des. esplits; eauto. i. eapply rclo10_clo_base. econs; eauto. }
    { econs 5; eauto. des. esplits; eauto. i. hexploit SIM; eauto. i. eapply rclo10_clo_base. econs; eauto. }
    { econs 6; eauto. i. eapply rclo10_clo_base. econs; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. des. esplits; eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 11; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 12; eauto. des. esplits; eauto. }
    { econs 13; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. }
    { econs 17; eauto. eapply rclo10_clo_base. econs; eauto. }
  Qed.

  Variant hframeC_aux (r: forall R_src R_tgt
                             (OwnT: Σ)
                             (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                             (res: Σ),
                      option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop)
          {R_src R_tgt}
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (res: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop :=
  | hframeC_aux_intro
      res0 frm
      f_src f_tgt fuel
      st_src st_tgt
      (PRE: URA.wf res)
      (UPD: URA.updatable res (res0 ⋅ frm))
      (SIM: r _ _ OwnT (fun st_src st_tgt ret_src ret_tgt => Own frm -* #=> Q st_src st_tgt ret_src ret_tgt)
              res0 fuel f_src f_tgt st_src st_tgt)
    :
      hframeC_aux r OwnT Q res fuel f_src f_tgt st_src st_tgt
  .

  Lemma hframeC_aux_mon:
    monotone10 hframeC_aux.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hframeC_aux_mon: paco.

  Lemma hframeC_aux_spec: hframeC_aux <11= gupaco10 (_hsim) (cpn10 _hsim).
  Proof.
    eapply wrespect10_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { econs 1; eauto. eapply current_iProp_upd. eapply current_iProp_updatable; et.
      eapply current_iProp_frame_own; eauto.
      { eapply URA.updatable_wf; et. }
      eapply current_iProp_entail; eauto. iIntros "[A B]". iFrame. eauto.
    }
    { econs 2; eauto. i. hexploit PRE0; eauto. i; des. esplits; eauto.
      { eapply current_iProp_updatable; et. eapply current_iProp_frame_own; eauto.
        { eapply URA.updatable_wf; et. }
        eapply current_iProp_entail.
        { eauto. }
        iIntros "[A B] C". iSplitL "A"; [iAssumption|].
        iIntros "D". iDestruct ("B" with "D") as "B". iMod "B". iModIntro. iDestruct "B" as "[[A B] D]".
        iCombine "A C" as "A". iFrame. iAssumption.
      }
      { i. exploit POST; eauto. i; des. esplits; eauto.
        { iIntros "[[[H0 H1] H2] H3]". iDestruct (UPD0 with "[H0 H2 H3]") as "H".
          { iFrame. }
          iMod "H". iModIntro. iDestruct "H" as "[A B]". iCombine "H1 B" as "B". iFrame. iAssumption.
        }
        i. eapply rclo10_clo_base.
        eapply current_iProp_entail in ACC; cycle 1.
        { iIntros "[H0 [H1 H2]]". iCombine "H0 H2" as "H". instantiate (1:= _ ** _).
          iSplitL "H1"; iAssumption. }
        eapply current_iProp_frame_own_rev in ACC. des.
        econs; et.
      }
    }
    { econs 3; eauto. }
    { econs 4; eauto. i. hexploit PRE0; eauto. i; des. esplits; eauto.
      { eapply current_iProp_updatable; et. eapply current_iProp_frame_own; eauto.
        { eapply URA.updatable_wf; et. }
        eapply current_iProp_entail.
        { eauto. }
        iIntros "[A B] C". iSplitL "A"; [iAssumption|].
        iIntros "D". iDestruct ("B" with "D") as "B". iMod "B". iModIntro. iDestruct "B" as "[[A B] D]".
        iCombine "A C" as "A". iFrame. iAssumption.
      }
      { i. exploit POST; eauto. i; des. esplits; eauto.
        { iIntros "[[[H0 H1] H2] H3]". iDestruct (UPD0 with "[H0 H2 H3]") as "H".
          { iFrame. }
          iMod "H". iModIntro. iDestruct "H" as "[A B]". iCombine "H1 B" as "B". iFrame. iAssumption.
        }
        i. eapply rclo10_clo_base.
        eapply current_iProp_entail in ACC; cycle 1.
        { iIntros "[H0 [H1 H2]]". iCombine "H1 H0 H2" as "H". iAssumption. }
        eapply current_iProp_frame_own_rev in ACC. des.
        econs; et.
      }
    }
    { econs 5; eauto.
      { eapply current_iProp_updatable; et.
        eapply current_iProp_frame_own; et.
        { eapply URA.updatable_wf; et. }
        eapply current_iProp_entail.
        { eapply PRE0. }
        iIntros "[[H0 H1] H2] H3". iFrame. iCombine "H2 H3" as "H". iAssumption.
      }
      { des. esplits; eauto.
        i. eapply rclo10_clo_base.
        eapply current_iProp_entail in ACC; cycle 1.
        { iIntros "[[H0 H1] [H2 H3]]". iCombine "H3 H0 H1 H2" as "H". iAssumption. }
        eapply current_iProp_frame_own_rev in ACC. des.
        econs; et.
        { eapply SIM; eauto.
          eapply current_iProp_entail.
          { eapply ACC1. }
          iIntros "[H0 [H1 H2]]".
          iFrame.
        }
      }
    }
    { econs 6; eauto. i. eapply rclo10_clo_base. econs; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. des. esplits; eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 11; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 12; eauto. des. esplits; eauto. }
    { econs 13; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. }
    { econs 17; eauto. eapply rclo10_clo_base. econs; eauto. }
  Qed.

  Variant hframeC (r: forall R_src R_tgt
                             (OwnT: Σ)
                             (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                             (fmr: Σ),
                      option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop)
          {R_src R_tgt}
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop :=
  | hframeC_intro
      P0 P1
      f_src f_tgt fuel
      st_src st_tgt
      (PRE: current_iProp fmr (P0 ** P1))
      (SIM: forall fmr (PRE: current_iProp fmr P1),
          r _ _ OwnT (fun st_src st_tgt ret_src ret_tgt => P0 -* #=> Q st_src st_tgt ret_src ret_tgt) fmr fuel f_src f_tgt st_src st_tgt)
    :
      hframeC r OwnT Q fmr fuel f_src f_tgt st_src st_tgt
  .

  Lemma hframeC_spec: hframeC <11= gupaco10 (_hsim) (cpn10 _hsim).
  Proof.
    ii. inv PR.
    inv PRE. rr in IPROP.
    autounfold with iprop in IPROP.
    autorewrite with iprop in IPROP. des. clarify.
    guclo hframeC_aux_spec. econs.
    { ss. }
    { rewrite URA.add_comm. eauto. }
    { guclo hmonoC_spec. econs.
      { gbase. eapply SIM. econs; eauto.
        - eapply URA.updatable_wf; et. etrans; et. eapply URA.extends_updatable. exists a; r_solve.
        - refl.
      }
      { i. ss. iIntros "H0". iModIntro. iIntros "H1".
        iApply bupd_trans. iApply "H0".
        iStopProof. uipropall.
        i. red in H. des. clarify. esplits; [eassumption|eauto].
        i. eapply URA.wf_extends. { exists ctx. r_solve. } r_wf H.
      }
    }
  Qed.

  Variant hupdC (r: forall R_src R_tgt
                           (OwnT: Σ)
                           (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                           (fmr: Σ),
                     option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop)
          {R_src R_tgt}
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : option Ord.t -> bool -> bool -> Any.t * itree hEs R_src -> Any.t * itree hEs R_tgt -> Prop :=
  | hupdC_intro
      f_src f_tgt fuel
      st_src st_tgt
      fmr1
      (WF: URA.wf fmr)
      (UPD: URA.updatable fmr fmr1)
      (SIM: r _ _ OwnT Q fmr1 fuel f_src f_tgt st_src st_tgt)
    :
      hupdC r OwnT Q fmr fuel f_src f_tgt st_src st_tgt
  .

  Lemma hupdC_mon:
    monotone10 hupdC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hupdC_mon: paco.

  Lemma hupdC_spec: hupdC <11= gupaco10 (_hsim) (cpn10 _hsim).
  Proof.
    eapply wrespect10_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { econs 1; eauto. eapply current_iProp_updatable; et. }
    { econs 2; eauto. i. hexploit PRE; eauto. i; des. esplits; eauto.
      { eapply current_iProp_updatable; et. }
      i. exploit POST; eauto. i; des. esplits; eauto.
      i. eapply rclo10_clo_base. econs; eauto; try refl. apply ACC.
    }
    { econs 3; eauto. }
    { econs 4; eauto. i. hexploit PRE; eauto. i; des. esplits; eauto.
      { eapply current_iProp_updatable; et. }
      i. exploit POST; eauto. i; des. esplits; eauto.
      i. eapply rclo10_clo_base. econs; eauto; try refl. apply ACC.
    }
    { econs 5; eauto. i. hexploit PRE; eauto. i; des. esplits; eauto.
      { eapply current_iProp_updatable; et. }
      i. eapply rclo10_clo_base. econs; eauto; try refl. apply ACC.
    }
    { econs 6; eauto. i. eapply rclo10_clo_base. econs; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. des. esplits; eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 11; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 12; eauto. des. esplits; eauto. }
    { econs 13; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. }
    { econs 17; eauto. eapply rclo10_clo_base. econs; eauto. }
  Qed.
End SIM.
#[export] Hint Resolve _hsim_mon: paco.
#[export] Hint Resolve cpn9_wcompat: paco.
