Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem.
Import EventsL.
Require Import Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import Any.
Require Import TODOYJ.

From Ordinal Require Import Ordinal Arithmetic.

Set Implicit Arguments.

Local Open Scope nat_scope.















Module W.
Section WORLD.

  Context `{Σ: GRA.t}.

  Class t := {
    car: Type;
    le: car -> car -> Prop;
    wf: car -> Prop;
    le_PreOrder: PreOrder le;
    src: car -> alist mname Σ;
    tgt: car -> alist mname Σ;
  }
  .

End WORLD.
End W.






(* Section PLAYGROUND. *)
(*   Variable A B: Type. *)
(*   Variable left: A -> A -> Prop. *)
(*   Variable right: B -> B -> Prop. *)
(*   Inductive _sim (sim: nat -> A -> B -> Prop): nat -> A -> B -> Prop := *)
(*   | go_left *)
(*       i0 a0 b0 a1 *)
(*       i1 *)
(*       (*** can't choose i1 depending on a1 ***) *)
(*       (ORD: i1 < i0) *)
(*       (GO: left a0 a1) *)
(*       (K: sim i1 a1 b0) *)
(*     : *)
(*       _sim sim i0 a0 b0 *)
(*   | go_right *)
(*       i0 a0 b0 b1 *)
(*       i1 *)
(*       (ORD: i1 < i0) *)
(*       (GO: right b0 b1) *)
(*       (K: sim i1 a0 b1) *)
(*     : *)
(*       _sim sim i0 a0 b0 *)
(*   | go_both *)
(*       i0 a0 b0 i1 a1 b1 *)
(*       (GO: left a0 a1) *)
(*       (GO: right b0 b1) *)
(*       (K: sim i1 a1 b1) *)
(*     : *)
(*       _sim sim i0 a1 b1 *)
(*   . *)
(* End PLAYGROUND. *)
(* Reset PLAYGROUND. *)
(* (*** i1 can't depend on a1, or the internal choices inside "left" ***) *)


(* Section PLAYGROUND. *)
(*   Variable A B: Type. *)
(*   Variable left: nat -> A -> nat -> A -> Prop. *)
(*   Variable right: nat -> B -> nat -> B -> Prop. *)
(*   Variable both: (nat -> A -> B -> Prop) -> (nat -> A -> B -> Prop). *)
(*   Inductive _sim (sim: nat -> A -> B -> Prop): nat -> A -> B -> Prop := *)
(*   | go_left *)
(*       i0 a0 b0 a1 *)
(*       i1 *)
(*       (* (ORD: i1 < i0) *) *)
(*       (GO: left i0 a0 i1 a1) *)
(*       (K: sim i1 a1 b0) *)
(*     : *)
(*       _sim sim i0 a0 b0 *)
(*   | go_right *)
(*       i0 a0 b0 b1 *)
(*       i1 *)
(*       (* (ORD: i1 < i0) *) *)
(*       (GO: right i0 b0 i1 b1) *)
(*       (K: sim i1 a0 b1) *)
(*     : *)
(*       _sim sim i0 a0 b0 *)
(*   | go_left_right *)
(*       i0 a0 b0 _unused0_ _unused1_ i1 a1 b1 *)
(*       (GO: left i0 a0 _unused0_ a1) *)
(*       (GO: right i0 b0 _unused1_ b1) *)
(*       (K: sim i1 a1 b1) *)
(*     : *)
(*       _sim sim i0 a1 b1 *)
(*   | go_both *)
(*       i0 a0 b0 *)
(*       (GO: both sim i0 a0 b0) *)
(*     : *)
(*       _sim sim i0 a0 b0 *)
(*   . *)

(*   Definition sim: _ -> _ -> _ -> Prop := paco3 _sim bot3. *)

(*   Lemma sim_mon (MON: monotone3 both): monotone3 _sim. *)
(*   Proof. *)
(*     ii. inv IN. *)
(*     - econs 1; eauto. *)
(*     - econs 2; eauto. *)
(*     - econs 3; eauto. *)
(*     - econs 4; eauto. *)
(*   Qed. *)

(* End PLAYGROUND. *)

(* Hint Constructors _sim. *)
(* Hint Unfold sim. *)
(* Hint Resolve sim_mon: paco. *)












Section SIM.

  Context `{Σ: GRA.t}.

  (* Let st_local: Type := (list (string * GRA) * GRA). *)
  Let st_local: Type := ((alist mname (Σ * Any.t)) * Σ).


  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).
  Variable wf: W -> Prop.
  Variable le: relation W.
  Hypothesis le_PreOrder: PreOrder le.

  Variable namespace: gname -> Prop.

  Variant _sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), Ord.t -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : Ord.t -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_ret
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      (WF: wf (mrs_src0, mrs_tgt0))
      v_src v_tgt
      (RET: RR (mrs_src0, fr_src0) (mrs_tgt0, fr_tgt0) v_src v_tgt)
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), (Ret v_src)) ((mrs_tgt0, fr_tgt0), (Ret v_tgt))
  | sim_itree_tau
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (K: sim_itree _ _ RR i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 (st_src0, tau;; i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_call
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      fn varg k_src k_tgt
      (WF: wf (mrs_src0, mrs_tgt0))
      (K: forall vret mrs_src1 mrs_tgt1 (WF: wf (mrs_src1, mrs_tgt1)),
          exists i1, sim_itree _ _ RR i1 ((mrs_src1, fr_src0), k_src vret) ((mrs_tgt1, fr_tgt0), k_tgt vret))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), (trigger PushFrame;;; r <- trigger (Call fn varg);; trigger PopFrame;;; tau;; k_src r))
                 ((mrs_tgt0, fr_tgt0), (trigger PushFrame;;; r <- trigger (Call fn varg);; trigger PopFrame;;; tau;; k_tgt r))
  | sim_itree_syscall
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      fn varg k_src k_tgt rvs
      (K: forall vret,
          exists i1, sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src vret) ((mrs_tgt0, fr_tgt0), k_tgt vret))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Syscall fn varg rvs) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Syscall fn varg rvs) >>= k_tgt)
  (*** TODO: sim_syscall is nontrivial; it should accept "injected" memory... ***)
  (*** TODO: simplify the model: Syscall: list val -> val ***)

  | sim_itree_choose_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      X_src X_tgt k_src k_tgt
      (K: forall (x_tgt: X_tgt), exists (x_src: X_src) i1, sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src x_src) ((mrs_tgt0, fr_tgt0), k_tgt x_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Choose X_src) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Choose X_tgt) >>= k_tgt)
  | sim_itree_take_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      X_src X_tgt k_src k_tgt
      (K: forall (x_src: X_src), exists (x_tgt: X_tgt) i1, sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src x_src) ((mrs_tgt0, fr_tgt0), k_tgt x_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Take X_src) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Take X_tgt) >>= k_tgt)
  | sim_itree_pput_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mn mr_src0 mr_tgt0 mp_src1 mp_tgt1 mrs_src1 mrs_tgt1 mp_src0 mp_tgt0
      (MRSRC: alist_find mn mrs_src0 = Some (mr_src0, mp_src0))
      (MRTGT: alist_find mn mrs_tgt0 = Some (mr_tgt0, mp_tgt0))
      (EQSRC: mrs_src1 = alist_add mn (mr_src0, mp_src1) mrs_src0)
      (EQTGT: mrs_tgt1 = alist_add mn (mr_tgt0, mp_tgt1) mrs_tgt0)
      (K: sim_itree _ _ RR i1 ((mrs_src1, fr_src0), k_src tt) ((mrs_tgt1, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (PPut mn mp_src1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (PPut mn mp_tgt1) >>= k_tgt)
  | sim_itree_mput_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mn mr_src0 mr_tgt0 mr_src1 mr_tgt1 mrs_src1 mrs_tgt1 mp_src0 mp_tgt0
      (MRSRC: alist_find mn mrs_src0 = Some (mr_src0, mp_src0))
      (MRTGT: alist_find mn mrs_tgt0 = Some (mr_tgt0, mp_tgt0))
      (EQSRC: mrs_src1 = alist_add mn (mr_src1, mp_src0) mrs_src0)
      (EQSRC: mrs_tgt1 = alist_add mn (mr_tgt1, mp_tgt0) mrs_tgt0)
      (K: sim_itree _ _ RR i1 ((mrs_src1, fr_src0), k_src tt) ((mrs_tgt1, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (MPut mn mr_src1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (MPut mn mr_tgt1) >>= k_tgt)
  | sim_itree_fput_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      fr_src1 fr_tgt1
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src1), k_src tt) ((mrs_tgt0, fr_tgt1), k_tgt tt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (FPut fr_src1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FPut fr_tgt1) >>= k_tgt)
  | sim_itree_pget_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mn mr_src0 mp_src0 mr_tgt0 mp_tgt0
      (MRSRC: alist_find mn mrs_src0 = Some (mr_src0, mp_src0))
      (MRTGT: alist_find mn mrs_tgt0 = Some (mr_tgt0, mp_tgt0))
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src mp_src0) ((mrs_tgt0, fr_tgt0), k_tgt mp_tgt0))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (PGet mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (PGet mn) >>= k_tgt)
  | sim_itree_mget_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mn mr_src0 mp_src0 mr_tgt0 mp_tgt0
      (MRSRC: alist_find mn mrs_src0 = Some (mr_src0, mp_src0))
      (MRTGT: alist_find mn mrs_tgt0 = Some (mr_tgt0, mp_tgt0))
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src mr_src0) ((mrs_tgt0, fr_tgt0), k_tgt mr_tgt0))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (MGet mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (MGet mn) >>= k_tgt)
  | sim_itree_fget_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src fr_src0) ((mrs_tgt0, fr_tgt0), k_tgt fr_tgt0))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (FGet) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FGet) >>= k_tgt)



  | sim_itree_tau_src
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_choose_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X k_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: exists (x: X), sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src x) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Choose X) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_take_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X k_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: forall (x: X), sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src x) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (Take X) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)

  | sim_itree_pput_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      mn mr0 mp1 mrs_src1 mp0
      (MR0: alist_find mn mrs_src0 = Some (mr0, mp0))
      (EQ: mrs_src1 = alist_add mn (mr0, mp1) mrs_src0)
      (K: sim_itree _ _ RR i1 ((mrs_src1, fr_src0), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (PPut mn mp1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_mput_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      mn mr0 mr1 mrs_src1 mp0
      (MR0: alist_find mn mrs_src0 = Some (mr0, mp0))
      (EQ: mrs_src1 = alist_add mn (mr1, mp0) mrs_src0)
      (K: sim_itree _ _ RR i1 ((mrs_src1, fr_src0), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (MPut mn mr1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_fput_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      fr_src1
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src1), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (FPut fr_src1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)

  | sim_itree_pget_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      mn mr0 mp0
      (MR0: alist_find mn mrs_src0 = Some (mr0, mp0))
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src mp0) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (PGet mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_mget_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      mn mr0 mp0
      (MR0: alist_find mn mrs_src0 = Some (mr0, mp0))
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src mr0) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (MGet mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_fget_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src fr_src0) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (FGet) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)






  | sim_itree_tau_tgt
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_choose_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X i_src k_tgt
      (ORD: Ord.lt i1 i0)
      (K: forall (x: X), sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt x))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Choose X) >>= k_tgt)
  | sim_itree_take_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X i_src k_tgt
      (ORD: Ord.lt i1 i0)
      (K: exists (x: X), sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt x))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Take X) >>= k_tgt)

  | sim_itree_pput_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: Ord.lt i1 i0)
      mn mr0 mp1 mrs_tgt1 mp0
      (MR0: alist_find mn mrs_tgt0 = Some (mr0, mp0))
      (EQ: mrs_tgt1 = alist_add mn (mr0, mp1) mrs_tgt0)
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt1, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (PPut mn mp1) >>= k_tgt)
  | sim_itree_mput_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: Ord.lt i1 i0)
      mn mr0 mr1 mrs_tgt1 mp0
      (MR0: alist_find mn mrs_tgt0 = Some (mr0, mp0))
      (EQ: mrs_tgt1 = alist_add mn (mr1, mp0) mrs_tgt0)
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt1, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (MPut mn mr1) >>= k_tgt)
  | sim_itree_fput_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: Ord.lt i1 i0)
      fr_tgt1
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt1), k_tgt tt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FPut fr_tgt1) >>= k_tgt)

  | sim_itree_pget_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: Ord.lt i1 i0)
      mn mr0 mp0
      (MR0: alist_find mn mrs_tgt0 = Some (mr0, mp0))
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt mp0))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (PGet mn) >>= k_tgt)
  | sim_itree_mget_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: Ord.lt i1 i0)
      mn mr0 mp0
      (MR0: alist_find mn mrs_tgt0 = Some (mr0, mp0))
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt mr0))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (MGet mn) >>= k_tgt)
  | sim_itree_fget_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: Ord.lt i1 i0)
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt  fr_tgt0))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FGet) >>= k_tgt)
  (* | sim_itree_hint *)
  (*     i0 i1 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0 *)
  (*     fn varg k_src i_tgt *)
  (*     (ORD: Ord.lt i1 i0) *)
  (*     (K: forall (HINT: namespace fn), *)
  (*         sim_itree _ _ RR i1 ((mrs_src0, fr_src0), (trigger PushFrame;;; r <- trigger (Call fn varg);; trigger PopFrame;;; tau;; k_src r)) ((mrs_tgt0, fr_tgt0), i_tgt)) *)
  (*   : *)
  (*     _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), (trigger PushFrame;;; r <- trigger (Call fn varg);; trigger PopFrame;;; tau;; k_src r)) *)
  (*                ((mrs_tgt0, fr_tgt0), i_tgt) *)
  | sim_itree_hint2
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      fn varg k_src i_tgt
      (K: forall (HINT: namespace fn), exists i1,
          sim_itree _ _ RR i1 ((mrs_src0, fr_src0), (trigger PushFrame;;; r <- trigger (Call fn varg);;
                                    trigger PopFrame;;; tau;; k_src r)) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), (tau;; trigger PushFrame;;; r <- trigger (Call fn varg);;
                                                        trigger PopFrame;;; tau;; k_src r))
                 ((mrs_tgt0, fr_tgt0), tau;; i_tgt)
  .

  Program Definition sim_itree: _ -> relation _ :=
    paco6 _sim_itree bot6 _ _ (fun _ _ => @eq Any.t).

  Lemma sim_itree_mon: monotone6 _sim_itree.
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - eapply sim_itree_hint2. ii. exploit K; et. i; des. esplits; et.
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree_mon: paco.

  Lemma sim_itree_mon_ord r S_src S_tgt SS i0 i1 (ORD: (i0 <= i1)%ord): @_sim_itree r S_src S_tgt SS i0 <2= @_sim_itree r S_src S_tgt SS i1.
  Proof.
    ii. inv PR; try (by econs; et).
    (* - econs; try apply SIM; et. etrans; et. *)
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
    - econs; try apply SIM; et. eapply Ord.lt_le_lt; et.
  Qed.

  Definition sim_fsem: relation (Any.t -> itree Es Any.t) :=
    (eq ==> (fun it_src it_tgt => forall mrs_src mrs_tgt (SIMMRS: wf (mrs_src, mrs_tgt)),
                 exists n, sim_itree n ((mrs_src, URA.unit), it_src)
                                     ((mrs_tgt, URA.unit), it_tgt)))%signature
  .

  Definition sim_fnsem: relation (string * (Any.t -> itree Es Any.t)) := RelProd eq sim_fsem.


  Variant lordC (r: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), Ord.t -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : Ord.t -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | lordC_intro
      o0 o1 st_src st_tgt
      (ORD: Ord.le o0 o1)
      (SIM: r _ _ RR o0 st_src st_tgt)
    :
      lordC r RR o1 st_src st_tgt
  .
  Hint Constructors lordC: core.

  Lemma lordC_mon
        r1 r2
        (LE: r1 <6= r2)
    :
      @lordC r1 <6= @lordC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve lordC_mon: paco.

  Lemma lordC_compatible: compatible6 (_sim_itree) lordC.
  Proof.
    econs; eauto with paco.
    ii. inv PR. eapply sim_itree_mon_ord; eauto.
    eapply sim_itree_mon; eauto.
    i. econs; eauto. refl.
  Qed.

  Lemma lordC_spec: lordC <7= gupaco6 (_sim_itree) (cpn6 _sim_itree).
  Proof.
    intros. gclo. econs.
    { eapply lordC_compatible. }
    ss. eapply lordC_mon; [|eauto]. i. gbase. auto.
  Qed.

  Variant lbindR (r s: forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), Ord.t -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop):
    forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), Ord.t -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop :=
  | lbindR_intro
      o0 o1

      R_src R_tgt RR
      (st_src0 st_tgt0: st_local)
      (i_src: itree Es R_src) (i_tgt: itree Es R_tgt)
      (SIM: r _ _ RR o0 (st_src0, i_src) (st_tgt0, i_tgt))

      S_src S_tgt SS
      (k_src: ktree Es R_src S_src) (k_tgt: ktree Es R_tgt S_tgt)
      (SIMK: forall st_src1 st_tgt1 vret_src vret_tgt (SIM: RR st_src1 st_tgt1 vret_src vret_tgt), s _ _ SS o1 (st_src1, k_src vret_src) (st_tgt1, k_tgt vret_tgt))
    :
      lbindR r s SS (OrdArith.add o1 o0) (st_src0, ITree.bind i_src k_src) (st_tgt0, ITree.bind i_tgt k_tgt)
  .

  Hint Constructors lbindR: core.

  Lemma lbindR_mon
        r1 r2 s1 s2
        (LEr: r1 <6= r2) (LEs: s1 <6= s2)
    :
      lbindR r1 s1 <6= lbindR r2 s2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Definition lbindC r := lbindR r r.
  Hint Unfold lbindC: core.

  Lemma lbindC_wrespectful: wrespectful6 (_sim_itree) lbindC.
  Proof.
    econstructor; repeat intro.
    { eapply lbindR_mon; eauto. }
    rename l into llll.
    eapply lbindR_mon in PR; cycle 1.
    { eapply GF. }
    { i. eapply PR0. }
    inv PR. csc. inv SIM.
    + rewrite ! bind_ret_l. exploit SIMK; eauto. i.
      eapply sim_itree_mon_ord.
      { instantiate (1:=o1). eapply OrdArith.add_base_l. }
      eapply sim_itree_mon; eauto with paco.
    + rewrite ! bind_tau. econs; eauto.
      econs 2; eauto with paco. econs; eauto with paco.
    + replace (x <- (trigger PushFrame;;; r0 <- trigger (Call fn varg);; trigger PopFrame;;; (tau;; k_src0 r0));; k_src x) with
          (trigger PushFrame;;; r <- trigger (Call fn varg);; trigger PopFrame;;; tau;; (k_src0 >=> k_src) r); cycle 1.
      { grind. }
      replace (x <- (trigger PushFrame;;; r0 <- trigger (Call fn varg);; trigger PopFrame;;; (tau;; k_tgt0 r0));; k_tgt x) with
          (trigger PushFrame;;; r <- trigger (Call fn varg);; trigger PopFrame;;; tau;; (k_tgt0 >=> k_tgt) r); cycle 1.
      { grind. }
      econs; eauto.
      i. exploit K; eauto. i. des. eexists.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      i. exploit K; eauto. i. des. eexists.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      i. exploit K; eauto. i. des. esplits.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      i. exploit K; eauto. i. des. esplits.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      econs 2; eauto with paco. econs; eauto with paco.
    + rewrite ! bind_bind. des. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eexists. eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      i. hexploit K; eauto. i.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      econs 2; eauto with paco. econs; eauto with paco.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      i. hexploit K; eauto. i.
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. des. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eexists. eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      eapply rclo6_clo_base. econs; eauto.
    + replace (x <- (trigger PushFrame;;; r0 <- trigger (Call fn varg);; trigger PopFrame;;; (tau;; k_src0 r0));; k_src x) with
          (trigger PushFrame;;; r <- trigger (Call fn varg);; trigger PopFrame;;; tau;; (k_src0 >=> k_src) r); cycle 1.
      { grind. }
      econs; eauto.
      { eapply OrdArith.lt_add_r; eauto. }
      i. exploit K; eauto. i. des.
      replace (trigger PushFrame;;; r <- trigger (Call fn varg);; trigger PopFrame;;; tau;; (k_src0 >=> k_src) r) with
          ((trigger PushFrame;;; r <- trigger (Call fn varg);; trigger PopFrame;;; tau;; k_src0 r) >>= k_src); cycle 1.
      { grind. }
      eapply rclo6_clo_base. econs; eauto.
  Qed.

  Lemma lbindC_spec: lbindC <7= gupaco6 (_sim_itree) (cpn6 (_sim_itree)).
  Proof.
    intros. eapply wrespect6_uclo; eauto with paco. eapply lbindC_wrespectful.
  Qed.

End SIM.
Hint Resolve sim_itree_mon: paco.


Variant _wf_function `{Σ: GRA.t} (ms: list mname)
        (wf_function: itree Es Any.t -> Prop) (st0: itree Es Any.t): Prop :=
| wf_function_ret
    v
    (RET: st0 = Ret v)
| wf_function_tau
    st1
    (TAU: st0 = Tau st1)
    (WF: wf_function st1)
| wf_function_choose
    X k
    (VIS: st0 = trigger (Choose X) >>= k)
    (WF: forall x, wf_function (k x))
| wf_function_take
    X k
    (VIS: st0 = trigger (Take X) >>= k)
    (WF: forall x, wf_function (k x))
| wf_function_pput
    mn mp k
    (VIS: st0 = trigger (PPut mn mp) >>= k)
    (MN: List.In mn ms)
    (WF: forall x, wf_function (k x))
| wf_function_mput
    mn mr k
    (VIS: st0 = trigger (MPut mn mr) >>= k)
    (MN: List.In mn ms)
    (WF: forall x, wf_function (k x))
| wf_function_fput
    fr k
    (VIS: st0 = trigger (FPut fr) >>= k)
    (WF: forall x, wf_function (k x))
| wf_function_pget
    mn k
    (VIS: st0 = trigger (PGet mn) >>= k)
    (MN: List.In mn ms)
    (WF: forall x, wf_function (k x))
| wf_function_mget
    mn k
    (VIS: st0 = trigger (MGet mn) >>= k)
    (MN: List.In mn ms)
    (WF: forall x, wf_function (k x))
| wf_function_fget
    k
    (VIS: st0 = trigger (FGet) >>= k)
    (WF: forall x, wf_function (k x))
| wf_function_call
    fn varg k
    (CALL: st0 = trigger PushFrame;;; r <- trigger (Call fn varg);; trigger PopFrame;;; tau;; k r)
    (WF: forall x, wf_function (k x))
| wf_function_syscall
    fn varg rvs k
    (CALL: st0 = trigger (Syscall fn varg rvs) >>= k)
    (WF: forall x, wf_function (k x))
.

Lemma wf_function_gen_mon `{Σ: GRA.t} (ms: list mname):
  monotone1 (_wf_function ms).
Proof.
  ii. inv IN.
  - econs 1; eauto.
  - econs 2; eauto.
  - econs 3; eauto.
  - econs 4; eauto.
  - econs 5; eauto.
  - econs 6; eauto.
  - econs 7; eauto.
  - econs 8; eauto.
  - econs 9; eauto.
  - econs 10; eauto.
  - econs 11; eauto.
  - econs 12; eauto.
Qed.
Hint Resolve wf_function_gen_mon: paco.

Definition wf_function `{Σ: GRA.t} (ms: list mname) := paco1 (_wf_function ms) bot1.

Lemma wf_function_mon `{Σ: GRA.t} (ms0 ms1: list mname)
      (LE: forall mn (IN: List.In mn ms0), List.In mn ms1):
  wf_function ms0 <1= wf_function ms1.
Proof.
  pcofix CIH. i. pfold.
  punfold PR. inv PR; pclearbot.
  - econs 1; eauto.
  - econs 2; eauto.
  - econs 3; eauto. i. right. eapply CIH. eapply WF.
  - econs 4; eauto. i. right. eapply CIH. eapply WF.
  - econs 5; eauto. i. right. eapply CIH. eapply WF.
  - econs 6; eauto. i. right. eapply CIH. eapply WF.
  - econs 7; eauto. i. right. eapply CIH. eapply WF.
  - econs 8; eauto. i. right. eapply CIH. eapply WF.
  - econs 9; eauto. i. right. eapply CIH. eapply WF.
  - econs 10; eauto. i. right. eapply CIH. eapply WF.
  - econs 11; eauto. i. right. eapply CIH. eapply WF.
  - econs 12; eauto. i. right. eapply CIH. eapply WF.
Qed.

Definition wf_mrs `{Σ: GRA.t} (ms: list mname) (mrs: alist mname (Σ * Any.t)): Prop :=
  forall mn (IN: List.In mn ms),
  exists mr mp, <<FIND: alist_find mn mrs = Some (mr, mp)>>.

Lemma wf_mrs_add `{Σ: GRA.t} (ms: list mname) (mrs: alist mname (Σ * Any.t))
      (WF: wf_mrs ms mrs)
      mn mr:
  wf_mrs ms (alist_add mn mr mrs).
Proof.
  ii. destruct (string_Dec mn mn0).
  - subst. destruct mr as [mr mp]. exists mr, mp. eapply alist_add_find_eq.
  - hexploit (WF mn0); auto. i. des.
    exists mr0, mp. rewrite alist_add_find_neq; auto.
Qed.

Lemma self_sim_itree `{Σ: GRA.t} (ms: list mname):
  forall n mrs fr st
         (WF: wf_function ms st)
         (MRS: wf_mrs ms mrs),
    @sim_itree _ (fun p => fst p = snd p /\ wf_mrs ms (fst p)) bot1
               n ((mrs, fr), st) ((mrs, fr), st).
Proof.
  pcofix CIH. i. pfold. punfold WF. inv WF; pclearbot.
  - eapply sim_itree_ret; ss.
  - eapply sim_itree_tau. right. eapply CIH; ss.
  - eapply sim_itree_choose_both. i. exists x_tgt.
    eexists. right. eapply CIH; ss.
  - eapply sim_itree_take_both. i. exists x_src.
    eexists. right. eapply CIH; ss.
  - hexploit (MRS mn); eauto. i. des.
    eapply sim_itree_pput_both; eauto.
    right. eapply CIH; ss. apply wf_mrs_add. auto.
  - hexploit (MRS mn); eauto. i. des.
    eapply sim_itree_mput_both; eauto. right. eapply CIH; ss.
    eapply wf_mrs_add; eauto.
  - eapply sim_itree_fput_both; eauto. right. eapply CIH; ss.
  - hexploit (MRS mn); eauto. i. des.
    eapply sim_itree_pget_both; eauto.
    right. eapply CIH; ss.
  - hexploit (MRS mn); eauto. i. des.
    eapply sim_itree_mget_both; eauto. right. eapply CIH; ss.
  - eapply sim_itree_fget_both; eauto. right. eapply CIH; ss.
    Unshelve. all: exact 0.
  - eapply sim_itree_call; eauto. i. exists 0.
    ss. des; subst. right. eapply CIH; ss.
  - eapply sim_itree_syscall; eauto. i. exists 0.
    ss. des; subst. right. eapply CIH; ss.
Qed.



(*** Q: do we need SimMemOh.le (and lepriv) ??? ***)

(*** Let's say that le/lepriv can be encoded using RA and CheckWf... ***)
(*** Q: Is "Source CheckWf >= Target CheckWf" trivial? or can be derived automatically? ***)
(*** A: I think no. It looks like a real user obligation. ***)
(*** N.B.: In the course of verifying "Source CheckWf >= Target CheckWf", one may need "le".
         For an instance, if target RA is in some sense monotonic, while source RA is unit,
         we have to prove that "Target CheckWf" holds from the ground. To do so, we need "le".
         I am not entirely sure that we don't need "lepriv",
         but (1) lepriv alone won't scale with concurrency,
         so we need separation (putting into/out of function local resource), then
         (2) it seems function-local resource (without lepriv) is sufficient for the cases
         that I can think of ***)

(*** desiderata: (1) state-aware simulation relation !!!! ***)
(*** (2) not whole function frame, just my function frame !!!! ***)
(*** (3) would be great if induction tactic works !!!! (study itree case study more) ***)



Definition wf_mod `{Σ: GRA.t} (ms: ModSemL.t): Prop :=
  let mns := List.map fst ms.(ModSemL.initial_mrs) in
  (<<ND: NoDup mns>>) /\
  (<<WFFUN: List.Forall (fun '(_, fn) => forall arg, wf_function mns (fn arg)) ms.(ModSemL.fnsems)>>).

Module ModSemLPair.
Section SIMMODSEML.

  Context `{Σ: GRA.t}.
  Variable (ms_src ms_tgt: ModSemL.t).

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).
  Inductive sim: Prop := mk {
    wf: W -> Prop;
    le: W -> W -> Prop;
    le_PreOrder: PreOrder le;
    (*** TODO: incorporate le properly ***)
    sim_fnsems: Forall2 (sim_fnsem wf bot1) ms_src.(ModSemL.fnsems) ms_tgt.(ModSemL.fnsems);
    sim_initial_mrs: wf (ms_src.(ModSemL.initial_mrs), ms_tgt.(ModSemL.initial_mrs));
  }.

End SIMMODSEML.

Lemma self_sim_mod `{Σ: GRA.t} (ms: ModSemL.t) (WF: wf_mod ms):
  sim ms ms.
Proof.
  eapply mk with (wf:=fun p => fst p = snd p /\ wf_mrs (List.map fst ms.(ModSemL.initial_mrs)) (fst p)) (le:=top2); ss.
  2: {
    split; auto. ii. eapply in_map_iff in IN. des. subst.
    destruct (alist_find (fst x) (ModSemL.initial_mrs ms)) eqn:EQ.
    - destruct p. et.
    - destruct x. eapply alist_find_none in EQ.
      exfalso. ss. eapply EQ; et.
  }
  unfold wf_mod in *. des.
  revert WFFUN. generalize (ModSemL.fnsems ms).
  induction a; i; ss. inv WFFUN. destruct a. econs; eauto.
  econs; ss. ii. subst. ss. des. subst.
  exists 0. eapply self_sim_itree; eauto.
Qed.

Section ADD.

  Lemma alist_add_disjoint_filter K `{Dec K} V f0 f1 (l: alist K V) k v v0
        (FIND: alist_find k (alist_filter f0 l) = Some v0)
        (ND: forall k' v0' v1'
                    (IN0: alist_find k' (alist_filter f0 l) = Some v0')
                    (IN1: alist_find k' (alist_filter f1 l) = Some v1'),
            False)
    :
      alist_filter f1 (alist_add k v l) =
      alist_filter f1 l.
  Proof.
    eapply alist_add_other_filter.
    destruct (f1 k) eqn:EQ1; auto.
    exfalso. eapply (ND k v0 v0); et.
    assert (EQ0: f0 k = true).
    { clear - FIND. eapply alist_find_some in FIND.
      eapply filter_In in FIND. des. auto. }
    clear v ND. rewrite <- FIND. clear FIND.
    induction l; ss. destruct a. ss. des_ifs.
    { ss. rewrite eq_rel_dec_correct in *. des_ifs; auto. }
    { ss. rewrite eq_rel_dec_correct in *. des_ifs; auto. }
    { ss. rewrite eq_rel_dec_correct in *. des_ifs; auto. }
  Qed.

  Lemma alist_find_add_filter K `{Dec K} V (l: alist K V) k v0 v1 f
        (FIND: alist_find k (alist_filter f l) = Some v0)
    :
      alist_filter f (alist_add k v1 l) =
      alist_add k v1 (alist_filter f l).
  Proof.
    eapply alist_add_filter.
    eapply alist_find_some in FIND.
    unfold alist_filter in FIND. eapply filter_In in FIND. des. ss.
  Qed.

  Lemma alist_disjoint_find K `{Dec K} V f0 f1 (l: alist K V)
        (DISJOINT: forall k (IN0: f0 k = true) (IN1: f1 k = true), False)
    :
      forall k v0 v1
             (IN0: alist_find k (alist_filter f0 l) = Some v0)
             (IN1: alist_find k (alist_filter f1 l) = Some v1),
        False.
  Proof.
    i. eapply alist_find_some in IN0. eapply alist_find_some in IN1.
    unfold alist_filter in *. eapply filter_In in IN0. eapply filter_In in IN1.
    des. ss. et.
  Qed.

  Lemma all_true_filter A (l: list A) f
        (TRUE: List.Forall (fun a => f a = true) l)
    :
      List.filter f l = l.
  Proof.
    revert TRUE. induction l; ss; i.
    inv TRUE. rewrite H1. f_equal. auto.
  Qed.

  Lemma all_false_filter A (l: list A) f
        (FALSE: List.Forall (fun a => f a = false) l)
    :
      List.filter f l = [].
  Proof.
    revert FALSE. induction l; ss; i.
    inv FALSE. rewrite H1. et.
  Qed.

  Lemma app_nodup A (l0 l1: list A) (ND: NoDup (l0 ++ l1))
    :
      forall a
             (IN0: In a l0)
             (IN1: In a l1),
        False.
  Proof.
    revert l0 ND. induction l0; ss. i. inv ND. des; subst.
    { eapply H1. eapply in_or_app. auto. }
    { eapply IHl0; eauto. }
  Qed.


  Context `{Σ: GRA.t}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).

  Variant add_wf
          (ms_src0 ms_src1 ms_tgt0 ms_tgt1: list mname)
          (wf0 wf1: W -> Prop):
    W -> Prop :=
  | add_wf_intro
      mrs_src mrs_tgt
      (WF0: wf0 (alist_filter (fun mn => in_dec string_Dec mn ms_src0) mrs_src,
                 alist_filter (fun mn => in_dec string_Dec mn ms_tgt0) mrs_tgt))
      (WF1: wf1 (alist_filter (fun mn => in_dec string_Dec mn ms_src1) mrs_src,
                 alist_filter (fun mn => in_dec string_Dec mn ms_tgt1) mrs_tgt))
      (NDSRC: NoDup (List.map fst mrs_src))
      (NDTGT: NoDup (List.map fst mrs_tgt))
    :
      add_wf ms_src0 ms_src1 ms_tgt0 ms_tgt1 wf0 wf1 (mrs_src, mrs_tgt)
  .

  Lemma add_wf_sym ms_src0 ms_src1 ms_tgt0 ms_tgt1 wf0 wf1 mrs_src mrs_tgt
        (WF: add_wf ms_src0 ms_src1 ms_tgt0 ms_tgt1 wf0 wf1 (mrs_src, mrs_tgt))
    :
      add_wf ms_src1 ms_src0 ms_tgt1 ms_tgt0 wf1 wf0 (mrs_src, mrs_tgt).
  Proof.
    inv WF. econs; eauto.
  Qed.

  Lemma sim_itree_sym wf0 wf1 (EQV: forall w, wf0 w <-> wf1 w)
        n ns ms_src ms_tgt
        (SIM: sim_itree wf0 n ns ms_src ms_tgt)
    :
      sim_itree wf1 n ns ms_src ms_tgt.
  Proof.
    assert(wf0 = wf1).
    { extensionality x. apply prop_ext; ss. }
    subst; ss.
  Qed.

  Lemma add_sim_itree ms_src0 ms_src1 ms_tgt0 ms_tgt1 (wf0 wf1: W -> Prop) ns
        (DISJSRC: forall mn
                         (IN0: (in_dec string_Dec mn ms_src1: bool) = true)
                         (IN1: (in_dec string_Dec mn ms_src0: bool) = true),
            False)
        (DISJTGT: forall mn
                         (IN0: (in_dec string_Dec mn ms_tgt1: bool) = true)
                         (IN1: (in_dec string_Dec mn ms_tgt0: bool) = true),
            False)
    : forall st_src st_tgt fr_src fr_tgt mrs_src mrs_tgt n
             (SIM: sim_itree wf1 ns n
                             (alist_filter (fun mn => in_dec string_Dec mn ms_src1)
                                           mrs_src, fr_src, st_src)
                             (alist_filter (fun mn => in_dec string_Dec mn ms_tgt1)
                                           mrs_tgt, fr_tgt, st_tgt))
             (WF: wf0 (alist_filter (fun mn => in_dec string_Dec mn ms_src0)
                                    mrs_src,
                       alist_filter (fun mn => in_dec string_Dec mn ms_tgt0)
                                    mrs_tgt))
             (NDSRC: NoDup (List.map fst mrs_src))
             (NDTGT: NoDup (List.map fst mrs_tgt)),
      sim_itree
        (add_wf ms_src0 ms_src1 ms_tgt0 ms_tgt1 wf0 wf1) ns n
        (mrs_src, fr_src, st_src) (mrs_tgt, fr_tgt, st_tgt).
  Proof.
    i. ginit. { eapply cpn6_wcompat; eauto with paco. } revert_until DISJTGT. gcofix CIH. i.
    gstep. punfold SIM. inv SIM; pclearbot.
    * econs 1; eauto. econs; eauto.
    * econs 2. gbase. eapply CIH; eauto.
    * econs 3; eauto.
      { econs; eauto. }
      { i. inv WF1. exploit K; eauto. i. des. pclearbot.
        exists i1. gbase. eapply CIH; eauto. }
    * econs 4; eauto.
      i. hexploit K; eauto. i. des. pclearbot. esplits; eauto with paco.
    * econs 5; eauto.
      i. hexploit K; eauto. i. des. pclearbot. esplits; eauto with paco.
    * econs 6; eauto.
      i. hexploit K; eauto. i. des. pclearbot. esplits; eauto with paco.
    * econs 7; eauto.
      { eapply alist_find_filter; eauto. }
      { eapply alist_find_filter; eauto. }
      { gbase. eapply CIH; eauto.
        { repeat erewrite alist_find_add_filter; eauto. }
        { repeat erewrite alist_add_disjoint_filter; eauto.
          { eapply alist_disjoint_find; eauto. }
          { eapply alist_disjoint_find; eauto. }
        }
        { eapply alist_add_nodup; eauto. }
        { eapply alist_add_nodup; eauto. }
      }
    * econs 8; eauto.
      { eapply alist_find_filter; eauto. }
      { eapply alist_find_filter; eauto. }
      { gbase. eapply CIH; eauto.
        { repeat erewrite alist_find_add_filter; eauto. }
        { repeat erewrite alist_add_disjoint_filter; eauto.
          { eapply alist_disjoint_find; eauto. }
          { eapply alist_disjoint_find; eauto. }
        }
        { eapply alist_add_nodup; eauto. }
        { eapply alist_add_nodup; eauto. }
      }
    * econs 9; eauto with paco.
    * econs 10; eauto with paco.
      { eapply alist_find_filter; eauto. }
      { eapply alist_find_filter; eauto. }
    * econs 11; eauto with paco.
      { eapply alist_find_filter; eauto. }
      { eapply alist_find_filter; eauto. }
    * econs 12; eauto with paco.
    * econs 13; eauto with paco.
    * econs 14; eauto with paco.
      i. hexploit K; eauto. i. des. pclearbot. esplits; eauto with paco.
    * econs 15; eauto.
      i. hexploit K; eauto with paco.
    * econs 16; eauto with paco.
      { eapply alist_find_filter; eauto. }
      gbase. eapply CIH; eauto.
      { repeat erewrite alist_find_add_filter; eauto. }
      { repeat erewrite alist_add_disjoint_filter; eauto.
        { eapply alist_disjoint_find; eauto. }
      }
      { eapply alist_add_nodup; eauto. }
    * econs 17; eauto with paco.
      { eapply alist_find_filter; eauto. }
      gbase. eapply CIH; eauto.
      { repeat erewrite alist_find_add_filter; eauto. }
      { repeat erewrite alist_add_disjoint_filter; eauto.
        { eapply alist_disjoint_find; eauto. }
      }
      { eapply alist_add_nodup; eauto. }
    * econs 18; eauto with paco.
    * econs 19; eauto with paco.
      { eapply alist_find_filter; eauto. }
    * econs 20; eauto with paco.
      { eapply alist_find_filter; eauto. }
    * econs 21; eauto with paco.
    * econs 22; eauto with paco.
    * econs 23; eauto.
      i. hexploit K; eauto with paco.
    * econs 24; eauto.
      i. hexploit K; eauto. i. des. pclearbot. esplits; eauto with paco.
    * econs 25; eauto with paco.
      { eapply alist_find_filter; eauto. }
      gbase. eapply CIH; eauto.
      { repeat erewrite alist_find_add_filter; eauto. }
      { repeat erewrite alist_add_disjoint_filter; eauto.
        { eapply alist_disjoint_find; eauto. }
      }
      { eapply alist_add_nodup; eauto. }
    * econs 26; eauto with paco.
      { eapply alist_find_filter; eauto. }
      gbase. eapply CIH; eauto.
      { repeat erewrite alist_find_add_filter; eauto. }
      { repeat erewrite alist_add_disjoint_filter; eauto.
        { eapply alist_disjoint_find; eauto. }
      }
      { eapply alist_add_nodup; eauto. }
    * econs 27; eauto with paco.
    * econs 28; eauto with paco.
      { eapply alist_find_filter; eauto. }
    * econs 29; eauto with paco.
      { eapply alist_find_filter; eauto. }
    * econs 30; eauto with paco.
    * econs 31; eauto.
      { i. exploit K; eauto. i. des. pclearbot. gbase. eapply CIH; eauto. }
  Qed.

  Lemma add_modsempair (ms_src0 ms_src1 ms_tgt0 ms_tgt1: ModSemL.t)
        (WFSRC: ModSemL.wf (ModSemL.add ms_src0 ms_src1))
        (WFTGT: ModSemL.wf (ModSemL.add ms_tgt0 ms_tgt1))
        (SIM0: sim ms_src0 ms_tgt0)
        (SIM1: sim ms_src1 ms_tgt1)
    :
      sim (ModSemL.add ms_src0 ms_src1) (ModSemL.add ms_tgt0 ms_tgt1).
  Proof.
    assert (DISJSRC: forall mn
                            (IN0: (in_dec string_Dec mn (List.map fst (ModSemL.initial_mrs ms_src1)): bool) = true)
                            (IN1: (in_dec string_Dec mn (List.map fst (ModSemL.initial_mrs ms_src0)): bool) = true),
               False).
    { inv WFSRC. ss. rewrite map_app in *.
      i. des_sumbool. eapply app_nodup in wf_initial_mrs; eauto. }
    assert (DISJTGT: forall mn
                            (IN0: (in_dec string_Dec mn (List.map fst (ModSemL.initial_mrs ms_tgt1)): bool) = true)
                            (IN1: (in_dec string_Dec mn (List.map fst (ModSemL.initial_mrs ms_tgt0)): bool) = true),
               False).
    { inv WFTGT. ss. rewrite map_app in *.
      i. des_sumbool. eapply app_nodup in wf_initial_mrs; eauto. }
    destruct SIM0 as [wf0 le0 le_PreOrder0 sim_fnsems0 sim_initial_mrs0].
    destruct SIM1 as [wf1 le1 le_PreOrder1 sim_fnsems1 sim_initial_mrs1].
    eapply mk with (wf:=add_wf (List.map fst ms_src0.(ModSemL.initial_mrs))
                               (List.map fst ms_src1.(ModSemL.initial_mrs))
                               (List.map fst ms_tgt0.(ModSemL.initial_mrs))
                               (List.map fst ms_tgt1.(ModSemL.initial_mrs))
                               wf0 wf1) (le:=top2); ss.
    - eapply Forall2_app.
      + eapply Forall2_impl; [|eauto].
        i. destruct x0 as [fn0 f0]. destruct x1 as [fn1 f1].
        inv PR. split; auto. ii. subst.
        exploit (H0 y); [eauto|..].
        { inv SIMMRS. eapply WF0. } i. des. exists n.
        inv SIMMRS. hexploit add_sim_itree; [| |eauto|..]; eauto.
        i. eapply sim_itree_sym; [..|eauto]. i. destruct w. split.
        * i. eapply add_wf_sym. auto.
        * i. eapply add_wf_sym. auto.
      + eapply Forall2_impl; [|eauto ].
        i. destruct x0 as [fn0 f0]. destruct x1 as [fn1 f1].
        inv PR. split; auto. ii. subst.
        exploit (H0 y); [eauto|..].
        { inv SIMMRS. eapply WF1. } i. des. exists n.
        inv SIMMRS. eapply add_sim_itree; eauto.
    - inv WFSRC. inv WFTGT. econs; eauto.
      + unfold alist_filter. rewrite ! List.filter_app.
        rewrite (@all_true_filter _ (ModSemL.initial_mrs ms_src0)).
        2: { eapply List.Forall_forall. i. des_sumbool. eapply in_map. auto. }
        rewrite (@all_true_filter _ (ModSemL.initial_mrs ms_tgt0)).
        2: { eapply List.Forall_forall. i. des_sumbool. eapply in_map. auto. }
        rewrite (@all_false_filter _ (ModSemL.initial_mrs ms_src1)).
        2: {
          eapply List.Forall_forall. i. des_sumbool. ii.
          eapply DISJSRC; des_sumbool; et. eapply in_map; et.
        }
        rewrite (@all_false_filter _ (ModSemL.initial_mrs ms_tgt1)).
        2: {
          eapply List.Forall_forall. i. des_sumbool. ii.
          eapply DISJTGT; des_sumbool; et. eapply in_map; et.
        }
        rewrite ! List.app_nil_r. auto.
      + unfold alist_filter. rewrite ! List.filter_app.
        rewrite (@all_true_filter _ (ModSemL.initial_mrs ms_src1)).
        2: { eapply List.Forall_forall. i. des_sumbool. eapply in_map. auto. }
        rewrite (@all_true_filter _ (ModSemL.initial_mrs ms_tgt1)).
        2: { eapply List.Forall_forall. i. des_sumbool. eapply in_map. auto. }
        rewrite (@all_false_filter _ (ModSemL.initial_mrs ms_src0)).
        2: {
          eapply List.Forall_forall. i. des_sumbool. ii.
          eapply DISJSRC; des_sumbool; et. eapply in_map; et.
        }
        rewrite (@all_false_filter _ (ModSemL.initial_mrs ms_tgt0)).
        2: {
          eapply List.Forall_forall. i. des_sumbool. ii.
          eapply DISJTGT; des_sumbool; et. eapply in_map; et.
        }
        auto.
  Qed.

End ADD.
End ModSemLPair.




Require Import SimGlobal.



























   Ltac igo := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r; try rewrite bind_tau;
                       try rewrite interp_vis;
                       try rewrite interp_ret;
                       try rewrite interp_tau
                      (* try rewrite interp_trigger *)
                      ).

  Ltac mgo := repeat (try rewrite ! interp_Es_bind; try rewrite ! interp_Es_ret; try rewrite ! interp_Es_tau;
                      try rewrite ! interp_Es_rE; try rewrite ! interp_Es_eventE; try rewrite ! interp_Es_callE;
                      try rewrite ! interp_Es_triggerNB; try rewrite ! interp_Es_triggerUB; igo).
  Ltac mstep := gstep; econs; eauto; [eapply OrdArith.lt_from_nat; ss|].







































Module ModLPair.
Section SIMMOD.
   Context `{Σ: GRA.t}.
   Variable (md_src md_tgt: ModL.t).
   Inductive sim: Prop := mk {
     sim_modsem:
       <<SIM: ModSemLPair.sim (md_src.(ModL.enclose)) (md_tgt.(ModL.enclose))>>;
     sim_sk: <<SIM: md_src.(ModL.sk) = md_tgt.(ModL.sk)>>;
     sim_wf:
       forall sk (INCL: Sk.incl md_src.(ModL.sk) sk) (SKWF: Sk.wf sk) (WF: ModSemL.wf (md_src.(ModL.get_modsem) sk)), <<WF: ModSemL.wf (md_tgt.(ModL.get_modsem) sk)>>;
   }.

   Hint Resolve cpn6_wcompat: paco.

   Definition eqv (mrsl: alist string (Σ * Any.t)) (mrs: string -> Σ) (mps: string -> Any.t): Prop :=
     forall mn mr mp
            (FIND: alist_find mn mrsl = Some (mr, mp)),
       mrs mn = mr /\ mps mn = mp.

   Lemma eqv_lookup_mr mrsl mrs mps (EQV: eqv mrsl mrs mps)
         mn mr mp
         (LOOKUP: alist_find mn mrsl = Some (mr, mp))
     :
       mrs mn = mr.
   Proof.
     eapply EQV in LOOKUP. des; auto.
   Qed.

   Lemma eqv_lookup_mp mrsl mrs mps (EQV: eqv mrsl mrs mps)
         mn mr mp
         (LOOKUP: alist_find mn mrsl = Some (mr, mp))
     :
       mps mn = mp.
   Proof.
     eapply EQV in LOOKUP. des; auto.
   Qed.

   Lemma eqv_add_mr mrsl mrs mps (EQV: eqv mrsl mrs mps)
         mn mr0 mr1 mp0
         (LOOKUP: alist_find mn mrsl = Some (mr0, mp0))
     :
       eqv (alist_add mn (mr1, mp0) mrsl) (update mrs mn mr1) mps.
   Proof.
     ii. unfold update. des_ifs.
     { erewrite alist_add_find_eq in FIND. clarify. split; auto.
       eapply eqv_lookup_mp in LOOKUP; eauto.
     }
     { erewrite alist_add_find_neq in FIND; auto. }
   Qed.

   Lemma eqv_add_ms mrsl mrs mps (EQV: eqv mrsl mrs mps)
         mn mr0 mp0 mp1
         (LOOKUP: alist_find mn mrsl = Some (mr0, mp0))
     :
       eqv (alist_add mn (mr0, mp1) mrsl) mrs (update mps mn mp1).
   Proof.
     ii. unfold update. des_ifs.
     { erewrite alist_add_find_eq in FIND. clarify. split; auto.
       eapply eqv_lookup_mr in LOOKUP; eauto.
     }
     { erewrite alist_add_find_neq in FIND; auto. }
   Qed.

   Variant lift_wf (wf: alist string (Σ * Any.t) * alist string (Σ * Any.t) -> Prop)
           (mrs_src mrs_tgt: string -> Σ) (mps_src mps_tgt: string -> Any.t): Prop :=
   | lift_wf_intro
       mrsl_src mrsl_tgt
       (EQVSRC: eqv mrsl_src mrs_src mps_src)
       (EQVTGT: eqv mrsl_tgt mrs_tgt mps_tgt)
       (WF: wf (mrsl_src, mrsl_tgt))
   .

   Let arith (o: Ord.t) (n0: nat) (n1: nat): Ord.t :=
     (n0 * o + n1)%ord.

   Let arith_lt_1 o0 o1 n0 n1 n2
         (OLT: (o0 < o1)%ord)
         (LT: n1 < n0 + n2)
     :
       Ord.lt (arith o0 n0 n1) (arith o1 n0 n2).
   Proof.
     unfold arith. eapply Ord.lt_le_lt.
     2: {
       eapply OrdArith.le_add_l.
       eapply OrdArith.le_mult_r.
       eapply Ord.S_supremum. eauto.
     }
     eapply Ord.lt_eq_lt.
     { eapply OrdArith.eq_add_l.
       eapply OrdArith.mult_S.
     }
     eapply Ord.lt_eq_lt.
     { eapply OrdArith.add_assoc. }
     eapply OrdArith.lt_add_r.
     eapply Ord.lt_eq_lt.
     { symmetry. eapply OrdArith.add_from_nat.  }
     eapply OrdArith.lt_from_nat. eauto.
   Qed.

   Lemma arith_lt_2 o n0 n1 n2
         (LT: (n1 < n2)%nat)
     :
       Ord.lt (arith o n0 n1) (arith o n0 n2).
   Proof.
     eapply OrdArith.lt_add_r. eapply OrdArith.lt_from_nat. eauto.
   Qed.

   Lemma lift_sim ms_src ms_tgt ns
         (NAMESPACE: forall fn arg (IN: ~ns fn), (ModSemL.prog ms_src) _ (Call fn arg) = triggerUB)
         (wf: alist string (Σ * Any.t) * alist string (Σ * Any.t) -> Prop)
         (FNS: forall fn : string,
             option_rel (sim_fsem wf ns)
                        (alist_find fn (ModSemL.fnsems ms_src))
                        (alist_find fn (ModSemL.fnsems ms_tgt)))
     :
       forall n mrsl_src fr_src f_src mrsl_tgt fr_tgt f_tgt
              (* (WF: wf (mrsl_src, mrsl_tgt)) *)
              (SIM: sim_itree wf ns n (mrsl_src, fr_src, f_src) (mrsl_tgt, fr_tgt, f_tgt))
              mrs_src mrs_tgt mps_src mps_tgt
              (EQVSRC: eqv mrsl_src mrs_src mps_src)
              (EQVTGT: eqv mrsl_tgt mrs_tgt mps_tgt)
              frs_src frs_tgt,
         simg (fun (vret_src vret_tgt: r_state * p_state * Any.t) =>
                 exists fr_src' fr_tgt',
                   (<<WF: lift_wf wf (fst (fst (fst vret_src))) (fst (fst (fst vret_tgt))) (snd (fst vret_src)) (snd (fst vret_tgt))>>) /\
                   (<<FRSRC: snd (fst (fst vret_src)) = fr_src'::frs_src>>) /\
                   (<<FRTGT: snd (fst (fst vret_tgt)) = fr_tgt'::frs_tgt>>) /\
                   (<<VAL: snd vret_src = snd vret_tgt>>)) (arith n 4 4)
              (interp_Es
                 (ModSemL.prog ms_src)
                 f_src
                 (mrs_src, fr_src::frs_src, mps_src))
              (interp_Es
                 (ModSemL.prog ms_tgt)
                 f_tgt
                 (mrs_tgt, fr_tgt::frs_tgt, mps_tgt)).
   Proof.
     ginit. gcofix CIH. i.
     punfold SIM. gstep. Local Opaque interp_Es.
     inv SIM; pclearbot; ss; mgo; ss; mgo.
     - econs; ss. esplits; et. econs; eauto.
     - econs; ss. gbase. eapply CIH; eauto.
     - rewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)).
       rewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)).
       mgo. ss. mgo.

       generalize (FNS fn). i. inv H; cycle 1.
       { unfold ModSemL.prog at 3.
         rewrite <- H1. unfold unwrapU, triggerUB. mgo.
         econs; ss; et.
         gstep. econs; ss; et.
         gstep. econs; ss; et.
         gstep. econs; ss; et.
         instantiate (1:=1). instantiate (1:=0). eapply OrdArith.lt_from_nat; ss.
       }
       mgo. rename a into f_src. rename b into f_tgt.
       exploit IN; eauto. instantiate (2:=varg). i. des.
       econs; et.
       gstep. econs; et.
       gstep. econs; et.
       instantiate (1:=(20 + (arith n0 4 4))%ord).
       gclo. eapply wrespect6_companion; auto with paco.
       { eapply bindC_wrespectful. }
       econs.
       + gbase. eapply CIH; eauto. ss.
         unfold unwrapU. des_ifs. mgo. ss.
       + i. ss. des.
         destruct vret_src as [[mrs_src' frs_src'] val_src].
         destruct vret_tgt as [[mrs_tgt' frs_tgt'] val_tgt].
         destruct mrs_src', mrs_tgt'. ss. subst. mgo. ss. mgo.
         gstep. econs; auto.
         inv WF0. hexploit K; eauto. i. des. pclearbot.
         eapply CIH in H; eauto; ss.
         gstep. econs; auto.
         gstep. econs; auto.
         gbase. eapply H.
     - econs. ii. mgo.
       gstep. econs; auto.
       gstep. econs; auto.
       subst. hexploit K; eauto. i. des. pclearbot.
       eapply CIH in H; eauto; ss.
       gstep. econs; auto.
       gbase. eapply H.
     - econs; eauto. i. hexploit K; eauto. i. des. pclearbot.
       eexists. mgo.
       gstep. econs; auto.
       gstep. econs; auto.
       gstep. econs; auto.
       gbase. eapply CIH; eauto.
     - econs; eauto. i. hexploit K; eauto. i. des. pclearbot.
       eexists. mgo.
       gstep. econs; auto.
       gstep. econs; auto.
       gstep. econs; auto.
       gbase. eapply CIH; eauto.
     - erewrite interp_Es_pE with (rst0:=(mrs_src, fr_src :: frs_src)).
       erewrite interp_Es_pE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       gstep. econs; auto.
       gstep. econs; auto.
       gbase. eapply CIH; eauto.
       { eapply eqv_add_ms; eauto. }
       { eapply eqv_add_ms; eauto. }
     - erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)).
       erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       gstep. econs; auto.
       gbase. eapply CIH; eauto.
       { eapply eqv_add_mr; eauto. }
       { eapply eqv_add_mr; eauto. }
     - erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)).
       erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       gstep. econs; auto.
       gbase. eapply CIH; eauto.
     - eapply eqv_lookup_mp in MRSRC; eauto.
       eapply eqv_lookup_mp in MRTGT; eauto. subst.
       erewrite interp_Es_pE with (rst0:=(mrs_src, fr_src :: frs_src)).
       erewrite interp_Es_pE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       gstep. econs; auto.
       gstep. econs; auto.
       gbase. eapply CIH; eauto.
     - eapply eqv_lookup_mr in MRSRC; eauto.
       eapply eqv_lookup_mr in MRTGT; eauto. subst.
       erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)).
       erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       gstep. econs; auto.
       gbase. eapply CIH; eauto.
     - erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)).
       erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       gstep. econs; auto.
       gbase. eapply CIH; eauto.
     - econs; eauto.
       { eapply arith_lt_1 with (n1:=4); auto.
         - eassumption.
         - clear. lia. }
       gbase. eapply CIH; eauto.
     - des. pclearbot. econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       eexists. mgo. gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=6); auto. }
       gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=5); auto. }
       gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       i. mgo. gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=6); auto. }
       gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=5); auto. }
       gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto. eapply K.
     - erewrite interp_Es_pE with (rst0:=(mrs_src, fr_src :: frs_src)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=6); auto. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
       { eapply eqv_add_ms; eauto. }
     - erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)).  ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
       { eapply eqv_add_mr; eauto. }
     - erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - eapply eqv_lookup_mp in MR0; eauto. subst.
       erewrite interp_Es_pE with (rst0:=(mrs_src, fr_src :: frs_src)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=6); auto. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - eapply eqv_lookup_mr in MR0; eauto. subst.
       erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - erewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - econs; eauto.
       { eapply arith_lt_1 with (n1:=4); auto.
         - eassumption.
         - clear. lia. }
       gbase. eapply CIH; eauto.
     - econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       i. mgo. gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=6); auto. }
       gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=5); auto. }
       gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto. eapply K.
     - des. pclearbot. econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       eexists. mgo. gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=6); auto. }
       gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=5); auto. }
       gstep. econs; eauto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - erewrite interp_Es_pE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=6); auto. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
       { eapply eqv_add_ms; eauto. }
     - erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
       { eapply eqv_add_mr; eauto. }
     - erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - eapply eqv_lookup_mp in MR0; eauto. subst.
       erewrite interp_Es_pE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=6); auto. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - eapply eqv_lookup_mr in MR0; eauto. subst.
       erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
     - erewrite interp_Es_rE with (rst0:=(mrs_tgt, fr_tgt :: frs_tgt)). ss. mgo.
       econs; eauto.
       { eapply arith_lt_1 with (n1:=7); auto.
         - eassumption. }
       gstep. econs; auto.
       { eapply arith_lt_2 with (n1:=4); auto. }
       gbase. eapply CIH; eauto.
       Unshelve. all: exact O.
     - destruct (classic (ns fn)).
       + exploit K; et. i; des. pclearbot. gbase.

       rewrite interp_Es_rE with (rst0:=(mrs_src, fr_src :: frs_src)).
       mgo. ss. mgo.
       econs; et.
       { eapply arith_lt_2 with (n1:=3); auto. }
       gstep. econs; et.
       { eapply arith_lt_2 with (n1:=2); auto. }
       gstep. econs; et.
       { eapply arith_lt_1 with (n1:=4); eauto. cbn. lia. }

       destruct (classic (ns fn)).
       + exploit K; et. i; des. pclearbot. gbase.
         match goal with
         | |- r _ _ _ _ ?src _ =>
           replace src with (interp_Es (ModSemL.prog ms_src) (trigger (Call fn varg) >>=
         end.
         eapply CIH.

       generalize (FNS fn). i. inv H; cycle 1.
       { unfold ModSemL.prog at 3.
         rewrite <- H1. unfold unwrapU, triggerUB. mgo.
         econs; ss; et.
         gstep. econs; ss; et.
         gstep. econs; ss; et.
         gstep. econs; ss; et.
         instantiate (1:=1). instantiate (1:=0). eapply OrdArith.lt_from_nat; ss.
       }
       mgo. rename a into f_src. rename b into f_tgt.
       exploit IN; eauto. instantiate (2:=varg). i. des.
       econs; et.
       gstep. econs; et.
       gstep. econs; et.
       instantiate (1:=(20 + (arith n0 4 4))%ord).
       gclo. eapply wrespect6_companion; auto with paco.
       { eapply bindC_wrespectful. }
       econs.
       + gbase. eapply CIH; eauto. ss.
         unfold unwrapU. des_ifs. mgo. ss.
       + i. ss. des.
         destruct vret_src as [[mrs_src' frs_src'] val_src].
         destruct vret_tgt as [[mrs_tgt' frs_tgt'] val_tgt].
         destruct mrs_src', mrs_tgt'. ss. subst. mgo. ss. mgo.
         gstep. econs; auto.
         inv WF0. hexploit K; eauto. i. des. pclearbot.
         eapply CIH in H; eauto; ss.
         gstep. econs; auto.
         gstep. econs; auto.
         gbase. eapply H.
   Qed.


   Theorem adequacy_local_closed
           (SIM: sim)
     :
       Beh.of_program (ModL.compile md_tgt) <1=
       Beh.of_program (ModL.compile md_src)
   .
   Proof.
     inv SIM. inv sim_modsem0. red in sim_sk0.
     unfold ModL.enclose in *.

     eapply adequacy_global; et. exists (OrdArith.add Ord.O Ord.O).
     unfold ModSemL.initial_itr, ModSemL.initial_itr_arg, ModL.enclose.

     assert (FNS: forall fn : string,
                option_rel (sim_fsem wf)
                           (alist_find fn
                                       (ModSemL.fnsems (ModL.get_modsem md_src (Sk.sort (ModL.sk md_src)))))
                           (alist_find fn
                                       (ModSemL.fnsems (ModL.get_modsem md_tgt (Sk.sort (ModL.sk md_tgt)))))).
     { rewrite <- sim_sk0 in *.
       remember (ModSemL.fnsems (ModL.get_modsem md_src (Sk.sort (ModL.sk md_src)))).
       remember (ModSemL.fnsems (ModL.get_modsem md_tgt (Sk.sort (ModL.sk md_src)))).
       clear - sim_fnsems. induction sim_fnsems; ss.
       i. inv H. destruct x, y. inv H0. ss. subst.
       rewrite ! eq_rel_dec_correct. des_ifs; eauto.
     }

     ginit. unfold assume. mgo.
     generalize (FNS "main"). i. inv H; cycle 1.
     { gstep. econs; eauto. i. esplits; eauto.
       { inv x_src. red. unfold ModL.enclose in *. rewrite <- sim_sk0.
         split; et. eapply sim_wf0; et.
         eapply Sk.sort_incl. eapply Sk.sort_wf. assumption. } clear x_src.
       ss. unfold ITree.map, unwrapU, triggerUB.
       mgo. rewrite <- H1. mgo.
       des_ifs_safe.
       mgo. gstep. econs; eauto. ss. }
     exploit IN; eauto. i. des.

     gstep. econs; eauto. i. esplits; eauto.
     { inv x_src. red. unfold ModL.enclose in *. rewrite <- sim_sk0.
       split; et. eapply sim_wf0; et. eapply Sk.sort_incl.
       eapply Sk.sort_wf. assumption. } clear x_src.
     ss. unfold ITree.map, unwrapU, triggerUB. mgo.
     des_ifs_safe. ss. mgo.
     guclo bindC_spec. econs.
     { gfinal. right. eapply lift_sim.
       { eapply FNS. }
       { eapply x. }
       { ii. unfold ModSemL.initial_p_state. des_ifs. }
       { ii. rewrite sim_sk0 in *. unfold ModSemL.initial_p_state. des_ifs. }
     }
     { i. ss. des.
       destruct vret_src as [[[mrs_src frs_src] p_src] v_src].
       destruct vret_tgt as [[[mrs_tgt frs_tgt] p_tgt] v_tgt]. ss. subst.
       mgo. ss. mgo.
       gstep. econs; eauto.
     }
     Unshelve. all: exact Ord.O.
   Qed.

End SIMMOD.

End ModLPair.
