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

From Ordinal Require Import Ordinal Arithmetic.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.







Print function_Map. (*** TODO: use Dec. Move to proper place ***)

Global Instance Dec_RelDec K `{Dec K}: @RelDec K eq :=
  { rel_dec := dec }.

Global Instance Dec_RelDec_Correct K `{Dec K}: RelDec_Correct Dec_RelDec.
Proof.
  unfold Dec_RelDec. ss.
  econs. ii. ss. unfold Dec_RelDec. split; ii.
  - unfold rel_dec in *. unfold sumbool_to_bool in *. des_ifs.
  - unfold rel_dec in *. unfold sumbool_to_bool in *. des_ifs.
Qed.









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
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), (trigger PushFrame;; r <- trigger (Call fn varg);; trigger PopFrame;; tau;; k_src r))
                 ((mrs_tgt0, fr_tgt0), (trigger PushFrame;; r <- trigger (Call fn varg);; trigger PopFrame;; tau;; k_tgt r))
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
      (MRSRC: Maps.lookup mn mrs_src0 = Some (mr_src0, mp_src0))
      (MRTGT: Maps.lookup mn mrs_tgt0 = Some (mr_tgt0, mp_tgt0))
      (EQSRC: mrs_src1 = Maps.add mn (mr_src0, mp_src1) mrs_src0)
      (EQTGT: mrs_tgt1 = Maps.add mn (mr_tgt0, mp_tgt1) mrs_tgt0)
      (K: sim_itree _ _ RR i1 ((mrs_src1, fr_src0), k_src tt) ((mrs_tgt1, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (PPut mn mp_src1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (PPut mn mp_tgt1) >>= k_tgt)
  | sim_itree_mput_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mn mr_src0 mr_tgt0 mr_src1 mr_tgt1 mrs_src1 mrs_tgt1 mp_src0 mp_tgt0
      (MRSRC: Maps.lookup mn mrs_src0 = Some (mr_src0, mp_src0))
      (MRTGT: Maps.lookup mn mrs_tgt0 = Some (mr_tgt0, mp_tgt0))
      (EQSRC: mrs_src1 = Maps.add mn (mr_src1, mp_src0) mrs_src0)
      (EQSRC: mrs_tgt1 = Maps.add mn (mr_tgt1, mp_tgt0) mrs_tgt0)
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
      (MRSRC: Maps.lookup mn mrs_src0 = Some (mr_src0, mp_src0))
      (MRTGT: Maps.lookup mn mrs_tgt0 = Some (mr_tgt0, mp_tgt0))
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src mp_src0) ((mrs_tgt0, fr_tgt0), k_tgt mp_tgt0))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (PGet mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (PGet mn) >>= k_tgt)
  | sim_itree_mget_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mn mr_src0 mp_src0 mr_tgt0 mp_tgt0
      (MRSRC: Maps.lookup mn mrs_src0 = Some (mr_src0, mp_src0))
      (MRTGT: Maps.lookup mn mrs_tgt0 = Some (mr_tgt0, mp_tgt0))
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
      (MR0: Maps.lookup mn mrs_src0 = Some (mr0, mp0))
      (EQ: mrs_src1 = Maps.add mn (mr0, mp1) mrs_src0)
      (K: sim_itree _ _ RR i1 ((mrs_src1, fr_src0), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (PPut mn mp1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_mput_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      mn mr0 mr1 mrs_src1 mp0
      (MR0: Maps.lookup mn mrs_src0 = Some (mr0, mp0))
      (EQ: mrs_src1 = Maps.add mn (mr1, mp0) mrs_src0)
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
      (MR0: Maps.lookup mn mrs_src0 = Some (mr0, mp0))
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), k_src mp0) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), trigger (PGet mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_mget_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: Ord.lt i1 i0)
      mn mr0 mp0
      (MR0: Maps.lookup mn mrs_src0 = Some (mr0, mp0))
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
      (MR0: Maps.lookup mn mrs_tgt0 = Some (mr0, mp0))
      (EQ: mrs_tgt1 = Maps.add mn (mr0, mp1) mrs_tgt0)
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt1, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (PPut mn mp1) >>= k_tgt)
  | sim_itree_mput_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: Ord.lt i1 i0)
      mn mr0 mr1 mrs_tgt1 mp0
      (MR0: Maps.lookup mn mrs_tgt0 = Some (mr0, mp0))
      (EQ: mrs_tgt1 = Maps.add mn (mr1, mp0) mrs_tgt0)
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
      (MR0: Maps.lookup mn mrs_tgt0 = Some (mr0, mp0))
      (K: sim_itree _ _ RR i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt mp0))
    :
      _sim_itree sim_itree RR i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (PGet mn) >>= k_tgt)
  | sim_itree_mget_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: Ord.lt i1 i0)
      mn mr0 mp0
      (MR0: Maps.lookup mn mrs_tgt0 = Some (mr0, mp0))
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
    + replace (x <- (trigger PushFrame;; r0 <- trigger (Call fn varg);; trigger PopFrame;; (tau;; k_src0 r0));; k_src x) with
          (trigger PushFrame;; r <- trigger (Call fn varg);; trigger PopFrame;; tau;; (k_src0 >=> k_src) r); cycle 1.
      { grind. }
      replace (x <- (trigger PushFrame;; r0 <- trigger (Call fn varg);; trigger PopFrame;; (tau;; k_tgt0 r0));; k_tgt x) with
          (trigger PushFrame;; r <- trigger (Call fn varg);; trigger PopFrame;; tau;; (k_tgt0 >=> k_tgt) r); cycle 1.
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
Qed.

Definition wf_mrs `{Σ: GRA.t} (ms: list mname) (mrs: alist mname (Σ * Any.t)): Prop :=
  forall mn (IN: List.In mn ms),
  exists mr mp, <<FIND: Maps.lookup mn mrs = Some (mr, mp)>>.

Lemma wf_mrs_add `{Σ: GRA.t} (ms: list mname) (mrs: alist mname (Σ * Any.t))
      (WF: wf_mrs ms mrs)
      mn mr:
  wf_mrs ms (Maps.add mn mr mrs).
Proof.
  ii. destruct (string_Dec mn mn0).
  - subst. destruct mr as [mr mp]. exists mr, mp. eapply mapsto_lookup.
    eapply mapsto_add_eq.
  - hexploit (WF mn0); auto. i. des.
    exists mr0, mp. eapply mapsto_lookup.
    erewrite <- mapsto_add_neq; eauto.
Qed.

Lemma self_sim_itree `{Σ: GRA.t} (ms: list mname):
  forall n mrs fr st
         (WF: wf_function ms st)
         (MRS: wf_mrs ms mrs),
    @sim_itree _ (fun p => fst p = snd p /\ wf_mrs ms (fst p))
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
    sim_fnsems: Forall2 (sim_fnsem wf) ms_src.(ModSemL.fnsems) ms_tgt.(ModSemL.fnsems);
    sim_initial_mrs: wf (ms_src.(ModSemL.initial_mrs), ms_tgt.(ModSemL.initial_mrs));
  }.

End SIMMODSEML.

Lemma self_sim_mod `{Σ: GRA.t} (ms: ModSemL.t) (WF: wf_mod ms):
  sim ms ms.
Proof.
  eapply mk with (wf:=fun p => fst p = snd p /\ wf_mrs (List.map fst ms.(ModSemL.initial_mrs)) (fst p)) (le:=top2); ss.
  2: {
    split; auto. ii. eapply in_map_iff in IN. des. subst. admit "ez".
  }
  unfold wf_mod in *. des.
  revert WFFUN. generalize (ModSemL.fnsems ms).
  induction l; i; ss. inv WFFUN. destruct a. econs; eauto.
  econs; ss. ii. subst. ss. des. subst.
  exists 0. eapply self_sim_itree; eauto.
Qed.

Section ADD.
  Context `{Σ: GRA.t}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).

  Variant add_wf
          (ms_src0 ms_src1 ms_tgt0 ms_tgt1: list mname)
          (wf0 wf1: W -> Prop):
    W -> Prop :=
  | add_wf_intro
      mrs_src mrs_tgt
      (WF0: wf0 (filter _ (fun mn _ => in_dec string_Dec mn ms_src0) mrs_src,
                 filter _ (fun mn _ => in_dec string_Dec mn ms_tgt0) mrs_tgt))
      (WF1: wf1 (filter _ (fun mn _ => in_dec string_Dec mn ms_src1) mrs_src,
                 filter _ (fun mn _ => in_dec string_Dec mn ms_tgt1) mrs_tgt))
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
        n ms_src ms_tgt
        (SIM: sim_itree wf0 n ms_src ms_tgt)
    :
      sim_itree wf1 n ms_src ms_tgt.
  Proof.
    assert (EQV0: forall w, wf0 w -> wf1 w).
    { i. apply EQV. auto. }
    assert (EQV1: forall w, wf1 w -> wf0 w).
    { i. apply EQV. auto. } clear EQV.
    revert n ms_src ms_tgt SIM. pcofix CIH. i. pfold.
    punfold SIM. inv SIM; pclearbot.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto. i.
      clear WF. hexploit K; eauto. i. des. pclearbot. eauto.
    - econs 4; eauto. i.
      hexploit K; eauto. i. des. pclearbot. esplits; eauto.
    - econs 5; eauto. i.
      hexploit K; eauto. i. des. pclearbot. esplits; eauto.
    - econs 6; eauto. i.
      hexploit K; eauto. i. des. pclearbot. esplits; eauto.
    - econs 7; eauto.
    - econs 8; eauto.
    - econs 9; eauto.
    - econs 10; eauto.
    - econs 11; eauto.
    - econs 12; eauto.
    - econs 13; eauto.
    - econs 14; eauto. des. pclearbot. esplits; eauto.
    - econs 15; eauto. i. hexploit K; eauto.
    - econs 16; eauto.
    - econs 17; eauto.
    - econs 18; eauto.
    - econs 19; eauto.
    - econs 20; eauto.
    - econs 21; eauto.
    - econs 22; eauto.
    - econs 23; eauto. i. hexploit K; eauto.
    - econs 24; eauto. des. pclearbot. esplits; eauto.
    - econs 25; eauto.
    - econs 26; eauto.
    - econs 27; eauto.
    - econs 28; eauto.
    - econs 29; eauto.
    - econs 30; eauto.
  Qed.

  Lemma lookup_filter ms (mrs: alist mname (Σ * Any.t)) mn mr
        (LOOK: lookup mn (filter _ (fun mn _ => in_dec string_Dec mn ms) mrs) = Some mr)
        (ND: NoDup (List.map fst mrs))
    :
      lookup mn mrs = Some mr.
  Proof.
  Admitted.

  Lemma add_filter ms (mrs: alist mname (Σ * Any.t)) mn mr0 mr
        (LOOK: lookup mn (filter _ (fun mn _ => in_dec string_Dec mn ms) mrs) = Some mr0)
        (ND: NoDup (List.map fst mrs))
    :
      filter _ (fun mn _ => in_dec string_Dec mn ms) (add mn mr mrs) =
      add mn mr (filter _ (fun mn _ => in_dec string_Dec mn ms) mrs).
  Proof.
  Admitted.

  Lemma add_other_filter ms0 ms1 (mrs: alist mname (Σ * Any.t)) mn mr mr0
        (LOOK: lookup mn (filter _ (fun mn _ => in_dec string_Dec mn ms0) mrs) = Some mr0)
        (ND: forall mn' mr0' mr1'
                    (IN0: lookup mn' (filter _ (fun mn _ => in_dec string_Dec mn ms0) mrs) = Some mr0')
                    (IN1: lookup mn' (filter _ (fun mn _ => in_dec string_Dec mn ms1) mrs) = Some mr1'),
            False)
    :
      filter _ (fun mn _ => in_dec string_Dec mn ms1) (add mn mr mrs) =
      filter _ (fun mn _ => in_dec string_Dec mn ms1) mrs.
  Proof.
  Admitted.

  Lemma nodup_add (mrs: alist mname (Σ * Any.t)) mn mr0 mr1
        (ND: NoDup (List.map fst mrs))
        (FIND: lookup mn mrs = Some mr0)
    :
      NoDup (List.map fst (add mn mr1 mrs)).
  Proof.
  Admitted.

  Lemma nodup_disjoint ms0 ms1 (mrs: alist mname (Σ * Any.t))
        (DISJOINT: forall mn (IN0: List.In mn ms0) (IN1: List.In mn ms1), False)
    :
      forall mn mr0 mr1
             (IN0: lookup mn (filter _ (fun mn _ => in_dec string_Dec mn ms0) mrs) = Some mr0)
             (IN1: lookup mn (filter _ (fun mn _ => in_dec string_Dec mn ms1) mrs) = Some mr1),
        False.
  Proof.
  Admitted.

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

  Lemma disjoint_filter_l (mrs0 mrs1: alist mname (Σ * Any.t))
        (DISJSRC: forall mn
                         (IN0: In mn (List.map fst mrs0))
                         (IN1: In mn (List.map fst mrs1)),
            False)
    :
      filter _ (fun mn _ => in_dec string_Dec mn (List.map fst mrs0)) (mrs0 ++ mrs1) = mrs0.
  Proof.
  Admitted.

  Lemma disjoint_filter_r (mrs0 mrs1: alist mname (Σ * Any.t))
        (DISJSRC: forall mn
                         (IN0: In mn (List.map fst mrs0))
                         (IN1: In mn (List.map fst mrs1)),
            False)
    :
      filter _ (fun mn _ => in_dec string_Dec mn (List.map fst mrs1)) (mrs0 ++ mrs1) = mrs1.
  Proof.
  Admitted.

  Lemma add_sim_itree ms_src0 ms_src1 ms_tgt0 ms_tgt1 (wf0 wf1: W -> Prop)
        (DISJSRC: forall mn
                         (IN0: In mn ms_src1)
                         (IN1: In mn ms_src0),
            False)
        (DISJTGT: forall mn
                         (IN0: In mn ms_tgt1)
                         (IN1: In mn ms_tgt0),
            False)
    : forall st_src st_tgt fr_src fr_tgt mrs_src mrs_tgt n
             (SIM: sim_itree wf1 n
                             (filter _ (fun mn _ => in_dec string_Dec mn ms_src1)
                                     mrs_src, fr_src, st_src)
                             (filter _ (fun mn _ => in_dec string_Dec mn ms_tgt1)
                                     mrs_tgt, fr_tgt, st_tgt))
             (WF: wf0 (filter _ (fun mn _ => in_dec string_Dec mn ms_src0)
                              mrs_src,
                       filter _ (fun mn _ => in_dec string_Dec mn ms_tgt0)
                              mrs_tgt))
             (NDSRC: NoDup (List.map fst mrs_src))
             (NDTGT: NoDup (List.map fst mrs_tgt)),
      sim_itree
        (add_wf ms_src0 ms_src1 ms_tgt0 ms_tgt1 wf0 wf1) n
        (mrs_src, fr_src, st_src) (mrs_tgt, fr_tgt, st_tgt).
  Proof.
    pcofix CIH. i.
    pfold. punfold SIM. inv SIM; pclearbot.
    * econs 1; eauto. econs; eauto.
    * econs 2. right. eapply CIH; eauto.
    * econs 3; eauto.
      { econs; eauto. }
      { i. inv WF1. exploit K; eauto. i. des. pclearbot.
        exists i1. right. eapply CIH; eauto. }
    * econs 4; eauto.
      i. hexploit K; eauto. i. des. pclearbot. esplits; eauto.
    * econs 5; eauto.
      i. hexploit K; eauto. i. des. pclearbot. esplits; eauto.
    * econs 6; eauto.
      i. hexploit K; eauto. i. des. pclearbot. esplits; eauto.
    * econs 7; eauto.
      { eapply lookup_filter; eauto. }
      { eapply lookup_filter; eauto. }
      { right. eapply CIH; eauto.
        { repeat erewrite add_filter; eauto. }
        { repeat erewrite add_other_filter; eauto.
          { eapply nodup_disjoint; eauto. }
          { eapply nodup_disjoint; eauto. }
        }
        { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
        { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
      }
    * econs 8; eauto.
      { eapply lookup_filter; eauto. }
      { eapply lookup_filter; eauto. }
      { right. eapply CIH; eauto.
        { repeat erewrite add_filter; eauto. }
        { repeat erewrite add_other_filter; eauto.
          { eapply nodup_disjoint; eauto. }
          { eapply nodup_disjoint; eauto. }
        }
        { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
        { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
      }
    * econs 9; eauto.
    * econs 10; eauto.
      { eapply lookup_filter; eauto. }
      { eapply lookup_filter; eauto. }
    * econs 11; eauto.
      { eapply lookup_filter; eauto. }
      { eapply lookup_filter; eauto. }
    * econs 12; eauto.
    * econs 13; eauto.
    * econs 14; eauto.
      i. hexploit K; eauto. i. des. pclearbot. esplits; eauto.
    * econs 15; eauto.
      i. hexploit K; eauto.
    * econs 16; eauto.
      { eapply lookup_filter; eauto. }
      right. eapply CIH; eauto.
      { repeat erewrite add_filter; eauto. }
      { repeat erewrite add_other_filter; eauto.
        { eapply nodup_disjoint; eauto. }
      }
      { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
    * econs 17; eauto.
      { eapply lookup_filter; eauto. }
      right. eapply CIH; eauto.
      { repeat erewrite add_filter; eauto. }
      { repeat erewrite add_other_filter; eauto.
        { eapply nodup_disjoint; eauto. }
      }
      { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
    * econs 18; eauto.
    * econs 19; eauto.
      { eapply lookup_filter; eauto. }
    * econs 20; eauto.
      { eapply lookup_filter; eauto. }
    * econs 21; eauto.
    * econs 22; eauto.
    * econs 23; eauto.
      i. hexploit K; eauto.
    * econs 24; eauto.
      i. hexploit K; eauto. i. des. pclearbot. esplits; eauto.
    * econs 25; eauto.
      { eapply lookup_filter; eauto. }
      right. eapply CIH; eauto.
      { repeat erewrite add_filter; eauto. }
      { repeat erewrite add_other_filter; eauto.
        { eapply nodup_disjoint; eauto. }
      }
      { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
    * econs 26; eauto.
      { eapply lookup_filter; eauto. }
      right. eapply CIH; eauto.
      { repeat erewrite add_filter; eauto. }
      { repeat erewrite add_other_filter; eauto.
        { eapply nodup_disjoint; eauto. }
      }
      { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
    * econs 27; eauto.
    * econs 28; eauto.
      { eapply lookup_filter; eauto. }
    * econs 29; eauto.
      { eapply lookup_filter; eauto. }
    * econs 30; eauto.
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
                            (IN0: In mn (List.map fst (ModSemL.initial_mrs ms_src1)))
                            (IN1: In mn (List.map fst (ModSemL.initial_mrs ms_src0))),
               False).
    { inv WFSRC. ss. rewrite map_app in *.
      i. eapply app_nodup in wf_initial_mrs; eauto. }
    assert (DISJTGT: forall mn
                            (IN0: In mn (List.map fst (ModSemL.initial_mrs ms_tgt1)))
                            (IN1: In mn (List.map fst (ModSemL.initial_mrs ms_tgt0))),
               False).
    { inv WFTGT. ss. rewrite map_app in *.
      i. eapply app_nodup in wf_initial_mrs; eauto. }
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
      + rewrite disjoint_filter_l; eauto.
        rewrite disjoint_filter_l; eauto.
      + rewrite disjoint_filter_r; eauto.
        rewrite disjoint_filter_r; eauto.
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







































  Variant option_rel A B (P: A -> B -> Prop): option A -> option B -> Prop :=
  | option_rel_some
      a b (IN: P a b)
    :
      option_rel P (Some a) (Some b)
  | option_rel_none
    :
      option_rel P None None
  .
  Hint Constructors option_rel: core.


Module ModLPair.
Section SIMMOD.
   Context `{Σ: GRA.t}.
   Variable (md_src md_tgt: ModL.t).
   Inductive sim: Prop := mk {
     sim_modsem:
       forall sk, <<SIM: ModSemLPair.sim (md_src.(ModL.get_modsem) sk) (md_tgt.(ModL.get_modsem) sk)>>;
     sim_sk: <<SIM: md_src.(ModL.sk) = md_tgt.(ModL.sk)>>;
     sim_wf:
       forall skenv (WF: ModSemL.wf (md_src.(ModL.get_modsem) skenv)), <<WF: ModSemL.wf (md_tgt.(ModL.get_modsem) skenv)>>;
   }.

   Hint Resolve cpn5_wcompat: paco.

   Definition eqv (mrsl: alist string (Σ * Any.t)) (mrs: string -> Σ) (mps: string -> Any.t): Prop :=
     forall mn mn' mr mp
            (FIND: find (fun mnr : string * (Σ * Any.t) => dec mn (fst mnr)) mrsl = Some (mn', (mr, mp))),
       mrs mn = mr /\ mps mn = mp.

   Lemma lookup_find (mrsl: alist string (Σ * Any.t)) mn mr
         (LOOKUP: Maps.lookup mn mrsl = Some mr)
     :
       find (fun mnr : string * (Σ * Any.t) => dec mn (fst mnr)) mrsl = Some (mn, mr).
   Proof.
     induction mrsl; ss. unfold sumbool_to_bool. des_ifs; ss; eauto.
     { eapply neg_rel_dec_correct in Heq0. ss. }
     { rewrite rel_dec_correct in Heq0. ss. }
   Qed.

   Lemma find_lookup (mrsl: alist string (Σ * Any.t)) mn0 mn1 mr
         (FIND: find (fun mnr : string * (Σ * Any.t) => dec mn0 (fst mnr)) mrsl = Some (mn1, mr))
     :
       mn0 = mn1 /\ Maps.lookup mn0 mrsl = Some mr.
   Proof.
     induction mrsl; ss.
     unfold sumbool_to_bool in *. des_ifs; auto.
     { rewrite rel_dec_correct in Heq. ss. }
     { eapply neg_rel_dec_correct in Heq. ss. }
   Qed.

   Lemma eqv_lookup_mr mrsl mrs mps (EQV: eqv mrsl mrs mps)
         mn mr mp
         (LOOKUP: Maps.lookup mn mrsl = Some (mr, mp))
     :
       mrs mn = mr.
   Proof.
     eapply lookup_find in LOOKUP.
     eapply EQV in LOOKUP. des; auto.
   Qed.

   Lemma eqv_lookup_mp mrsl mrs mps (EQV: eqv mrsl mrs mps)
         mn mr mp
         (LOOKUP: Maps.lookup mn mrsl = Some (mr, mp))
     :
       mps mn = mp.
   Proof.
     eapply lookup_find in LOOKUP.
     eapply EQV in LOOKUP. des; auto.
   Qed.

   Lemma eqv_add_mr mrsl mrs mps (EQV: eqv mrsl mrs mps)
         mn mr0 mr1 mp0
         (LOOKUP: Maps.lookup mn mrsl = Some (mr0, mp0))
     :
       eqv (Maps.add mn (mr1, mp0) mrsl) (update mrs mn mr1) mps.
   Proof.
     ii. eapply find_lookup in FIND. des; subst.
     simpl. unfold update. des_ifs.
     { assert (lookup mn' (add mn' (mr1, mp0) mrsl) = Some (mr1, mp0)).
       { eapply mapsto_lookup. eapply mapsto_add_eq. }
       clarify. split; auto. eapply eqv_lookup_mp in LOOKUP; eauto.
     }
     { split.
       { eapply eqv_lookup_mr; eauto. eapply mapsto_lookup in FIND0.
         eapply mapsto_lookup. eapply mapsto_add_neq; eauto. }
       { eapply eqv_lookup_mp; eauto. eapply mapsto_lookup in FIND0.
         eapply mapsto_lookup. eapply mapsto_add_neq; eauto. }
     }
   Qed.

   Lemma eqv_add_ms mrsl mrs mps (EQV: eqv mrsl mrs mps)
         mn mr0 mp0 mp1
         (LOOKUP: Maps.lookup mn mrsl = Some (mr0, mp0))
     :
       eqv (Maps.add mn (mr0, mp1) mrsl) mrs (update mps mn mp1).
   Proof.
     ii. eapply find_lookup in FIND. des; subst.
     simpl. unfold update. des_ifs.
     { assert (lookup mn' (add mn' (mr0, mp1) mrsl) = Some (mr0, mp1)).
       { eapply mapsto_lookup. eapply mapsto_add_eq. }
       clarify. split; auto. eapply eqv_lookup_mr in LOOKUP; eauto.
     }
     { split.
       { eapply eqv_lookup_mr; eauto. eapply mapsto_lookup in FIND0.
         eapply mapsto_lookup. eapply mapsto_add_neq; eauto. }
       { eapply eqv_lookup_mp; eauto. eapply mapsto_lookup in FIND0.
         eapply mapsto_lookup. eapply mapsto_add_neq; eauto. }
     }
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

   Lemma lift_sim ms_src ms_tgt
         (wf: alist string (Σ * Any.t) * alist string (Σ * Any.t) -> Prop)
         (FNS: forall fn : string,
             option_rel (sim_fnsem wf)
                        (find (fun fnsem : string * (Any.t -> itree Es Any.t) => dec fn (fst fnsem))
                              (ModSemL.fnsems ms_src))
                        (find (fun fnsem : string * (Any.t -> itree Es Any.t) => dec fn (fst fnsem))
                              (ModSemL.fnsems ms_tgt)))
     :
       forall n mrsl_src fr_src f_src mrsl_tgt fr_tgt f_tgt
              (* (WF: wf (mrsl_src, mrsl_tgt)) *)
              (SIM: sim_itree wf n (mrsl_src, fr_src, f_src) (mrsl_tgt, fr_tgt, f_tgt))
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
       { unfold ModSemL.prog at 3. mgo. unfold unwrapU. des_ifs_safe. mgo. unfold triggerUB. mgo.
         econs; ss; et.
         gstep. econs; ss; et.
         gstep. econs; ss; et.
         gstep. econs; ss; et.
         instantiate (1:=1). instantiate (1:=0). eapply OrdArith.lt_from_nat; ss.
       }
       mgo.
       destruct a as [fn_src f_src]. destruct b as [fn_tgt f_tgt].
       inv IN. inv H. simpl in H1. clarify.
       exploit H0; eauto. instantiate (2:=varg). i. des.
       econs; et.
       gstep. econs; et.
       gstep. econs; et.
       instantiate (1:=(20 + (arith n0 4 4))%ord).
       gclo. eapply wrespect5_companion; auto with paco.
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
   Qed.


   Theorem adequacy_local_closed
           (SIM: sim)
     :
       Beh.of_program (ModL.compile md_tgt) <1=
       Beh.of_program (ModL.compile md_src)
   .
   Proof.
     inv SIM. specialize (sim_modsem0 (ModL.sk md_src)).
     inv sim_modsem0. red in sim_sk0.

     eapply adequacy_global; et. exists (OrdArith.add Ord.O Ord.O).
     unfold ModSemL.initial_itr, ModL.enclose.

     assert (FNS: forall fn : string,
                option_rel (sim_fnsem wf)
                           (find (fun fnsem : string * (Any.t -> itree Es Any.t) => dec fn (fst fnsem))
                                 (ModSemL.fnsems (ModL.get_modsem md_src (ModL.sk md_src))))
                           (find (fun fnsem : string * (Any.t -> itree Es Any.t) => dec fn (fst fnsem))
                                 (ModSemL.fnsems (ModL.get_modsem md_tgt (ModL.sk md_tgt))))).
     { rewrite <- sim_sk0 in *.
       remember (ModSemL.fnsems (ModL.get_modsem md_src (ModL.sk md_src))).
       remember (ModSemL.fnsems (ModL.get_modsem md_tgt (ModL.sk md_src))).
       clear - sim_fnsems. induction sim_fnsems; ss.
       i. unfold sumbool_to_bool. des_ifs; eauto.
       - inv H. ss.
       - inv H. exfalso. eapply n. ss.
     }

     ginit. unfold assume. mgo.
     generalize (FNS "main"). i. inv H; cycle 1.
     { gstep. econs; eauto. i. esplits; eauto.
       { eapply sim_wf0. rewrite sim_sk0 in *. ss. } clear x_src.
       ss. unfold ITree.map, unwrapU, triggerUB. mgo.
       des_ifs_safe.
       mgo. gstep. econs; eauto. ss. }
     destruct a, b. inv IN. mgo.
     exploit H0; eauto. i. des.


     gstep. econs; eauto. i. esplits; eauto.
     { eapply sim_wf0. rewrite sim_sk0 in *. ss. } clear x_src.
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

   (* Theorem adequacy_local *)
   (*         (SIM: sim) *)
   (*         (*** You will need some wf conditions for ctx ***) *)
   (*   : *)
   (*     <<CR: forall ctx, Beh.of_program (Mod.compile (Mod.add ctx md_tgt)) <1= *)
   (*                       Beh.of_program (Mod.compile (Mod.add ctx md_src))>> *)
   (* . *)
   (* Proof. *)
   (*   ii. eapply adequacy_global; et. exists Ordinal.O. *)
   (*   admit "TODO". *)
   (* Qed. *)

End SIMMOD.

Section SIMMOD.
   Context `{Σ: GRA.t}.

   Theorem adequacy_local md_src md_tgt
           (SIM: sim md_src md_tgt)
     (*** You will need some wf conditions for ctx ***)
     :
       <<CR: forall ctx, Beh.of_program (ModL.compile (ModL.add ctx md_tgt)) <1=
                         Beh.of_program (ModL.compile (ModL.add ctx md_src))>>
   .
   Proof.
     ii. eapply adequacy_local_closed; eauto. econs.
     { ss. red. ii. eapply ModSemLPair.add_modsempair.
       { admit "ModSemL wf". }
       { admit "ModSemL wf". }
       { eapply ModSemLPair.self_sim_mod. admit "ModSemL wf". }
       { eapply SIM. }
     }
     { ss. red. f_equal. eapply SIM. }
     { ii. red. ss. admit "ModSemL wf". }
   Qed.
End SIMMOD.

End ModLPair.

(* TODO: prove sim *)
(* TODO: write client *)
(* TODO: show cancellation *)
(* TODO: meta-level (no forge -> checkwf always succeeds) *)
