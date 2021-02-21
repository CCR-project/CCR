Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem.
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

  Variant _sim_itree (sim_itree: nat -> relation (st_local * (itree Es Any.t)))
    : nat -> relation (st_local * (itree Es Any.t)) :=
  | sim_itree_ret
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      (WF: wf (mrs_src0, mrs_tgt0))
      v
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), (Ret v)) ((mrs_tgt0, fr_tgt0), (Ret v))
  | sim_itree_tau
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (K: sim_itree i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree i0 (st_src0, tau;; i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_call
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      fn varg k_src k_tgt
      (WF: wf (mrs_src0, mrs_tgt0))
      (K: forall vret mrs_src1 mrs_tgt1 (WF: wf (mrs_src1, mrs_tgt1)),
          exists i1, sim_itree i1 ((mrs_src1, fr_src0), k_src vret) ((mrs_tgt1, fr_tgt0), k_tgt vret))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Call fn varg) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Call fn varg) >>= k_tgt)
  | sim_itree_syscall
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      fn varg k_src k_tgt
      (K: forall vret,
          exists i1, sim_itree i1 ((mrs_src0, fr_src0), k_src vret) ((mrs_tgt0, fr_tgt0), k_tgt vret))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Syscall fn varg) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Syscall fn varg) >>= k_tgt)
  (*** TODO: sim_syscall is nontrivial; it should accept "injected" memory... ***)
  (*** TODO: simplify the model: Syscall: list val -> val ***)

  | sim_itree_choose_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      X_src X_tgt k_src k_tgt
      (K: forall (x_tgt: X_tgt), exists (x_src: X_src) i1, sim_itree i1 ((mrs_src0, fr_src0), k_src x_src) ((mrs_tgt0, fr_tgt0), k_tgt x_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Choose X_src) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Choose X_tgt) >>= k_tgt)
  | sim_itree_take_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      X_src X_tgt k_src k_tgt
      (K: forall (x_src: X_src), exists (x_tgt: X_tgt) i1, sim_itree i1 ((mrs_src0, fr_src0), k_src x_src) ((mrs_tgt0, fr_tgt0), k_tgt x_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Take X_src) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Take X_tgt) >>= k_tgt)
  | sim_itree_pput_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mn mr_src0 mr_tgt0 mp_src1 mp_tgt1 mrs_src1 mrs_tgt1 mp_src0 mp_tgt0
      (MRSRC: Maps.lookup mn mrs_src0 = Some (mr_src0, mp_src0))
      (MRTGT: Maps.lookup mn mrs_tgt0 = Some (mr_tgt0, mp_tgt0))
      (EQSRC: mrs_src1 = Maps.add mn (mr_src0, mp_src1) mrs_src0)
      (EQTGT: mrs_tgt1 = Maps.add mn (mr_tgt0, mp_tgt1) mrs_tgt0)
      (K: sim_itree i1 ((mrs_src1, fr_src0), k_src tt) ((mrs_tgt1, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (PPut mn mp_src1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (PPut mn mp_tgt1) >>= k_tgt)
  | sim_itree_mput_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mn mr_src0 mr_tgt0 mr_src1 mr_tgt1 mrs_src1 mrs_tgt1 mp_src0 mp_tgt0
      (MRSRC: Maps.lookup mn mrs_src0 = Some (mr_src0, mp_src0))
      (MRTGT: Maps.lookup mn mrs_tgt0 = Some (mr_tgt0, mp_tgt0))
      (EQSRC: mrs_src1 = Maps.add mn (mr_src1, mp_src0) mrs_src0)
      (EQSRC: mrs_tgt1 = Maps.add mn (mr_tgt1, mp_tgt0) mrs_tgt0)
      (K: sim_itree i1 ((mrs_src1, fr_src0), k_src tt) ((mrs_tgt1, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (MPut mn mr_src1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (MPut mn mr_tgt1) >>= k_tgt)
  | sim_itree_fput_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      fr_src1 fr_tgt1
      (K: sim_itree i1 ((mrs_src0, fr_src1), k_src tt) ((mrs_tgt0, fr_tgt1), k_tgt tt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (FPut fr_src1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FPut fr_tgt1) >>= k_tgt)
  | sim_itree_pget_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mn mr_src0 mp_src0 mr_tgt0 mp_tgt0
      (MRSRC: Maps.lookup mn mrs_src0 = Some (mr_src0, mp_src0))
      (MRTGT: Maps.lookup mn mrs_tgt0 = Some (mr_tgt0, mp_tgt0))
      (K: sim_itree i1 ((mrs_src0, fr_src0), k_src mp_src0) ((mrs_tgt0, fr_tgt0), k_tgt mp_tgt0))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (PGet mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (PGet mn) >>= k_tgt)
  | sim_itree_mget_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      mn mr_src0 mp_src0 mr_tgt0 mp_tgt0
      (MRSRC: Maps.lookup mn mrs_src0 = Some (mr_src0, mp_src0))
      (MRTGT: Maps.lookup mn mrs_tgt0 = Some (mr_tgt0, mp_tgt0))
      (K: sim_itree i1 ((mrs_src0, fr_src0), k_src mr_src0) ((mrs_tgt0, fr_tgt0), k_tgt mr_tgt0))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (MGet mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (MGet mn) >>= k_tgt)
  | sim_itree_fget_both
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src k_tgt
      (K: sim_itree i1 ((mrs_src0, fr_src0), k_src fr_src0) ((mrs_tgt0, fr_tgt0), k_tgt fr_tgt0))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (FGet) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FGet) >>= k_tgt)



  | sim_itree_tau_src
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: i1 < i0)
      (K: sim_itree i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree i0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_choose_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X k_src i_tgt
      (ORD: i1 < i0)
      (K: exists (x: X), sim_itree i1 ((mrs_src0, fr_src0), k_src x) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Choose X) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_take_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X k_src i_tgt
      (ORD: i1 < i0)
      (K: forall (x: X), sim_itree i1 ((mrs_src0, fr_src0), k_src x) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Take X) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)

  | sim_itree_pput_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      mn mr0 mp1 mrs_src1 mp0
      (MR0: Maps.lookup mn mrs_src0 = Some (mr0, mp0))
      (EQ: mrs_src1 = Maps.add mn (mr0, mp1) mrs_src0)
      (K: sim_itree i1 ((mrs_src1, fr_src0), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (PPut mn mp1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_mput_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      mn mr0 mr1 mrs_src1 mp0
      (MR0: Maps.lookup mn mrs_src0 = Some (mr0, mp0))
      (EQ: mrs_src1 = Maps.add mn (mr1, mp0) mrs_src0)
      (K: sim_itree i1 ((mrs_src1, fr_src0), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (MPut mn mr1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_fput_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      fr_src1
      (K: sim_itree i1 ((mrs_src0, fr_src1), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (FPut fr_src1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)

  | sim_itree_pget_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      mn mr0 mp0
      (MR0: Maps.lookup mn mrs_src0 = Some (mr0, mp0))
      (K: sim_itree i1 ((mrs_src0, fr_src0), k_src mp0) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (PGet mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_mget_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      mn mr0 mp0
      (MR0: Maps.lookup mn mrs_src0 = Some (mr0, mp0))
      (K: sim_itree i1 ((mrs_src0, fr_src0), k_src mr0) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (MGet mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_fget_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      (K: sim_itree i1 ((mrs_src0, fr_src0), k_src fr_src0) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (FGet) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)






  | sim_itree_tau_tgt
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: i1 < i0)
      (K: sim_itree i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree i0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_choose_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X i_src k_tgt
      (ORD: i1 < i0)
      (K: forall (x: X), sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt x))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Choose X) >>= k_tgt)
  | sim_itree_take_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 X i_src k_tgt
      (ORD: i1 < i0)
      (K: exists (x: X), sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt x))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Take X) >>= k_tgt)

  | sim_itree_pput_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      mn mr0 mp1 mrs_tgt1 mp0
      (MR0: Maps.lookup mn mrs_tgt0 = Some (mr0, mp0))
      (EQ: mrs_tgt1 = Maps.add mn (mr0, mp1) mrs_tgt0)
      (K: sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt1, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (PPut mn mp1) >>= k_tgt)
  | sim_itree_mput_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      mn mr0 mr1 mrs_tgt1 mp0
      (MR0: Maps.lookup mn mrs_tgt0 = Some (mr0, mp0))
      (EQ: mrs_tgt1 = Maps.add mn (mr1, mp0) mrs_tgt0)
      (K: sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt1, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (MPut mn mr1) >>= k_tgt)
  | sim_itree_fput_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      fr_tgt1
      (K: sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt1), k_tgt tt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FPut fr_tgt1) >>= k_tgt)

  | sim_itree_pget_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      mn mr0 mp0
      (MR0: Maps.lookup mn mrs_tgt0 = Some (mr0, mp0))
      (K: sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt mp0))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (PGet mn) >>= k_tgt)
  | sim_itree_mget_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      mn mr0 mp0
      (MR0: Maps.lookup mn mrs_tgt0 = Some (mr0, mp0))
      (K: sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt mr0))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (MGet mn) >>= k_tgt)
  | sim_itree_fget_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      (K: sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt  fr_tgt0))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (FGet) >>= k_tgt)
  .

  Definition sim_itree: _ -> relation _ := paco3 _sim_itree bot3.

  Lemma sim_itree_mon: monotone3 _sim_itree.
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree: paco.

  Definition sim_fsem: relation (Any.t -> itree Es Any.t) :=
    (eq ==> (fun it_src it_tgt => forall mrs_src mrs_tgt (SIMMRS: wf (mrs_src, mrs_tgt)),
                 exists n, sim_itree n ((mrs_src, URA.unit), it_src)
                                     ((mrs_tgt, URA.unit), it_tgt)))%signature
  .

  Definition sim_fnsem: relation (string * (Any.t -> itree Es Any.t)) := RelProd eq sim_fsem.

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
  - eapply sim_itree_ret. ss.
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


Module ModSemPair.
Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Variable (ms_src ms_tgt: ModSem.t).

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).
  Inductive sim: Prop := mk {
    wf: W -> Prop;
    le: W -> W -> Prop;
    le_PreOrder: PreOrder le;
    (*** TODO: incorporate le properly ***)
    sim_fnsems: Forall2 (sim_fnsem wf) ms_src.(ModSem.fnsems) ms_tgt.(ModSem.fnsems);
    sim_initial_mrs: wf (ms_src.(ModSem.initial_mrs), ms_tgt.(ModSem.initial_mrs));
  }.

End SIMMODSEM.

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
    - econs 6; eauto.
    - econs 7; eauto.
    - econs 8; eauto.
    - econs 9; eauto.
    - econs 10; eauto.
    - econs 11; eauto.
    - econs 12; eauto.
    - econs 13; eauto. des. pclearbot. esplits; eauto.
    - econs 14; eauto. i. hexploit K; eauto.
    - econs 15; eauto.
    - econs 16; eauto.
    - econs 17; eauto.
    - econs 18; eauto.
    - econs 19; eauto.
    - econs 20; eauto.
    - econs 21; eauto.
    - econs 22; eauto. i. hexploit K; eauto.
    - econs 23; eauto. des. pclearbot. esplits; eauto.
    - econs 24; eauto.
    - econs 25; eauto.
    - econs 26; eauto.
    - econs 27; eauto.
    - econs 28; eauto.
    - econs 29; eauto.
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
    * econs 1. econs; eauto.
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

        { eapply nodup_disjoint; eauto. }

          disjoint_filter_l.
        { repeat erewrite add_filter; eauto. }
        {
          repeat erewrite add_filter; eauto.

        }
        {


          in *; eauto.
        eapply K.

      i. he

      exists i1. splits; auto. right. eapply CIH; eauto.
      { erewrite add_filter; eauto.
        erewrite add_filter; eauto. }
      { erewrite add_other_filter; eauto.
        2: { eapply nodup_disjoint; eauto. }
        erewrite add_other_filter; eauto.
        eapply nodup_disjoint; eauto. }
      { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
      { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
    * econs 5; eauto.
      { eapply lookup_filter; eauto. }
      { eapply lookup_filter; eauto. }
    * econs 6; eauto.
    * econs 7; eauto.
    * econs 8; eauto. i. hexploit K; eauto. i. des. pclearbot.
      esplits; eauto.
    * econs 9; eauto.
      { eapply lookup_filter; eauto. }
      { eapply lookup_filter; eauto. }
      i. hexploit K; auto. i. des. pclearbot.
      splits; auto. right. eapply CIH; eauto.
    * econs 10; eauto. i. hexploit K; eauto. i. des. pclearbot.
      esplits; eauto.
    * econs 11; eauto. i. hexploit K; eauto. i. des. pclearbot.
      esplits; eauto.
    * econs 12; eauto. i. hexploit K; eauto.
    * econs 13; eauto.
    * econs 14; eauto.
      { eapply lookup_filter; eauto. }
      right. eapply CIH; eauto.
      { erewrite add_filter; eauto. }
      { erewrite add_other_filter; eauto.
        eapply nodup_disjoint; eauto. }
      { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
    * econs 15; eauto. eapply lookup_filter; eauto.
    * econs 16; eauto.
    * econs 17; eauto.
    * econs 18; eauto.
    * econs 19; eauto.
      { eapply lookup_filter; eauto. }
      i. hexploit K; eauto. i. pclearbot.
      right. eapply CIH; eauto.
    * econs 20; eauto. des. pclearbot.
      eexists. right. eapply CIH; eauto.
    * econs 21; eauto. i. hexploit K; auto. i.
      right. eapply CIH; eauto.
    * econs 22; eauto.
    * econs 23; eauto.
      { eapply lookup_filter; eauto. }
      i. hexploit K; eauto. i. pclearbot.
      right. eapply CIH; eauto.
      { erewrite add_filter; eauto. }
      { erewrite add_other_filter; eauto.
        eapply nodup_disjoint; eauto. }
      { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
    * econs 24; eauto.
      { eapply lookup_filter; eauto. }
    * econs 25; eauto.
    * econs 26; eauto.
    * econs 27; eauto. i. hexploit K; eauto. i. pclearbot.
      right. eapply CIH; eauto.
    * econs 28; eauto.
      { eapply lookup_filter; eauto. }
      des. pclearbot. esplits; eauto.
    * econs 29; eauto.
      i. hexploit K; eauto.
    * econs 30; eauto. des. pclearbot.
      esplits; eauto.


    * econs 4; eauto.
      { eapply lookup_filter; eauto. }
      { eapply lookup_filter; eauto. }
      i. hexploit K; eauto. i. des. pclearbot.
      exists i1. splits; auto. right. eapply CIH; eauto.
      { erewrite add_filter; eauto.
        erewrite add_filter; eauto. }
      { erewrite add_other_filter; eauto.
        2: { eapply nodup_disjoint; eauto. }
        erewrite add_other_filter; eauto.
        eapply nodup_disjoint; eauto. }
      { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
      { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
    * econs 5; eauto.
      { eapply lookup_filter; eauto. }
      { eapply lookup_filter; eauto. }
    * econs 6; eauto.
    * econs 7; eauto.
    * econs 8; eauto. i. hexploit K; eauto. i. des. pclearbot.
      esplits; eauto.
    * econs 9; eauto.
      { eapply lookup_filter; eauto. }
      { eapply lookup_filter; eauto. }
      i. hexploit K; auto. i. des. pclearbot.
      splits; auto. right. eapply CIH; eauto.
    * econs 10; eauto. i. hexploit K; eauto. i. des. pclearbot.
      esplits; eauto.
    * econs 11; eauto. i. hexploit K; eauto. i. des. pclearbot.
      esplits; eauto.
    * econs 12; eauto. i. hexploit K; eauto.
    * econs 13; eauto.
    * econs 14; eauto.
      { eapply lookup_filter; eauto. }
      right. eapply CIH; eauto.
      { erewrite add_filter; eauto. }
      { erewrite add_other_filter; eauto.
        eapply nodup_disjoint; eauto. }
      { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
    * econs 15; eauto. eapply lookup_filter; eauto.
    * econs 16; eauto.
    * econs 17; eauto.
    * econs 18; eauto.
    * econs 19; eauto.
      { eapply lookup_filter; eauto. }
      i. hexploit K; eauto. i. pclearbot.
      right. eapply CIH; eauto.
    * econs 20; eauto. des. pclearbot.
      eexists. right. eapply CIH; eauto.
    * econs 21; eauto. i. hexploit K; auto. i.
      right. eapply CIH; eauto.
    * econs 22; eauto.
    * econs 23; eauto.
      { eapply lookup_filter; eauto. }
      i. hexploit K; eauto. i. pclearbot.
      right. eapply CIH; eauto.
      { erewrite add_filter; eauto. }
      { erewrite add_other_filter; eauto.
        eapply nodup_disjoint; eauto. }
      { eapply nodup_add; eauto. eapply lookup_filter; eauto. }
    * econs 24; eauto.
      { eapply lookup_filter; eauto. }
    * econs 25; eauto.
    * econs 26; eauto.
    * econs 27; eauto. i. hexploit K; eauto. i. pclearbot.
      right. eapply CIH; eauto.
    * econs 28; eauto.
      { eapply lookup_filter; eauto. }
      des. pclearbot. esplits; eauto.
    * econs 29; eauto.
      i. hexploit K; eauto.
    * econs 30; eauto. des. pclearbot.
      esplits; eauto.
  Qed.

  Lemma add_modsempair (ms_src0 ms_src1 ms_tgt0 ms_tgt1: ModSem.t)
        (WFSRC: ModSem.wf (ModSem.add ms_src0 ms_src1))
        (WFTGT: ModSem.wf (ModSem.add ms_tgt0 ms_tgt1))
        (SIM0: sim ms_src0 ms_tgt0)
        (SIM1: sim ms_src1 ms_tgt1)
    :
      sim (ModSem.add ms_src0 ms_src1) (ModSem.add ms_tgt0 ms_tgt1).
  Proof.
    assert (DISJSRC: forall mn
                            (IN0: In mn (List.map fst (ModSem.initial_mrs ms_src1)))
                            (IN1: In mn (List.map fst (ModSem.initial_mrs ms_src0))),
               False).
    { inv WFSRC. ss. rewrite map_app in *.
      i. eapply app_nodup in wf_initial_mrs; eauto. }
    assert (DISJTGT: forall mn
                            (IN0: In mn (List.map fst (ModSem.initial_mrs ms_tgt1)))
                            (IN1: In mn (List.map fst (ModSem.initial_mrs ms_tgt0))),
               False).
    { inv WFTGT. ss. rewrite map_app in *.
      i. eapply app_nodup in wf_initial_mrs; eauto. }
    destruct SIM0 as [wf0 le0 le_PreOrder0 sim_fnsems0 sim_initial_mrs0].
    destruct SIM1 as [wf1 le1 le_PreOrder1 sim_fnsems1 sim_initial_mrs1].
    eapply mk with (wf:=add_wf (List.map fst ms_src0.(ModSem.initial_mrs))
                               (List.map fst ms_src1.(ModSem.initial_mrs))
                               (List.map fst ms_tgt0.(ModSem.initial_mrs))
                               (List.map fst ms_tgt1.(ModSem.initial_mrs))
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

    apply wf_mrs_add. auto.

End ModSemPair.




Require Import SimGlobal.
Require Import Ordinal ClassicalOrdinal.



























  Lemma S_lt_O
        o
    :
      <<LT: Ordinal.lt Ordinal.O (Ordinal.S o)>>
  .
  Proof.
    r. econs. unfold Ordinal.O. unfold unit_rect. des_ifs. destruct o. econs. ii; ss.
    Unshelve.
    all: ss.
  Qed.

  Lemma le_trans: Transitive Ordinal.le. typeclasses eauto. Qed.
  Lemma lt_trans: Transitive Ordinal.le. typeclasses eauto. Qed.
  Hint Resolve Ordinal.lt_le_lt Ordinal.le_lt_lt Ordinal.add_lt_r Ordinal.add_le_l
       Ordinal.add_le_r Ordinal.lt_le
       Ordinal.S_lt_mon
       Ordinal.S_lt
       Ordinal.S_spec
       S_lt_O
    : ord.
  Hint Resolve le_trans lt_trans: ord_trans.
  Hint Resolve Ordinal.add_base_l Ordinal.add_base_r: ord_proj.

  Lemma from_nat_lt
        n m
        (LT: Nat.lt n m)
    :
      <<LT: Ordinal.lt (Ordinal.from_nat n) (Ordinal.from_nat m)>>
  .
  Proof.
    generalize dependent m. induction n; ii; ss.
    - destruct m; try lia. r; ss. eapply S_lt_O.
    - destruct m; ss; try lia. r. rewrite <- Ordinal.S_lt_mon. eapply IHn; try lia.
  Qed.

  Lemma from_nat_le
        n m
        (LT: Nat.le n m)
    :
      <<LT: Ordinal.le (Ordinal.from_nat n) (Ordinal.from_nat m)>>
  .
  Proof.
    generalize dependent m. induction n; ii; ss.
    - destruct m; try lia; ss.
    - destruct m; ss; try lia; ss. r. rewrite <- Ordinal.S_le_mon. eapply IHn; try lia.
  Qed.

  Lemma from_nat_eq
        n m
        (LT: Nat.eq n m)
    :
      <<LT: Ordinal.eq (Ordinal.from_nat n) (Ordinal.from_nat m)>>
  .
  Proof.
    generalize dependent m. induction n; ii; ss.
    - destruct m; try lia; ss.
    - destruct m; ss; try lia; ss. r. rewrite <- Ordinal.S_eq_mon. eapply IHn; try lia.
  Qed.

  Opaque Ordinal.from_nat.

   Ltac igo := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r; try rewrite bind_tau;
                       try rewrite interp_vis;
                       try rewrite interp_ret;
                       try rewrite interp_tau
                      (* try rewrite interp_trigger *)
                      ).

  Ltac mgo := repeat (try rewrite ! interp_Es_bind; try rewrite ! interp_Es_ret; try rewrite ! interp_Es_tau;
                      try rewrite ! interp_Es_rE; try rewrite ! interp_Es_eventE; try rewrite ! interp_Es_callE;
                      try rewrite ! interp_Es_triggerNB; try rewrite ! interp_Es_triggerUB; igo).
  Ltac mstep := gstep; econs; eauto; [eapply from_nat_lt; ss|].








































Module ModPair.
Section SIMMOD.
   Context `{Σ: GRA.t}.
   Variable (md_src md_tgt: Mod.t).
   Inductive sim: Prop := mk {
     sim_modsem:
       forall skenv, <<SIM: ModSemPair.sim (md_src.(Mod.get_modsem) skenv) (md_tgt.(Mod.get_modsem) skenv)>>;
     sim_sk: <<SIM: md_src.(Mod.sk) = md_tgt.(Mod.sk)>>;
   }
   .

   (* Hypothesis SIM: sim. *)
   (* Variable ske: SkEnv.t. *)
   (* Variable (md_ctx: Mod.t). *)
   (* Let ms_src: ModSem.t := md_src.(Mod.get_modsem) ske. *)
   (* Let ms_tgt: ModSem.t := md_tgt.(Mod.get_modsem) ske. *)
   (* Let ms_ctx: ModSem.t := md_ctx.(Mod.get_modsem) ske. *)

   (* Let adequacy_local_aux: *)
   (*   forall (R: Type) (RR: R -> R -> Prop) (TY: R = val) (REL: RR = (@eq R)) *)
   (*          i_src i_tgt *)
   (*          (SRC: i_src ~= (ModSem.initial_itr (ModSem.add ms_ctx *)
   (*                                                         ms_src))) *)
   (*          (TGT: i_tgt ~= (ModSem.initial_itr (ModSem.add ms_ctx *)
   (*                                                         ms_tgt))) *)
   (*   , *)
   (*     simg RR Ordinal.O i_src i_tgt *)
   (* . *)
   (* Proof. *)
   (*   inv SIM. spc sim_modsem0. rename sim_modsem0 into SIMMS. rename sim_sk0 into SIMSK. des. *)
   (*   i. ginit. *)
   (*   { eapply cpn5_wcompat; eapply simg_mon. } *)
   (*   revert_until ske. do 4 intro. gcofix CIH. i. clarify. *)
   (*   unfold ModSem.initial_itr. ss. unfold ITree.map. mgo. folder. *)
   (*   unfold assume. mgo. *)
   (*   Ltac mstep := try (gstep; econs; eauto; try (by eapply from_nat_lt;ss); check_safe; i). *)
   (*   mstep. unshelve esplits; et. *)
   (*   { clear - SIMMS. inv SIMMS. ss. *)
   (*     admit "ez -- probably need to add some trivial condition on initial_mrs". *)
   (*   } *)
   (*   unfold unwrapU at 1. des_ifs; cycle 1. *)
   (*   { mgo. unfold triggerUB. mgo. mstep; ss. } *)
   (*   unfold unwrapU. des_ifs; cycle 1. *)
   (*   { ss. admit "ez". } *)
   (*   mgo. *)
   (*   TTTT *)
   (*   irw. *)
   (*   ss. *)
   (*   ss. inv SIM. rewrite <- ! sim_sk0 in *. *)
   (*   set (Sk.load_skenv (Sk.add (Mod.sk ctx) (Mod.sk md_src))) as skenv_link in *. *)
   (*   gstep. *)
   (* Qed. *)

   Theorem adequacy_local
           (SIM: sim)
           (*** You will need some wf conditions for ctx ***)
     :
       <<CR: forall ctx, Beh.of_program (Mod.interp (Mod.add ctx md_tgt)) <1=
                         Beh.of_program (Mod.interp (Mod.add ctx md_src))>>
   .
   Proof.
     ii. eapply adequacy_global; et. exists Ordinal.O.
     admit "TODO".
   Qed.

   Theorem adequacy_local_closed
           (SIM: sim)
     :
       Beh.of_program (Mod.interp md_tgt) <1=
       Beh.of_program (Mod.interp md_src).
   Proof.
     hexploit adequacy_local.
     { eauto. }
     i. specialize (H Mod.empty). repeat rewrite Mod.add_empty_l in H. auto.
   Qed.

End SIMMOD.

Section SIMMODS.
  Context `{Σ: GRA.t}.

  Lemma sim_list_adequacy (mds_src mds_tgt: list Mod.t)
        (FORALL: List.Forall2 sim mds_src mds_tgt)
    :
      <<CR: forall ctx, Beh.of_program (Mod.interp (Mod.add ctx (Mod.add_list mds_tgt))) <1=
                        Beh.of_program (Mod.interp (Mod.add ctx (Mod.add_list mds_src)))>>.
  Proof.
    induction FORALL; ss.
    cut (forall ctx,
            Beh.of_program (Mod.interp (Mod.add ctx (Mod.add y (Mod.add_list l')))) <1=
            Beh.of_program (Mod.interp (Mod.add ctx (Mod.add y (Mod.add_list l))))).
    { ii. eapply H0 in PR.
      apply Mod.add_comm in PR. apply Mod.add_comm.
      erewrite <- Mod.add_assoc in *.
      apply Mod.add_comm in PR. apply Mod.add_comm.
      eapply adequacy_local.
      { eauto. }
      { eapply PR. }
    }
    { i. erewrite Mod.add_assoc in *. eapply IHFORALL. auto. }
  Qed.

  Lemma sim_list_adequacy_closed (mds_src mds_tgt: list Mod.t)
        (FORALL: List.Forall2 sim mds_src mds_tgt)
    :
      Beh.of_program (Mod.interp (Mod.add_list mds_tgt)) <1=
      Beh.of_program (Mod.interp (Mod.add_list mds_src)).
  Proof.
    hexploit sim_list_adequacy.
    { eauto. }
    i. specialize (H Mod.empty). repeat rewrite Mod.add_empty_l in H. auto.
  Qed.
End SIMMODS.
End ModPair.

(* TODO: prove sim *)
(* TODO: write client *)
(* TODO: show cancellation *)
(* TODO: meta-level (no forge -> checkwf always succeeds) *)



Lemma sim_l_bind_bind `{Σ: GRA.t} a b c d e f g
      (R S : Type) (s : itree _ R) (k : R -> itree _ S) (h : S -> itree _ _)
      (SIM: gpaco3 (_sim_itree c) d e f g (b, ` r : R <- s;; ` x : _ <- k r;; h x) a)
  :
    gpaco3 (_sim_itree c) d e f g (b, ` x : _ <- (` x : _ <- s;; k x);; h x) a.
Proof.
  rewrite bind_bind. auto.
Qed.

Lemma sim_l_bind_tau `{Σ: GRA.t} a b c d e f g
      (U : Type) (t : itree _ _) (k : U -> itree _ _)
      (SIM: gpaco3 (_sim_itree c) d e f g (b, Tau (` x : _ <- t;; k x)) a)
  :
    gpaco3 (_sim_itree c) d e f g (b, ` x : _ <- Tau t;; k x) a.
Proof.
  rewrite bind_tau. auto.
Qed.

Lemma sim_l_bind_ret_l `{Σ: GRA.t} a b c d e f g
      (R : Type) (r : R) (k : R -> itree _ _)
      (SIM: gpaco3 (_sim_itree c) d e f g (b, k r) a)
  :
    gpaco3 (_sim_itree c) d e f g (b, ` x : _ <- Ret r;; k x) a.
Proof.
  rewrite bind_ret_l. auto.
Qed.

Lemma sim_r_bind_bind `{Σ: GRA.t} a b c d e f g
      (R S : Type) (s : itree _ R) (k : R -> itree _ S) (h : S -> itree _ _)
      (SIM: gpaco3 (_sim_itree c) d e f g a (b, ` r : R <- s;; ` x : _ <- k r;; h x))
  :
    gpaco3 (_sim_itree c) d e f g a (b, ` x : _ <- (` x : _ <- s;; k x);; h x).
Proof.
  rewrite bind_bind. auto.
Qed.

Lemma sim_r_bind_tau `{Σ: GRA.t} a b c d e f g
      (U : Type) (t : itree _ _) (k : U -> itree _ _)
      (SIM: gpaco3 (_sim_itree c) d e f g a (b, Tau (` x : _ <- t;; k x)))
  :
    gpaco3 (_sim_itree c) d e f g a (b, ` x : _ <- Tau t;; k x).
Proof.
  rewrite bind_tau. auto.
Qed.

Lemma sim_r_bind_ret_l `{Σ: GRA.t} a b c d e f g
      (R : Type) (r : R) (k : R -> itree _ _)
      (SIM: gpaco3 (_sim_itree c) d e f g a (b, k r))
  :
    gpaco3 (_sim_itree c) d e f g a (b, ` x : _ <- Ret r;; k x).
Proof.
  rewrite bind_ret_l. auto.
Qed.

Ltac interp_red := rewrite interp_vis ||
                           rewrite interp_ret ||
                           rewrite interp_tau ||
                           rewrite interp_trigger ||
                           rewrite interp_bind.

Ltac interp_mrec_red := rewrite interp_mrec_hit ||
                                rewrite interp_mrec_miss ||
                                rewrite interp_mrec_bind ||
                                rewrite interp_mrec_tau ||
                                rewrite interp_mrec_ret.

Ltac interp_state_red := rewrite interp_state_trigger ||
                                 rewrite interp_state_bind ||
                                 rewrite interp_state_tau ||
                                 rewrite interp_state_ret.

Ltac ired_l :=
  cbn;
  match goal with
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, ITree.bind' _ (ITree.bind' _ _)) _) ] =>
    apply sim_l_bind_bind; ired_l
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, ITree.bind' _ (Tau _)) _) ] =>
    apply sim_l_bind_tau
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, ITree.bind' _ (Ret _)) _) ] =>
    apply sim_l_bind_ret_l; ired_l
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, interp _ _) _) ] =>
    ((interp_red; ired_l) || idtac)
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, ITree.bind' _ (interp _ _)) _) ] =>
    ((interp_red; ired_l) || idtac)
  | _ => idtac
  end.

Ltac ired_r :=
  cbn;
  match goal with
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ _ (_, ITree.bind' _ (ITree.bind' _ _))) ] =>
    apply sim_r_bind_bind; ired_r
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ _ (_, ITree.bind' _ (Tau _))) ] =>
    apply sim_r_bind_tau
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ _ (_, ITree.bind' _ (Ret _))) ] =>
    apply sim_r_bind_ret_l
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ _ (_, interp _ _)) ] =>
    ((interp_red; ired_r) || idtac)
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ _ (_, ITree.bind' _ (interp _ _))) ] =>
    ((interp_red; ired_l) || idtac)
  | _ => idtac
  end.

Ltac ired_all := ired_l; ired_r.

Ltac prep := ired_all.

Ltac force_l :=
  prep;
  match goal with
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, guarantee ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_all; gstep; eapply sim_itree_choose_src; [eauto|exists name]|contradict name]; cycle 1

  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_tgt; gstep; econs; eauto; unseal i_tgt
  end
.
Ltac force_r :=
  prep;
  match goal with
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    destruct (classic P) as [name|name]; [ired_all; gstep; eapply sim_itree_take_tgt; [eauto|exists name]|contradict name]; cycle 1

  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_src; gstep; econs; eauto; unseal i_src
  end
.

Ltac _step :=
  match goal with
  (*** blacklisting ***)
  (* | [ |- (gpaco3 (_sim_itree wf) _ _ _ _ (_, trigger (Choose _) >>= _) (_, ?i_tgt)) ] => idtac *)
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_all; _step; ss; fail]
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    ired_all; gstep; eapply sim_itree_take_src; [apply Nat.lt_succ_diag_r|]; intro name

  (*** blacklisting ***)
  (* | [ |- (gpaco3 (_sim_itree wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_all; _step; ss; fail]
  | [ |- (gpaco3 (_sim_itree _) _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    ired_all; gstep; eapply sim_itree_choose_tgt; [apply Nat.lt_succ_diag_r|]; intro name



  | _ => (*** default ***)
    gstep; econs; try apply Nat.lt_succ_diag_r; i
  end;
  (* idtac *)
  match goal with
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end
.
Ltac steps := repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) unfold alist_add; simpl; des_ifs_safe).

Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 tgt1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco3 (_sim_itree wf) _ _ _ n (([(_, src0)], src1), src2) (([(_, tgt0)], tgt1), tgt2))
      (at level 60,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' tgt1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").
