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
  Let st_local: Type := ((alist mname Σ) * Σ).

  Let W: Type := (alist mname Σ) * (alist mname Σ).
  Variable wf: W -> Prop.
  Variable le: relation W.
  Hypothesis le_PreOrder: PreOrder le.

  Variant _sim_itree (sim_itree: nat -> relation (st_local * (itree Es val)))
    : nat -> relation (st_local * (itree Es val)) :=
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
  (*** TODO: sim_syscall is nontrivial; it should accept "injected" memory... ***)
  (*** TODO: simplify the model: Syscall: list val -> val ***)


  | sim_itree_tau_src
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: i1 < i0)
      (K: sim_itree i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree i0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_put_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      mn mr0 mr1 fr_src1
      (MR0: Maps.lookup mn mrs_src0 = Some mr0)
      (UPD: URA.updatable (URA.add mr0 fr_src0) (URA.add mr1 fr_src1))
      mrs_src1
      (EQ: mrs_src1 = Maps.add mn mr1 mrs_src0)
      (K: sim_itree i1 ((mrs_src1, fr_src1), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Put mn mr1 fr_src1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_mget_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      mn mr0
      (MR0: Maps.lookup mn mrs_src0 = Some mr0)
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
  | sim_itree_forge_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      delta
      (K: sim_itree i1 ((mrs_src0, URA.add fr_src0 delta), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Forge delta) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_discard_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      delta fr_src1
      (SPLIT: fr_src0 = URA.add fr_src1 delta)
      (K: sim_itree i1 ((mrs_src0, fr_src1), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Discard delta) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  | sim_itree_check_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 k_src i_tgt
      (ORD: i1 < i0)
      mn mr0
      (MR0: Maps.lookup mn mrs_src0 = Some mr0)
      (K: forall (WF: (URA.wf (URA.add mr0 fr_src0))),
          sim_itree i1 ((mrs_src0, fr_src0), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (CheckWf mn) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
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






  | sim_itree_tau_tgt
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: i1 < i0)
      (K: sim_itree i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree i0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_put_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      mn mr0 mr1 fr_tgt1
      (MR0: Maps.lookup mn mrs_tgt0 = Some mr0)
      (* (UPD: URA.updatable (URA.add mr0 fr_tgt0) (URA.add mr1 fr_tgt1)) *)
      mrs_tgt1
      (EQ: mrs_tgt1 = Maps.add mn mr1 mrs_tgt0)
      (* (K: sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt1, fr_tgt1), k_tgt tt)) *)
      (K: forall (UPD: URA.updatable (URA.add mr0 fr_tgt0) (URA.add mr1 fr_tgt1)),
          sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt1, fr_tgt1), k_tgt tt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Put mn mr1 fr_tgt1) >>= k_tgt)
  | sim_itree_mget_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      mn mr0
      (MR0: Maps.lookup mn mrs_tgt0 = Some mr0)
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
  | sim_itree_forge_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      delta
      (K: sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, URA.add fr_tgt0 delta), k_tgt tt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Forge delta) >>= k_tgt)
  | sim_itree_discard_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      delta
      (K: forall fr_tgt1 (SPLIT: fr_tgt0 = URA.add fr_tgt1 delta),
          sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt1), k_tgt tt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (Discard delta) >>= k_tgt)
  | sim_itree_check_tgt
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 i_src k_tgt
      (ORD: i1 < i0)
      mn mr0
      (MR0: Maps.lookup mn mrs_tgt0 = Some mr0)
      (K: exists (WF: (URA.wf (URA.add mr0 fr_tgt0))),
          sim_itree i1 ((mrs_src0, fr_src0), i_src) ((mrs_tgt0, fr_tgt0), k_tgt tt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), i_src)
                 ((mrs_tgt0, fr_tgt0), trigger (CheckWf mn) >>= k_tgt)
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
  .

  Definition sim_itree: _ -> relation _ := paco3 _sim_itree bot3.

  Lemma sim_itree_mon: monotone3 _sim_itree.
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree: paco.

  Definition sim_fsem: relation (list val -> itree Es val) :=
    (eq ==> (fun it_src it_tgt => forall mrs_src mrs_tgt (SIMMRS: wf (mrs_src, mrs_tgt)),
                 exists n, sim_itree n ((mrs_src, URA.unit), it_src)
                                     ((mrs_tgt, URA.unit), it_tgt)))%signature
  .

  Definition sim_fnsem: relation (string * (list val -> itree Es val)) := RelProd eq sim_fsem.

End SIM.



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

  Let W: Type := (alist mname Σ) * (alist mname Σ).
  Inductive sim: Prop := mk {
    wf: W -> Prop;
    le: W -> W -> Prop;
    le_PreOrder: PreOrder le;
    (*** TODO: incorporate le properly ***)
    sim_fnsems: Forall2 (sim_fnsem wf) ms_src.(ModSem.fnsems) ms_tgt.(ModSem.fnsems);
    sim_initial_mrs: wf (ms_src.(ModSem.initial_mrs), ms_tgt.(ModSem.initial_mrs));
  }.

End SIMMODSEM.
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
  Opaque string_dec.

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

End SIMMOD.
End ModPair.

(* TODO: prove sim *)
(* TODO: write client *)
(* TODO: show cancellation *)
(* TODO: meta-level (no forge -> checkwf always succeeds) *)
