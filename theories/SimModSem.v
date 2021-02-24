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
  (*** TODO: sim_syscall is nontrivial; it should accept "injected" memory... ***)
  (*** TODO: simplify the model: Syscall: list val -> val ***)


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
