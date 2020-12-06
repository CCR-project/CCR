Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem.
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
  (* | sim_itree_check_src *)
  (*     i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0 *)
  (*     i1 k_src i_tgt *)
  (*     (ORD: i1 < i0) *)
  (*     mn mr0 *)
  (*     (MR0: Maps.lookup mn mrs_src0 = Some mr0) *)
  (*     (K: forall (WF: (URA.wf (URA.add mr0 fr_src0))), *)
  (*         sim_itree i1 ((mrs_src0, fr_src0), k_src tt) ((mrs_tgt0, fr_tgt0), i_tgt)) *)
  (*   : *)
  (*     _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (CheckWf mn) >>= k_src) *)
  (*                ((mrs_tgt0, fr_tgt0), i_tgt) *)
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



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Variable (ms0 ms1: ModSem.t).

  Let W: Type := (alist mname Σ) * (alist mname Σ).
  Inductive sim: Prop := mk {
    wf: W -> Prop;
    le: W -> W -> Prop;
    le_PreOrder: PreOrder le;
    sim_fnsems: Forall2 (sim_fnsem wf) ms0.(ModSem.fnsems) ms1.(ModSem.fnsems);
    sim_initial_mrs: wf (ms0.(ModSem.initial_mrs), ms1.(ModSem.initial_mrs));
  }.

End SIMMODSEM.

(*** TODO: SimMod, Mod for Mem0/Mem1 ***)





Require Import Mem0 Mem1 Hoare.

Ltac go := try first[pfold; econs; [..|M]; (Mskip ss); et; check_safe; ii; left|
                     pfold; econsr; [..|M]; (Mskip ss); et; check_safe; ii; left].
Ltac igo := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r).
Ltac force_l := pfold; econs; [..|M]; Mskip ss; et.
Ltac force_r := pfold; econsr; [..|M]; Mskip ss; et.
Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ} `{@GRA.inG (RA.excl Mem.t) Σ}.

  Let W: Type := (alist mname Σ) * (alist mname Σ).
  (* Eval compute in (@RA.car (RA.excl Mem.t)). *)
  Eval compute in (@RA.car Mem1._memRA).
  Inductive sim_loc: option val -> (option val + unit) -> Prop :=
  | sim_loc_present v: sim_loc (Some v) (inl (Some v))
  | sim_loc_absent: sim_loc None (inr tt)
  .

  Let wf: W -> Prop :=
    fun '(mrs_src0, mrs_tgt0) =>
      exists mem_src (mem_tgt: Mem.t),
        (<<SRC: mrs_src0 = Maps.add "mem" (GRA.padding (URA.black mem_src)) Maps.empty>>) /\
        (<<TGT: mrs_tgt0 = Maps.add "mem" (GRA.padding ((inl (Some mem_tgt)): URA.car (t:=RA.excl Mem.t)))
                                    Maps.empty>>) /\
        (<<SIM: forall b ofs, sim_loc ((mem_tgt.(Mem.cnts)) b ofs) (mem_src b ofs)>>)
  .

  Infix "⋅" := URA.add (at level 50, left associativity).
  Notation "(⋅)" := URA.add (only parsing).

  Theorem correct: sim Mem1.mem Mem0.mem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. esplits; ss; et. ii. econs 2. }
    econs; ss.
    { split; ss. ii; clarify. rename y into varg. eexists 100%nat. ss. des; clarify.
      unfold alist_add, alist_remove; ss.
      unfold Mem1.allocF, Mem0.allocF.
      go. rename x into sz.
      unfold assume.
      igo.
      go. clarify. unfold HoareFun. go. rename x into rarg_src.
      unfold assume.
      igo.
      repeat go. clear_tac.
      Opaque URA.add.
      unfold unpadding, assume.
      igo.
      pfold. econsr; et. esplits; et.
      { ii. unfold GRA.padding. des_ifs. (*** TODO: should be trivial ***) }
      left.
      unfold unleftU. des_ifs; cycle 1.
      { exfalso. ss. unfold GRA.padding in Heq. des_ifs.
        admit "dependent type... use cast? lemma?".
        (* unfold PCM.GRA.cast_ra in *. *)
        (* unfold eq_rect_r, eq_rect, eq_sym in *. *)
        (* destruct (GRA.inG_prf). *)
        (* unfold eq_rect_r in *. ss. *)
        (* Set Printing All. *)
        (* erewrite rew_opp_l in Heq. *)
        (* unfold eq_rect_r in *. unfold eq_rect in *. unfold eq_sym in *. csc. *)
      }
      igo.
      assert(c = (Some mem_tgt)).
      { admit "dependent type". }
      clarify.
      unfold unwrapU. des_ifs. igo. des_ifs. unfold MPut. igo. repeat go.
      rename n into blk. rename z into ofs. rename mem_tgt into mem0. rename t into mem1.


      force_l. exists (Vptr blk 0). left.
      force_l.
      (* Eval compute in URA.car (t:=Mem1._memRA). *)
      (*** mret, fret ***)
      Check (mem_src: URA.car (t:=Mem1._memRA)).
      assert(sz = 1) by admit "let's consider only sz 1 case at the moment"; subst.
      set (fun _b _ofs => if (dec _b blk) && (dec _ofs 0%Z) then inl (Some (Vint 0)) else inr tt)
        as delta.
      eexists (GRA.padding (URA.black (URA.add (mem_src: URA.car (t:=Mem1._memRA)) delta)),
               GRA.padding
                 (fold_left URA.add
                            (mapi (fun n _ => (blk, Z.of_nat n) |-> Vint 0)
                                  (repeat () 1)) URA.unit)). left.
      igo. force_l.
      {
        replace (fun k => URA.unit) with (URA.unit (t:=Σ)) by ss.
        rewrite URA.unit_idl.
        rewrite GRA.padding_add.
        rewrite <- URA.unit_id.
        apply URA.updatable_add; cycle 1.
        { apply URA.updatable_unit. }
        eapply GRA.padding_updatable.
        ss. clarify.
        clear - Heq1.
        replace (@URA.frag Mem1._memRA (fun _ _ => @inr (option val) unit tt)) with
            (URA.unit (t:=Mem1.memRA)) by ss.
        rewrite URA.unit_idl.
        fold delta.
        eapply URA.auth_alloc2.
        admit "wf -- Need to know mem_src is wf. (1) Add checkwf, or (2) add wf in W.wf.
I think (1) is better; in (2), it seems like we are doing the same reasoning again
   ".
      }
      left. ss. fold delta. clarify.
      force_l.
      exists (GRA.padding (URA.white (delta: URA.car(t:=Mem1._memRA)))). left.
      unfold guarantee. igo.
      force_l. esplits.
      { ss. f_equal.
        replace (@URA.frag Mem1._memRA (fun (_ : nat) (_ : Z) => @inr (option val) unit tt)) with
            (URA.unit: URA.car (t:=Mem1.memRA)) by ss.
        rewrite URA.unit_idl.
        unfold delta. eauto.
      }
      left.
      force_l.
      { instantiate (1:= GRA.padding _). rewrite GRA.padding_add. f_equal. }
      left.
      force_r.
      (* { eapply URA.updatable_add. *)
      (*   - eapply GRA.padding_updatable. clear - H. *)
      (*     (** TODO: this should be a lemma **) *)
      (*     hexploit RA.excl_updatable; et. intro A. des. *)
      (*     (*** TODO: RA.updatable --> URA.updatable ***) *)
      (*     admit "ez". *)
      (*   - refl. *)
      (* } *)
      (* left. *)
      (* pfold. econs; et. *)
      rr. esplits; ss; et. ii.
      hexploit (SIM b ofs); et. intro A. inv A.
      {
        assert(T: Mem.cnts mem1 b ofs = Some v).
        { admit "ez: memory model". }
        rewrite T.
        Local Transparent URA.add.
        ss. des_ifs.
        Local Opaque URA.add.
        + unfold delta in *. des_ifs. bsimpl. des. des_sumbool. clarify.
          admit "ez: memory model".
        + econs.
      }
      destruct (classic (b = blk /\ ofs = 0%Z)).
      { des. clarify.
        assert(T: Mem.cnts mem1 blk 0 = Some (Vint 0)).
        { admit "ez: memory model". }
        rewrite T.
        Local Transparent URA.add.
        ss. des_ifs.
        Local Opaque URA.add.
        unfold delta. ss. des_ifs; bsimpl; des; des_sumbool; ss; econs.
      }
      Psimpl. des; clarify.
      {
        assert(T: Mem.cnts mem1 b 0 = None).
        { admit "ez: memory model". }
        rewrite T.
        Local Transparent URA.add.
        ss. des_ifs.
        Local Opaque URA.add.
        unfold delta. ss. des_ifs; bsimpl; des; des_sumbool; ss; econs.
      }
      {
        assert(T: Mem.cnts mem1 b ofs = None).
        { admit "ez: memory model". }
        rewrite T.
        Local Transparent URA.add.
        ss. des_ifs.
        Local Opaque URA.add.
        unfold delta. ss. des_ifs; bsimpl; des; des_sumbool; ss; econs.
      }
    }
    econs; ss.
    { admit "free". }
    econs; ss.
    { admit "load". }
  Unshelve.
    all: ss.
    all: try (by repeat econs; et).
  Unshelve.
    all: try (by repeat econs; et).
  Qed.

End SIMMODSEM.





Section CANCEL.

  Context `{Σ: GRA.t}.
  Variable mn_caller mn_callee: mname.
  Variable P: Σ -> Prop.
  (*** TODO: Maybe P should be able to depend on list val ***)
  (*** TODO: name it... htree (hoare tree), hktree (hoare ktree)? ***)
  Variable Q: val -> Σ -> Prop.
  Variable fn: fname.

  Let W: Type := (alist mname Σ) * (alist mname Σ).
  Let wf: W -> Prop :=
    fun '(mrs_src0, mrs_tgt0) =>
      exists _mr_caller_src _mr_caller_tgt _mr_callee_src _mr_callee_tgt,
        (<<SRC: mrs_src0 = Maps.add mn_callee _mr_callee_src
                                    (Maps.add mn_caller _mr_caller_src Maps.empty)
                                    >>) /\
        (<<TGT: mrs_tgt0 = Maps.add mn_callee _mr_callee_tgt
                                    (Maps.add mn_caller _mr_caller_tgt Maps.empty)
                                    >>)
  .
  Hypothesis DIF: mn_caller <> mn_callee.

  Goal sim_fsem wf (fun _ => Ret (Vint 0)) (fun _ => (HoareCall mn_caller P Q fn [])).
  Proof.
    ii. clarify. exists 100.
    ss. des. clarify.
    force_r. ii. des_ifs. left. rename c into marg_caller. rename c0 into farg_caller.
    force_r.
    { unfold rel_dec. ss. instantiate (1:=_mr_caller_tgt).
      des_ifs; bsimpl; des; des_sumbool; ss; clarify.
      - unfold rel_dec. ss. des_ifs; bsimpl; des; des_sumbool; ss; clarify.
    }
    ii. left.
    go. rename x into rarg.
    repeat go.
    unfold guarantee. igo.
    go.





    assert(trigger (Call fn []) = HoareFun mn_callee P Q (Ret tt)).
    { admit "call inline". }
    rewrite H. unfold HoareFun. igo.
    replace fr_tgt1 with (URA.unit (t:=Σ)) by admit "push frame".
    force_r.
    exists rarg. left.
    igo.
    force_r. left.
    unfold assume. igo.
    force_r. esplits; et. left.
    force_r. intro vret. left.
    igo.
    force_r. intro tmp. destruct tmp as [mret_callee fret_callee]. left.
    igo. force_r.
    { unfold rel_dec. ss. instantiate (1:=_mr_callee_tgt).
      repeat (unfold rel_dec in *; ss; des_ifs; bsimpl; des; des_sumbool; ss; clarify).
    }
    i. rewrite URA.unit_idl in UPD0.
    left. force_r. intro rret. left.
    igo. unfold guarantee. igo. force_r. i. left.
    force_r. intro fret_garbage; i.
    left.


    replace fret_garbage with fr_tgt1 by admit "pop frame".
    force_r. exists rret. left. force_r. left. igo. force_r.
    esplits; et. left.
  Abort.

End CANCEL.


(* TODO: prove sim *)
(* TODO: write client *)
(* TODO: show cancellation *)
(* TODO: meta-level (no forge -> checkwf always succeeds) *)
