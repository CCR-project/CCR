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






Section PLAYGROUND.
  Variable A B: Type.
  Variable left: A -> A -> Prop.
  Variable right: B -> B -> Prop.
  Inductive _sim (sim: nat -> A -> B -> Prop): nat -> A -> B -> Prop :=
  | go_left
      i0 a0 b0 a1
      i1
      (*** can't choose i1 depending on a1 ***)
      (ORD: i1 < i0)
      (GO: left a0 a1)
      (K: sim i1 a1 b0)
    :
      _sim sim i0 a0 b0
  | go_right
      i0 a0 b0 b1
      i1
      (ORD: i1 < i0)
      (GO: right b0 b1)
      (K: sim i1 a0 b1)
    :
      _sim sim i0 a0 b0
  | go_both
      i0 a0 b0 i1 a1 b1
      (GO: left a0 a1)
      (GO: right b0 b1)
      (K: sim i1 a1 b1)
    :
      _sim sim i0 a1 b1
  .
End PLAYGROUND.
Reset PLAYGROUND.
(*** i1 can't depend on a1, or the internal choices inside "left" ***)


Section PLAYGROUND.
  Variable A B: Type.
  Variable left: nat -> A -> nat -> A -> Prop.
  Variable right: nat -> B -> nat -> B -> Prop.
  Variable both: (nat -> A -> B -> Prop) -> (nat -> A -> B -> Prop).
  Inductive _sim (sim: nat -> A -> B -> Prop): nat -> A -> B -> Prop :=
  | go_left
      i0 a0 b0 a1
      i1
      (* (ORD: i1 < i0) *)
      (GO: left i0 a0 i1 a1)
      (K: sim i1 a1 b0)
    :
      _sim sim i0 a0 b0
  | go_right
      i0 a0 b0 b1
      i1
      (* (ORD: i1 < i0) *)
      (GO: right i0 b0 i1 b1)
      (K: sim i1 a0 b1)
    :
      _sim sim i0 a0 b0
  | go_left_right
      i0 a0 b0 _unused0_ _unused1_ i1 a1 b1
      (GO: left i0 a0 _unused0_ a1)
      (GO: right i0 b0 _unused1_ b1)
      (K: sim i1 a1 b1)
    :
      _sim sim i0 a1 b1
  | go_both
      i0 a0 b0
      (GO: both sim i0 a0 b0)
    :
      _sim sim i0 a0 b0
  .

  Definition sim: _ -> _ -> _ -> Prop := paco3 _sim bot3.

  Lemma sim_mon (MON: monotone3 both): monotone3 _sim.
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
  Qed.

End PLAYGROUND.

Hint Constructors _sim.
Hint Unfold sim.
Hint Resolve sim_mon: paco.












Section SIM.

  Context `{Σ: GRA.t}.

  (* Let st_local: Type := (list (string * GRA) * GRA). *)
  Let st_local: Type := ((alist mname Σ) * Σ).

  Let W: Type := (alist mname Σ) * (alist mname Σ).
  Variable wf: W -> Prop.
  Variable le: relation W.
  Hypothesis le_PreOrder: PreOrder le.

  Inductive _sim_itree (sim_itree: nat -> relation (st_local * (itree Es val)))
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


  | sim_itree_tau_src
      i0 st_src0 st_tgt0
      i1 i_src i_tgt
      (ORD: i1 < i0)
      (K: sim_itree i1 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree i0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_put_src
      i0 mrs_src0 mrs_tgt0 fr_src0 fr_tgt0
      i1 mn mr0 mr1 fr_src1 k_src i_tgt
      (ORD: i1 < i0)
      (MR0: Maps.lookup mn mrs_src0 = Some mr0)
      (UPD: URA.updatable (URA.add mr0 fr_src0) (URA.add mr1 fr_src1))
      (K: sim_itree i1 ((mrs_src0, fr_src1), k_src) ((mrs_tgt0, fr_tgt1), i_tgt))
    :
      _sim_itree sim_itree i0 ((mrs_src0, fr_src0), trigger (Put mn mr0 fr_src1) >>= k_src)
                 ((mrs_tgt0, fr_tgt0), i_tgt)
  .

  Definition sim_itree: _ -> relation _ := paco3 _sim_itree bot3.

  Lemma sim_itree_mon: monotone3 _sim_itree.
  Proof.
    admit "ez: TODO".
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree: paco.

  Definition sim_fsem: relation (list val -> itree Es val) :=
    (eq ==> (fun it_src it_tgt => forall mrs_src mrs_tgt (SIMMRS: R mrs_src mrs_tgt),
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

  Inductive sim: Prop := mk {
    R: relation (alist string Σ);
    sim_fnsems: Forall2 (sim_fnsem R) ms0.(ModSem.fnsems) ms1.(ModSem.fnsems);
    sim_initial_mrs: R ms0.(ModSem.initial_mrs) ms1.(ModSem.initial_mrs);
  }.

End SIMMODSEM.

(*** TODO: SimMod, Mod for Mem0/Mem1 ***)





Require Import Mem0 Mem1.

Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ} `{@GRA.inG (RA.excl Mem.t) Σ}.

  Let R :=

  Theorem correct: sim Mem1.mem Mem0.mem.
  Proof.
    unshelve econs.
    { ii.
  Qed.

End SIMMODSEM.























Section SIMMODSEM.

  Variable world: Type.
  Variable src: world -> GRA.
  Variable tgt: world -> GRA.

  Variable wf: world -> Prop.
  Variable le: world -> world -> Prop.
  Hypothesis le_PreOrder: PreOrder le.


  (* Variable idx: Type. *)
  (* Variable ord: idx -> idx -> Prop. *)
  (* Variable wf_ord: well_founded ord. *)

  (* Variable R: GRA -> GRA -> Prop. *)
  (* Variable R: list (string * (GRA -> GRA -> Prop)). *)
  (* Variable R: string -> option (GRA -> GRA -> Prop). *)
























  (* Let r_state := ModSem.r_state. *)
  (* Let handle_r := ModSem.handle_rE. *)
  (* Let interp_r := ModSem.interp_rE. *)

  (* Inductive _sim_fn sim_fn: nat -> (itree Es val * r_state) -> (itree Es val * r_state) -> Prop := *)
  (* | sim_fn_ret *)
  (*     i0 m_src0 m_tgt0 f_src0 f_tgt0 *)
  (*     (SIMM: R m_src0 m_tgt0) *)
  (*     v *)
  (*   : *)
  (*     _sim_fn sim_fn i0 ((Ret v), (m_src0, f_src0)) ((Ret v), (m_tgt0, f_tgt0)) *)
  (* | sim_fn_call *)
  (*     i0 m_src0 m_tgt0 f_src0 f_tgt0 *)
  (*     (SIMM: R m_src0 m_tgt0) *)
  (*     fn varg (i1: nat) k_src k_tgt *)
  (*     (K: forall rv m_src1 m_tgt1 (SIMM: R m_src1 m_tgt1), *)
  (*         sim_fn i1 (mk (k_src rv) f_src0 m_src1) (mk (k_src rv) f_tgt0 m_tgt1)) *)
  (*   : *)
  (*     _sim_fn sim_fn i0 (mk (trigger (Call fn varg) >>= k_src) f_src0 m_src0) *)
  (*             (mk (trigger (Call fn varg) >>= k_tgt) f_tgt0 m_tgt0) *)
  (* . *)
















  (* Variable R: string -> option (GRA -> GRA -> Prop). *)
  (* Hypothesis SIMMN: List.map fst ms0.(ModSem.initial_mrs) = List.map fst ms1.(ModSem.initial_mrs). *)
  (* Hypothesis RWF: forall mn, *)
  (*     is_some (R mn) -> is_some (List.find (dec mn) (List.map fst ms0.(ModSem.initial_mrs))). *)
  (* Definition RAll (m_src0 m_tgt0: list (string * GRA)): Prop := *)
  (*   Forall2 () m_src0 m_tgt0 *)
  (* . *)

  Variable R: relation (list (string * GRA)).

  (* Record st_local: Type := mk { *)
  (*   code: itree Es val; *)
  (*   fr: GRA; *)
  (*   (* mr: GRA; *) *)
  (*   mr: list (string * GRA); *)
  (* } *)
  (* . *)
  (* Let st_local: Type := (list (string * GRA) * GRA). *)

  Inductive _sim_fn sim_fn: nat -> sim_state -> sim_state -> Prop :=
  | sim_fn_ret
      i0 m_src0 m_tgt0 f_src0 f_tgt0
      (SIMM: R m_src0 m_tgt0)
      v
    :
      _sim_fn sim_fn i0 (mk (Ret v) f_src0 m_src0) (mk (Ret v) f_tgt0 m_tgt0)
  | sim_fn_call
      i0 m_src0 m_tgt0 f_src0 f_tgt0
      (SIMM: R m_src0 m_tgt0)
      fn varg (i1: nat) k_src k_tgt
      (K: forall rv m_src1 m_tgt1 (SIMM: R m_src1 m_tgt1),
          sim_fn i1 (mk (k_src rv) f_src0 m_src1) (mk (k_src rv) f_tgt0 m_tgt1))
    :
      _sim_fn sim_fn i0 (mk (trigger (Call fn varg) >>= k_src) f_src0 m_src0)
              (mk (trigger (Call fn varg) >>= k_tgt) f_tgt0 m_tgt0)
  | sim_fn_put_src
      i0 m_src0 m_tgt0 f_src0 f_tgt0
      (SIMM: R m_src0 m_tgt0)
      mn k_src c_tgt m_src1 f_src1
      i1
      (ORD: i1 < i0)
      (K: sim_fn i1 (nat 
    :
      _sim_fn sim_fn i0 (mk (trigger (Put mn m_src1 f_src1) >>= k_src) f_src0 m_src0)
              (mk (c_tgt) f_tgt0 m_tgt0)
  .
  callE
    rE
    ModSem.interp

  Definition sim_fn (fn_src fn_tgt: list val -> itree Es val): Prop.

End SIMMODSEM.



Module ModSem.
Section MODSEM.

  (* Record t: Type := mk { *)
  (*   state: Type; *)
  (*   local_data: Type; *)
  (*   step (skenv: SkEnv.t) (st0: state) (ev: option event) (st1: state): Prop; *)
  (*   state_sort: state -> sort; *)
  (*   initial_local_data: local_data; *)
  (*   sk: Sk.t; *)
  (*   name: string; *)
  (* } *)
  (* . *)

  Context `{GRA: GRA.t}.

  Record t: Type := mk {
    (* initial_ld: mname -> GRA; *)
    fnsems: list (fname * (list val -> itree Es val));
    initial_mrs: list (mname * GRA);
    sem: callE ~> itree Es :=
      fun _ '(Call fn args) =>
        '(_, sem) <- (List.find (fun fnsem => dec fn (fst fnsem)) fnsems)?;;
        sem args
  }
  .

  Record wf (ms: t): Prop := mk_wf {
    wf_fnsems: NoDup (List.map fst ms.(fnsems));
    wf_initial_mrs: NoDup (List.map fst ms.(initial_mrs));
  }
  .

  (*** using "Program Definition" makes the definition uncompilable; why?? ***)
  Definition add (ms0 ms1: t): t := {|
    (* sk := Sk.add md0.(sk) md1.(sk); *)
    (* initial_ld := URA.add (t:=URA.pointwise _ _) md0.(initial_ld) md1.(initial_ld); *)
    (* sem := fun _ '(Call fn args) => *)
    (*          (if List.in_dec string_dec fn md0.(sk) then md0.(sem) else md1.(sem)) _ (Call fn args); *)
    fnsems := app ms0.(fnsems) ms1.(fnsems);
    initial_mrs := app ms0.(initial_mrs) ms1.(initial_mrs);
  |}
  .



  Section INTERP.

  Variable ms: t.

  Let itr0: callE ~> itree Es :=
    fun _ ce =>
      trigger PushFrame;;
      rv <- (ms.(sem) ce);;
      trigger PopFrame;;
      Ret rv
  .
  Let itr1: itree (rE +' eventE) val := (mrec itr0) _ (Call "main" nil).



  Definition r_state: Type := ((mname -> GRA) * list GRA).
  Definition handle_rE `{eventE -< E}: rE ~> stateT r_state (itree E) :=
    fun _ e '(mrs, frs) =>
      match frs with
      | hd :: tl =>
        match e with
        | Put mn mr fr =>
          guarantee(URA.updatable (URA.add (mrs mn) hd) (URA.add mr fr));;
          Ret (((update mrs mn mr), fr :: tl), tt)
        | MGet mn => Ret ((mrs, frs), mrs mn)
        | FGet => Ret ((mrs, frs), hd)
        | Forge fr => Ret ((mrs, (URA.add hd fr) :: tl), tt)
        | Discard fr =>
          rest <- trigger (Choose _);;
          guarantee(hd = URA.add fr rest);;
          Ret ((mrs, rest :: tl), tt)
        | CheckWf mn =>
          assume(URA.wf (URA.add (mrs mn) hd));;
          Ret ((mrs, frs), tt)
        | PushFrame =>
          Ret ((mrs, URA.unit :: frs), tt)
        | PopFrame =>
          Ret ((mrs, tl), tt)
        end
      | _ => triggerNB
      end.
  Definition interp_rE `{eventE -< E}: itree (rE +' E) ~> stateT r_state (itree E) :=
    State.interp_state (case_ handle_rE State.pure_state).
  Definition initial_r_state: r_state :=
    (fun mn => match List.find (fun mnr => dec mn (fst mnr)) ms.(initial_mrs) with
               | Some r => snd r
               | None => URA.unit
               end, []).
  Let itr2: itree (eventE) val := assume(<<WF: wf ms>>);; snd <$> (interp_rE itr1) initial_r_state.



  Let state: Type := itree eventE val.

  Definition state_sort (st0: state): sort :=
    match (observe st0) with
    | TauF _ => demonic
    | RetF rv => final rv
    | VisF (Choose X) k => demonic
    | VisF (Take X) k => angelic
    | VisF (Syscall fn args m0) k => vis
    end
  .

  Inductive step: state -> option event -> state -> Prop :=
  | step_tau
      itr
    :
      step (Tau itr) None itr
  | step_choose
      X k (x: X)
    :
      step (Vis (subevent _ (Choose X)) k) None (k x)
  | step_take
      X k (x: X)
    :
      step (Vis (subevent _ (Take X)) k) None (k x)
  | step_syscall
      fn args m0 k ev m1 rv
      (SYSCALL: syscall_sem fn args m0 = (ev, m1, rv))
    :
      step (Vis (subevent _ (Syscall fn args m0)) k) (Some ev) (k (m1, rv))
  .

  Program Definition interp: semantics := {|
    STS.state := state;
    STS.step := step;
    STS.initial_state := itr2;
    STS.state_sort := state_sort;
  |}
  .
  Next Obligation. inv STEP; inv STEP0; ss. csc. rewrite SYSCALL in *. csc. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.

  End INTERP.

  (*** TODO: probably we can make ModSem.t as an RA too. (together with Sk.t) ***)
  (*** However, I am not sure what would be the gain; and there might be universe problem. ***)

  Let add_comm_aux
      ms0 ms1 stl0 str0
      (SIM: stl0 = str0)
    :
      <<COMM: Beh.of_state (interp (add ms0 ms1)) stl0 <1= Beh.of_state (interp (add ms1 ms0)) str0>>
  .
  Proof.
    revert_until ms1.
    pcofix CIH. i. pfold.
    clarify.
    punfold PR. induction PR using Beh.of_state_ind; ss.
    - econs 1; et.
    - econs 2; et.
      clear CIH. clear_tac. revert_until ms1.
      pcofix CIH. i. punfold H0. pfold.
      inv H0.
      + econs 1; eauto. ii. ss. exploit STEP; et. i; des. right. eapply CIH; et. pclearbot. ss.
      + econs 2; eauto. des. esplits; eauto. right. eapply CIH; et. pclearbot. ss.
    - econs 4; et. pclearbot. right. eapply CIH; et.
    - econs 5; et. rr in STEP. des. rr. esplits; et.
    - econs 6; et. ii. exploit STEP; et. i; des. clarify.
  Qed.

  Lemma wf_comm
        ms0 ms1
    :
      <<EQ: wf (add ms0 ms1) = wf (add ms1 ms0)>>
  .
  Proof.
    r. eapply prop_ext. split; i.
    - admit "ez".
    - admit "ez".
  Qed.

  Theorem add_comm
          ms0 ms1
          (* (WF: wf (add ms0 ms1)) *)
    :
      <<COMM: Beh.of_program (interp (add ms0 ms1)) <1= Beh.of_program (interp (add ms1 ms0))>>
  .
  Proof.
    destruct (classic (wf (add ms1 ms0))); cycle 1.
    { ii. clear PR. eapply Beh.ub_top. pfold. econsr; ss; et. rr. ii; ss. unfold assume in *.
      inv STEP; ss; irw in H1; (* clarify <- TODO: BUG, runs infloop. *) inv H1; simpl_depind; subst.
      clarify.
    }
    rename H into WF.
    ii. ss. r in PR. r. eapply add_comm_aux; et.
    rp; et. clear PR. cbn. do 1 f_equal; cycle 1.
    { unfold assume. rewrite wf_comm. ss. }
    apply func_ext; ii.
    f_equiv.
    f_equal; cycle 1.
    - unfold initial_r_state. f_equal. apply func_ext. intros fn. ss. des_ifs.
      + admit "ez: wf".
      + admit "ez: wf".
      + admit "ez: wf".
    - repeat f_equal. apply func_ext_dep. intro T. apply func_ext. intro c. destruct c.
      repeat f_equal. apply func_ext. i. f_equal. ss. do 2 f_equal.
      admit "ez: wf".
  Qed.

  Theorem add_assoc
          ms0 ms1 ms2
          (WF: wf (add ms0 (add ms1 ms2)))
    :
      <<COMM: Beh.of_program (interp (add ms0 (add ms1 ms2))) <1=
              Beh.of_program (interp (add (add ms0 ms1) ms2))>>
  .
  Proof.
    admit "TODO".
  Qed.

  Theorem add_assoc_rev
          ms0 ms1 ms2
          (WF: wf (add ms0 (add ms1 ms2)))
    :
      <<COMM: Beh.of_program (interp (add ms0 (add ms1 ms2))) <1=
              Beh.of_program (interp (add (add ms0 ms1) ms2))>>
  .
  Proof.
    admit "TODO".
  Qed.

End MODSEM.
End ModSem.



Module Mod.
Section MOD.

  Context `{GRA: GRA.t}.

  Record t: Type := mk {
    get_modsem: SkEnv.t -> ModSem.t;
    sk: Sk.t;
    interp: semantics := ModSem.interp (get_modsem (Sk.load_skenv sk));
  }
  .

  (* Record wf (md: t): Prop := mk_wf { *)
  (*   wf_sk: Sk.wf md.(sk); *)
  (* } *)
  (* . *)
  Definition wf (md: t): Prop := <<WF: Sk.wf md.(sk)>>.
  (*** wf about modsem is enforced in the semantics ***)

  Definition add (md0 md1: t): t := {|
    get_modsem := fun skenv_link =>
                    ModSem.add (md0.(get_modsem) skenv_link) (md1.(get_modsem) skenv_link);
    sk := Sk.add md0.(sk) md1.(sk);
  |}
  .

  Theorem add_comm
          md0 md1
    :
      <<COMM: Beh.of_program (interp (add md0 md1)) <1= Beh.of_program (interp (add md1 md0))>>
  .
  Proof.
    ii.
    unfold interp in *. ss.
    eapply ModSem.add_comm; et.
    rp; et. do 4 f_equal.
    - admit "TODO: maybe the easy way is to 'canonicalize' the list by sorting.".
    - admit "TODO: maybe the easy way is to 'canonicalize' the list by sorting.".
  Qed.

  Theorem add_assoc
          md0 md1 md2
    :
      <<COMM: Beh.of_program (interp (add md0 (add md1 md2))) =
              Beh.of_program (interp (add (add md0 md1) md2))>>
  .
  Proof.
    admit "ez".
  Qed.

End MOD.
End Mod.


Module Equisatisfiability.
  Inductive pred: Type :=
  | true
  | false
  | meta (P: Prop)

  | disj: pred -> pred -> pred
  | conj: pred -> pred -> pred
  | neg: pred -> pred
  | impl: pred -> pred -> pred

  | univ (X: Type): (X -> pred) -> pred
  | exst (X: Type): (X -> pred) -> pred
  .

  (*** https://en.wikipedia.org/wiki/Negation_normal_form ***)
  Fixpoint embed (p: pred): itree eventE unit :=
    match p with
    | true => triggerUB
    | false => triggerNB
    | meta P => guarantee P

    | disj p0 p1 => b <- trigger (Choose _);; if (b: bool) then embed p0 else embed p1
    | conj p0 p1 => b <- trigger (Take _);; if (b: bool) then embed p0 else embed p1
    | neg p =>
      match p with
      | meta P => assume P
      | _ => triggerNB (*** we are assuming negation normal form ***)
      end
    | impl _ _ => triggerNB (*** we are assuming negation normal form ***)

    | @univ X k => x <- trigger (Take X);; embed (k x)
    | @exst X k => x <- trigger (Choose X);; embed (k x)
    end
  .

  (*** TODO: implication --> function call? ***)
  (***
P -> Q
~=
pname :=
  embed P

pqname :=
  (call pname) (finite times);;
  embed Q




(P -> Q) -> R
~=
pname :=
  embed P

pqname :=
  (call pname) (finite times);;
  embed Q

pqrname :=
  (call pqname) (finite times);;
  embed R
   ***)

  (* Fixpoint embed (p: pred) (is_pos: bool): itree eventE unit := *)
  (*   match p with *)
  (*   | true => triggerUB *)
  (*   | false => triggerNB *)
  (*   | meta P => guarantee P *)
  (*   | disj p0 p1 => b <- trigger (Choose _);; if (b: bool) then embed p0 is_pos else embed p1 is_pos *)
  (*   | conj p0 p1 => b <- trigger (Take _);; if (b: bool) then embed p0 is_pos else embed p1 is_pos *)
  (*   | @univ X k => x <- trigger (Take X);; embed (k x) is_pos *)
  (*   | @exst X k => x <- trigger (Choose X);; embed (k x) is_pos *)
  (*   | _ => triggerNB *)
  (*   end *)
  (* . *)
End Equisatisfiability.
