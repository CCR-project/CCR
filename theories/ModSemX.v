Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.


Section EVENTS.

  (* Variable tb: fname -> option (Type * Type). *)
  Variable tb: fname -> (Type * Type).

  Variant eventE: Type -> Type :=
  | Choose (X: Type): eventE X
  | Take X: eventE X
  | Syscall (fn: fname) (m: Mem.t) (args: list val): eventE (Mem.t * val)
  (*** Syscall should be able to look at current memory (full information).
       Normal modules will call Memory (Language) module in order to call system call,
       because Memory (Language) module is the only one with access to Mem.t.
   ***)
  .

  Inductive callE: Type -> Type :=
  (* | Call X Y (fn: fname) (prf: tb fn = Some (X, Y)) (args: X): callE Y *)
  | Call (fn: fname) (args: fst (tb fn)): callE (snd (tb fn))
  .

  (* Notation "'Choose' X" := (trigger (Choose X)) (at level 50, only parsing). *)
  (* Notation "'Take' X" := (trigger (Take X)) (at level 50, only parsing). *)

  Definition triggerUB {E A} `{eventE -< E}: itree E A :=
    v <- trigger (Take void);; match v: void with end
  .

  Definition triggerNB {E A} `{eventE -< E}: itree E A :=
    v <- trigger (Choose void);; match v: void with end
  .

  Definition unwrapN {E X} `{eventE -< E} (x: option X): itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerNB
    end.

  Definition unwrapU {E X} `{eventE -< E} (x: option X): itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerUB
    end.

  Definition assume {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Take P) ;; Ret tt.
  Definition guarantee {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Choose P) ;; Ret tt.

  (* Notation "'unint?'" := (unwrapA <*> unint) (at level 57, only parsing). *)
  (* Notation "'unint﹗'" := (unwrapG <*> unint) (at level 57, only parsing). *)
  (* Notation "'Ret!' f" := (RetG f) (at level 57, only parsing). *)
  (* Notation "'Ret?' f" := (RetA f) (at level 57, only parsing). *)

  Context `{Σ: GRA.t}.

  Inductive rE: Type -> Type :=
  (* | MPut (mn: mname) (r: GRA): rE unit *)
  (* | MGet (mn: mname): rE GRA *)
  (* | FPut (r: GRA): rE unit *)
  (* | FGet: rE GRA *)
  | Put (mn: mname) (mr: Σ) (fr: Σ): rE unit
  | MGet (mn: mname): rE Σ
  | FGet: rE Σ
  (* | Get (mn: mname): rE (GRA * GRA) *)

  (*** NOTE: These methods can be implemented using Put/Get,
       but making it explicit will be helpful for meta-theory.
       E.g., In top-level, if all modules are well-typed,
       we can make "CheckWf" to Nop by adjusting handler.
   ***)
  | Forge (fr: Σ): rE unit
  | Discard (fr: Σ): rE unit
  | CheckWf (mn: mname): rE unit

  | PushFrame: rE unit
  | PopFrame: rE unit
  .

  Definition MPut E `{rE -< E} (mn: mname) (mr: Σ): itree E unit :=
    fr <- trigger FGet;;
    trigger (Put mn mr fr)
  .

  (*** TODO: we don't want to require "mname" here ***)
  (*** use dummy mname? ***)
  (* Definition FPut E `{rE -< E} (mn: mname) (fr: GRA): itree E unit := *)

  Definition Es: Type -> Type := (callE +' rE +' eventE).

  (* Inductive mdE: Type -> Type := *)
  (* | MPut (mn: mname) (r: GRA): mdE unit *)
  (* | MGet (mn: mname): mdE GRA *)
  (* . *)

  (* Inductive fnE: Type -> Type := *)
  (* | FPut (r: GRA): fnE unit *)
  (* | FGet: fnE GRA *)
  (* | FPush: fnE unit *)
  (* | FPop: fnE unit *)
  (* . *)

End EVENTS.

Notation "f '?'" := (unwrapU f) (at level 60, only parsing).
Notation "f '﹗'" := (unwrapN f) (at level 60, only parsing).





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

  Context `{Σ: GRA.t}.

  Record funX (tytable: string -> (Type * Type)): Type := mk_fun {
    XY: Type * Type;
    ktr:> (fst XY) -> itree (Es tytable) (snd XY);
  }
  .

  Record t: Type := mk {
    (* initial_ld: mname -> GRA; *)
    tytable: string -> (Type * Type);
    fnsems: list (fname * (funX tytable));
    initial_mrs: list (mname * Σ);
    (* wf_tytable: forall fn, tytable fn = option_map (fun '(_, fx) => fx.(XY)) *)
    (*                                                (List.find (fun '(_fn, _) => dec fn _fn) fnsems) *)
    wf_tytable: forall fn X Y,
        (List.find (fun '(_fn, _) => dec fn _fn) fnsems)
    (* sem: callE ~> itree Es := *)
    (*   fun _ '(Call fn args) => *)
    (*     '(_, sem) <- (List.find (fun fnsem => dec fn (fst fnsem)) fnsems)?;; *)
    (*     sem args *)
  }
  .

  Record wf (ms: t): Prop := mk_wf {
    wf_fnsems: NoDup (List.map fst ms.(fnsems));
    wf_initial_mrs: NoDup (List.map fst ms.(initial_mrs));
  }
  .

  (*** using "Program Definition" makes the definition uncompilable; why?? ***)



  Section INTERP.

  Variable ms: t.

  Let tb := ms.(tytable).

  Let sem: callE tb ~> itree (callE tb +' rE +' eventE) :=
    fun _ '(@Call _ X Y fn prf args) =>
      '(_, funX) <- (List.find (fun fnsem => dec fn (fst fnsem)) fnsems)?;;
      funX.(ktr) args
  .

  Let itr0: callE ~> itree Es :=
    fun _ ce =>
      trigger PushFrame;;
      rv <- (ms.(sem) ce);;
      trigger PopFrame;;
      Ret rv
  .
  Let itr1: itree (rE +' eventE) val := (mrec itr0) _ (Call "main" nil).



  Definition r_state: Type := ((mname -> Σ) * list Σ).
  Definition handle_rE `{eventE -< E} (no_forge: bool): rE ~> stateT r_state (itree E) :=
    fun _ e '(mrs, frs) =>
      match frs with
      | hd :: tl =>
        match e with
        | Put mn mr fr =>
          guarantee(URA.updatable (URA.add (mrs mn) hd) (URA.add mr fr));;
          Ret (((update mrs mn mr), fr :: tl), tt)
        | MGet mn => Ret ((mrs, frs), mrs mn)
        | FGet => Ret ((mrs, frs), hd)
        | Forge fr =>
          if no_forge then triggerUB else Ret ((mrs, (URA.add hd fr) :: tl), tt)
        | Discard fr =>
          rest <- trigger (Choose _);;
          guarantee(hd = URA.add fr rest);;
          Ret ((mrs, rest :: tl), tt)
        | CheckWf mn =>
          (if no_forge then Ret tt else assume(URA.wf (URA.add (mrs mn) hd)));;
          Ret ((mrs, frs), tt)
        | PushFrame =>
          Ret ((mrs, URA.unit :: frs), tt)
        | PopFrame =>
          Ret ((mrs, tl), tt)
        end
      | _ => triggerNB
      end.
  Definition interp_rE `{eventE -< E} (no_forge: bool): itree (rE +' E) ~> stateT r_state (itree E) :=
    State.interp_state (case_ (handle_rE no_forge) State.pure_state).
  Definition initial_r_state: r_state :=
    (fun mn => match List.find (fun mnr => dec mn (fst mnr)) ms.(initial_mrs) with
               | Some r => snd r
               | None => URA.unit
               end, []).
  Let itr2: itree (eventE) val := assume(<<WF: wf ms>>);; snd <$> (interp_rE false itr1) initial_r_state.
  Let itr2': itree (eventE) val := assume(<<WF: wf ms>>);; snd <$> (interp_rE true itr1) initial_r_state.



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

  Program Definition interp_no_forge: semantics := {|
    STS.state := state;
    STS.step := step;
    STS.initial_state := itr2';
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

  Context `{Σ: GRA.t}.

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
