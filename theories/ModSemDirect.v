Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.


Section EVENTS.

  Context `{Σ: GRA.t}.

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
  | Call (fn: fname) (varg: list val) (rarg: Σ): callE val
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
  | Discard (fr: Σ): rE unit

  | PushFrame (fr: Σ): rE unit
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



Section AUX.
  Context {Σ: GRA.t}.
  Definition ε: Σ := URA.unit. (*** TODO: move to PCM.v ***)
End AUX.



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

  Record t: Type := mk {
    (* initial_ld: mname -> GRA; *)
    fnsems: list (fname * (list val -> itree Es val));
    initial_mrs: list (mname * Σ);
  }
  .

  Record wf (ms: t): Prop := mk_wf {
    wf_fnsems: NoDup (List.map fst ms.(fnsems));
    wf_initial_mrs: NoDup (List.map fst ms.(initial_mrs));
  }
  .

  Section INTERP.

  Variable ms: t.

  Let itr0: callE ~> itree Es :=
    fun _ '(Call fn varg rarg) =>
      '(_, sem) <- (List.find (fun fnsem => dec fn (fst fnsem)) ms.(fnsems))?;;
      trigger (Discard rarg);;
      trigger (PushFrame rarg);;
      rv <- (sem varg);;
      rest <- trigger (Choose _);;
      trigger (Discard rest);;
      trigger PopFrame;;
      Ret rv
  .
  Let itr1: itree (rE +' eventE) val := (mrec itr0) _ (Call "main" nil ε).



  Definition r_state: Type := ((mname -> Σ) * list Σ).
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
        | Discard fr =>
          rest <- trigger (Choose _);;
          guarantee(hd = URA.add fr rest);;
          Ret ((mrs, rest :: tl), tt)
        | PushFrame fr =>
          Ret ((mrs, fr :: frs), tt)
        | PopFrame =>
          match tl with
          | nil => Ret ((mrs, nil), tt)
          | hd_caller :: tl => Ret ((mrs, (URA.add hd hd_caller) :: tl), tt)
          end
        end
      | _ => triggerNB
      end.
  Definition interp_rE `{eventE -< E} (no_forge: bool): itree (rE +' E) ~> stateT r_state (itree E) :=
    State.interp_state (case_ (handle_rE) State.pure_state).
  Definition initial_r_state: r_state :=
    (fun mn => match List.find (fun mnr => dec mn (fst mnr)) ms.(initial_mrs) with
               | Some r => snd r
               | None => ε
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

End MOD.
End Mod.

