Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Generalizable Variables E R A B C X Y Z.

Set Implicit Arguments.






Section INTERP.

  Context `{GRA: GRA.t}.
  Variable ms: ModSem.t.

  Let itr0: callE ~> itree (callE +' mdE +' fnE +' eventE) :=
    fun _ ce =>
      trigger FPush;;
      rv <- (ms.(ModSem.sem) ce);;
      trigger FPop;;
      Ret rv
  .
  Let itr1: itree (mdE +' fnE +' eventE) val := (mrec itr0) _ (Call "main" nil).



  Definition md_state: Type := mname -> GRA.
  Definition handle_mdE `{eventE -< E}: mdE ~> stateT md_state (itree E) :=
    fun _ e st0 =>
      match e with
      | MPut mn gr =>
        guarantee(RA.updatable (st0 mn) gr);;
        Ret (update st0 mn gr, tt)
      | MGet mn => Ret (st0, st0 mn)
      end.
  Definition interp_mdE `{eventE -< E}: itree (mdE +' E) ~> stateT md_state (itree E) :=
    State.interp_state (case_ handle_mdE State.pure_state).
  Let itr2: itree (fnE +' eventE) val := snd <$> (interp_mdE itr1) (fun _ => URA.unit).



  Definition fn_state: Type := list GRA.
  Definition handle_fnE `{eventE -< E}: fnE ~> stateT fn_state (itree E) :=
    fun _ e st0 =>
      match e with
      | FPut gr =>
        match st0 with
        | nil => triggerNB
        | hd :: tl =>
          guarantee(RA.updatable hd gr);;
          Ret (gr :: tl, tt)
        end
      | FGet =>
        hd <- (hd_error st0)﹗ ;;
        Ret (st0, hd)
      | FPush =>
        Ret (URA.unit :: st0, tt)
      | FPop =>
        Ret (tl st0, tt)
      end.
  Definition interp_fnE `{eventE -< E}: itree (fnE +' E) ~> stateT fn_state (itree E) :=
    State.interp_state (case_ handle_fnE State.pure_state).
  Let itr3: itree (eventE) val := snd <$> (interp_fnE itr2) nil.

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
    STS.initial_state := itr3;
    STS.state_sort := state_sort;
  |}
  .
  Next Obligation. inv STEP; inv STEP0; ss. csc. rewrite SYSCALL in *. csc. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.

End INTERP.
