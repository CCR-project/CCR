Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.






Section INTERP.

  Context `{GRA: GRA.t}.
  Variable ms: ModSem.t.

  Let itr0: callE ~> itree Es :=
    fun _ ce =>
      trigger PushFrame;;
      rv <- (ms.(ModSem.sem) ce);;
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
    (fun mn => match List.find (fun mnr => dec mn (fst mnr)) ms.(ModSem.initial_ld) with
               | Some r => snd r
               | None => URA.unit
               end, []).
  Let itr2: itree (eventE) val := snd <$> (interp_rE itr1) initial_r_state.



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
