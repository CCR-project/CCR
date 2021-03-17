Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.

Set Implicit Arguments.

(** 
Any state st & given step relation step (transition system)
st0 -(step A)-> st1/st2/st3/...
->
itree trigger Choose {states which satisfy (st0 -(step A)->) | all state}

f(st0) = Vis (Choose X) (cont: f(st1/st2/st3/...))

interp: ModSem.t -> semantics
semantics -> ModSem.t
 **)

Section CONV.

(**

function f (sm: semantics) (st0: semantics.state) 
: itree Es Any.t :=
stepA <- trigger (Choose sm.step);;
_ <- trigger (stepA st0);;
st1 <- trigger (Choose {states st' that satisfy (st0 -(stepA)-> st') | sm.state});;
f sm st1

 **)

  Context `{Σ: GRA.t}.
  CoFixpoint interpSTS
             (state: Type)
             (step: state -> option event -> state -> Prop)
             (state_sort: state -> sort):
    state -> itree eventE Any.t :=
    fun st0 =>
      match (state_sort st0) with
      | angelic =>
        Vis (Take {st': state | @step st0 None st' })
            (fun st1 => interpSTS step state_sort (proj1_sig st1))
      | demonic =>
        Vis (Choose {st': state | @step st0 None st' })
            (fun st1 => interpSTS step state_sort (proj1_sig st1))
      | final z =>
        Ret z↑
      | vis =>
        '(exist _ (event_sys fn args) _) <-
        trigger (Choose {ev': event | exists st', @step st0 (Some ev') st' });;
        v <- trigger (Syscall fn args);;
        Vis (Choose {st': state | @step st0 (Some (event_sys fn args)) st' })
            (fun st1 => interpSTS step state_sort (proj1_sig st1))
      end.

        (* let (fn, args) := *)
        (*     (iota _ (fun ev: event => exists st1, step st0 (Some ev) st1)) *)
        (* in *)
        (* v <- trigger (Syscall fn args);; *)
        (* Vis (subevent _ (Choose {st': state | @step st0 None st' })) *)
        (*     (fun st1 => interpSTS step state_sort (proj1_sig st1)) *)
  
  (* CoFixpoint interpSTS (state: Type) (step: state -> option event -> state -> Prop) : *)
  (*   state -> itree Es Any.t := *)
  (*   fun st0 => *)
  (*     Vis (subevent _ (Choose {st': state | @step st0 None st' })) *)
  (*         (fun st1 => interpSTS step (proj1_sig st1)). *)

End CONV.

