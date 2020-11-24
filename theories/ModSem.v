Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.

Set Implicit Arguments.



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

  Inductive eventE: Type -> Type :=
  | Choose X: eventE X
  | Take X: eventE X
  .

  Context `{GRA: GRA.t}.

  Inductive callE: Type -> Type :=
  | Call (fptr: val) (args: list val): callE val
  .

  Inductive ldE: Type -> Type :=
  | LPut (r: (GRA.construction GRA)): ldE unit
  | LGet: ldE (GRA.construction GRA)
  .

  Record t: Type := mk {
    sk: Sk.t;
    initial_ld: GRA.construction GRA;
    sem: callE ~> itree (callE +' ldE);
  }
  .

  Definition wf (md: t): Prop := Sk.wf md.(sk).

  (*** using "Program Definition" makes the definition uncompilable; why?? ***)
  Definition merge (md0 md1: t): t := {|
    sk := Sk.add md0.(sk) md1.(sk);
    initial_ld := URA.add md0.(initial_ld) md1.(initial_ld);
    (* sem := fun _ c => match c with *)
    (*                   | call fptr args => md0.(sem) (call fptr args) *)
    (*                   end *)
    sem := fun _ '(Call fptr args) =>
             if md0.(sk) md0.(sem) (Call fptr args);
  |}
  .

End MODSEM.
End ModSem.

Inductive ModSem: Type :=
  mk_ModSem { fnames: string -> bool ;
              owned_heap: Type;
              initial_owned_heap: owned_heap;
              customE: Type -> Type ;
              handler: customE ~> stateT owned_heap (itree (GlobalE +' Event));

              (* handler: forall E, AnyState ~> stateT Any (itree E); *)
              (* sem: CallExternalE ~> itree (CallExternalE +' Event); *)

              sem: CallExternalE ~> itree (CallExternalE +' customE +' GlobalE +' Event);
            }.
