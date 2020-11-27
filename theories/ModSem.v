Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.

Set Implicit Arguments.


Section EVENTS.

  Inductive eventE: Type -> Type :=
  | Choose X: eventE X
  | Take X: eventE X
  | Syscall (fn: fname) (m: Mem.t) (args: list val): eventE (Mem.t * val)
  (*** Syscall should be able to look at current memory (full information).
       Normal modules will call Memory (Language) module in order to call system call,
       because Memory (Language) module is the only one with access to Mem.t.
   ***)
  .

  Inductive callE: Type -> Type :=
  | Call (fn: fname) (args: list val): callE val
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
    | Some x => ret x
    | None => triggerNB
    end.

  Definition unwrapU {E X} `{eventE -< E} (x: option X): itree E X :=
    match x with
    | Some x => ret x
    | None => triggerUB
    end.

  Definition assume {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Take P) ;; Ret tt.
  Definition guarantee {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Choose P) ;; Ret tt.

  (* Notation "'unint?'" := (unwrapA <*> unint) (at level 57, only parsing). *)
  (* Notation "'unint﹗'" := (unwrapG <*> unint) (at level 57, only parsing). *)
  (* Notation "'Ret!' f" := (RetG f) (at level 57, only parsing). *)
  (* Notation "'Ret?' f" := (RetA f) (at level 57, only parsing). *)

  Context `{GRA: GRA.t}.

  Inductive mdE: Type -> Type :=
  | MPut (mn: mname) (r: GRA): mdE unit
  | MGet (mn: mname): mdE GRA
  .

  Inductive fnE: Type -> Type :=
  | FPut (r: GRA): fnE unit
  | FGet: fnE GRA
  | FPush: fnE unit
  | FPop: fnE unit
  .

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

  Context `{GRA: GRA.t}.

  Record t: Type := mk {
    sk: Sk.t;
    (* initial_ld: mname -> GRA; *)
    sem: callE ~> itree (callE +' mdE +' fnE +' eventE);
    initial_ld: list (mname * GRA);
  }
  .

  Definition wf (md: t): Prop := Sk.wf md.(sk).

  (*** using "Program Definition" makes the definition uncompilable; why?? ***)
  Definition merge (md0 md1: t): t := {|
    sk := Sk.add md0.(sk) md1.(sk);
    (* initial_ld := URA.add (t:=URA.pointwise _ _) md0.(initial_ld) md1.(initial_ld); *)
    sem := fun _ '(Call fn args) =>
             (if List.in_dec string_dec fn md0.(sk) then md0.(sem) else md1.(sem)) _ (Call fn args);
    initial_ld := app md0.(initial_ld) md0.(initial_ld);
  |}
  .

End MODSEM.
End ModSem.
