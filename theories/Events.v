Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import PCM.
Require Import STS Behavior.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.


Section EVENTS.

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



Section AUX.
  Context {Σ: GRA.t}.
  Definition ε: Σ := URA.unit. (*** TODO: move to PCM.v ***)
End AUX.


