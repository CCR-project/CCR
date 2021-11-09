Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.



Section PROOF.
  Context `{Σ: GRA.t}.

  Import ImpNotations.
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition initF :=
    mk_function
      []
      ["init"; "initv"]
      ("init" =#& "initialized" ;# "initv" =#* "init" ;#
       if# "initv"
       then# @! "print" [(- 1)%Z : expr]
       else# @ "put" [0%Z: expr; 42%Z: expr] ;# "init" *=# 1%Z
       fi#
      )
  .

  Definition runF :=
    mk_function
      []
      ["init"; "initv"; "v"]
      ("init" =#& "initialized" ;# "initv" =#* "init" ;#
       if# ("initv" =? (1%Z))
       then# @! "print" [(- 1)%Z : expr]
       else# "v" =@ "get" [0%Z: expr] ;# @! "print" ["v": expr]
       fi#
      )
  .

  Definition Appprog: program :=
    mk_program
      "App"
      []
      [("put", 2); ("get", 1)]
      [("initialized", 0%Z)]
      [("init", initF); ("run", runF)]
  .

  Definition AppSem ge: ModSem.t := ImpMod.modsem Appprog ge.
  Definition App: Mod.t := ImpMod.get_mod Appprog.

End PROOF.
