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


(***
F.f(n) {
  if (n < 0) {
    Log.log("error")
    r := -1
  } else if (n == 0) {
    r := 0
  } else if (n == 100) {
    r := ...
  } else {
    r := 2 + call G.g(n)
  }
  r
}
***)

Section F.
  Context `{Σ: GRA.t}.

  Import ImpNotations.
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition fF :=
    mk_function
      ["n"]
      ["r"]
      (if# ("n" < 0%Z)
       then# @ "log" ["n" : expr] ;# return# (- 1)%Z
       else#
         (if# ("n" =? 0%Z)
          then# return# 0%Z
          else#
            (if# ("n" =? 100%Z)
             then# return# 500%Z
             else# "r" =@ "g" ["n" : expr] ;# return# ("r" + 2%Z)
             fi#)
          fi#) 
       fi#).

  Definition f_prog : program :=
    mk_program
      "F"
      []
      [("g", 1)]
      []
      [("f", fF)]
  .

  Definition FSem ge: ModSem.t := ImpMod.modsem f_prog ge.
  Definition F : Mod.t := ImpMod.get_mod f_prog.

End F.
