Require Import ImpPrelude.
Require Import PCM.
Require Import ModSem.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.


Section Knot.

  Import ImpNotations.

  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Context `{Σ: GRA.t}.

  Definition fib : function := {|
    fn_params := ["fb"; "n"];
    fn_vars := ["n0"; "n1"];
    fn_body :=
      if# ("n" < 2%Z)
      then# return# 1%Z
      else#
            "n0" =@* "fb" ["n" - 1%Z] ;#
            "n1" =@* "fb" ["n" - 2%Z] ;#
            return# ("n0" + "n1")
      fi#
  |}.

  Definition main : function := {|
    fn_params := [];
    fn_vars := ["fibb"; "fb"; "ret"];
    fn_body := 
      "fibb" =#& "fib" ;#
      "fb" =@ "knot" ["fibb" : expr] ;#
      "ret" =@* "fb" [10%Z : expr] ;#
      return# "ret"
  |}.

  Definition KnotMain_prog : program := {|
    name := "Main";
    ext_vars := [];
    ext_funs := [("knot", 1)];
    prog_vars := [];
    prog_funs := [("fib", fib); ("main", main)];
  |}.

  Definition KnotMainSem ge : ModSem.t := ImpMod.modsem KnotMain_prog ge.
  Definition KnotMain : Mod.t := ImpMod.get_mod KnotMain_prog.

End Knot.
