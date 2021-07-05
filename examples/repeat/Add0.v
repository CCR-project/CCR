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

  Definition succ : function := {|
    fn_params := ["n"];
    fn_vars := [];
    fn_body :=
      return# ("n" + 1%Z)
  |}.

  Definition add : function := {|
    fn_params := ["n"; "m"];
    fn_vars := ["succb"; "ret"];
    fn_body :=
      "succb" =#& "succ" ;#
      "ret" =@ "repeat" ["succb": expr; "m": expr; "n": expr] ;#
      return# "ret"
  |}.

  Definition Add_prog : program := {|
    name := "Add";
    ext_vars := [];
    ext_funs := [];
    prog_vars := [];
    prog_funs := [("succ", succ); ("add", add)];
  |}.

  Definition AddSem ge : ModSem.t := ImpMod.modsem Add_prog ge.
  Definition Add : Mod.t := ImpMod.get_mod Add_prog.

End Knot.
