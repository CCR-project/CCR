Require Import Coqlib.
Require Import ImpPrelude.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.

Section Example_Extract.

  Import ImpNotations.

  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition main : stmt :=
    return# 99%Z.

  Definition main_fundef : function := {|
    fn_params := [];
    fn_vars := [];
    fn_body := main
  |}.

  Definition imp_simple_prog : program := {|
    name := "Simple";
    ext_vars := [];
    ext_funs := [];
    prog_vars := [];
    prog_funs := [("main", main_fundef)];
  |}.

End Example_Extract.
