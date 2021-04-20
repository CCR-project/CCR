Require Import Coqlib.
Require Import Universe.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.

Section Example_Extract.

  Import ImpNotations.

  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition main : stmt :=
    99%Z.

  Definition main_fundef : function := {|
    fn_params := [];
    fn_vars := [];
    fn_body := main
  |}.

  Definition imp_simple_mod : module := {|
    mod_vars := [];
    mod_funs := [("main", main_fundef)];
  |}.

End Example_Extract.
