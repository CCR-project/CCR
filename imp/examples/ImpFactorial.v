Require Import Coqlib.
Require Import ImpPrelude.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.

Section Example_Extract.

  Import ImpNotations.

  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition factorial : stmt :=
    "fptr" =#& "factorial" ;#
    if# "n"
    then# "output" =@* "fptr" ["n" - 1%Z] ;#
          "output" =# "n" * "output"
    else# "output" =# 1%Z
    fi#;#
    return# "output".

  Definition factorial_fundef : function := {|
    fn_params := ["n"];
    fn_vars := ["output"; "fptr"];
    fn_body := factorial
  |}.

  Definition main : stmt :=
    "in" =# 4%Z ;#
    "result" =@ "factorial" ["in": expr] ;#
    return# "result".

  Definition main_fundef : function := {|
    fn_params := [];
    fn_vars := ["in"; "result"];
    fn_body := main
  |}.

  Definition imp_factorial_prog : program := {|
    name := "Factorial";
    ext_vars := [];
    ext_funs := [];
    prog_vars := [];
    prog_funs := [("factorial", factorial_fundef); ("main", main_fundef)];
  |}.

End Example_Extract.
