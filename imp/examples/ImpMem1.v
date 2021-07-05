Require Import Coqlib.
Require Import ImpPrelude.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.

Import ImpNotations.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.
Section Mem1.

  Definition f :=
    mk_function
      []
      ["GP"; "ret"]
      ( "GP" =#& "G" ;#
        "GP" *=# 55%Z ;#
        "ret" =#* "GP" ;#
        return# "ret")
  .

  Definition imp_mem1_f : program := {|
    name := "Mem1F";
    ext_vars := ["G"];
    ext_funs := [];
    prog_vars := [];
    prog_funs := [("f", f)];
  |}.

  Definition main :=
    "GP" =#& "G" ;#
    "GP" *=# 33%Z ;#
    "ret" =@ "f" [] ;#
    "Gval" =#* "GP" ;#
    return# "Gval"
  .

  Definition main_def : function := {|
    fn_params := [];
    fn_vars := ["GP"; "ret"; "Gval"];
    fn_body := main
  |}.

  Definition imp_mem1_main : program := {|
    name := "Mem1Main";
    ext_vars := [];
    ext_funs := [("f", 0)];
    prog_vars := [("G", 3%Z)];
    prog_funs := [("main", main_def)];
  |}.

End Mem1.
