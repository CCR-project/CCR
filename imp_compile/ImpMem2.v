Require Import Coqlib.
Require Import Universe.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.

Import ImpNotations.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Section Mem2.

  Definition f :=
    mk_function
      ["ptr"]
      ["ptrV"; "newV"]
      ("ptrV" =#* "ptr" ;#
       "newV" =# 2%Z * "ptrV" ;#
       "ptr" + 8%Z *=# "newV")
  .

  Definition main : function := {|
    fn_params := [];
    fn_vars := ["ptr"; "a"; "b"];
    fn_body :=
      "ptr" =# alloc# (16%Z : expr) ;#
      "ptr" *=# 20%Z ;#
      @ "f" ["ptr" : expr] ;#
      "a" =#* "ptr" ;#
      "b" =#* "ptr" + 8%Z ;#
      free# ("ptr" : expr) ;#
      "a" + "b"
  |}.

  Definition imp_mem2_prog : program := {|
    prog_vars := [];
    prog_funs := [("main", main); ("f", f)];
  |}.

End Mem2.
