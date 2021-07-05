Require Import Coqlib.
Require Import ImpPrelude.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.

Import ImpNotations.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Section Knot.

  Definition rec : function := {|
    fn_params := ["n"];
    fn_vars := ["_fA"; "_fP"; "recP"; "ret"];
    fn_body :=
      "_fA" =#& "_f" ;#
      "_fP" =#* "_fA" ;#
      "recP" =#& "rec" ;#
      "ret" =@* "_fP" ["recP" : expr; "n" : expr] ;#
      return# "ret"  
  |}.

  Definition knot : function := {|
    fn_params := ["fP"];
    fn_vars := ["_fA"; "recP"];
    fn_body :=
      "_fA" =#& "_f" ;#
      "_fA" *=# "fP" ;#
      "recP" =#& "rec" ;#
      return# "recP"
  |}.

  Definition _fib : function := {|
    fn_params := ["fibP"; "n"];
    fn_vars := ["a"; "b"];
    fn_body :=
      if# ("n")
      then#
            if# ("n" - 1%Z)
            then#
                  "a" =@* "fibP" ["n" - 1%Z] ;#
                  "b" =@* "fibP" ["n" - 2%Z] ;#
                  return# ("a" + "b")
            else# return# 1%Z
            fi#
      else# return# 1%Z
      fi#
  |}.

  Definition main : function := {|
    fn_params := [];
    fn_vars := ["_fibP"; "fibP"; "ret"];
    fn_body := 
      "_fibP" =#& "_fib" ;#
      "fibP" =@ "knot" ["_fibP" : expr] ;#
      "ret" =@* "fibP" [10%Z : expr] ;#
      return# "ret"
  |}.

  Definition imp_knot_prog : program := {|
    name := "Knot";
    ext_vars := [];
    ext_funs := [];
    prog_vars := [("_f", 0%Z)];
    prog_funs :=
      [("rec", rec); ("knot", knot);
       ("_fib", _fib); ("main", main)];
  |}.

End Knot.
