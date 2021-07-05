Require Import Coqlib.
Require Import ImpPrelude.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.

Import ImpNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Section F.

  Definition fF :=
    mk_function
      ["n"]
      ["g_ret"]
      (if# "n"
       then# "g_ret" =@ "g" ["n" - 1%Z : expr] ;#
             return# ("n" + "g_ret")
       else# return# (0%Z)
       fi#).

  Definition imp_mutsumF_prog : program :=
    mk_program
      "MutSumF"
      []
      [("g", 1)]
      []
      [("f", fF)]
  .

End F.

Section G.

  Definition gF :=
    mk_function
      ["n"]
      ["f_ret"]
      (if# "n"
       then# "f_ret" =@ "f" ["n" - 1%Z : expr] ;#
             return# ("n" + "f_ret")
       else# return# (0%Z)
       fi#).

  Definition imp_mutsumG_prog : program :=
    mk_program
      "MutSumG"
      []
      [("f", 1)]
      []
      [("g", gF)]
  .

End G.

Section Main.

  Definition mainF :=
    mk_function
      []
      ["r"]
      ("r" =@ "f" [10%Z : expr] ;#
       return# "r").

  Definition imp_mutsumMain_prog : program :=
    mk_program
      "MutSumMain"
      []
      [("f", 1)]
      []
      [("main", mainF)]
  .

End Main.
