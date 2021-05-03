Require Import Coqlib.
Require Import Universe.
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
             "n" + "g_ret"
       else# 0%Z
       fi#).

  Definition imp_mutsumF_prog : program :=
    mk_program
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
             "n" + "f_ret"
       else# 0%Z
       fi#).

  Definition imp_mutsumG_prog : program :=
    mk_program
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
       "r").

  Definition imp_mutsumMain_prog : program :=
    mk_program
      []
      [("main", mainF)]
  .

End Main.
