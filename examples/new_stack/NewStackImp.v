Require Import Universe.
Require Import PCM.
Require Import ModSem.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.



Section STACK.

  Context `{Σ: GRA.t}.

  Import ImpNotations.
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition new :=
    mk_function
      []
      ["new_node"]
      (
        "new_node" =# malloc# 1%Z ;#
        "new_node" *=# 0%Z ;#
        return# "new_node"
      ).

  Definition pop :=
    mk_function
      ["stk"]
      ["hd"; "b"; "v"; "next"]
      (
        "hd" =#* "stk" ;#
        "b" =# ("hd" == 0%Z) ;#
        if# "b"
        then# return# (-1)%Z
        else# ("v" =#* "hd" ;#
               "next" =#* ("hd" + 8%Z) ;#
               free# "hd" ;#
               free# ("hd" + 8%Z) ;#
               "stk" *=# "next" ;#
               return# "v")
        fi#
      ).

  Definition push :=
    mk_function
      ["stk"; "v"]
      ["new_node"; "addr_next"; "hd"]
      (
        "new_node" =# malloc# 2%Z ;#
        "addr_next" =# "new_node" + 8%Z ;#
        "hd" =#* "stk" ;#
        "new_node" *=# "v" ;#
        "addr_next" *=# "hd" ;#
        "stk" *=# "new_node"
      ).

  Definition Stack_prog : program :=
    mk_program
      "Stack"
      []
      []
      []
      [("new", new); ("pop", pop); ("push", push)]
  .

  Definition StackSem ge : ModSem.t := ImpMod.modsem Stack_prog ge.
  Definition Stack : Mod.t := ImpMod.get_mod Stack_prog.

End STACK.
