Require Import ImpPrelude.
Require Import PCM.
Require Import ModSem.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.



Section MAP.

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

  Definition update :=
    mk_function
      ["h"; "k"; "v"]
      ["new_node"; "hd"]
      (
        "new_node" =# malloc# 3%Z ;#
        "hd" =#* "h" ;#
        ("new_node") *=# "k" ;#
        ("new_node" + 8%Z) *=# "v" ;#
        ("new_node" + 16%Z) *=# "hd" ;#
        "h" *=# "new_node"
      ).

  Definition access :=
    mk_function
      ["h"; "k"]
      ["hd"; "r"]
      (
        "hd" =#* "h" ;#
         "r" =@ "Map.loop" ["hd": expr; "k": expr] ;#
         return# "r"
      ).

  Definition loop :=
    mk_function
      ["cur"; "k"]
      ["curk"; "next"; "r"]
      ("curk" =#* "cur" ;#
        if# ("curk" =? "k")
        then# "r" =#* ("cur" + 8%Z) ;# return# "r"
        else# "next" =#* ("cur" + 16%Z) ;# "r" =@ "Map.loop" ["next": expr; "k": expr] ;# return# "r"
        fi#
      ).

  Definition Map_prog : program :=
    mk_program
      "Map"
      []
      []
      []
      [("Map.new", new); ("Map.update", update); ("Map.access", access); ("Map.loop", loop)]
  .

  Definition MapSem ge : ModSem.t := ImpMod.modsem Map_prog ge.
  Definition Map : Mod.t := ImpMod.get_mod Map_prog.

End MAP.
