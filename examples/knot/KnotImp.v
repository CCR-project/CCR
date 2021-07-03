Require Import ImpPrelude.
Require Import PCM.
Require Import ModSem.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.


Section Knot.

  Import ImpNotations.

  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Context `{Σ: GRA.t}.

  Definition knot : function := {|
    fn_params := ["fb"];
    fn_vars := ["blk"; "rb"];
    fn_body :=
      "blk" =#& "_f" ;#
      "blk" *=# "fb" ;#
      "rb" =#& "rec" ;#
      return# "rb"
  |}.

  Definition rec : function := {|
    fn_params := ["n"];
    fn_vars := ["blk"; "fb"; "rb"; "ret"];
    fn_body :=
      "blk" =#& "_f" ;#
      "fb" =#* "blk" ;#
      "rb" =#& "rec" ;#
      "ret" =@* "fb" ["rb" : expr; "n" : expr] ;#
      return# "ret"  
  |}.

  Definition Knot_prog : program := {|
    name := "Knot";
    ext_vars := [];
    ext_funs := [];
    prog_vars := [("_f", 0%Z)];
    prog_funs := [("rec", rec); ("knot", knot)];
  |}.

  Definition KnotSem ge : ModSem.t := ImpMod.modsem Knot_prog ge.
  Definition Knot : Mod.t := ImpMod.get_mod Knot_prog.

End Knot.
