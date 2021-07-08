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

  Definition repeat : function := {|
    fn_params := ["fb"; "n"; "x"];
    fn_vars := ["v"; "ret"];
    fn_body :=
      if# ("n" < 1%Z)
      then# return# "x"
      else# ("v" =@* "fb" ["x" : expr] ;#
             "ret" =@ "repeat" ["fb": expr; ("n" - 1%Z): expr; "v": expr] ;#
             return# "ret"
            )
      fi#
  |}.

  Definition Repeat_prog : program := {|
    name := "Repeat";
    ext_vars := [];
    ext_funs := [];
    prog_vars := [];
    prog_funs := [("repeat", repeat)];
  |}.

  Definition RepeatSem ge : ModSem.t := ImpMod.modsem Repeat_prog ge.
  Definition Repeat : Mod.t := ImpMod.get_mod Repeat_prog.

End Knot.
