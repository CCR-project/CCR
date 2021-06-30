Require Import Universe.
Require Import PCM.
Require Import ModSem.
Require Import Imp.
Require Import ImpNotations.

Set Implicit Arguments.

Section CLIENT.

  Context `{Σ: GRA.t}.

  Import ImpNotations.
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.


  (* Definition pop := *)
  (*   mk_function *)
  (*     ["stk"] *)
  (*     ["hd"; "b"; "v"; "next"] *)
  (*     ( *)
  (*       "hd" =#* "stk" ;# *)
  (*       "b" =# ("hd" == 0%Z) ;# *)
  (*       if# "b" *)
  (*       then# return# (-1)%Z *)
  (*       else# ("v" =#* "hd" ;# *)
  (*              "next" =#* ("hd" + 8%Z) ;# *)
  (*              free# "hd" ;# *)
  (*              free# ("hd" + 8%Z) ;# *)
  (*              "stk" *=# "next" ;# *)
  (*              return# "v") *)
  (*       fi# *)
  (*     ). *)

  (* Definition Stack_prog : program := *)
  (*   mk_program *)
  (*     "Stack" *)
  (*     [] *)
  (*     [] *)
  (*     [] *)
  (*     [("new", new); ("pop", pop); ("push", push)] *)
  (* . *)

  (* Definition StackSem ge : ModSem.t := ImpMod.modsem Stack_prog ge. *)
  (* Definition Stack : Mod.t := ImpMod.get_mod Stack_prog. *)

End CLIENT.
