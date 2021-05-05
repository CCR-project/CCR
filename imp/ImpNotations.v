Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.

Set Implicit Arguments.

(* ========================================================================== *)
(** ** Notations *)

Module ImpNotations.

  (** A few notations for convenience.  *)
  Definition Expr_coerce: expr -> stmt := Expr.
  Definition Var_coerce: string -> expr := Var.
  Definition Lit_coerce: val -> expr := Lit.
  Definition Vint_coerce: Z -> val := Vint.
  Coercion Expr_coerce: expr >-> stmt.
  Coercion Var_coerce: string >-> expr.
  Coercion Lit_coerce: val >-> expr.
  Coercion Vint_coerce: Z >-> val.

  Declare Scope expr_scope.
  Bind Scope expr_scope with expr.

  Infix "+" := Plus : expr_scope.
  Infix "-" := Minus : expr_scope.
  Infix "*" := Mult : expr_scope.

  Declare Scope stmt_scope.
  Bind Scope stmt_scope with stmt.

  Notation "x '=#' e" :=
    (Assign x e) (at level 60, e at level 50): stmt_scope.

  Notation "a ';#' b" :=
    (Seq a b)
      (at level 100, right associativity,
       format
         "'[v' a  ';#' '/' '[' b ']' ']'"
      ): stmt_scope.

  Notation "'if#' i 'then#' t 'else#' e 'fi#'" :=
    (If i t e)
      (at level 100,
       right associativity,
       format
         "'[v ' 'if#'  i '/' '[' 'then#'  t  ']' '/' '[' 'else#'  e ']' '/' 'fi#' ']'").

  Notation "'skip#'" :=
    (Skip) (at level 100): stmt_scope.
 
  (* Different methods for function calls *)
  Notation "x '=@' f args" :=
    (CallFun1 x f args)
      (at level 60, f at level 9): stmt_scope.

  Notation "'@' f args" :=
    (CallFun2 f args)
      (at level 60, f at level 9): stmt_scope.

  Notation "x '=@*' fp args" :=
    (CallPtr1 x fp args)
      (at level 60, fp at level 9): stmt_scope.

  Notation "'@*' fp args" :=
    (CallPtr2 fp args)
      (at level 60, fp at level 9): stmt_scope.

  Notation "x '=@!' f args" :=
    (CallSys1 x f args)
      (at level 60, f at level 9): stmt_scope.

  Notation "'@!' f args" :=
    (CallSys2 f args)
      (at level 60, f at level 9): stmt_scope.

  (* interaction with the memory module *)
  Notation "x '=#&' X" :=
    (AddrOf x X) (at level 60): stmt_scope.

  Notation "x '=#' 'malloc#' s" :=
    (Malloc x s) (at level 60): stmt_scope.

  Notation "'free#' p" :=
    (Free p) (at level 60): stmt_scope.

  Notation "x '=#*' p" :=
    (Load x p) (at level 60): stmt_scope.

  Notation " p '*=#' v" :=
    (Store p v) (at level 60): stmt_scope.

  Notation "x '=#' '(' a '==' b ')'" :=
    (Cmp x a b) (at level 60): stmt_scope.

End ImpNotations.

(* ========================================================================== *)
(** ** Example *)
Section Example_Extract.

  Import ImpNotations.
  Let Σ: GRA.t := fun _ => of_RA.t RA.empty.
  Local Existing Instance Σ.

  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Definition factorial : stmt :=
    "fptr" =#& "factorial" ;#
    if# "input"
    then# "output" =@* "fptr" ["input" - 1%Z] ;#
          "output" =# "input" * "output"
    else# "output" =# 1%Z
    fi#;#
    "output".

  Definition factorial_fundef : function := {|
    fn_params := ["input"];
    fn_vars := ["output"; "fptr"];
    fn_body := factorial
  |}.

  Definition main : stmt :=
    "in" =@! "scanf" [] ;#
    "result" =@ "factorial" ["in": expr] ;#
    @! "printf" ["in": expr] ;#
    "result".

  Definition main_fundef : function := {|
    fn_params := [];
    fn_vars := ["in"; "result"];
    fn_body := main
  |}.

  Definition ex_extract : program := {|
    ext_vars := [];
    ext_funs := [];
    prog_vars := [];
    prog_funs := [("factorial", factorial_fundef); ("main", main_fundef)];
  |}.
  
  Definition ex_prog: Mod.t := ImpMod.get_mod "Main" ex_extract.

  Definition imp_ex := ModSemL.initial_itr_no_check (ModL.enclose ex_prog).

End Example_Extract.
