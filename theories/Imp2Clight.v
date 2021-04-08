Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.

From compcert Require Import AST.
From compcert Require Import Integers.
From compcert Require Import Ctypes.
From compcert Require Import Clight.

Import Int.

Set Implicit Arguments.

Section Compile.
  
  (* Definition cast (nextID: AST.ident) := var -> option (AST.ident * type). *)
  (* Definition empty : cast 1%positive := fun _ => None. *)

  (* Definition update_cast {i} newKey newType (curr: cast i) : cast (Pos.succ i):= *)
  (*   fun key => *)
  (*     if (String.string_dec key newKey) then (Some (i, newType)) *)
  (*     else (curr key). *)

  (* Hypothesis is_int : *)
  (*   forall (intval : Z), *)
  (*     ((Zneg xH) < intval < modulus)%Z. *)

  Variable m : Imp.module.
  Variable f : Imp.function.
  
  Variable s2p : string -> ident.
  Variable to_int : Z -> int.

  Let canon_Tint :=
    (Tint I32 Signed noattr).

  Let canon_Tptr tgt :=
    (Tpointer tgt noattr).

  Fixpoint compile_type imp_ty : type :=
    match imp_ty with
    | Imp.Tint => canon_Tint
    | Imp.Tptr tgt => canon_Tptr (compile_type tgt)
    end.

  Let i2c_names inames :=
    List.map (fun '(name, ty) => (s2p name, compile_type ty)) inames.

  Let cfn_params := i2c_names f.(Imp.fn_params).
  Let cfn_temps := i2c_names f.(Imp.fn_vars).

  Let string_key {T} l x : option T :=
    SetoidList.findA (sflib.beq_str x) l.

  Let imp_vs := f.(Imp.fn_params) ++ f.(Imp.fn_vars).

  Let iv2t x := string_key imp_vs x.
  
  Fixpoint compile_expr expr : option Clight.expr :=
    match expr with
    | Var x =>
      do ty <- (iv2t x); Some (Etempvar (s2p x) (compile_type ty))
    | Lit v =>
      match v with
      | Vint z => Some (Econst_int (to_int z) canon_Tint)
      | _ => None
      end
    | Plus a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb =>
        match (typeof ca), (typeof cb) with
        | Tint _ _ _, Tint _ _ _ =>
          Some (Ebinop Cop.Oadd ca cb canon_Tint)
        | Tint _ _ _, Tpointer _ _ =>
          Some (Ebinop Cop.Oadd ca cb (typeof cb))
        | Tpointer _ _, Tint _ _ _ =>
          Some (Ebinop Cop.Oadd ca cb (typeof ca))
        | _, _ => None
        end
      | _, _ => None
      end
    | Minus a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb =>
        match (typeof ca), (typeof cb) with
        | Tint _ _ _, Tint _ _ _ =>
          Some (Ebinop Cop.Osub ca cb canon_Tint)
        | Tint _ _ _, Tpointer _ _ =>
          Some (Ebinop Cop.Osub ca cb (typeof cb))
        | Tpointer _ _, Tint _ _ _ =>
          Some (Ebinop Cop.Osub ca cb (typeof ca))
        | _, _ => None
        end
      | _, _ => None
      end
    | Mult a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb =>
        match (typeof ca), (typeof cb) with
        | Tint _ _ _, Tint _ _ _ =>
          Some (Ebinop Cop.Omul ca cb canon_Tint)
        | Tint _ _ _, Tpointer _ _ =>
          Some (Ebinop Cop.Omul ca cb (typeof cb))
        | Tpointer _ _, Tint _ _ _ =>
          Some (Ebinop Cop.Omul ca cb (typeof ca))
        | _, _ => None
        end
      | _, _ => None
      end
    end
  .

  Fixpoint compile_exprs (exprs: list Imp.expr) acc : option (list Clight.expr) :=
    match exprs with
    | h :: t =>
      do hexp <- (compile_expr h); compile_exprs t (hexp :: acc)
    | [] => Some acc
    end
  .

  Definition get_fun_expr fn rt : option Clight.expr :=
    do (string_key m.(mod_funs)
  
  Fixpoint compile_stmt stmt : option Clight.statement :=
    match stmt with
    | Assign x e =>
      do ex <- (compile_expr e);
      Some (Sset (s2p x) ex)
    | Seq s1 s2 =>
      do cs1 <- (compile_stmt s1);
      do cs2 <- (compile_stmt s2);
      Some (Ssequence cs1 cs2)
    | If cond sif selse =>
      do cc <- (compile_expr cond);
      do cif <- (compile_stmt sif);
      do celse <- (compile_stmt selse);
      Some (Sifthenelse cc cif celse)
    | While cond body =>
      do cc <- (compile_expr cond);
      do cbody <- (compile_stmt body);
      Some (Swhile cc cbody)
    | Skip =>
      Some Sskip
    | CallFun x ftype args =>
      do cargs <- (compile_exprs args []);
      match ftype with
      | Fun fn rt =>
        let f = (Evar (s2p fn) (Tfunction )) in
        Some (Scall (Some (s2p x)) f cargs)
      | Sys sn rt =>
        do s <- (compile_expr (Var sn));
        Some (Scall (Some (s2p x)) s cargs)
      end
    | Return r =>
      do cr <- (compile_expr r);
      Some (Sreturn (Some cr))
    end
  .

End Compile.
