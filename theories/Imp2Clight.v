Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.

From compcert Require Import Clight.
From compcert Require Import Integers.
From compcert Require Import Ctypes.

Import Int.

Set Implicit Arguments.

Section Compile.

  Definition cast (nextID: AST.ident) := var -> option (AST.ident * type).
  Definition empty : cast 1%positive := fun _ => None.

  Definition update_cast {i} newKey newType (curr: cast i) : cast (Pos.succ i):=
    fun key =>
      if (String.string_dec key newKey) then (Some (i, newType))
      else (curr key).

  Hypothesis is_int :
    forall (intval : Z),
      ((Zneg xH) < intval < modulus)%Z.
  
  Let attr_bot : attr := {|
    attr_volatile := false; attr_alignas := None;
  |}.

  Let canon_Tint :=
    (Tint I32 Signed attr_bot).

  (* Let canon_Tptr := *)
  (*   (Tpointer canon_Tint attr_bot). *)
  
  Fixpoint compile_expr leCast expr : option Clight.expr :=
    match expr with
    | Var x =>
      match (leCast x) with
      | None => None
      | Some (i, t) => Some (Etempvar i t)
      end
    | Lit v =>
      match v with
      | Vint z => Some (Econst_int (mkint z (is_int z)) canon_Tint)
      | _ => None
      end
    | Plus a b =>
      match (compile_expr leCast a), (compile_expr leCast b) with
      | Some (Econst_int x t), Some (Econst_int y s) =>
        Some (Ebinop Cop.Oadd (Econst_int x t) (Econst_int y s) canon_Tint)
      | _, _ => None
      end
    | Minus a b =>
      match (compile_expr leCast a), (compile_expr leCast b) with
      | Some (Econst_int x t), Some (Econst_int y s) =>
        Some (Ebinop Cop.Osub (Econst_int x t) (Econst_int y s) canon_Tint)
      | _, _ => None
      end
    | Mult a b =>
      match (compile_expr leCast a), (compile_expr leCast b) with
      | Some (Econst_int x t), Some (Econst_int y s) =>
        Some (Ebinop Cop.Omul (Econst_int x t) (Econst_int y s) canon_Tint)
      | _, _ => None
      end
    end
  .

  Fixpoint compile_exprs leCast (exprs: list Imp.expr) : option (list Clight.expr) :=
    match exprs with
    | h :: t =>
      match (compile_expr leCast h), (compile_exprs leCast t) with
      | Some h', Some t' => Some (h' :: t')
      | _, _ => None
      end
    | [] => Some []
    end
  .
  
  Fixpoint type_Imp_expr (leCast: string -> option (AST.ident * type)) expr : option type :=
    match expr with
    | Var x =>
      match (leCast x) with
      | None => None
      | Some (_, t) => Some t
      end
    | Lit v =>
      match v with
      | Vint _ => Some canon_Tint
      | _ => None
      end
    | Plus a b =>
      match (type_Imp_expr leCast a), (type_Imp_expr leCast b) with
      | Some (Tint _ _ _), Some (Tint _ _ _) => Some canon_Tint
      | _, _ => None
      end
    | Minus a b =>
      match (type_Imp_expr leCast a), (type_Imp_expr leCast b) with
      | Some (Tint _ _ _), Some (Tint _ _ _) => Some canon_Tint
      | _, _ => None
      end
    | Mult a b =>
      match (type_Imp_expr leCast a), (type_Imp_expr leCast b) with
      | Some (Tint _ _ _), Some (Tint _ _ _) => Some canon_Tint
      | _, _ => None
      end
    end
  .
  
  Fixpoint compile_stmt leCast stmt : option Clight.statement :=
    match stmt with
    | Assign x e =>
      match (type_Imp_expr leCast e) with
      | Some t => Some (Sset ((update_cast x t leCast) x) (compile_expr leCast e))
      | _ => None
      end
    | Seq s1 s2 =>
      match (compile_stmt leCast s1), (compile_stmt leCast s2) with
      | Some cs1, Some cs2 => Some (Ssequence cs1 cs2)
      | _ => None
      end
    | If cond sif selse =>
      match (compile_expr leCast cond), (compile_stmt leCast sif), (compile_stmt leCast selse) with
      | Some cc, Some cif, Some celse =>
        Some (Sifthenelse cc cif celse)
      | _ => None
      end
    | While cond body =>
      match (compile_expr leCast cond), (compile_stmt leCast body) with
      | Some cc, Some cb => Some (Swhile cc cb)
      | _ => None
      end
    | Skip =>
      Some Sskip
    | CallFun x ftype args =>
      match (leCast x), (compile_exprs leCast args) with
      | Some (i, t), Some cargs =>
        match ftype with
        | Fun fn =>
          Some (Scall (Some i) (compile_expr (Var fn)) cargs
      
    | Return r =>
    end
  .
  


End Compile.
