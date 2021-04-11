Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.

From compcert Require Import AST Integers Ctypes Clight Globalenvs.

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

  Context `{Σ: GRA.t}.
  Variable src : Mod.t.
  Variable src_ge : SkEnv.t.
  Variable tgt : program.
  (* Variable tgt_ge0 : Genv.t (Ctypes.fundef function) type. *)

  Context {s2p : string -> ident}.
  Context {to_long : Z -> int64}.

  Let Tlong0 :=
    (Tlong Signed noattr).

  Let Tptr0 tgt :=
    (Tpointer tgt noattr).

  Let string_key {T} l x : option T :=
    SetoidList.findA (String.string_dec x) l.

  Fixpoint compile_expr expr : option Clight.expr :=
    match expr with
    | Var x =>
      Some (Etempvar (s2p x) Tlong0)
    | Lit v =>
      match v with
      | Vint z => Some (Econst_long (to_long z) Tlong0)
      | _ => None
      end
    | Plus a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb =>
        Some (Ebinop Cop.Oadd ca cb Tlong0)
      | _, _ => None
      end
    | Minus a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb =>
        Some (Ebinop Cop.Osub ca cb Tlong0)
      | _, _ => None
      end
    | Mult a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb =>
        Some (Ebinop Cop.Omul ca cb Tlong0)
      | _, _ => None
      end
    end
  .
  (** vsub, vmul may not match with compcert's cop semantics *)

  Fixpoint compile_exprs (exprs: list Imp.expr) acc : option (list Clight.expr) :=
    match exprs with
    | h :: t =>
      do hexp <- (compile_expr h); compile_exprs t (hexp :: acc)
    | [] => Some acc
    end
  .

  Fixpoint compile_stmt stmt : option Clight.statement :=
    match stmt with
    | Assign x e =>
      do ex <- (compile_expr e); Some (Sset (s2p x) ex)
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

    | CallFun1 x f args =>
    | CallFun2 f args =>
    | CallPtr1 x pe args =>
    | CallPtr2 pe args =>
    | CallSys1 x f args =>
    | CallSys2 f args =>

    | Return1 r =>
      do cr <- (compile_expr r); Some (Sreturn (Some cr))
    | Return2 =>
      Some (Sreturn None)
    | AddrOf x GN =>
      Some (Sset (s2p x) (Eaddrof (Evar (s2p GN) Tlong0) Tlong0))
    | Load x pe =>
      do cpe <- (compile_expr pe); Some (Sset (s2p x) (Ederef cpe Tlong0))
    | Store X ve =>
      do vpe <- (compile_expr ve); Some (Sassign (Evar (s2p X) Tlong0) vpe)
    end
  .

End Compile.
