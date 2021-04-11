Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.

From compcert Require Import AST Integers Ctypes Clight Globalenvs Linking.

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

  (* compile each module indiv, 
     prove behavior refinement for whole (closed) prog after linking *)
  Context `{Σ: GRA.t}.
  Variable src : Mod.t.
  Variable src_ge : SkEnv.t.
  Variable tgt : program.
  (* Variable tgt_ge0 : Genv.t (Ctypes.fundef function) type. *)

  Context {s2p : string -> ident}.
  Context {to_long : Z -> int64}.

  (* initial gdefs = Imp.module, 
     contains single module's glob vars & internal funs. *)
  (* compile_stmt updates gdefs to include syscall defs. *)
  (* external funs (not syscall) : in other mod (resolved by linking) / 
     syscall : update gdefs dynamically by syntax *)
  (* no external variables: with weak typing, can resort to linking *)
  (* alloc/free should remain external (EF_malloc, EF_free)
     -> memory mod is not compiled with other Imps, 
     load/store are compiled in other way, so OK.
     cmp: ?? *)
  Let tgt_gdefs := list (ident * globdef (Ctypes.fundef function) type).

  Let Tlong0 :=
    (Tlong Signed noattr).

  Let Tptr0 tgt :=
    (Tpointer tgt noattr).

  Definition ident_key {T} id l : option T :=
    SetoidList.findA (Pos.eqb id) l.

  Definition string_key {T} l x : option T :=
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
  (** vsub, vmul may not agree with compcert's cop semantics *)

  (* for function pointer call *)
  Definition compile_expr_ptr tyargs expr : option Clight.expr :=
    match expr with
    | Var x =>
      Some (Etempvar (s2p x) (Tptr0 (Tfunction tyargs Tlong0 cc_default)))
    | _ => None
    end
  .

  Fixpoint compile_exprs (exprs: list Imp.expr) acc : option (list Clight.expr) :=
    match exprs with
    | h :: t =>
      do hexp <- (compile_expr h); compile_exprs t (hexp :: acc)
    | [] => Some acc
    end
  .

  (* only check number of arguments, exploit Tlong <-> Tptr64 *)
  Fixpoint cnt_args (tyargs: typelist) (args: list expr) : bool :=
    match tyargs, args with
    | Tnil, [] => true
    | Tcons ty tys, e::es => cnt_args tys es
    | _, _ => false
    end
  .

  Fixpoint args_to_typelist (args: list expr) : typelist :=
    match args with
    | [] => Tnil
    | h::t => Tcons Tlong0 (args_to_typelist t)
    end
  .

  Fixpoint typelist_to_typs (tl: typelist) : list typ :=
    match tl with
    | Tnil => []
    | Tcons h t => AST.Tlong :: (typelist_to_typs t)
    end
  .

  (* Imp has no type, value is either int64/ptr64 -> sem_cast can convert *)
  Fixpoint compile_stmt (g0: tgt_gdefs) stmt : option (tgt_gdefs * statement) :=
    match stmt with
    | Assign x e =>
      do ex <- (compile_expr e); Some (g0, Sset (s2p x) ex)
    | Seq s1 s2 =>
      do '(g1, cs1) <- (compile_stmt g0 s1);
      do '(g2, cs2) <- (compile_stmt g1 s2);
      Some (g2, Ssequence cs1 cs2)
    | If cond sif selse =>
      do cc <- (compile_expr cond);
      do '(g1, cif) <- (compile_stmt g0 sif);
      do '(g2, celse) <- (compile_stmt g1 selse);
      Some (g2, Sifthenelse cc cif celse)
    | While cond body =>
      do cc <- (compile_expr cond);
      do '(g1, cbody) <- (compile_stmt g0 body);
      Some (g1, Swhile cc cbody)
    | Skip =>
      Some (g0, Sskip)

    | CallFun1 x f args =>
      do al <- (compile_exprs args []);
      Some
        (g0,
         Scall
           (Some (s2p x))
           (Evar (s2p f) (Tfunction (args_to_typelist al) Tlong0 cc_default))
           al)
    | CallFun2 f args =>
      do al <- (compile_exprs args []);
      Some
        (g0,
         Scall
           None
           (Evar (s2p f) (Tfunction (args_to_typelist al) Tlong0 cc_default))
           al)
      
    | CallPtr1 x pe args =>
      do al <- (compile_exprs args []);
      do a <- compile_expr_ptr (args_to_typelist al) pe;
      Some (g0, Scall (Some (s2p x)) a al)
    | CallPtr2 pe args =>
      do al <- (compile_exprs args []);
      do a <- compile_expr_ptr (args_to_typelist al) pe;
      Some (g0, Scall None a al)

    | CallSys1 x f args =>
      match ident_key (s2p f) g0 with
      | Some gd =>
        match gd with
        | Gfun fd =>
          match fd with
          | External ef tyargs tyres cconv =>
            do al <- (compile_exprs args []);
            if (cnt_args tyargs al)
            then
              Some
                (g0,
                 Scall
                   (Some (s2p x))
                   (Evar (s2p f) (Tfunction tyargs tyres cconv))
                   al)
            else None
          | _ => None
          end
        | _ => None
        end
      | None =>
        do al <- (compile_exprs args []);
        let tyargs := args_to_typelist al in
        let sg := mksignature (typelist_to_typs tyargs) (Tret AST.Tlong) cc_default in
        let fd := Gfun (External (EF_external f sg) tyargs Tlong0 cc_default) in
        let g1 := ((s2p f), fd)::g0 in
        Some
          (g1,
           Scall
             (Some (s2p x))
             (Evar (s2p f) (Tfunction tyargs Tlong0 cc_default))
             al)
      end
    | CallSys2 f args =>
      match ident_key (s2p f) g0 with
      | Some gd =>
        match gd with
        | Gfun fd =>
          match fd with
          | External ef tyargs tyres cconv =>
            do al <- (compile_exprs args []);
            if (cnt_args tyargs al)
            then
              Some
                (g0,
                 Scall
                   None
                   (Evar (s2p f) (Tfunction tyargs tyres cconv))
                   al)
            else None
          | _ => None
          end
        | _ => None
        end
      | None =>
        do al <- (compile_exprs args []);
        let tyargs := args_to_typelist al in
        let sg := mksignature (typelist_to_typs tyargs) (Tret AST.Tlong) cc_default in
        let fd := Gfun (External (EF_external f sg) tyargs Tlong0 cc_default) in
        let g1 := ((s2p f), fd)::g0 in
        Some
          (g1,
           Scall
             None
             (Evar (s2p f) (Tfunction tyargs Tlong0 cc_default))
             al)
      end

    | Return1 r =>
      do cr <- (compile_expr r); Some (g0, Sreturn (Some cr))
    | Return2 =>
      Some (g0, Sreturn None)

    | AddrOf x GN =>
      (* GN: global name, tgt_g may not contain -> resolved by linking *)
      Some (g0, Sset (s2p x) (Eaddrof (Evar (s2p GN) Tlong0) Tlong0))
    | Load x pe =>
      do cpe <- (compile_expr pe); Some (g0, Sset (s2p x) (Ederef cpe Tlong0))
    | Store pe ve =>
      do cpe <- (compile_expr pe);
      do cve <- (compile_expr ve);
      Some (g0, Sassign (Ederef cpe Tlong0) cve)
    end
  .

End Compile.
