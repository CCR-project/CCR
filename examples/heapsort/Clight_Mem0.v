Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import AList.

From compcert Require Import
     AST Maps Globalenvs Memory Values Linking Integers.
From compcert Require Import
     Ctypes Clight.

Set Implicit Arguments.

Section PROOF.

  Section BODY.
    Context {Es: Type -> Type}.
    Context `{has_pE: pE -< Es}.
    Context `{has_eventE: eventE -< Es}.

    Definition allocF: Z -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let sz := varg in
        let (m1, blk) := Mem.alloc m0 0 sz in
        trigger (PPut m1↑);;;
        Ret (Vptr blk (Ptrofs.repr 0)).
    
    Definition freeF: block * Z * Z -> itree Es unit :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(b, lo, hi) := varg in
        m1 <- (Mem.free m0 b lo hi)?;;
        trigger (PPut m1↑);;;
        Ret tt
    .

    Definition loadF: memory_chunk * block * Z -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(chunk, b, ofs) := varg in
        v <- (Mem.load chunk m0 b ofs)?;;
        Ret v
    .

    Definition loadbytesF: block * Z * Z -> itree Es (list memval) :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(b, ofs, n) := varg in
        v <- (Mem.loadbytes m0 b ofs n)?;;
        Ret v
    .

    Definition storeF: memory_chunk * block * Z * val -> itree Es unit :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(chunk, b, ofs, v) := varg in
        m1 <- (Mem.store chunk m0 b ofs v)?;;
        trigger (PPut m1↑);;;
        Ret tt
    .

    Definition storebytesF: block * Z * list memval -> itree Es unit :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(b, ofs, bytes) := varg in
        m1 <- (Mem.storebytes m0 b ofs bytes)?;;
        trigger (PPut m1↑);;;
        Ret tt
    .

    Definition unary_opF: Cop.unary_operation * val * type -> itree Es (option val):=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(op, v, ty) := varg in
        Ret (Cop.sem_unary_operation
               op v ty m0)
    .

    Definition binary_opF:
      composite_env * Cop.binary_operation * val * type * val * type -> itree Es (option val):=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(ce, op, v1, ty1, v2, ty2) := varg in
        Ret (Cop.sem_binary_operation
               ce op v1 ty1 v2 ty2 m0)
    .

    Definition sem_castF: val * type * type -> itree Es (option val) :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(v, ty1, ty2) := varg in
        Ret (Cop.sem_cast v ty1 ty2 m0)
    .

    Definition bool_valF: val * type -> itree Es (option bool) :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(v, ty) := varg in
        Ret (Cop.bool_val v ty m0)
    .

  End BODY.

  Variable csl: gname -> bool.
  Definition MemSem (sk: Sk.t): ModSem.t :=
    {|
    ModSem.fnsems := [("alloc", cfunU allocF); ("free", cfunU freeF);
                     ("load", cfunU loadF); ("loadbytes", cfunU loadbytesF);
                     ("store", cfunU storeF); ("storebytes", cfunU storebytesF);
                     ("unary_op", cfunU unary_opF); ("binary_op", cfunU binary_opF);
                     ("sem_cast", cfunU sem_castF); ("bool_val", cfunU bool_valF)];
      ModSem.mn := "Mem";
      ModSem.initial_st := Mem.empty↑;
      (* ModSem.initial_st := (Mem.load_mem csl sk)↑; *)
    |}
  .

  Definition Mem: Mod.t := {|
    Mod.get_modsem := MemSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
