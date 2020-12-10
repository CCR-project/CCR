Require Import Coqlib.
Require Export ZArith.
Require Export String.

Set Implicit Arguments.



Notation block := nat (only parsing).
Notation ptrofs := Z (only parsing).

Inductive val: Type :=
| Vint (n: Z): val
| Vptr (blk: block) (ofs: ptrofs): val
(* | Vundef *)
.

Notation ofs0 := 0%Z.

Definition vadd (x y: val): option val :=
  match x, y with
  | Vint n, Vint m => Some (Vint (Z.add n m))
  | Vptr blk ofs, Vint n => Some (Vptr blk (Z.add ofs n))
  | Vint n, Vptr blk ofs => Some (Vptr blk (Z.add ofs n))
  | Vptr _ _, Vptr _ _ => None
  end
.

Definition vsub (x y: val): option val :=
  match x, y with
  | Vint n, Vint m => Some (Vint (Z.sub n m))
  | Vptr blk ofs, Vint n => Some (Vptr blk (Z.sub ofs n))
  | Vint n, Vptr blk ofs => Some (Vptr blk (Z.sub ofs n))
  | Vptr _ _, Vptr _ _ => None
  end
.

Definition vmul (x y: val): option val :=
  match x, y with
  | Vint n, Vint m => Some (Vint (Z.mul n m))
  | Vptr blk ofs, Vint n => Some (Vptr blk (Z.mul ofs n))
  | Vint n, Vptr blk ofs => Some (Vptr blk (Z.mul ofs n))
  | Vptr _ _, Vptr _ _ => None
  end
.

Notation fname := string (only parsing).
Notation mname := string (only parsing).



Inductive event: Type :=
| event_sys
    (fn: fname)
    (args: list val)
.
