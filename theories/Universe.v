Require Import Coqlib.
Require Export ZArith.
Require Export String.

Set Implicit Arguments.

(************ temporary buffer before putting it in Coqlib ***********)
(************ temporary buffer before putting it in Coqlib ***********)
(************ temporary buffer before putting it in Coqlib ***********)

Class Dec (A: Type) := dec: forall (a0 a1: A), { a0 = a1 } + { a0 <> a1 }.

Global Program Instance positive_Dec: Dec positive. Next Obligation. decide equality. Defined.
Global Program Instance string_Dec: Dec String.string. Next Obligation. apply String.string_dec. Defined.
Global Program Instance nat_Dec: Dec nat. Next Obligation. apply Nat.eq_dec. Defined.
Global Program Instance Z_Dec: Dec Z. Next Obligation. apply Z.eq_dec. Defined.

Definition update K `{Dec K} V (f: K -> V) (k: K) (v: V): K -> V :=
  fun _k => if dec k _k then v else f _k.

(************ temporary buffer before putting it in Coqlib ***********)
(************ temporary buffer before putting it in Coqlib ***********)
(************ temporary buffer before putting it in Coqlib ***********)



Notation block := nat (only parsing).

Inductive val: Type :=
| Vint (n: Z): val
| Vptr (blk: block) (ofs: Z): val
(* | Vundef *)
.

Notation fname := string (only parsing).
Notation mname := string (only parsing).



Inductive event: Type :=
| event_sys
    (fn: fname)
    (args: list val)
.

Module Mem.

  (* Definition t: Type := block -> option (Z -> val). *)
  Record t: Type := mk {
    contents: block -> Z -> option val;
    nextblock: block;
    (*** nextblock_noaccess ? ***)
  }
  .

  Definition empty: t := mk (fun _ _ => None) 0.

  Definition alloc (m0: Mem.t) (sz: Z): (block * Mem.t) :=
    ((m0.(nextblock)),
     Mem.mk (update (m0.(contents)) (m0.(nextblock))
                    (fun ofs => if (0 <=? ofs) && (ofs <? sz) then Some (Vint 0) else None))
            (S m0.(nextblock))
    )
  .

End Mem.

Axiom syscall_sem: fname -> Mem.t -> list val -> (event * Mem.t * val).
