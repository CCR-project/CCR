Require Export ZArith.
Require Export String.

Notation block := nat (only parsing).

Inductive val: Type :=
| Vint (n: Z): val
| Vptr (blk: block) (ofs: Z): val
| Vundef
.

Notation fname := string (only parsing).
Notation mname := string (only parsing).



Inductive event: Type :=
| event_sys
    (fn: fname)
    (args: list val)
.

Module Mem.

  Definition t: Type := block -> option (Z -> val).

End Mem.

Axiom syscall_sem: fname -> Mem.t -> list val -> (event * Mem.t * val).
