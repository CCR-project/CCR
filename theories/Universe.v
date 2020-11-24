Require Export ZArith.
Require Export String.

Notation block := nat (only parsing).

Inductive val: Type :=
| Vint (n: Z): val
| Vptr (blk: block) (ofs: Z): val
| Vundef
.

Notation ident := string (only parsing).

Inductive event: Type :=
| event_sys
    (name: ident)
    (args: list val)
.
