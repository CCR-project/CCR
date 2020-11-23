Require Export ZArith.
Require Export String.

Notation block := positive (only parsing).

Inductive val: Type :=
| Vint (n: Z): val
| Vptr (blk: block) (ofs: Z): val 
.

Notation ident := positive (only parsing).

Inductive event: Type :=
| event_sys
    (name: string)
    (args: list val)
.
