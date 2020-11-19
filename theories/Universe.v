Require Import ZArith.
Require Import String.

Notation block := nat.

Inductive val: Type :=
| Vint (n: Z): val
| Vptr (blk: block): val 
.

Inductive event: Type :=
| event_sys
    (name: string)
    (args: list val)
.
