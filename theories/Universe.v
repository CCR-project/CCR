Require Import Coqlib.
Require Export ZArith.
Require Export String.
Require Export Any.
Require Export Axioms.
Require Export Ordinal ClassicalOrdinal.
Require Export sflib.
Require Export ITreelib.

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

Notation fname := string (only parsing). (*** convention: not capitalized ***)
Notation mname := string (only parsing). (*** convention: capitalized ***)



Inductive event: Type :=
| event_sys
    (fn: fname)
    (args: list val)
.

Module Mem.

  (* Definition t: Type := block -> option (Z -> val). *)
  Record t: Type := mk {
    cnts: block -> Z -> option val;
    nb: block;
    (*** Q: wf conditions like nextblock_noaccess ? ***)
    (*** A: Unlike in CompCert, the memory object will not float in various places in the program.
            It suffices to state wf only inside Mem module. (probably by utilizing URA.wf)
     ***)
  }
  .

  Definition wf (m0: t): Prop := forall blk ofs (LT: (blk < m0.(nb))%nat), m0.(cnts) blk ofs = None.

  Definition empty: t := mk (fun _ _ => None) 0.

  Definition alloc (m0: Mem.t) (sz: Z): (block * Mem.t) :=
    ((m0.(nb)),
     Mem.mk (update (m0.(cnts)) (m0.(nb))
                    (fun ofs => if (0 <=? ofs)%Z && (ofs <? sz)%Z then Some (Vint 0) else None))
            (S m0.(nb))
    )
  .

  (*** TODO: Unlike CompCert, this "free" function does not take offset.
       In order to support this, we need more sophisticated RA. it would be interesting.
   ***)
  (* Definition free (m0: Mem.t) (b: block): option (Mem.t) := *)
  (*   match m0.(cnts) b ofs0 with *)
  (*   | Some _ => Some (Mem.mk (update m0.(cnts) b (fun _ => None)) m0.(nb)) *)
  (*   | _ => None *)
  (*   end *)
  (* . *)

  Definition free (m0: Mem.t) (b: block) (ofs: Z): option (Mem.t) :=
    match m0.(cnts) b ofs with
    | Some _ => Some (Mem.mk (update m0.(cnts) b (update (m0.(cnts) b) ofs None)) m0.(nb))
    | _ => None
    end
  .

  Definition load (m0: Mem.t) (b: block) (ofs: Z): option val := m0.(cnts) b ofs.

  Definition store (m0: Mem.t) (b: block) (ofs: Z) (v: val): option Mem.t :=
    match m0.(cnts) b ofs0 with
    | Some _ => Some (Mem.mk (fun _b _ofs => if (dec b _b) && (dec ofs _ofs)
                                             then Some v
                                             else m0.(cnts) _b _ofs) m0.(nb))
    | _ => None
    end
  .

End Mem.

Axiom syscall_sem: fname -> list val -> (event * val).
