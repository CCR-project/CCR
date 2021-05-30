Require Import Coqlib.
Require Export ZArith.
Require Export String.
Require Export Any.
Require Export Axioms.
Require Export sflib.
Require Export ITreelib.
Require Export AList.

Set Implicit Arguments.



Notation mblock := nat (only parsing).
Notation ptrofs := Z (only parsing).

Inductive val: Type :=
| Vint (n: Z): val
| Vptr (blk: mblock) (ofs: ptrofs): val
| Vundef
.

Definition wordsize_64 := 64.
Definition modulus_64 := two_power_nat wordsize_64.
Definition intrange_64 : Z -> Prop := fun z => ((- 1) < z < modulus_64)%Z.
Definition wf_val (v : val) :=
  match v with
  | Vint z => intrange_64 z
  | Vptr _ z => intrange_64 z
  | Vundef => True
  end.

(* Notation ofs0 := 0%Z. *)

Definition Vnullptr := Vint 0.

Definition vadd (x y: val): option val :=
  match x, y with
  | Vint n, Vint m => Some (Vint (Z.add n m))
  | Vptr blk ofs, Vint n => Some (Vptr blk (Z.add ofs n))
  | Vint n, Vptr blk ofs => Some (Vptr blk (Z.add ofs n))
  (* | Vptr _ _, Vptr _ _ => None *)
  | _, _ => None
  end
.

Definition vsub (x y: val): option val :=
  match x, y with
  | Vint n, Vint m => Some (Vint (Z.sub n m))
  | Vptr blk ofs, Vint n => Some (Vptr blk (Z.sub ofs n))
  | Vint n, Vptr blk ofs => Some (Vptr blk (Z.sub ofs n))
  (* | Vptr _ _, Vptr _ _ => None *)
  | _, _ => None
  end
.

Definition vmul (x y: val): option val :=
  match x, y with
  | Vint n, Vint m => Some (Vint (Z.mul n m))
  | Vptr blk ofs, Vint n => Some (Vptr blk (Z.mul ofs n))
  | Vint n, Vptr blk ofs => Some (Vptr blk (Z.mul ofs n))
  (* | Vptr _ _, Vptr _ _ => None *)
  | _, _ => None
  end
.

Notation gname := string (only parsing). (*** convention: not capitalized ***)
Notation mname := string (only parsing). (*** convention: capitalized ***)



Inductive event: Type :=
| event_sys
    (fn: gname)
    (args: list val)
    (rv: val)
.

Module Mem.

  (* Definition t: Type := mblock -> option (Z -> val). *)
  Record t: Type := mk {
    cnts: mblock -> Z -> option val;
    nb: mblock;
    (*** Q: wf conditions like nextmblock_noaccess ? ***)
    (*** A: Unlike in CompCert, the memory object will not float in various places in the program.
            It suffices to state wf only inside Mem module. (probably by utilizing URA.wf)
     ***)
  }
  .

  Definition wf (m0: t): Prop := forall blk ofs (LT: (blk < m0.(nb))%nat), m0.(cnts) blk ofs = None.

  Definition alloc (m0: Mem.t) (sz: Z): (mblock * Mem.t) :=
    ((m0.(nb)),
     Mem.mk (update (m0.(cnts)) (m0.(nb))
                    (fun ofs => if (0 <=? ofs)%Z && (ofs <? sz)%Z then Some (Vint 0) else None))
            (S m0.(nb))
    )
  .

  Opaque Z.ltb Z.leb Z.mul Z.eq_dec Nat.eq_dec.
  (* Definition empty: t := mk (update (fun _ _ => None) 0 (fun ofs => if dec ofs 0%Z then Some Vundef else None)) 0. *)
  Definition empty: t := mk (fun _ _ => None) 0.
  (* Let empty2: t := Eval compute in *)
  (*   let m0 := mk (fun _ _ => None) 0 in *)
  (*   let (_, m1) := alloc m0 1%Z in *)
  (*   m1 *)
  (* . *)
  (*** shoul allocated with Vundef, not 0 ***)

  (*** TODO: Unlike CompCert, this "free" function does not take offset.
       In order to support this, we need more sophisticated RA. it would be interesting.
   ***)
  (* Definition free (m0: Mem.t) (b: mblock): option (Mem.t) := *)
  (*   match m0.(cnts) b ofs0 with *)
  (*   | Some _ => Some (Mem.mk (update m0.(cnts) b (fun _ => None)) m0.(nb)) *)
  (*   | _ => None *)
  (*   end *)
  (* . *)

  Definition free (m0: Mem.t) (b: mblock) (ofs: Z): option (Mem.t) :=
    match m0.(cnts) b ofs with
    | Some _ => Some (Mem.mk (update m0.(cnts) b (update (m0.(cnts) b) ofs None)) m0.(nb))
    | _ => None
    end
  .

  Definition load (m0: Mem.t) (b: mblock) (ofs: Z): option val := m0.(cnts) b ofs.

  Definition store (m0: Mem.t) (b: mblock) (ofs: Z) (v: val): option Mem.t :=
    match m0.(cnts) b ofs with
    | Some _ => Some (Mem.mk (fun _b _ofs => if (dec b _b) && (dec ofs _ofs)
                                             then Some v
                                             else m0.(cnts) _b _ofs) m0.(nb))
    | _ => None
    end
  .

  Definition valid_ptr (m0: Mem.t) (b: mblock) (ofs: ptrofs): bool := is_some (m0.(cnts) b ofs).

End Mem.

Definition vcmp (m0: Mem.t) (x y: val): option bool :=
  match x, y with
  | Vint x, Vint y => Some (dec x y: bool)
  | Vptr x xofs, Vptr y yofs =>
    if Mem.valid_ptr m0 x xofs && Mem.valid_ptr m0 y yofs
    then Some (dec x y && dec xofs yofs)
    else None
  | Vptr x xofs, Vint y =>
    if Mem.valid_ptr m0 x xofs && dec y 0%Z
    then Some false
    else None
  | Vint x, Vptr y yofs =>
    if Mem.valid_ptr m0 y yofs && dec x 0%Z
    then Some false
    else None
  | _, _ => None
  (* | Vundef, _ => None *)
  (* | _, Vundef => None *)
  end.

Definition unptr (v: val): option (mblock * ptrofs) :=
  match v with
  | Vptr b ofs => Some (b, ofs)
  | _ => None
  end.

Definition unint (v: val): option Z :=
  match v with
  | Vint x => Some x
  | _ => None
  end.

(*** NOTE: Probably we can support comparison between nullptr and 0 ***)
(*** NOTE: Unlike CompCert, we don't support comparison with weak_valid_ptr (for simplicity) ***)

Parameter syscall_sem: event -> Prop.
