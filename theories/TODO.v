Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.


Definition unbool (v: val): option bool :=
  match v with
  | Vint x => Some (if (dec x 0%Z) then false else true)
  | _ => None
  end.

Definition unblk (v: val): option mblock :=
  match v with
  | Vptr b ofs =>
    if (Z.eq_dec ofs 0) then Some b else None
  | _ => None
  end.

Variant val_type: Set :=
| Tint
| Tbool
| Tptr
| Tblk
| Tuntyped
.

Definition val_type_sem (t: val_type): Set :=
  match t with
  | Tint => Z
  | Tbool => bool
  | Tptr => (mblock * ptrofs)
  | Tblk => mblock
  | Tuptyped => val
  end.

Fixpoint val_types_sem (ts: list val_type): Set :=
  match ts with
  | [] => unit
  | [hd] => val_type_sem hd
  | hd::tl => val_type_sem hd * val_types_sem tl
  end.

Definition parg (t: val_type) (v: val): option (val_type_sem t) :=
  match t with
  | Tint => unint v
  | Tbool => unbool v
  | Tptr => unptr v
  | Tblk => unblk v
  | Tuntyped => Some v
  end.

Definition pargs (ts: list val_type):
  forall (vs: list val), option (val_types_sem ts).
Proof.
  induction ts as [|thd ttl].
  - intros [|]; simpl.
    + exact (Some tt).
    + exact None.
  - simpl. destruct ttl as [|].
    + intros [|vhd []]; simpl.
      * exact None.
      * exact (parg thd vhd).
      * exact None.
    + intros [|vhd vtl].
      * exact None.
      * exact (match parg thd vhd with
               | Some vhd' =>
                 match IHttl vtl with
                 | Some vtl' => Some (vhd', vtl')
                 | None => None
                 end
               | None => None
               end).
Defined.
