open Archi
open BinInt
open BinNums
open Coqlib
open Datatypes
open List0
open Zbits
open Zpower

type comparison =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

(** val negate_comparison : comparison -> comparison **)

let negate_comparison = function
| Ceq -> Cne
| Cne -> Ceq
| Clt -> Cge
| Cle -> Cgt
| Cgt -> Cle
| Cge -> Clt

(** val swap_comparison : comparison -> comparison **)

let swap_comparison = function
| Clt -> Cgt
| Cle -> Cge
| Cgt -> Clt
| Cge -> Cle
| x -> x

module type WORDSIZE =
 sig
  val wordsize : nat
 end

module Make =
 functor (WS:WORDSIZE) ->
 struct
  (** val wordsize : nat **)

  let wordsize =
    WS.wordsize

  (** val zwordsize : coq_Z **)

  let zwordsize =
    Z.of_nat wordsize

  (** val modulus : coq_Z **)

  let modulus =
    two_power_nat wordsize

  (** val half_modulus : coq_Z **)

  let half_modulus =
    Z.div modulus (Zpos (Coq_xO Coq_xH))

  (** val max_unsigned : coq_Z **)

  let max_unsigned =
    Z.sub modulus (Zpos Coq_xH)

  (** val max_signed : coq_Z **)

  let max_signed =
    Z.sub half_modulus (Zpos Coq_xH)

  (** val min_signed : coq_Z **)

  let min_signed =
    Z.opp half_modulus

  type int = coq_Z
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : int -> coq_Z **)

  let intval i =
    i

  (** val coq_Z_mod_modulus : coq_Z -> coq_Z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> coq_P_mod_two_p p wordsize
  | Zneg p ->
    let r = coq_P_mod_two_p p wordsize in
    if zeq r Z0 then Z0 else Z.sub modulus r

  (** val unsigned : int -> coq_Z **)

  let unsigned =
    intval

  (** val signed : int -> coq_Z **)

  let signed n =
    let x = unsigned n in if zlt x half_modulus then x else Z.sub x modulus

  (** val repr : coq_Z -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val zero : int **)

  let zero =
    repr Z0

  (** val one : int **)

  let one =
    repr (Zpos Coq_xH)

  (** val mone : int **)

  let mone =
    repr (Zneg Coq_xH)

  (** val iwordsize : int **)

  let iwordsize =
    repr zwordsize

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    zeq

  (** val eq : int -> int -> bool **)

  let eq x y =
    if zeq (unsigned x) (unsigned y) then true else false

  (** val lt : int -> int -> bool **)

  let lt x y =
    if zlt (signed x) (signed y) then true else false

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    if zlt (unsigned x) (unsigned y) then true else false

  (** val neg : int -> int **)

  let neg x =
    repr (Z.opp (unsigned x))

  (** val add : int -> int -> int **)

  let add x y =
    repr (Z.add (unsigned x) (unsigned y))

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Z.sub (unsigned x) (unsigned y))

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Z.mul (unsigned x) (unsigned y))

  (** val divs : int -> int -> int **)

  let divs x y =
    repr (Z.quot (signed x) (signed y))

  (** val mods : int -> int -> int **)

  let mods x y =
    repr (Z.rem (signed x) (signed y))

  (** val divu : int -> int -> int **)

  let divu x y =
    repr (Z.div (unsigned x) (unsigned y))

  (** val modu : int -> int -> int **)

  let modu x y =
    repr (Z.modulo (unsigned x) (unsigned y))

  (** val coq_and : int -> int -> int **)

  let coq_and x y =
    repr (Z.coq_land (unsigned x) (unsigned y))

  (** val coq_or : int -> int -> int **)

  let coq_or x y =
    repr (Z.coq_lor (unsigned x) (unsigned y))

  (** val xor : int -> int -> int **)

  let xor x y =
    repr (Z.coq_lxor (unsigned x) (unsigned y))

  (** val not : int -> int **)

  let not x =
    xor x mone

  (** val shl : int -> int -> int **)

  let shl x y =
    repr (Z.shiftl (unsigned x) (unsigned y))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr (Z.shiftr (unsigned x) (unsigned y))

  (** val shr : int -> int -> int **)

  let shr x y =
    repr (Z.shiftr (signed x) (unsigned y))

  (** val rol : int -> int -> int **)

  let rol x y =
    let n = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftl (unsigned x) n)
        (Z.shiftr (unsigned x) (Z.sub zwordsize n)))

  (** val ror : int -> int -> int **)

  let ror x y =
    let n = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftr (unsigned x) n)
        (Z.shiftl (unsigned x) (Z.sub zwordsize n)))

  (** val rolm : int -> int -> int -> int **)

  let rolm x a m =
    coq_and (rol x a) m

  (** val shrx : int -> int -> int **)

  let shrx x y =
    divs x (shl one y)

  (** val mulhu : int -> int -> int **)

  let mulhu x y =
    repr (Z.div (Z.mul (unsigned x) (unsigned y)) modulus)

  (** val mulhs : int -> int -> int **)

  let mulhs x y =
    repr (Z.div (Z.mul (signed x) (signed y)) modulus)

  (** val negative : int -> int **)

  let negative x =
    if lt x zero then one else zero

  (** val add_carry : int -> int -> int -> int **)

  let add_carry x y cin =
    if zlt (Z.add (Z.add (unsigned x) (unsigned y)) (unsigned cin)) modulus
    then zero
    else one

  (** val add_overflow : int -> int -> int -> int **)

  let add_overflow x y cin =
    let s = Z.add (Z.add (signed x) (signed y)) (signed cin) in
    if (&&) ((fun x -> x) (zle min_signed s))
         ((fun x -> x) (zle s max_signed))
    then zero
    else one

  (** val sub_borrow : int -> int -> int -> int **)

  let sub_borrow x y bin =
    if zlt (Z.sub (Z.sub (unsigned x) (unsigned y)) (unsigned bin)) Z0
    then one
    else zero

  (** val sub_overflow : int -> int -> int -> int **)

  let sub_overflow x y bin =
    let s = Z.sub (Z.sub (signed x) (signed y)) (signed bin) in
    if (&&) ((fun x -> x) (zle min_signed s))
         ((fun x -> x) (zle s max_signed))
    then zero
    else one

  (** val shr_carry : int -> int -> int **)

  let shr_carry x y =
    if (&&) (lt x zero) (negb (eq (coq_and x (sub (shl one y) one)) zero))
    then one
    else zero

  (** val zero_ext : coq_Z -> int -> int **)

  let zero_ext n x =
    repr (coq_Zzero_ext n (unsigned x))

  (** val sign_ext : coq_Z -> int -> int **)

  let sign_ext n x =
    repr (coq_Zsign_ext n (unsigned x))

  (** val one_bits : int -> int list **)

  let one_bits x =
    map repr (coq_Z_one_bits wordsize (unsigned x) Z0)

  (** val is_power2 : int -> int option **)

  let is_power2 x =
    match coq_Z_is_power2 (unsigned x) with
    | Some i -> Some (repr i)
    | None -> None

  (** val cmp : comparison -> int -> int -> bool **)

  let cmp c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> lt x y
    | Cle -> negb (lt y x)
    | Cgt -> lt y x
    | Cge -> negb (lt x y)

  (** val cmpu : comparison -> int -> int -> bool **)

  let cmpu c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> ltu x y
    | Cle -> negb (ltu y x)
    | Cgt -> ltu y x
    | Cge -> negb (ltu x y)

  (** val notbool : int -> int **)

  let notbool x =
    if eq x zero then one else zero

  (** val divmodu2 : int -> int -> int -> (int * int) option **)

  let divmodu2 nhi nlo d =
    if eq_dec d zero
    then None
    else let (q, r) =
           Z.div_eucl (Z.add (Z.mul (unsigned nhi) modulus) (unsigned nlo))
             (unsigned d)
         in
         if zle q max_unsigned then Some ((repr q), (repr r)) else None

  (** val divmods2 : int -> int -> int -> (int * int) option **)

  let divmods2 nhi nlo d =
    if eq_dec d zero
    then None
    else let (q, r) =
           Z.quotrem (Z.add (Z.mul (signed nhi) modulus) (unsigned nlo))
             (signed d)
         in
         if (&&) ((fun x -> x) (zle min_signed q))
              ((fun x -> x) (zle q max_signed))
         then Some ((repr q), (repr r))
         else None

  (** val testbit : int -> coq_Z -> bool **)

  let testbit x i =
    Z.testbit (unsigned x) i

  (** val int_of_one_bits : int list -> int **)

  let rec int_of_one_bits = function
  | [] -> zero
  | a :: b -> add (shl one a) (int_of_one_bits b)

  (** val no_overlap : int -> coq_Z -> int -> coq_Z -> bool **)

  let no_overlap ofs1 sz1 ofs2 sz2 =
    let x1 = unsigned ofs1 in
    let x2 = unsigned ofs2 in
    (&&)
      ((&&) ((fun x -> x) (zlt (Z.add x1 sz1) modulus))
        ((fun x -> x) (zlt (Z.add x2 sz2) modulus)))
      ((||) ((fun x -> x) (zle (Z.add x1 sz1) x2))
        ((fun x -> x) (zle (Z.add x2 sz2) x1)))

  (** val size : int -> coq_Z **)

  let size x =
    coq_Zsize (unsigned x)
 end

module Wordsize_32 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
 end

module Int = Make(Wordsize_32)

module Wordsize_8 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S O)))))))
 end

module Byte = Make(Wordsize_8)

module Wordsize_64 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 end

module Int64 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    Wordsize_64.wordsize

  (** val zwordsize : coq_Z **)

  let zwordsize =
    Z.of_nat wordsize

  (** val modulus : coq_Z **)

  let modulus =
    two_power_nat wordsize

  (** val half_modulus : coq_Z **)

  let half_modulus =
    Z.div modulus (Zpos (Coq_xO Coq_xH))

  (** val max_unsigned : coq_Z **)

  let max_unsigned =
    Z.sub modulus (Zpos Coq_xH)

  (** val max_signed : coq_Z **)

  let max_signed =
    Z.sub half_modulus (Zpos Coq_xH)

  (** val min_signed : coq_Z **)

  let min_signed =
    Z.opp half_modulus

  type int = coq_Z
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : int -> coq_Z **)

  let intval i =
    i

  (** val coq_Z_mod_modulus : coq_Z -> coq_Z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> coq_P_mod_two_p p wordsize
  | Zneg p ->
    let r = coq_P_mod_two_p p wordsize in
    if zeq r Z0 then Z0 else Z.sub modulus r

  (** val unsigned : int -> coq_Z **)

  let unsigned =
    intval

  (** val signed : int -> coq_Z **)

  let signed n =
    let x = unsigned n in if zlt x half_modulus then x else Z.sub x modulus

  (** val repr : coq_Z -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val zero : int **)

  let zero =
    repr Z0

  (** val one : int **)

  let one =
    repr (Zpos Coq_xH)

  (** val mone : int **)

  let mone =
    repr (Zneg Coq_xH)

  (** val iwordsize : int **)

  let iwordsize =
    repr zwordsize

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    zeq

  (** val eq : int -> int -> bool **)

  let eq x y =
    if zeq (unsigned x) (unsigned y) then true else false

  (** val lt : int -> int -> bool **)

  let lt x y =
    if zlt (signed x) (signed y) then true else false

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    if zlt (unsigned x) (unsigned y) then true else false

  (** val neg : int -> int **)

  let neg x =
    repr (Z.opp (unsigned x))

  (** val add : int -> int -> int **)

  let add x y =
    repr (Z.add (unsigned x) (unsigned y))

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Z.sub (unsigned x) (unsigned y))

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Z.mul (unsigned x) (unsigned y))

  (** val divs : int -> int -> int **)

  let divs x y =
    repr (Z.quot (signed x) (signed y))

  (** val mods : int -> int -> int **)

  let mods x y =
    repr (Z.rem (signed x) (signed y))

  (** val divu : int -> int -> int **)

  let divu x y =
    repr (Z.div (unsigned x) (unsigned y))

  (** val modu : int -> int -> int **)

  let modu x y =
    repr (Z.modulo (unsigned x) (unsigned y))

  (** val coq_and : int -> int -> int **)

  let coq_and x y =
    repr (Z.coq_land (unsigned x) (unsigned y))

  (** val coq_or : int -> int -> int **)

  let coq_or x y =
    repr (Z.coq_lor (unsigned x) (unsigned y))

  (** val xor : int -> int -> int **)

  let xor x y =
    repr (Z.coq_lxor (unsigned x) (unsigned y))

  (** val not : int -> int **)

  let not x =
    xor x mone

  (** val shl : int -> int -> int **)

  let shl x y =
    repr (Z.shiftl (unsigned x) (unsigned y))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr (Z.shiftr (unsigned x) (unsigned y))

  (** val shr : int -> int -> int **)

  let shr x y =
    repr (Z.shiftr (signed x) (unsigned y))

  (** val ror : int -> int -> int **)

  let ror x y =
    let n = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftr (unsigned x) n)
        (Z.shiftl (unsigned x) (Z.sub zwordsize n)))

  (** val mulhu : int -> int -> int **)

  let mulhu x y =
    repr (Z.div (Z.mul (unsigned x) (unsigned y)) modulus)

  (** val mulhs : int -> int -> int **)

  let mulhs x y =
    repr (Z.div (Z.mul (signed x) (signed y)) modulus)

  (** val is_power2 : int -> int option **)

  let is_power2 x =
    match coq_Z_is_power2 (unsigned x) with
    | Some i -> Some (repr i)
    | None -> None

  (** val cmp : comparison -> int -> int -> bool **)

  let cmp c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> lt x y
    | Cle -> negb (lt y x)
    | Cgt -> lt y x
    | Cge -> negb (lt x y)

  (** val cmpu : comparison -> int -> int -> bool **)

  let cmpu c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> ltu x y
    | Cle -> negb (ltu y x)
    | Cgt -> ltu y x
    | Cge -> negb (ltu x y)

  (** val iwordsize' : Int.int **)

  let iwordsize' =
    Int.repr zwordsize

  (** val shl' : int -> Int.int -> int **)

  let shl' x y =
    repr (Z.shiftl (unsigned x) (Int.unsigned y))

  (** val shru' : int -> Int.int -> int **)

  let shru' x y =
    repr (Z.shiftr (unsigned x) (Int.unsigned y))

  (** val shr' : int -> Int.int -> int **)

  let shr' x y =
    repr (Z.shiftr (signed x) (Int.unsigned y))

  (** val shrx' : int -> Int.int -> int **)

  let shrx' x y =
    divs x (shl' one y)

  (** val one_bits' : int -> Int.int list **)

  let one_bits' x =
    map Int.repr (coq_Z_one_bits wordsize (unsigned x) Z0)

  (** val is_power2' : int -> Int.int option **)

  let is_power2' x =
    match coq_Z_one_bits wordsize (unsigned x) Z0 with
    | [] -> None
    | i :: l -> (match l with
                 | [] -> Some (Int.repr i)
                 | _ :: _ -> None)

  (** val loword : int -> Int.int **)

  let loword n =
    Int.repr (unsigned n)

  (** val hiword : int -> Int.int **)

  let hiword n =
    Int.repr (unsigned (shru n (repr Int.zwordsize)))

  (** val ofwords : Int.int -> Int.int -> int **)

  let ofwords hi lo =
    coq_or (shl (repr (Int.unsigned hi)) (repr Int.zwordsize))
      (repr (Int.unsigned lo))

  (** val mul' : Int.int -> Int.int -> int **)

  let mul' x y =
    repr (Z.mul (Int.unsigned x) (Int.unsigned y))
 end

module Wordsize_Ptrofs =
 struct
  (** val wordsize : nat **)

  let wordsize =
    if ptr64
    then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
 end

module Ptrofs =
 struct
  (** val wordsize : nat **)

  let wordsize =
    Wordsize_Ptrofs.wordsize

  (** val modulus : coq_Z **)

  let modulus =
    two_power_nat wordsize

  (** val half_modulus : coq_Z **)

  let half_modulus =
    Z.div modulus (Zpos (Coq_xO Coq_xH))

  (** val max_unsigned : coq_Z **)

  let max_unsigned =
    Z.sub modulus (Zpos Coq_xH)

  (** val max_signed : coq_Z **)

  let max_signed =
    Z.sub half_modulus (Zpos Coq_xH)

  type int = coq_Z
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : int -> coq_Z **)

  let intval i =
    i

  (** val coq_Z_mod_modulus : coq_Z -> coq_Z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> coq_P_mod_two_p p wordsize
  | Zneg p ->
    let r = coq_P_mod_two_p p wordsize in
    if zeq r Z0 then Z0 else Z.sub modulus r

  (** val unsigned : int -> coq_Z **)

  let unsigned =
    intval

  (** val signed : int -> coq_Z **)

  let signed n =
    let x = unsigned n in if zlt x half_modulus then x else Z.sub x modulus

  (** val repr : coq_Z -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val zero : int **)

  let zero =
    repr Z0

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    zeq

  (** val eq : int -> int -> bool **)

  let eq x y =
    if zeq (unsigned x) (unsigned y) then true else false

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    if zlt (unsigned x) (unsigned y) then true else false

  (** val add : int -> int -> int **)

  let add x y =
    repr (Z.add (unsigned x) (unsigned y))

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Z.sub (unsigned x) (unsigned y))

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Z.mul (unsigned x) (unsigned y))

  (** val divs : int -> int -> int **)

  let divs x y =
    repr (Z.quot (signed x) (signed y))

  (** val cmpu : comparison -> int -> int -> bool **)

  let cmpu c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> ltu x y
    | Cle -> negb (ltu y x)
    | Cgt -> ltu y x
    | Cge -> negb (ltu x y)

  (** val to_int : int -> Int.int **)

  let to_int x =
    Int.repr (unsigned x)

  (** val to_int64 : int -> Int64.int **)

  let to_int64 x =
    Int64.repr (unsigned x)

  (** val of_int : Int.int -> int **)

  let of_int x =
    repr (Int.unsigned x)

  (** val of_intu : Int.int -> int **)

  let of_intu =
    of_int

  (** val of_ints : Int.int -> int **)

  let of_ints x =
    repr (Int.signed x)

  (** val of_int64 : Int64.int -> int **)

  let of_int64 x =
    repr (Int64.unsigned x)
 end
