open AST
open BinInt
open BinNums
open BinPos
open Coqlib
open Datatypes
open Integers
open Maps
open Memdata
open Memtype
open Values
open Znumtheory

module Mem =
 struct
  type mem' = { mem_contents : memval ZMap.t PMap.t;
                mem_access : (coq_Z -> perm_kind -> permission option) PMap.t;
                nextblock : block }

  (** val mem_contents : mem' -> memval ZMap.t PMap.t **)

  let mem_contents m =
    m.mem_contents

  (** val mem_access :
      mem' -> (coq_Z -> perm_kind -> permission option) PMap.t **)

  let mem_access m =
    m.mem_access

  (** val nextblock : mem' -> block **)

  let nextblock m =
    m.nextblock

  type mem = mem'

  (** val perm_order_dec : permission -> permission -> bool **)

  let perm_order_dec p1 p2 =
    match p1 with
    | Freeable -> true
    | Writable -> (match p2 with
                   | Freeable -> false
                   | _ -> true)
    | Readable ->
      (match p2 with
       | Freeable -> false
       | Writable -> false
       | _ -> true)
    | Nonempty -> (match p2 with
                   | Nonempty -> true
                   | _ -> false)

  (** val perm_order'_dec : permission option -> permission -> bool **)

  let perm_order'_dec op p =
    match op with
    | Some p0 -> perm_order_dec p0 p
    | None -> false

  (** val perm_dec :
      mem -> block -> coq_Z -> perm_kind -> permission -> bool **)

  let perm_dec m b ofs k p =
    perm_order'_dec (PMap.get b m.mem_access ofs k) p

  (** val range_perm_dec :
      mem -> block -> coq_Z -> coq_Z -> perm_kind -> permission -> bool **)

  let rec range_perm_dec m b lo hi k p =
    let s = zlt lo hi in
    if s
    then let s0 = perm_dec m b lo k p in
         if s0
         then let y = Z.add lo (Zpos Coq_xH) in range_perm_dec m b y hi k p
         else false
    else true

  (** val valid_access_dec :
      mem -> memory_chunk -> block -> coq_Z -> permission -> bool **)

  let valid_access_dec m chunk b ofs p =
    let s = range_perm_dec m b ofs (Z.add ofs (size_chunk chunk)) Cur p in
    if s then coq_Zdivide_dec (align_chunk chunk) ofs else false

  (** val valid_pointer : mem -> block -> coq_Z -> bool **)

  let valid_pointer m b ofs =
    (fun x -> x) (perm_dec m b ofs Cur Nonempty)

  (** val weak_valid_pointer : mem -> block -> coq_Z -> bool **)

  let weak_valid_pointer m b ofs =
    (||) (valid_pointer m b ofs) (valid_pointer m b (Z.sub ofs (Zpos Coq_xH)))

  (** val empty : mem **)

  let empty =
    { mem_contents = (PMap.init (ZMap.init Undef)); mem_access =
      (PMap.init (fun _ _ -> None)); nextblock = Coq_xH }

  (** val alloc : mem -> coq_Z -> coq_Z -> mem' * block **)

  let alloc m lo hi =
    ({ mem_contents =
      (PMap.set m.nextblock (ZMap.init Undef) m.mem_contents); mem_access =
      (PMap.set m.nextblock (fun ofs _ ->
        if (&&) ((fun x -> x) (zle lo ofs)) ((fun x -> x) (zlt ofs hi))
        then Some Freeable
        else None) m.mem_access); nextblock = (Pos.succ m.nextblock) },
      m.nextblock)

  (** val unchecked_free : mem -> block -> coq_Z -> coq_Z -> mem **)

  let unchecked_free m b lo hi =
    { mem_contents = m.mem_contents; mem_access =
      (PMap.set b (fun ofs k ->
        if (&&) ((fun x -> x) (zle lo ofs)) ((fun x -> x) (zlt ofs hi))
        then None
        else PMap.get b m.mem_access ofs k) m.mem_access); nextblock =
      m.nextblock }

  (** val free : mem -> block -> coq_Z -> coq_Z -> mem option **)

  let free m b lo hi =
    if range_perm_dec m b lo hi Cur Freeable
    then Some (unchecked_free m b lo hi)
    else None

  (** val free_list : mem -> ((block * coq_Z) * coq_Z) list -> mem option **)

  let rec free_list m = function
  | [] -> Some m
  | p :: l' ->
    let (p0, hi) = p in
    let (b, lo) = p0 in
    (match free m b lo hi with
     | Some m' -> free_list m' l'
     | None -> None)

  (** val getN : nat -> coq_Z -> memval ZMap.t -> memval list **)

  let rec getN n p c =
    match n with
    | O -> []
    | S n' -> (ZMap.get p c) :: (getN n' (Z.add p (Zpos Coq_xH)) c)

  (** val load : memory_chunk -> mem -> block -> coq_Z -> coq_val option **)

  let load chunk m b ofs =
    if valid_access_dec m chunk b ofs Readable
    then Some
           (decode_val chunk
             (getN (size_chunk_nat chunk) ofs (PMap.get b m.mem_contents)))
    else None

  (** val loadv : memory_chunk -> mem -> coq_val -> coq_val option **)

  let loadv chunk m = function
  | Vptr (b, ofs) -> load chunk m b (Ptrofs.unsigned ofs)
  | _ -> None

  (** val loadbytes : mem -> block -> coq_Z -> coq_Z -> memval list option **)

  let loadbytes m b ofs n =
    if range_perm_dec m b ofs (Z.add ofs n) Cur Readable
    then Some (getN (Z.to_nat n) ofs (PMap.get b m.mem_contents))
    else None

  (** val setN : memval list -> coq_Z -> memval ZMap.t -> memval ZMap.t **)

  let rec setN vl p c =
    match vl with
    | [] -> c
    | v :: vl' -> setN vl' (Z.add p (Zpos Coq_xH)) (ZMap.set p v c)

  (** val store :
      memory_chunk -> mem -> block -> coq_Z -> coq_val -> mem option **)

  let store chunk m b ofs v =
    if valid_access_dec m chunk b ofs Writable
    then Some { mem_contents =
           (PMap.set b
             (setN (encode_val chunk v) ofs (PMap.get b m.mem_contents))
             m.mem_contents); mem_access = m.mem_access; nextblock =
           m.nextblock }
    else None

  (** val storev : memory_chunk -> mem -> coq_val -> coq_val -> mem option **)

  let storev chunk m addr v =
    match addr with
    | Vptr (b, ofs) -> store chunk m b (Ptrofs.unsigned ofs) v
    | _ -> None

  (** val storebytes : mem -> block -> coq_Z -> memval list -> mem option **)

  let storebytes m b ofs bytes =
    if range_perm_dec m b ofs (Z.add ofs (Z.of_nat (length bytes))) Cur
         Writable
    then Some { mem_contents =
           (PMap.set b (setN bytes ofs (PMap.get b m.mem_contents))
             m.mem_contents); mem_access = m.mem_access; nextblock =
           m.nextblock }
    else None

  (** val drop_perm :
      mem -> block -> coq_Z -> coq_Z -> permission -> mem option **)

  let drop_perm m b lo hi p =
    if range_perm_dec m b lo hi Cur Freeable
    then Some { mem_contents = m.mem_contents; mem_access =
           (PMap.set b (fun ofs k ->
             if (&&) ((fun x -> x) (zle lo ofs)) ((fun x -> x) (zlt ofs hi))
             then Some p
             else PMap.get b m.mem_access ofs k) m.mem_access); nextblock =
           m.nextblock }
    else None
 end
