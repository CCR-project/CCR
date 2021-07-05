open BinNums
open Coqlib
open Datatypes
open EquivDec
open List0

module type TREE =
 sig
  type elt

  val elt_eq : elt -> elt -> bool

  type 'x t

  val empty : 'a1 t

  val get : elt -> 'a1 t -> 'a1 option

  val set : elt -> 'a1 -> 'a1 t -> 'a1 t

  val remove : elt -> 'a1 t -> 'a1 t

  val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val map : (elt -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val combine :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (elt * 'a1) list

  val fold : ('a2 -> elt -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val fold1 : ('a2 -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
 end

module PTree :
 sig
  type elt = positive

  val elt_eq : positive -> positive -> bool

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  val empty : 'a1 t

  val get : positive -> 'a1 t -> 'a1 option

  val set : positive -> 'a1 -> 'a1 t -> 'a1 t

  val remove : positive -> 'a1 t -> 'a1 t

  val bempty : 'a1 t -> bool

  val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val prev_append : positive -> positive -> positive

  val prev : positive -> positive

  val xmap : (positive -> 'a1 -> 'a2) -> 'a1 t -> positive -> 'a2 t

  val map : (positive -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val coq_Node' : 'a1 t -> 'a1 option -> 'a1 t -> 'a1 t

  val filter1 : ('a1 -> bool) -> 'a1 t -> 'a1 t

  val xcombine_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

  val xcombine_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

  val combine :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val xelements :
    'a1 t -> positive -> (positive * 'a1) list -> (positive * 'a1) list

  val elements : 'a1 t -> (positive * 'a1) list

  val xkeys : 'a1 t -> positive -> positive list

  val xfold :
    ('a2 -> positive -> 'a1 -> 'a2) -> positive -> 'a1 t -> 'a2 -> 'a2

  val fold : ('a2 -> positive -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val fold1 : ('a2 -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
 end

module PMap :
 sig
  type 'a t = 'a * 'a PTree.t

  val init : 'a1 -> 'a1 * 'a1 PTree.t

  val get : positive -> 'a1 t -> 'a1

  val set : positive -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.t

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module type INDEXED_TYPE =
 sig
  type t

  val index : t -> positive

  val eq : t -> t -> bool
 end

module IMap :
 functor (X:INDEXED_TYPE) ->
 sig
  type elt = X.t

  val elt_eq : X.t -> X.t -> bool

  type 'x t = 'x PMap.t

  val init : 'a1 -> 'a1 * 'a1 PTree.t

  val get : X.t -> 'a1 t -> 'a1

  val set : X.t -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.t

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module ZIndexed :
 sig
  type t = coq_Z

  val index : coq_Z -> positive

  val eq : coq_Z -> coq_Z -> bool
 end

module ZMap :
 sig
  type elt = ZIndexed.t

  val elt_eq : ZIndexed.t -> ZIndexed.t -> bool

  type 'x t = 'x PMap.t

  val init : 'a1 -> 'a1 * 'a1 PTree.t

  val get : ZIndexed.t -> 'a1 t -> 'a1

  val set : ZIndexed.t -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.t

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module ITree :
 functor (X:INDEXED_TYPE) ->
 sig
  type elt = X.t

  val elt_eq : X.t -> X.t -> bool

  type 'x t = 'x PTree.t

  val empty : 'a1 t

  val get : elt -> 'a1 t -> 'a1 option

  val set : elt -> 'a1 -> 'a1 t -> 'a1 t

  val remove : elt -> 'a1 t -> 'a1 t

  val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val combine :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
 end

module ZTree :
 sig
  type elt = ZIndexed.t

  val elt_eq : ZIndexed.t -> ZIndexed.t -> bool

  type 'x t = 'x PTree.t

  val empty : 'a1 t

  val get : elt -> 'a1 t -> 'a1 option

  val set : elt -> 'a1 -> 'a1 t -> 'a1 t

  val remove : elt -> 'a1 t -> 'a1 t

  val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val combine :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
 end

module Tree_Properties :
 functor (T:TREE) ->
 sig
  val cardinal : 'a1 T.t -> nat

  val for_all : 'a1 T.t -> (T.elt -> 'a1 -> bool) -> bool

  val exists_ : 'a1 T.t -> (T.elt -> 'a1 -> bool) -> bool

  val coq_Equal_dec : 'a1 coq_EqDec -> 'a1 T.t -> 'a1 T.t -> bool

  val coq_Equal_EqDec : 'a1 coq_EqDec -> 'a1 T.t coq_EqDec

  val of_list : (T.elt * 'a1) list -> 'a1 T.t
 end

module PTree_Properties :
 sig
  val cardinal : 'a1 PTree.t -> nat

  val for_all : 'a1 PTree.t -> (PTree.elt -> 'a1 -> bool) -> bool

  val exists_ : 'a1 PTree.t -> (PTree.elt -> 'a1 -> bool) -> bool

  val coq_Equal_dec : 'a1 coq_EqDec -> 'a1 PTree.t -> 'a1 PTree.t -> bool

  val coq_Equal_EqDec : 'a1 coq_EqDec -> 'a1 PTree.t coq_EqDec

  val of_list : (PTree.elt * 'a1) list -> 'a1 PTree.t
 end
