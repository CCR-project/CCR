open BinNums
open Coqlib0
open RelDec
open String0

type 'a coq_Dec = 'a -> 'a -> bool

val dec : 'a1 coq_Dec -> 'a1 -> 'a1 -> bool

val positive_Dec_obligation_1 : positive -> positive -> bool

val positive_Dec : positive coq_Dec

val string_Dec_obligation_1 : char list -> char list -> bool

val string_Dec : char list coq_Dec

val coq_Dec_RelDec : 'a1 coq_Dec -> 'a1 coq_RelDec
