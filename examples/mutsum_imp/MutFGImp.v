Require Import Any.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem.
Require Import Imp.
Require Import MutF0 MutMainImp MutFImp MutGImp.

Set Implicit Arguments.

Section IMP.
  Import ImpNotations.
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.

  Let Σ: GRA.t := fun _ => URA.of_RA RA.empty.
  Local Existing Instance Σ.

  Definition FGImp : Mod.t := Mod.add_list [MutMainImp.main ; MutF0.F ; MutGImp.g].

  Definition mutsum_imp := ModSem.initial_itr_no_check (Mod.enclose FGImp).
  
End IMP.
