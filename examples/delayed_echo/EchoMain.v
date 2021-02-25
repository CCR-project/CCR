Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Echo1.
Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  Definition mainF: Any.t -> itree Es val :=
    fun varg =>
      ccall "echo" [Vnullptr];;


      call
      '(ll, nref) <- (pop2F_parg varg)?;;
      `b: val <- (ccall "cmp"  [ll; Vnullptr]);;
      if (is_zero b)
      then (
          '(blk, ofs) <- (unptr ll)?;;
          let addr_val  := Vptr blk ofs in
          let addr_next := Vptr blk (ofs + 1) in
          `v: val    <- (ccall "load"  [addr_val]);;
          `next: val <- (ccall "load"  [addr_next]);;
          `_: val    <- (ccall "free"  [addr_val]);;
          `_: val    <- (ccall "free"  [addr_next]);; (*** change "free"s specification ***)
          `_: val    <- (ccall "store" [nref; v]);;
          Ret next
        )
      else Ret Vnullptr
  .


  Definition mainF: Any.t -> itree Es Any.t :=
    fun varg =>
      r <- trigger (Call "f" [Vint 10]↑);;
      Ret r.

  Definition mainSem: ModSem.t := {|
    ModSem.fnsems := [("main", mainF)];
    ModSem.initial_mrs := [("Main", (ε, tt↑))];
  |}
  .

  Definition main: Mod.t := {|
    Mod.get_modsem := fun _ => mainSem;
    Mod.sk := [("Main", Sk.Gfun)];
  |}
  .
End PROOF.
