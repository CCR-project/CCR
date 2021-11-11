Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import MWHeader.

Set Implicit Arguments.



Section PROOF.

  Definition newF: list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      `new_node: val  <- (ccallU "alloc" [Vint 1]);;
      assume(wf_val new_node);;;
      `_: val         <- (ccallU "store" [new_node; Vnullptr]);;
      Ret new_node
  .

  Definition updateF: list val -> itree Es val :=
    fun args =>
      '(h, (k, v))      <- (pargs [Tblk; Tuntyped; Tuntyped] args)?;;
      `r: val           <- (ccallU "alloc" [Vint 3]);;
      `new_node: mblock <- (pargs [Tblk] [r])?;;
      `hd: val          <- (ccallU "load"  [Vptr h 0]);;
      `_: val           <- (ccallU "store" [Vptr new_node 0; k]);;
      `_: val           <- (ccallU "store" [Vptr new_node 1; v]);;
      `_: val           <- (ccallU "store" [Vptr new_node 2; hd]);;
      `_: val           <- (ccallU "store" [Vptr h 0; Vptr new_node 0]);;
      Ret Vundef
  .

  Definition accessF: list val -> itree Es val :=
    fun args =>
      '(h, k)           <- (pargs [Tblk; Tuntyped] args)?;;
      `hd: val          <- (ccallU "load"  [Vptr h 0]);;
      (ccallU "Map.loop" [hd; k])
  .

  Definition loopF: list val -> itree Es val :=
    fun args =>
      '(cur, k)         <- (pargs [Tblk; Tint] args)?;;
      `curk: val        <- (ccallU "load"  [Vptr cur 0]);;
      curk              <- (pargs [Tint] [curk])?;;
      assume(intrange_64 k /\ intrange_64 curk);;;
      if (dec curk k)
      then (ccallU "load"  [Vptr cur 1])
      else
        `next: val      <- (ccallU "load"  [Vptr cur 2]);;
        (ccallU "Map.loop" [next; Vint k])
  .

  Definition MapSem (skenv: SkEnv.t): ModSem.t := {|
    ModSem.fnsems := [("Map.new", cfunU newF); ("Map.update", cfunU updateF);
                     ("Map.access", cfunU accessF); ("Map.loop", cfunU loopF)];
    ModSem.mn := "Map";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Map: Mod.t := {|
    Mod.get_modsem := fun sk => MapSem (Sk.load_skenv sk);
    Mod.sk := [("Map.new", Sk.Gfun); ("Map.update", Sk.Gfun); ("Map.access", Sk.Gfun); ("Map.loop", Sk.Gfun)];
  |}
  .

End PROOF.
