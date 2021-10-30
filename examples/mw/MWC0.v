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

  Notation pget := (p0 <- trigger PGet;; p0 <- p0↓ǃ;; Ret p0) (only parsing).
  Notation pput p0 := (trigger (PPut p0↑)) (only parsing).

  Definition loopF: list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      `_: val <- ccallU "run" ([]: list val);;
      `_: val <- ccallU "loop" ([]: list val);;
      Ret Vundef
  .

  Definition mainF: list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      `arr: val <- ccallU "alloc" ([Vint 100]);;
      `map: val <- ccallU "new" ([]: list val);;
      pput (arr, map);;;
      `_: val <- ccallU "init" ([]: list val);;
      `_: val <- ccallU "loop" ([]: list val);;
      Ret Vundef
  .

  Definition putF: list val -> itree Es val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tuntyped] varg)?;;
      '(arr, map) <- pget;;
      (if ((0 <=? k) && (k <? 100))%Z
       then `_: val <- ccallU "store" [arr; Vint k; v];; Ret tt
       else `_: val <- ccallU "update" ([map; Vint k; v]);; Ret tt);;;
      trigger (Syscall "print" [Vint k]↑ top1);;; (*** TODO: make something like "syscallu" ***)
      trigger (Syscall "print" [v]↑ top1);;;
      Ret Vundef
  .

  Definition getF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      '(arr, map) <- pget;;
      `v: val <- (if ((0 <=? k) && (k <? 100))%Z
                  then ccallU "load" [arr; Vint k]
                  else ccallU "access" ([map; Vint k]));;
      trigger (Syscall "print" [Vint k]↑ top1);;; (*** TODO: make something like "syscallu" ***)
      trigger (Syscall "print" [v]↑ top1);;;
      Ret Vundef
  .

  Definition MWSem (skenv: SkEnv.t): ModSem.t := {|
    ModSem.fnsems := [("main", cfunU mainF); ("loop", cfunU loopF); ("put", cfunU putF); ("get", cfunU getF)];
    ModSem.mn := "MW";
    ModSem.initial_st := (Vnullptr, Vnullptr)↑;
  |}
  .
  (* Vptr (or_else (skenv.(SkEnv.id2blk) "arr") 0) 0 *)
  Definition MW: Mod.t := {|
    Mod.get_modsem := fun sk => MWSem (Sk.load_skenv sk);
    Mod.sk := [("arr", Sk.Gvar 0); ("map", Sk.Gvar 0); ("main", Sk.Gfun); ("loop", Sk.Gfun); ("put", Sk.Gfun); ("get", Sk.Gfun)];
  |}
  .

End PROOF.