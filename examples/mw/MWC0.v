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

  Notation pget := (p0 <- trigger PGet;; p0 <- p0↓?;; Ret p0) (only parsing). (*** NOTE THAT IT IS UB CASTING ***)
  Notation pput p0 := (trigger (PPut p0↑)) (only parsing).
  Notation pupd_arr arr := (`st: val * val <- pget;; pput (arr, snd st)) (only parsing).
  Notation pupd_map map := (`st: val * val <- pget;; pput (fst st, map)) (only parsing).

  Definition loopF: list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      `_: val <- ccallU "App.run" ([]: list val);;
      `_: val <- ccallU "MW.loop" ([]: list val);;
      Ret Vundef
  .

  Definition mainF: list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      `arr: val <- ccallU "alloc" ([Vint 100]);; (pargs [Tblk] [arr])?;;;
      pupd_arr arr;;;
      `map: val <- ccallU "Map.new" ([]: list val);;
      pupd_map map;;;
      `_: val <- ccallU "App.init" ([]: list val);;
      `_: val <- ccallU "MW.loop" ([]: list val);;
      Ret Vundef
  .

  Definition putF: list val -> itree Es val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tuntyped] varg)?;;
      assume(intrange_64 k);;;
      '(arr, map) <- pget;;
      (if ((0 <=? k) && (k <? 100))%Z
       then addr <- (vadd arr (Vint (8 * k)))?;; `_: val <- ccallU "store" [addr; v];; Ret tt
       else `_: val <- ccallU "Map.update" ([map; Vint k; v]);; Ret tt);;;
      syscallU "print" [k];;;
      Ret Vundef
  .

  Definition getF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      assume(intrange_64 k);;;
      '(arr, map) <- pget;;
      `v: val <- (if ((0 <=? k) && (k <? 100))%Z
                  then addr <- (vadd arr (Vint (8 * k)))?;; ccallU "load" [addr]
                  else ccallU "Map.access" ([map; Vint k]));;
      syscallU "print" [k];;;
      Ret v
  .

  Definition MWSem (skenv: SkEnv.t): ModSem.t := {|
    ModSem.fnsems := [("MW.main", cfunU mainF); ("MW.loop", cfunU loopF);
                     ("MW.put", cfunU putF); ("MW.get", cfunU getF)];
    ModSem.mn := "MW";
    ModSem.initial_st := (Vint 0, Vint 0)↑;
  |}
  .
  (* Vptr (or_else (skenv.(SkEnv.id2blk) "arr") 0) 0 *)
  Definition MW: Mod.t := {|
    Mod.get_modsem := fun sk => MWSem (Sk.load_skenv sk);
    Mod.sk := [("MW.main", Sk.Gfun); ("MW.loop", Sk.Gfun); ("MW.put", Sk.Gfun); ("MW.get", Sk.Gfun);
               ("gv0", Sk.Gvar 0); ("gv1", Sk.Gvar 0)];
  |}
  .

End PROOF.
