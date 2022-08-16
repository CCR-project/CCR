Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Imp.
Require Import ImpNotations.
Require Import MWHeader.

Set Implicit Arguments.



Section PROOF.

  Variable skenv: SkEnv.t.

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
      arrb <- (skenv.(SkEnv.id2blk) "gv0")?;;
      mapb <- (skenv.(SkEnv.id2blk) "gv1")?;;
      `arr: val <- ccallU "alloc" ([Vint 100]);; (pargs [Tblk] [arr])?;;;
      `_: val   <- ccallU "store" [Vptr arrb 0; arr];;
      `map: val <- ccallU "Map.new" ([]: list val);;
      `_: val   <- ccallU "store" [Vptr mapb 0; map];;
      `_: val <- ccallU "App.init" ([]: list val);;
      `_: val <- ccallU "MW.loop" ([]: list val);;
      Ret Vundef
  .

  Definition putF: list val -> itree Es val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tuntyped] varg)?;;
      arrb <- (skenv.(SkEnv.id2blk) "gv0")?;;
      mapb <- (skenv.(SkEnv.id2blk) "gv1")?;;
      assume(intrange_64 k);;;
      (if ((0 <=? k) && (k <? 100))%Z
       then `arr: val <- (ccallU "load"  [Vptr arrb 0]);;
            addr <- (vadd arr (Vint (8 * k)))?;; assume(wf_val addr);;; `_: val <- ccallU "store" [addr; v];; Ret tt
       else `map: val <- (ccallU "load"  [Vptr mapb 0]);;
            `_: val <- ccallU "Map.update" ([map; Vint k; v]);; Ret tt);;;
      syscallU "print" [k];;;
      Ret Vundef
  .

  Definition getF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      arrb <- (skenv.(SkEnv.id2blk) "gv0")?;;
      mapb <- (skenv.(SkEnv.id2blk) "gv1")?;;
      assume(intrange_64 k);;;
      `v: val <- (if ((0 <=? k) && (k <? 100))%Z
                  then `arr: val <- (ccallU "load"  [Vptr arrb 0]);;
                       addr <- (vadd arr (Vint (8 * k)))?;; assume(wf_val addr);;; ccallU "load" [addr]
                  else `map: val <- (ccallU "load"  [Vptr mapb 0]);;
                       ccallU "Map.access" ([map; Vint k]));;
      syscallU "print" [k];;;
      Ret v
  .

  Definition MWSem: ModSem.t := {|
    ModSem.fnsems := [("main", cfunU mainF); ("MW.loop", cfunU loopF);
                     ("MW.put", cfunU putF); ("MW.get", cfunU getF)];
    ModSem.mn := "MW";
    ModSem.initial_st := tt↑;
  |}
  .

End PROOF.

Definition MW: Mod.t := {|
  Mod.get_modsem := fun sk => MWSem (Sk.load_skenv sk);
  Mod.sk := [("MW.loop", Sk.Gfun); ("MW.put", Sk.Gfun); ("MW.get", Sk.Gfun);
               ("gv0", Sk.Gvar 0); ("gv1", Sk.Gvar 0)];
|}
.
