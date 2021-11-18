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
  Notation pupd_idv idv := (`st: option (val * val) * val <- pget;; pput (idv, snd st)) (only parsing).
  Notation pupd_map map := (`st: option (val * val) * val <- pget;; pput (fst st, map)) (only parsing).

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
      pupd_idv (@None (val * val));;;
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
      '(idv, map) <- pget;;
      (match (idv: option (val * val)) with
       | Some (i, _) =>
         if dec i (Vint k)
         then pupd_idv (Some (Vint k, v))
         else `_: val <- ccallU "Map.update" ([map; Vint k; v]);; Ret tt
       | _ => pupd_idv (Some (Vint k, v))
       end);;;
      syscallU "print" [k];;;
      Ret Vundef
  .

  Definition getF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      assume(intrange_64 k);;;
      '(idv, map) <- pget;;
      `v: val <- (match idv with
                  | Some (i, v) =>
                    if dec i (Vint k)
                    then Ret v
                    else ccallU "Map.access" ([map; Vint k])
                  | _ => ccallU "Map.access" ([map; Vint k])
                  end);;
      syscallU "print" [k];;;
      Ret v
  .

  Definition MWSem (skenv: SkEnv.t): ModSem.t := {|
    ModSem.fnsems := [("main", cfunU mainF); ("MW.loop", cfunU loopF);
                     ("MW.put", cfunU putF); ("MW.get", cfunU getF)];
    ModSem.mn := "MW";
    ModSem.initial_st := (@None (val * val), Vint 0)↑;
  |}
  .
  (* Vptr (or_else (skenv.(SkEnv.id2blk) "arr") 0) 0 *)
  Definition MW: Mod.t := {|
    Mod.get_modsem := fun sk => MWSem (Sk.load_skenv sk);
    Mod.sk := [("MW.loop", Sk.Gfun); ("MW.put", Sk.Gfun); ("MW.get", Sk.Gfun);
               ("gv0", Sk.Gvar 0); ("gv1", Sk.Gvar 0)];
  |}
  .

End PROOF.
