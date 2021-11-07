Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import MWHeader.
Require Import PCM.
Require Import HoareDef OpenDef STB.
Require Import Mem1.

Set Implicit Arguments.



Section PROOF.

  (* Variant lunit: Type := ltt: lunit. *)

  Notation pget := (p0 <- trigger PGet;; p0 <- p0↓?;; Ret p0) (only parsing). (*** NOTE THAT IT IS UB CASTING ***)
  Notation pput p0 := (trigger (PPut p0↑)) (only parsing).
  Notation pupd_arr arr := (`st: mblock * val <- pget;; pput (arr, st.2)) (only parsing).
  Notation pupd_map map := (`st: mblock * val <- pget;; pput (st.1, map)) (only parsing).

  Notation check_lock := (p0 <- trigger PGet;; if (Any.split p0) then triggerUB else Ret tt) (only parsing).
  Notation lAPC := (p0 <- trigger PGet;; _ <- trigger (PPut (Any.pair tt↑ p0));;; trigger (PPut p0))
                     (only parsing).

  Let Es := (hAPCE +' Es).

  Definition loopF: list val -> itree Es val :=
    fun varg =>
      check_lock;;;
      _ <- (pargs [] varg)?;;
      `_: val <- ccallU "run" ([]: list val);;
      `_: val <- ccallU "loop" ([]: list val);;
      Ret Vundef
  .

  Definition mainF: list val -> itree Es val :=
    fun varg =>
      _ <- (pargs [] varg)?;;
      check_lock;;;
      arr <- ccallU "alloc" ([Vint 100]);;
      lAPC;;;
      arr <- (pargs [Tblk] [arr])?;;
      pupd_arr arr;;;
      `map: val <- ccallU "new" ([]: list val);;
      pupd_map map;;;
      lAPC;;;
      `_: val <- ccallU "init" ([]: list val);;
      `_: val <- ccallU "loop" ([]: list val);;
      Ret Vundef
  .

  Definition putF: list val -> itree Es val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tuntyped] varg)?;;
      '(arr, map) <- pget;;
      (if ((0 <=? k) && (k <? 100))%Z
       then `_: val <- ccallU "store" [Vptr arr k; v];; Ret tt
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
                  then ccallU "load" [Vptr arr k]
                  else ccallU "access" ([map; Vint k]));;
      trigger (Syscall "print" [Vint k]↑ top1);;; (*** TODO: make something like "syscallu" ***)
      trigger (Syscall "print" [v]↑ top1);;;
      Ret v
  .

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Definition MWsbtb: list (string * kspecbody) :=
    [("main", ksb_trivial (cfunU mainF)); ("loop", ksb_trivial (cfunU loopF));
    ("put", ksb_trivial (cfunU putF)); ("get", ksb_trivial (cfunU getF))].

  Definition MWStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun ksb => ksb.(ksb_fspec): fspec)) MWsbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition KMWSem ske: KModSem.t := {|
    KModSem.fnsems := MWsbtb;
    KModSem.mn := "MW";
    KModSem.initial_mr := GRA.embed (var_points_to ske "gv0" (Vint 0)) ⋅
                                    GRA.embed (var_points_to ske "gv1" (Vint 0));
    KModSem.initial_st := (Vint 0, Vint 0)↑;
  |}
  .

  (* Definition MWSem (stb: gname -> option fspec): ModSem.t := *)
  (*   KModSem.transl_tgt stb KMWSem. *)

  Definition KMW: KMod.t := {|
    KMod.get_modsem := fun sk => KMWSem (Sk.load_skenv sk);
    KMod.sk := [("loop", Sk.Gfun); ("put", Sk.Gfun); ("get", Sk.Gfun); ("gv0", Sk.Gvar 0); ("gv1", Sk.Gvar 0);
               ("gv2", Sk.Gvar 0); ("gv3", Sk.Gvar 0)]
  |}
  .

  Definition MW (stb: Sk.t -> gname -> option fspec): Mod.t := (KMod.transl_tgt stb KMW).

End PROOF.
Global Hint Unfold MWStb: stb.
