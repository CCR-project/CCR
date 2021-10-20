Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import MWHeader.
Require Import Mem1.

Set Implicit Arguments.



Section PROOF.

  Notation pget := (p0 <- trigger PGet;; p0 <- p0↓ǃ;; Ret p0) (only parsing).
  Notation pput p0 := (trigger (PPut p0↑)) (only parsing).

  Record local_state: Type := mk_lst {
    lst_dom: Z -> option unit;
    lst_opt: Z -> option val;
    lst_map: val;
    (* lst_wf: forall k, (is_some (lst_opt k)) -> (is_some (lst_dom k)) *)
  }
  .

  Notation upd_dom f := (lst0 <- pget;; pput (mk_lst (f lst0.(lst_dom)) lst0.(lst_opt) lst0.(lst_map))).
  Notation upd_opt f := (lst0 <- pget;; pput (mk_lst lst0.(lst_dom) (f lst0.(lst_opt)) lst0.(lst_map))).
  Notation upd_map f := (lst0 <- pget;; pput (mk_lst lst0.(lst_dom) lst0.(lst_opt) (f lst0.(lst_map)))).

  Let Es := (hAPCE +' Es).

  Definition ncall X Y (f: string): itree Es Y :=
    `b: bool <- trigger (Choose bool);;
    if b
    then `x: X <- trigger (Choose _);; ccallU f x
    else r <- trigger (Choose _);; Ret r
  .

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
      ncall (list val) val "alloc";;;
      `map: val <- ccallU "new" ([]: list val);;
      upd_map (fun _ => map);;;
      `_: val <- ccallU "loop" ([]: list val);;
      Ret Vundef
  .

  Definition putF: list val -> itree Es val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tuntyped] varg)?;;
      lst0 <- pget;; 
      assume(lst0.(lst_map) <> Vnullptr);;;
      assume((0 <= k)%Z);;;
      b <- trigger (Choose _);;
      (if (b: bool)
       then ncall (list val) val "store";;; upd_opt (fun opt => add k v opt)
       else `_: val <- ccallU "update" ([lst0.(lst_map); Vint k; v]);; upd_dom (fun dom => add k tt dom));;;
      trigger (Syscall "print" [Vint k]↑ top1);;;
      trigger (Syscall "print" [v]↑ top1);;;
      Ret Vundef
  .

  Definition getF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      `lst0: local_state <- pget;;
      assume(lst0.(lst_map) <> Vnullptr);;;
      assume(is_some (lst0.(lst_dom) k) \/ is_some (lst0.(lst_opt) k));;;
      v <- (match lst0.(lst_opt) k with
            | Some v => ncall (list val) val "load";;; Ret v
            | _ => ccallU "access" ([lst0.(lst_map); Vint k])
            end);;
      trigger (Syscall "print" [Vint k]↑ top1);;; (*** TODO: make something like "syscallu" ***)
      trigger (Syscall "print" [v]↑ top1);;;
      Ret Vundef
  .

  Context `{Σ: GRA.t}.

  Definition MWsbtb: list (string * fspecbody) :=
    [("main", mk_specbody fspec_trivial (cfunU mainF));
    ("loop", mk_specbody fspec_trivial (cfunU loopF));
    ("put", mk_specbody fspec_trivial (cfunU putF));
    ("get", mk_specbody fspec_trivial (cfunU getF))
    ].

  Definition SMWSem: SModSem.t := {|
    SModSem.fnsems := MWsbtb;
    SModSem.mn := "MW";
    SModSem.initial_mr := ε;
    SModSem.initial_st := (mk_lst empty empty Vnullptr)↑;
  |}
  .

  Definition SMW: SMod.t := {|
    SMod.get_modsem := fun _ => SMWSem;
    SMod.sk := [("main", Sk.Gfun); ("loop", Sk.Gfun); ("put", Sk.Gfun); ("get", Sk.Gfun)];
  |}
  .

  Context `{@GRA.inG memRA Σ}.

  Definition MW: Mod.t := (SMod.to_tgt (fun _ => GlobalStbC)) SMW.

End PROOF.
