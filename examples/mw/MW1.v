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

  Record local_state: Type := mk_lst {
    lst_dom: Z -> option unit;
    lst_opt: Z -> option val;
    lst_map: val;
    (* lst_wf: forall k, (is_some (lst_opt k)) -> (is_some (lst_dom k)) *)
  }
  .

  (* Program Definition add_dom (lst0: local_state) k: local_state := *)
  (*   (mk_lst (add k tt lst0.(lst_dom)) lst0.(lst_opt) lst0.(lst_map) _) *)
  (* . *)
  (* Next Obligation. *)
  (*   i. eapply lst0.(lst_wf) in H. unfold is_some in *. des_ifs. unfold add in *. ss. des_ifs. *)
  (* Qed. *)

  (* Program Definition add_opt (lst0: local_state) k v: local_state := *)
  (*   (mk_lst (add k v lst0.(lst_opt)) (add k v lst0.(lst_opt)) lst0.(lst_map) _) *)
  (* . *)
  (* Next Obligation. *)
  (*   i. unfold add in *. ss. des_ifs. *)
  (*   - eapply lst0.(lst_wf) in H. unfold is_some in *. des_ifs. unfold add in *. ss. des_ifs. *)
  (* Qed. *)

  Notation upd_dom f := (lst0 <- pget;; pput (mk_lst (f lst0.(lst_dom)) lst0.(lst_opt) lst0.(lst_map))).
  Notation upd_opt f := (lst0 <- pget;; pput (mk_lst lst0.(lst_dom) (f lst0.(lst_opt)) lst0.(lst_map))).
  Notation upd_map f := (lst0 <- pget;; pput (mk_lst lst0.(lst_dom) lst0.(lst_opt) (f lst0.(lst_map)))).

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
      `map: val <- ccallU "new" ([]: list val);;
      upd_map (fun _ => map);;;
      `_: val <- ccallU "loop" ([]: list val);;
      Ret Vundef
  .

  Definition putF: list val -> itree Es val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tuntyped] varg)?;;
      assume((0 <= k)%Z);;;
      b <- trigger (Choose _);;
      (if (b: bool)
       then upd_opt (fun opt => add k v opt)
       else lst0 <- pget;; `_: val <- ccallU "update" ([lst0.(lst_map); Vint k; v]);; upd_dom (fun dom => add k tt dom));;;
      trigger (Syscall "print" [Vint k]↑ top1);;;
      trigger (Syscall "print" [v]↑ top1);;;
      Ret Vundef
  .

  Definition getF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      `lst0: local_state <- pget;;
      assume(is_some (lst0.(lst_dom) k) \/ is_some (lst0.(lst_opt) k));;;
      v <- (match lst0.(lst_opt) k with
            | Some v => Ret v
            | _ => ccallU "access" ([lst0.(lst_map); Vint k])
            end);;
      trigger (Syscall "print" [Vint k]↑ top1);;; (*** TODO: make something like "syscallu" ***)
      trigger (Syscall "print" [v]↑ top1);;;
      Ret Vundef
  .

  Definition MWSem: ModSem.t := {|
    ModSem.fnsems := [("main", cfunU mainF); ("loop", cfunU loopF); ("put", cfunU putF); ("get", cfunU getF)];
    ModSem.mn := "MW";
    ModSem.initial_st := (mk_lst empty empty Vnullptr)↑;
  |}
  .

  Definition MW: Mod.t := {|
    Mod.get_modsem := fun _ => MWSem;
    Mod.sk := [("main", Sk.Gfun); ("loop", Sk.Gfun); ("put", Sk.Gfun); ("get", Sk.Gfun)];
  |}
  .

End PROOF.
