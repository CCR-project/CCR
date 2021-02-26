Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import LinkedList1.
Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.




(*** TODO: rename ccall into call; ***)
(*** TODO: move this to TODOYJ ***)
Definition hcall {X Y} (fn: gname) (varg: X): itree (hCallE +' pE +' eventE) Y :=
  vret <- trigger (hCall false fn varg↑);; vret <- vret↓ǃ;; Ret vret.





Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  Definition is_minus_one (v: val): bool :=
    match v with
    | Vint i => dec i (- 1)%Z
    | _ => false
    end
  .

  Definition echo_body: list val -> itree Es Any.t :=
    fun _ =>
      `n: val <- (ccall "in" ([]: list val));;
      `n: Z   <- (unint n)?;;
      if dec n (- 1)%Z
      then `_: val <- (ccall "echo_finish" ([]: list val));; Ret Vundef
      else
        ll0 <- trigger (PGet "Echo");;
        `ll0: list Z <- ll0↓?;;
        let ll1 := (n :: ll0) in
        trigger(PPut "Echo" ll1↑);;
        `_: val <- (hcall "echo" ([]: list val));;
        Ret Vundef
      (* `n: val <- (n↓)ǃ;; *)
      (* `n: Z   <- (unint n)?;; *)
      triggerUB.


      trigger (Call "in" []↑)ǃ;;
          triggerUB.

      `n: Z   <- (unint n)?;;
      if dec n (- 1)%Z
      then `_: val <- (hcall "echo_finish" ([]: list val));; Ret Vundef
      else
        ll0 <- trigger (PGet "Echo");;
        `ll0: list Z <- ll0↓?;;
        let ll1 := (n :: ll0) in
        trigger(PPut "Echo" ll1↑);;
        `_: val <- (hcall "echo" ([]: list val));;
        Ret Vundef
  .

  Definition echo_finish_body: list val -> itree (hCallE +' pE +' eventE) val :=
    fun _ =>
      ll0 <- trigger (PGet "Echo");; `ll0: list Z <- ll0↓?;;
      match ll0 with
      | [] => Ret Vundef
      | hd :: tl =>
        `_: val        <- (hcall "out" [Vint hd]);;
        trigger (PPut "Echo" tl↑);;
        `_: val        <- (hcall "echo_finish" ([]: list val));;
        Ret Vundef
      end
  .

  (* Definition echoF: list val -> itree (hCallE +' pE +' eventE) Any.t := *)
  (*   fun ns => *)
  (*     n <- trigger (hCall false "in" ([]: list val)↑);; *)
  (*     `n: val <- n↓?;; `n: Z <- (unint n)?;; *)
  (*     if dec n (- 1)%Z *)
  (*     then trigger (Call "echo_finish" ns↑);; Ret tt *)
  (*     else *)
  (*       trigger (Call "echo" (n :: ns));; *)
  (*       Ret tt *)
  (* . *)

  (* Definition echo_finishF: list Z -> itree (hCallE +' pE +' eventE) unit := *)
  (*   fun ns => *)
  (*     match ns with *)
  (*     | [] => Ret tt *)
  (*     | hd :: tl => *)
  (*       trigger (hCall false "out" [Vint hd]↑);; *)
  (*       trigger (hCall false "echo_finish" tl↑);; *)
  (*       Ret tt *)
  (*     end *)
  (* . *)

  Definition echo_body: list val -> itree (hCallE +' pE +' eventE) val :=
    fun _ =>
      `n: val <- (hcall "in" ([]: list val));;
      `n: Z   <- (unint n)?;;
      if dec n (- 1)%Z
      then `_: val <- (hcall "echo_finish" ([]: list val));; Ret Vundef
      else
        ll0 <- trigger (PGet "Echo");;
        APC;;
        `ll0: list Z <- ll0↓?;;
        let ll1 := (n :: ll0) in
        trigger(PPut "Echo" ll1↑);;
        `_: val <- (hcall "echo" ([]: list val));;
        Ret Vundef
  .

  Definition echo_finish_body: list val -> itree (hCallE +' pE +' eventE) val :=
    fun _ =>
      ll0 <- trigger (PGet "Echo");; `ll0: list Z <- ll0↓?;;
      match ll0 with
      | [] => Ret Vundef
      | hd :: tl =>
        `_: val        <- (hcall "out" [Vint hd]);;
        trigger (PPut "Echo" tl↑);;
        `_: val        <- (hcall "echo_finish" ([]: list val));;
        Ret Vundef
      end
  .

  (* Let echo_spec:        fspec := (@mk _ "Echo" unit (list Z) unit (fun _ _ _ o _ => o = ord_top) (top4)). *)
  (* Let echo_finish_spec: fspec := (@mk _ "Echo" unit (list Z) unit (fun _ _ _ o _ => o = ord_top) (top4)). *)
  Let echo_spec:        fspec := (mk_simple "Echo" (X:=unit) (fun _ _ o _ => o = ord_top) (top3)).
  Let echo_finish_spec: fspec := (mk_simple "Echo" (X:=unit) (fun _ _ o _ => o = ord_top) (top3)).

  Definition EchoStb: list (gname * fspec) :=
    [("echo", echo_spec) ; ("echo_finish", echo_finish_spec)]
  .

  Definition EchoSbtb: list (gname * fspecbody) :=
    [("echo", mk_specbody echo_spec echoF); ("echo_finish", mk_specbody echo_finish_spec echo_finishF)]
  .

  Definition EchoSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fsb) => (fn, fun_to_tgt (LinkedListStb ++ EchoStb) fn fsb)) EchoSbtb;
    ModSem.initial_mrs := [("Echo", (ε, ([]: list Z)↑))];
  |}
  .

  Definition Echo: Mod.t := {|
    Mod.get_modsem := fun _ => EchoSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
