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






Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  Definition is_minus_one (v: val): bool :=
    match v with
    | Vint i => dec i (- 1)%Z
    | _ => false
    end
  .

  Definition echoF: list Z -> itree (hCallE +' pE +' eventE) unit :=
    fun ns =>
      n <- trigger (hCall false "in" ([]: list val)↑);;
      `n: val <- n↓?;; `n: Z <- (unint n)?;;
      if dec n (- 1)%Z
      then trigger (hCall false "echo_finish" ns↑);; Ret tt
      else
        APC;;
        trigger (hCall false "echo" (n :: ns)↑);;
        Ret tt
  .

  Definition echo_finishF: list Z -> itree (hCallE +' pE +' eventE) unit :=
    fun ns =>
      match ns with
      | [] => Ret tt
      | hd :: tl =>
        APC;;
        trigger (hCall false "out" [Vint hd]↑);;
        trigger (hCall false "echo_finish" tl↑);;
        Ret tt
      end
  .

  (* Definition echoF: list val -> itree Es val := *)
  (*   fun _ => *)
  (*     `n: val <- (ccall "in" ([]: list val));; *)
  (*     `n: Z   <- (unint n)?;; *)
  (*     if dec n (- 1)%Z *)
  (*     then `_: val <- (ccall "echo_finish"  ([]: list val));; Ret Vundef *)
  (*     else *)
  (*       ll0 <- trigger (PGet "Echo");; *)
  (*       `ll0: list Z <- ll0↓?;; *)
  (*       let ll1 := (n :: ll0) in *)
  (*       trigger(PPut "Echo" ll1↑);; *)
  (*       `_: val <- ccall "echo" ([]: list val);; *)
  (*       Ret Vundef *)
  (* . *)

  (* Definition echo_finishF: list val -> itree Es val := *)
  (*   fun _ => *)
  (*     ll0 <- trigger (PGet "Echo");; `ll0: list Z <- ll0↓?;; *)
  (*     match ll0 with *)
  (*     | [] => Ret Vundef *)
  (*     | hd :: tl => *)
  (*       `_: val        <- (ccall "out" ([hd]));; *)
  (*       trigger (PPut "Echo" tl↑);; *)
  (*       `_: val        <- (ccall "echo_finish" ([]: list val));; *)
  (*       Ret Vundef *)
  (*     end *)
  (* . *)

  Let echo_spec:        fspec := (@mk _ "Echo" unit (list Z) unit (top5) (top4)).
  Let echo_finish_spec: fspec := (@mk _ "Echo" unit (list Z) unit (top5) (top4)).

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
