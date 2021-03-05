Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Stack1 Client1 Echo1.
Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.




Section PROOF.

  Context {Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ}.

  Definition is_minus_one (v: val): bool :=
    match v with
    | Vint i => dec i (- 1)%Z
    | _ => false
    end
  .

  Definition echo_body: list Z -> itree (hCallE +' pE +' eventE) unit :=
    fun ns =>
      n <- trigger (hCall false "in" ([]: list val)↑);;
      `n: val <- n↓?;; `n: Z <- (unint n)?;;
      if dec n (- 1)%Z
      then trigger (hCall false "echo_finish" ns↑);; Ret tt
      else
        trigger (hCall false "echo" (n :: ns)↑);;
        Ret tt
  .

  Definition echo_finish_body: list Z -> itree (hCallE +' pE +' eventE) unit :=
    fun ns =>
      match ns with
      | [] => Ret tt
      | hd :: tl =>
        trigger (hCall false "out" [Vint hd]↑);;
        trigger (hCall false "echo_finish" tl↑);;
        Ret tt
      end
  .

  Let echo_spec:        fspec := (@mk _ "Echo" (list Z) (list Z) unit
                                      (top5) (top4)).
  Let echo_finish_spec: fspec := (@mk _ "Echo" (list Z) (list Z) unit
                                      (top5) (top4)).

  Definition EchoStb: list (gname * fspec) :=
    [("echo", echo_spec) ; ("echo_finish", echo_finish_spec)]
  .

  Definition EchoSbtb: list (gname * fspecbody) :=
    [("echo", mk_specbody echo_spec echo_body); ("echo_finish", mk_specbody echo_finish_spec echo_finish_body)]
  .

  Definition EchoSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fsb) => (fn, fun_to_tgt (StackStb ++ ClientStb ++ EchoStb) fn fsb)) EchoSbtb;
    ModSem.initial_mrs := [("Echo", (ε, tt↑))];
  |}
  .

  Definition Echo: Mod.t := {|
    Mod.get_modsem := fun _ => EchoSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.

(* Section ECHO. *)
(*   Context {Σ: GRA.t}. *)

(*   Definition echo_body: list Z -> itree Es unit := *)
(*     fun ns => *)
(*       `n: val <- ccall "in" ([]: list val);; `n: Z <- (unint n)?;; *)
(*       if dec n (- 1)%Z *)
(*       then `_: unit <- ccall "echo_finish" ns;; Ret tt *)
(*       else *)
(*         `_: unit <- ccall "echo" (n :: ns);; *)
(*         Ret tt *)
(*   . *)

(*   Definition echo_finish_body: list Z -> itree Es unit := *)
(*     fun ns => *)
(*       match ns with *)
(*       | [] => Ret tt *)
(*       | hd :: tl => *)
(*         `_: val <- ccall "out" [Vint hd];; *)
(*         `_: unit <- ccall "echo_finish" tl;; *)
(*         Ret tt *)
(*       end. *)

(*   Definition EchoSem: ModSem.t := {| *)
(*     ModSem.fnsems := [("echo", cfun echo_body); ("echo_finish", cfun echo_finish_body)]; *)
(*     ModSem.initial_mrs := [("Echo", (ε, tt↑))]; *)
(*   |} *)
(*   . *)

(*   Definition Echo: Mod.t := {| *)
(*     Mod.get_modsem := fun _ => EchoSem; *)
(*     Mod.sk := Sk.unit; *)
(*   |} *)
(*   . *)
(* End ECHO. *)
