Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.
  (* Context `{@GRA.inG memRA Σ}. *)

  (***
        void* x = malloc(1);
        *x = 42;
        unknown_call(); // may GUESS the location &x and change the contents
        y = *x;
        return y;
   ***)
  Definition clientF: Any.t -> itree Es Any.t :=
    fun _ =>
      (* x <- ((↓) <$> trigger (Call "alloc" [Vint 1]↑)) >>= (ǃ);; *)
      x <- trigger (Call "alloc" [Vint 1]↑);;
      `x: val <- x↓ǃ;;
      trigger (Call "store" [x ; Vint 42]↑);;;
      trigger (Call "unknown_call" ([]: list val)↑);;;
      (* `y: val <- ((↓) <$> trigger (Call "load" [x]↑)) >>= (ǃ);; *)
      y <- trigger (Call "load" [x]↑);;
      `y: val <- y↓ǃ;;
      Ret y↑
  .

  Definition ClientSem: ModSem.t := {|
    ModSem.fnsems := [("client", clientF)];
    ModSem.mn := "Client";
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}
  .

  Definition Client: Mod.t := {|
    Mod.get_modsem := fun _ => ClientSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
