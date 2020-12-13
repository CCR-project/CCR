Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Require Import Mem1.



Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  (***
        void* x = malloc(1);
        *x = 42;
        unknown_call(x);
        y = *x;
        return y; ~~~> return 42;
   ***)
  Definition mainF: list val -> itree Es val :=
    fun _ =>
      x <- (HoareCall "Main"
                      (fun varg _ => exists sz, varg = [Vint (Z.of_nat sz)])
                      (fun varg _ vret rret =>
                         exists sz, varg = [Vint (Z.of_nat sz)] /\
                         exists b, vret = Vptr b 0 /\
                                   rret = GRA.padding (fold_left URA.add (mapi (fun n _ => (b, Z.of_nat n) |-> (Vint 0))
                                                                               (List.repeat tt sz)) URA.unit))
                 "alloc" [Vint 1]);;
      (HoareCall "Main"
                 (fun varg rarg => exists b ofs v_new, varg = [Vptr b ofs ; v_new] /\
                    exists v_old, rarg = (GRA.padding ((b, ofs) |-> v_old)))
                 (fun varg rarg _ rret =>
                    exists b ofs v_new, varg = [Vptr b ofs ; v_new] /\
                    exists v_old, rarg = (GRA.padding ((b, ofs) |-> v_old)) /\
                    rret = (GRA.padding ((b, ofs) |-> v_new)))
                 "store" [x ; Vint 42]);;
      trigger (Call "unknown_call" [x]);;
      y <- (HoareCall "Main"
                      (fun varg rarg => exists b ofs, varg = [Vptr b ofs] /\
                         exists v, rarg = (GRA.padding ((b, ofs) |-> v)))
                      (fun varg rarg vret rret =>
                         exists b ofs, varg = [Vptr b ofs] /\
                         exists v, rarg = (GRA.padding ((b, ofs) |-> v)) /\
                         rret = (GRA.padding ((b, ofs) |-> v)) /\ vret = v)
                      "load" [x]);;
      Ret (Vint 42)
  .

End PROOF.
