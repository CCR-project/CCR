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
                      (fun sz varg _ => varg = [Vint (Z.of_nat sz)])
                      (fun sz vret rret =>
                         exists b, vret = Vptr b 0 /\
                         rret = GRA.padding (fold_left URA.add (mapi
                                  (fun n _ => (b, Z.of_nat n) |-> (Vint 0)) (List.repeat tt sz))
                                                       URA.unit))
                 "alloc" [Vint 1]);;
      (HoareCall "Main"
                 (fun '(b, ofs, v_old, v_new) varg rarg =>
                    varg = [Vptr b ofs ; v_new] /\ rarg = (GRA.padding ((b, ofs) |-> v_old)))
                 (fun '(b, ofs, v_old, v_new) _ rret => rret = (GRA.padding ((b, ofs) |-> v_new)))
                 "store" [x ; Vint 42]);;
      trigger (Call "unknown_call" [x]);;
      (HoareCall "Main"
                 (fun '(b, ofs, v) varg rarg => varg = [Vptr b ofs] /\
                                                rarg = (GRA.padding ((b, ofs) |-> v)))
                 (fun '(b, ofs, v) vret rret =>
                    rret = (GRA.padding ((b, ofs) |-> v)) /\ vret = v)
                 "load" [x]);;
      Ret (Vint 42)
  .
  (***
Possible improvements:
(1) "exists b" in "alloc"
      --> it would be better if we can just use "b" in the remaning of the code.
(2) (fun x varg rarg => k x)
      --> We know what "x" will be, so why not just write "(fun varg rarg => k x)"?.
          In other words, the "Choose" in the code is choosing "x", but we want to choose "x" when writing the spec.
   ***)

End PROOF.
