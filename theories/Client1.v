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
  Definition mainBody: list val -> itree (hCallE +' eventE) val :=
    fun _ =>
      x <- trigger (hCall "alloc" [Vint 1]);;
      trigger (hCall "store" [x ; Vint 42]);;
      (* trigger (Call "unknown_call" [x]);; *)
      trigger (hCall "load" [x]);;
      Ret (Vint 42)
  .

  (*** main's view on stb ***)
  Definition MainStb: list (fname * funspec) := [("main", mk "Main" (X:=unit) top3 top3 mainBody)].
  Definition MemStb: list (fname * funspec) :=
  [("alloc", mk "Mem"
               (fun sz varg _ => varg = [Vint (Z.of_nat sz)])
               (fun sz vret rret =>
                  exists b, vret = Vptr b 0 /\
                            rret = GRA.padding (fold_left URA.add
                                                          (mapi (fun n _ => (b, Z.of_nat n) |-> (Vint 0))
                                                                (List.repeat tt sz)) URA.unit))
               (fun _ => trigger (Choose _))) ;
  ("free", mk "Mem"
              (fun '(b, ofs, v) varg rarg => varg = [Vptr b ofs] /\
                                             rarg = (GRA.padding ((b, ofs) |-> v)))
              (top3)
              (fun _ => trigger (Choose _))) ;
  ("load", mk "Mem"
              (fun '(b, ofs, v) varg rarg => varg = [Vptr b ofs] /\
                                             rarg = (GRA.padding ((b, ofs) |-> v)))
              (fun '(b, ofs, v) vret rret => rret = (GRA.padding ((b, ofs) |-> v)) /\ vret = v)
              (fun _ => trigger (Choose _))) ;
  ("store", mk "Mem"
               (fun '(b, ofs, v_old, v_new) varg rarg =>
                  varg = [Vptr b ofs ; v_new] /\ rarg = (GRA.padding ((b, ofs) |-> v_old)))
               (fun '(b, ofs, v_old, v_new) _ rret => rret = (GRA.padding ((b, ofs) |-> v_new)))
               (fun _ => trigger (Choose _)))
  ]
  .

  Definition mainF: list val -> itree Es val :=
    HoareFun "Main" (X:=unit) top3 top3 (body_to_tgt MainStb mainBody)
  .

  (***
Possible improvements:
(1) "exists b" in "alloc"
      --> it would be better if we can just use "b" in the remaning of the code.
(2) (fun x varg rarg => k x)
      --> We know what "x" will be, so why not just write "(fun varg rarg => k x)"?.
          In other words, the "Choose" in the code is choosing "x", but we want to choose "x" when writing the spec.
   ***)

  Definition MainSem: ModSem.t := {|
    (* ModSem.fnsems := [("main", mainF)]; *)
    ModSem.fnsems := List.map (map_snd (fun_to_tgt (MainStb ++ MemStb))) MainStb;
    ModSem.initial_mrs := [("Main", ε)];
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := List.map fst MainStb;
  |}
  .

End PROOF.
