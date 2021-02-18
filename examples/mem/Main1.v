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


(* Notation "'hCall2' fn varg" := *)
(*   (marg <- trigger (Choose _);; vret <- trigger (hCall fn marg varg);; vret <- vret↓?;; Ret vret) *)
(*     (at level 60). *)
(* Definition hCall' {X} (fn: string) (varg: Any.t): itree (hCallE +' eventE) X := *)
(*   marg <- trigger (Choose _);; vret <- trigger (hCall fn marg varg);; vret <- vret↓?;; Ret vret *)
(* . *)
  (* marg <- trigger (Choose _);; trigger (hCall fn marg varg) >>= ((?) <*> (↓)) *)

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

  Definition mainBody: Any.t -> itree (hCallE +' pE +' eventE) Any.t :=
    fun _ =>
      x <- trigger (hCall "alloc" [Vint 1]↑);; x <- x↓?;;
      trigger (hCall "store" [x ; Vint 42]↑);;
      (* trigger (Call "unknown_call" [x]);; *)
      trigger (hCall "load" [x]↑);;
      Ret (Vint 42)↑
  .

  (*** main's view on stb ***)
  Definition MainStb: list (gname * fspec) :=
    [("main", mk "Main" (X:=unit) (fun _ varg_high varg_low _ => varg_high = varg_low) (fun _ vret_high vret_low _ => vret_high = vret_low) (fun _ => None))].
  Definition MemStb: list (gname * fspec) :=
  [("alloc", mk "Mem"
               (fun sz _ varg _ => varg = [Vint (Z.of_nat sz)]↑)
               (fun sz _ vret rret =>
                  exists b, vret = (Vptr b 0)↑ /\
                            rret = GRA.padding (fold_left URA.add
                                                          (mapi (fun n _ => (b, Z.of_nat n) |-> (Vint 0))
                                                                (List.repeat tt sz)) URA.unit))
               (fun _ => None)) ;
  ("free", mk "Mem"
              (fun '(b, ofs, v) _ varg rarg => varg = [Vptr b ofs]↑ /\
                                             rarg = (GRA.padding ((b, ofs) |-> v)))
              (top4)
              (fun _ => None)) ;
  ("load", mk "Mem"
              (fun '(b, ofs, v) _ varg rarg => varg = [Vptr b ofs]↑ /\
                                             rarg = (GRA.padding ((b, ofs) |-> v)))
              (fun '(b, ofs, v) _ vret rret => rret = (GRA.padding ((b, ofs) |-> v)) /\ vret = v↑)
              (fun _ => None)) ;
  ("store", mk "Mem"
               (fun '(b, ofs, v_old, v_new) _ varg rarg =>
                  varg = [Vptr b ofs ; v_new]↑ /\ rarg = (GRA.padding ((b, ofs) |-> v_old)))
               (fun '(b, ofs, v_old, v_new) _ _ rret => rret = (GRA.padding ((b, ofs) |-> v_new)))
               (fun _ => None))
  ]
  .

  Definition MainFtb := zip pair [("main")] [mainBody].

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
    (* ModSem.fnsems := List.map (map_snd (fun_to_tgt (MainStb ++ MemStb))) MainStb; *)
    ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt (MainStb ++ MemStb) fn body)) MainFtb;
    ModSem.initial_mrs := [("Main", (ε, unit↑))];
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    Mod.sk := List.map (fun '(n, _) => (n, Sk.Gfun)) MainStb;
  |}
  .

End PROOF.
