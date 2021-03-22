Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic.
Require Import Mem1.
Require Import Logic.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.
  Context `{@GRA.inG memRA Σ}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.

  Let alloc_spec: fspec := (mk_simple "Mem"
                                      (fun sz varg o => ⌜varg = [Vint (Z.of_nat sz)]↑ /\ o = ord_pure 1⌝)
                                      (fun sz vret => Exists b, ⌜vret = (Vptr b 0)↑⌝ **
                                                   Own(GRA.embed ((b, 0%Z) |-> (List.repeat (Vint 0) sz))))).

  Let free_spec: fspec := (mk_simple "Mem"
                                     (fun '(b, ofs) varg o => Exists v, ⌜varg = ([Vptr b ofs])↑⌝ **
                                                                        Own(GRA.embed ((b, ofs) |-> [v])) **
                                                                        ⌜o = ord_pure 1⌝)
                                     (top3)).

  Let load_spec: fspec := (mk_simple "Mem"
                                     (fun '(b, ofs, v) varg o => ⌜varg = ([Vptr b ofs])↑⌝ **
                                                                      Own(GRA.embed ((b, ofs) |-> [v])) **
                                                                      ⌜o = ord_pure 1⌝)
                                     (fun '(b, ofs, v) vret => Own(GRA.embed ((b, ofs) |-> [v])) ** ⌜vret = v↑⌝)).

  Let store_spec: fspec := (mk_simple
                              "Mem"
                              (fun '(b, ofs, v_new) varg o => Exists v_old,
                                   ⌜varg = ([Vptr b ofs ; v_new])↑⌝ ** Own(GRA.embed ((b, ofs) |-> [v_old])) ** ⌜o = ord_pure 1⌝)
                              (fun '(b, ofs, v_new) _ => Own(GRA.embed ((b, ofs) |-> [v_new])))).

  Let cmp_spec: fspec :=
    (mk_simple
       "Mem"
       (fun '(result, resource) varg o =>
          ((Exists b ofs v, ⌜varg = [Vptr b ofs; Vnullptr]↑⌝ ** ⌜resource = (GRA.embed ((b, ofs) |-> [v]))⌝ ** ⌜result = false⌝) ∨
           (Exists b ofs v, ⌜varg = [Vnullptr; Vptr b ofs]↑⌝ ** ⌜resource = (GRA.embed ((b, ofs) |-> [v]))⌝ ** ⌜result = false⌝) ∨
           (Exists b0 ofs0 v0 b1 ofs1 v1, ⌜varg = [Vptr b0 ofs0; Vptr b1 ofs1]↑⌝ **
                     ⌜resource = (GRA.embed ((b0, ofs0) |-> [v0])) ⋅ (GRA.embed ((b1, ofs1) |-> [v1]))⌝ ** ⌜result = false⌝) ∨
           (Exists b ofs v, ⌜varg = [Vptr b ofs; Vptr b  ofs]↑⌝ ** ⌜resource = (GRA.embed ((b, ofs) |-> [v]))⌝ ** ⌜result = true⌝) ∨
           (⌜varg = [Vnullptr; Vnullptr]↑ /\ result = true⌝))
            ** Own(resource)
            ** ⌜o = ord_pure 1⌝
       )
       (fun '(result, resource) vret => Own(resource) ** ⌜vret = (if result then Vint 1 else Vint 0)↑⌝)
    ).

  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("alloc", alloc_spec) ; ("free", free_spec) ; ("load", load_spec) ; ("store", store_spec) ; ("cmp", cmp_spec)].
  Defined.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("alloc", mk_specbody alloc_spec (fun _ => trigger (Choose _)));
    ("free",   mk_specbody free_spec (fun _ => trigger (Choose _)));
    ("load",   mk_specbody load_spec (fun _ => trigger (Choose _)));
    ("store",  mk_specbody store_spec (fun _ => trigger (Choose _)));
    ("cmp",    mk_specbody cmp_spec (fun _ => trigger (Choose _)))
    ]
  .

  Definition MemSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fsb) => (fn, fun_to_tgt MemStb fn fsb)) MemSbtb;
    ModSem.initial_mrs :=
      [("Mem", (GRA.embed (URA.black (M:=Mem1._memRA) ε), tt↑))];
  |}
  .

  Definition Mem: Mod.t := {|
    Mod.get_modsem := fun _ => MemSem; (*** TODO: we need proper handling of function pointers ***)
    Mod.sk := List.map (fun '(n, _) => (n, Sk.Gfun)) MemStb;
  |}
  .

End PROOF.
Global Hint Unfold MemStb: stb.
