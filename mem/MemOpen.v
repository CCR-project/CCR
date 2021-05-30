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
Require Import TODO.
Require Import Mem0 Mem1.
Require Import OpenDef Open.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.





Let _memRA: URA.t := (block ==> Z ==> (Excl.t val))%ra.


Section AUX.
  Context `{Σ: GRA.t}.
  Definition mk_ksimple {X: Type} (PQ: X -> ((Any.t -> ord -> Σ -> Prop) * (Any.t -> Σ -> Prop))):
    ftspec unit unit := @mk_ftspec _ _ _ X (fun x _ a o => (fst ∘ PQ) x a o) (fun x _ a => (snd ∘ PQ) x a)
  .
End AUX.



Section PROOF.
  Context `{@GRA.inG memRA Σ}.

  Definition alloc_spec: ftspec unit unit :=
    (mk_ksimple (fun sz => (
                     (fun varg o => ⌜varg = [Vint (Z.of_nat sz)]↑ /\ o = ord_pure 0⌝),
                     (fun vret => Exists b, ⌜vret = (Vptr b 0)↑⌝ **
                                            Own(GRA.embed ((b, 0%Z) |-> (List.repeat (Vint 0) sz))))
    ))).

  Definition free_spec: ftspec unit unit :=
    (mk_ksimple (fun '(b, ofs) => (
                     (fun varg o => Exists v, ⌜varg = ([Vptr b ofs])↑⌝ **
                                              Own(GRA.embed ((b, ofs) |-> [v])) **
                                              ⌜o = ord_pure 0⌝),
                     top2
    ))).

  Definition load_spec: ftspec unit unit :=
    (mk_ksimple (fun '(b, ofs, v) => (
                     (fun varg o => ⌜varg = ([Vptr b ofs])↑⌝ **
                                    Own(GRA.embed ((b, ofs) |-> [v])) **
                                    ⌜o = ord_pure 0⌝),
                     (fun vret => Own(GRA.embed ((b, ofs) |-> [v])) ** ⌜vret = v↑⌝)
    ))).

  Definition store_spec: ftspec unit unit :=
    (mk_ksimple
       (fun '(b, ofs, v_new) => (
            (fun varg o => Exists v_old,
                           ⌜varg = ([Vptr b ofs ; v_new])↑⌝ ** Own(GRA.embed ((b, ofs) |-> [v_old])) ** ⌜o = ord_pure 0⌝),
            (fun _ => Own(GRA.embed ((b, ofs) |-> [v_new])))
    ))).

  Definition cmp_spec: ftspec unit unit :=
    (mk_ksimple
       (fun '(result, resource) => (
          (fun varg o =>
          ((Exists b ofs v, ⌜varg = [Vptr b ofs; Vnullptr]↑⌝ ** ⌜resource = (GRA.embed ((b, ofs) |-> [v]))⌝ ** ⌜result = false⌝) ∨
           (Exists b ofs v, ⌜varg = [Vnullptr; Vptr b ofs]↑⌝ ** ⌜resource = (GRA.embed ((b, ofs) |-> [v]))⌝ ** ⌜result = false⌝) ∨
           (Exists b0 ofs0 v0 b1 ofs1 v1, ⌜varg = [Vptr b0 ofs0; Vptr b1 ofs1]↑⌝ **
                     ⌜resource = (GRA.embed ((b0, ofs0) |-> [v0])) ⋅ (GRA.embed ((b1, ofs1) |-> [v1]))⌝ ** ⌜result = false⌝) ∨
           (Exists b ofs v, ⌜varg = [Vptr b ofs; Vptr b  ofs]↑⌝ ** ⌜resource = (GRA.embed ((b, ofs) |-> [v]))⌝ ** ⌜result = true⌝) ∨
           (⌜varg = [Vnullptr; Vnullptr]↑ /\ result = true⌝))
            ** Own(resource)
            ** ⌜o = ord_pure 0⌝
          ),
          (fun vret => Own(resource) ** ⌜vret = (if result then Vint 1 else Vint 0)↑⌝)
    ))).

End PROOF.



Section PROOF.
  Context `{@GRA.inG memRA Σ}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.

  Definition MemSbtb: list (gname * kspecbody) :=
    [("alloc", mk_kspecbody alloc_spec allocF);
    ("free",   mk_kspecbody free_spec freeF);
    ("load",   mk_kspecbody load_spec loadF);
    ("store",  mk_kspecbody store_spec storeF);
    ("cmp",    mk_kspecbody cmp_spec cmpF)
    ]
  .

  Definition KMemSem (sk: Sk.t): KModSem.t := {|
    KModSem.fnsems := MemSbtb;
    KModSem.mn := "Mem";
    KModSem.initial_mr := (GRA.embed (Auth.black (M:=_memRA) ε));
    KModSem.initial_st := (Sk.load_mem sk)↑;
  |}
  .

  Definition SMemSem: Sk.t -> SModSem.t := (KModSem.to_tgt) ∘ KMemSem.

  Definition MemSem: Sk.t -> ModSem.t := (SModSem.to_tgt []) ∘ SMemSem.

  Definition KMem: KMod.t := {|
    KMod.get_modsem := KMemSem;
    KMod.sk := Sk.unit;
  |}
  .

  Definition SMem: SMod.t := (KMod.to_tgt) KMem.

  Definition Mem: Mod.t := SMod.to_tgt (fun _ => []) SMem.

End PROOF.
Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
