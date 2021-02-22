Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import Mem1.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.





Section PROOF.
  Context {Σ: GRA.t}.
  (*** TODO: move to proper place, together with "mk_simple" ***)
  (*** TODO: rename sb into spb ***)
  (*** TODO: remove redundancy with Hoareproof0.v ***)
  Definition mk_simple (mn: string) {X: Type} (P: X -> Any.t -> ord -> Σ -> Prop) (Q: X -> Any.t -> Σ -> Prop): fspec :=
    @mk _ mn X (list val) (val) (fun x y a r o => P x a o r /\ y↑ = a) (fun x z a r => Q x a r /\ z↑ = a)
  .
  Definition mk_sb_simple (mn: string) {X: Type} (P: X -> Any.t -> ord -> Σ -> Prop) (Q: X -> Any.t -> Σ -> Prop)
             (body: list val -> itree (hCallE +' pE +' eventE) val): fspecbody := mk_specbody (mk_simple mn P Q) body.

End PROOF.






Section IRIS.
  Context {Σ: GRA.t}.
  Definition iProp := Σ -> Prop.
  Definition Sepconj (P Q: iProp): iProp :=
    fun r => exists a b, r = URA.add a b /\ P a /\ Q b
  .
  Definition Pure (P: Prop): iProp := fun _ => P.
  Definition Ex {X: Type} (P: X -> iProp): iProp := fun r => exists x, P x r.
  Definition Own (r0: Σ): iProp := fun r1 => URA.extends r0 r1.

End IRIS.

Infix "**" := Sepconj (at level 60).
Notation "'⌜' P '⌝'" := (Pure P).
Notation "'Exists' x .. y , p" := (Ex (fun x => .. (Ex (fun y => p)) ..))
                                    (at level 200, x binder, right associativity,
                                     format "'[' 'Exists'  '/  ' x  ..  y ,  '/  ' p ']'").






Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Fixpoint is_list (ll: val) (xs: list nat): iProp :=
    match xs with
    | [] => ⌜ll = Vnullptr⌝
    | xhd :: xtl =>
      Exists lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (Own (GRA.padding ((lhd,0%Z) |-> Vint (Z.of_nat xhd))))
                                 ** (Own (GRA.padding ((lhd,1%Z) |-> ltl))) ** is_list ltl xtl
    end
  .

  Let pop_spec: fspec := (mk_simple "LinkedList"
                                    (fun '(llref, xs) varg o =>
                                       Exists ll, ⌜varg = [llref]↑⌝ ** Own (GRA.padding ((llref,0%Z) |-> ll)) ** (is_list ll xs) ** ⌜o = ord_pure 42⌝)
                                    (fun '(llref, xs) vret =>
                                       match xs with
                                       | [] => ⌜vret = (Vint (- 1))↑⌝
                                       | xhd :: xtl => ⌜vret = (Vint (Z.of_nat xhd))↑⌝ ** (Exists ll', Own (GRA.padding ((llref,0%Z) |-> ll')) ** is_list ll' xtl)
                                       end)
                         ).

  Let push_spec: fspec := (mk_simple "LinkedList"
                                     (fun '(x, xs) varg o => Exists ll, ⌜varg = [ll; Vint (Z.of_nat x)]↑⌝ ** is_list ll xs ** ⌜o = ord_pure 42⌝)
                                     (fun '(x, xs) vret => Exists ll', is_list ll' (x :: xs) ** ⌜vret = ll'↑⌝)).

  Definition LinkedListStb: list (gname * fspec) :=
    [("pop", pop_spec) ; ("push", push_spec)]
  .

  Definition LinkedListSbtb: list (gname * fspecbody) :=
    [("pop", mk_specbody pop_spec (fun _ => APC;; trigger (Choose _)));
    ("push",   mk_specbody push_spec (fun _ => APC;; trigger (Choose _)))
    ]
  .

  Definition LinkedListSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fsb) => (fn, fun_to_tgt MemStb fn fsb)) MemSbtb;
    ModSem.initial_mrs := [("LinkedList", (ε, unit↑))];
  |}
  .

  Definition LinkedList: Mod.t := {|
    Mod.get_modsem := fun _ => LinkedListSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
