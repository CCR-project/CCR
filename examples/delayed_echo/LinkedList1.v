Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Mem1 Mem2.
Require Import TODOYJ.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.





Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Fixpoint is_list (ll: val) (xs: list val): iProp :=
    match xs with
    | [] => ⌜ll = Vnullptr⌝
    | xhd :: xtl =>
      Exists lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (Own (GRA.padding ((lhd,0%Z) |-> [xhd; ltl])))
                                 ** is_list ltl xtl
    end
  .

  Let pop_spec: fspec := (mk_simple "LinkedList"
                                    (fun '(llref, xs) varg o =>
                                       Exists ll, ⌜varg = [Vptr llref 0%Z]↑⌝ ** Own (GRA.padding ((llref,0%Z) |-> [ll])) ** (is_list ll xs) ** ⌜o = ord_pure 2⌝)
                                    (fun '(llref, xs) vret =>
                                       match xs with
                                       | [] => ⌜vret = (Vint (- 1))↑⌝
                                       | xhd :: xtl => ⌜vret = xhd↑⌝ ** (Exists ll', Own (GRA.padding ((llref,0%Z) |-> [ll'])) ** is_list ll' xtl)
                                       end)
                         ).

  Let pop2_spec: fspec := (mk_simple "LinkedList"
                                     (fun '(xs, nref) varg o => Exists ll, ⌜varg = [ll; Vptr nref 0%Z]↑⌝ ** (is_list ll xs) **
                                                                           (Exists v, Own (GRA.padding ((nref, 0%Z) |-> [v]))) ** ⌜o = ord_pure 2⌝)
                                     (fun '(xs, nref) vret =>
                                        match xs with
                                        | [] => ⌜vret = Vnullptr↑⌝
                                        | xhd :: xtl => Exists ll', ⌜vret = ll'↑⌝ ** is_list ll' xtl ** Own (GRA.padding ((nref, 0%Z) |-> [xhd]))
                                        end)
                          ).

(* struct Node* pop2(struct Node* ll, int *n) { *)
(*   if(ll) { *)
(*     int v = (ll)->val; *)
(*     struct Node* next = (ll)->next; *)
(*     free(ll); *)
(*     *n = v; *)
(*     return next; *)
(*   } *)
(*   return NULL; *)
(* } *)

  Let push_spec: fspec := (mk_simple "LinkedList"
                                     (fun '(x, xs) varg o => Exists ll, ⌜varg = [ll; x]↑⌝ ** is_list ll xs ** ⌜o = ord_pure 2⌝)
                                     (fun '(x, xs) vret => Exists ll', is_list ll' (x :: xs) ** ⌜vret = ll'↑⌝)).

  Definition LinkedListStb: list (gname * fspec) :=
    [("pop", pop_spec) ; ("pop2", pop2_spec) ; ("push", push_spec)]
  .

  Definition LinkedListSbtb: list (gname * fspecbody) :=
    [("pop", mk_specbody pop_spec (fun _ => APC;; trigger (Choose _)));
    ("pop2", mk_specbody pop2_spec (fun _ => APC;; trigger (Choose _)));
    ("push",   mk_specbody push_spec (fun _ => APC;; trigger (Choose _)))
    ]
  .

  Definition LinkedListSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, fsb) => (fn, fun_to_tgt (MemStb ++ LinkedListStb) fn fsb)) LinkedListSbtb;
    ModSem.initial_mrs := [("LinkedList", (ε, tt↑))];
  |}
  .

  Definition LinkedList: Mod.t := {|
    Mod.get_modsem := fun _ => LinkedListSem;
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
