Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import TODOYJ.
Require Import Logic.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Definition knotRA: URA.t := Auth.t (Excl.t (option (nat -> nat))).
Definition knot_full (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.black (M:=(Excl.t _)) (Some f).
Definition knot_frag (f: option (nat -> nat)) : (@URA.car knotRA) := Auth.white (M:=(Excl.t _)) (Some f).


Section HEADER.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG knotRA Σ}.

  Definition rec_spec:    fspec := mk_simple (X:=(nat -> nat) * nat)
                                             (fun '(f, n) => (
                                                  (fun varg o => Own (GRA.embed (knot_frag (Some f))) ** ⌜varg = [Vint (Z.of_nat n)]↑ /\ o = ord_pure (2 * n + 1)⌝),
                                                  (fun vret => Own (GRA.embed (knot_frag (Some f))) ** ⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                                             )).

  Variable RecStb: SkEnv.t -> list (gname * fspec).

  Section SKENV.
    Variable skenv: SkEnv.t.

    Definition fun_gen (f: nat -> nat): ftspec (list val) (val) :=
      mk_simple (X:=nat)
                (fun n => (
                     (fun varg o =>
                        ⌜exists fb fn,
                            varg = [Vptr fb 0; Vint (Z.of_nat n)]↑ /\ o = ord_pure (2 * n) /\
                            skenv.(SkEnv.blk2id) fb = Some fn /\
                            List.find (fun '(_fn, _) => dec fn _fn) (RecStb skenv) = Some (fn, rec_spec)⌝ ** Own (GRA.embed (knot_frag (Some f)))),
                     (fun vret => ⌜vret = (Vint (Z.of_nat (f n)))↑⌝ ** Own (GRA.embed (knot_frag (Some f))))
                )).
  End SKENV.

End HEADER.
