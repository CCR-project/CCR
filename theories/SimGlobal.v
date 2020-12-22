Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.


Section SIM.

Context `{Σ: GRA.t}.

Variable idx: Type.
Variable ord: idx -> idx -> Prop.
Hypothesis wf_ord: well_founded ord.

Section TY.
Context `{R: Type}.
Inductive _simg (simg: idx -> relation (itree eventE R)) (i0: idx): relation (itree eventE R) :=
| simg_ret
    r
  :
    _simg simg i0 (Ret r) (Ret r)
| simg_syscall
    i1 ktr_src0 ktr_tgt0 fn m0 varg
    (SIM: (eq ==> simg i1)%signature ktr_src0 ktr_tgt0)
  :
    _simg simg i0 (trigger (Syscall fn m0 varg) >>= ktr_src0) (trigger (Syscall fn m0 varg) >>= ktr_tgt0)



| simg_tau
    i1 itr_src0 itr_tgt0
    (SIM: simg i1 itr_src0 itr_tgt0)
  :
    _simg simg i0 (tau;; itr_src0) (tau;; itr_tgt0)
| simg_tauL
    i1 itr_src0 itr_tgt0
    (ORD: ord i1 i0)
    (SIM: simg i1 itr_src0 itr_tgt0)
  :
    _simg simg i0 (tau;; itr_src0) (itr_tgt0)
| simg_tauR
    i1 itr_src0 itr_tgt0
    (ORD: ord i1 i0)
    (SIM: simg i1 itr_src0 itr_tgt0)
  :
    _simg simg i0 (itr_src0) (tau;; itr_tgt0)



| simg_choose
    i1 X_src X_tgt ktr_src0 ktr_tgt0
    (SIM: forall x_tgt, exists x_src, simg i1 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg i0 (trigger (Choose X_src) >>= ktr_src0) (trigger (Choose X_tgt) >>= ktr_tgt0)
| simg_chooseL
    i1 X ktr_src0 itr_tgt0
    (ORD: ord i1 i0)
    (SIM: exists x, simg i1 (ktr_src0 x) itr_tgt0)
  :
    _simg simg i0 (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
| simg_chooseR
    i1 X itr_src0 ktr_tgt0
    (ORD: ord i1 i0)
    (SIM: forall x, simg i1 itr_src0 (ktr_tgt0 x))
  :
    _simg simg i0 (itr_src0) (trigger (Choose X) >>= ktr_tgt0)



| simg_take
    i1 X_src X_tgt ktr_src0 ktr_tgt0
    (SIM: forall x_src, exists x_tgt, simg i1 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg i0 (trigger (Take X_src) >>= ktr_src0) (trigger (Take X_tgt) >>= ktr_tgt0)
| simg_takeL
    i1 X ktr_src0 itr_tgt0
    (ORD: ord i1 i0)
    (SIM: forall x, simg i1 (ktr_src0 x) itr_tgt0)
  :
    _simg simg i0 (trigger (Take X) >>= ktr_src0) (itr_tgt0)
| simg_takeR
    i1 X itr_src0 ktr_tgt0
    (ORD: ord i1 i0)
    (SIM: exists x, simg i1 itr_src0 (ktr_tgt0 x))
  :
    _simg simg i0 (itr_src0) (trigger (Take X) >>= ktr_tgt0)
.

Definition simg: idx -> relation (itree eventE R) := paco3 _simg bot3.

Lemma simg_mon: monotone3 _simg.
Proof.
  ii. inv IN; try (by econs; et).
  - econs; et. ii. eapply LE; et.
  - econs; et. ii. hexploit SIM; et. i; des. esplits; et.
  - des. econs; et.
  - econs; et. ii. hexploit SIM; et. i; des. esplits; et.
  - des. econs; et.
Qed.
End TY.


(*** TODO: for bind rule, take a look at "respectful" thing again. ***)






Definition resum_itr E F `{E -< F}: itree E ~> itree F := fun _ itr => interp (fun _ e => trigger e) itr.

Variable md_src md_tgt: Mod.t.
Let ms_src: ModSem.t := md_src.(Mod.enclose).
Let ms_tgt: ModSem.t := md_tgt.(Mod.enclose).
Let sim_fnsem: relation (string * (list val -> itree Es val)) :=
  fun '(fn_src, fsem_src) '(fn_tgt, fsem_tgt) =>
    (<<NAME: fn_src = fn_tgt>>) /\
    (<<SEM: forall varg, exists itr_src itr_tgt,
          (<<SRC: fsem_src varg = resum_itr itr_src>>) /\
          (<<TGT: fsem_tgt varg = resum_itr itr_tgt>>) /\
          (<<SIM: exists i0, simg i0 itr_src itr_tgt>>)>>)
.

Hypothesis (SIM: Forall2 sim_fnsem ms_src.(ModSem.fnsems) ms_tgt.(ModSem.fnsems)).

Theorem adequacy_global: Beh.of_program (Mod.interp md_tgt) <1= Beh.of_program (Mod.interp md_src).
Proof.
  admit "TODO".
Qed.

End SIM.
