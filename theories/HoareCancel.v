Require Import Mem0 Mem1 SimModSem Hoare.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior Hoare.
Require Import ModSemDirect.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.


Section CANCEL.

  Context `{Σ: GRA.t}.
  Variable mn_caller mn_callee: mname.
  Variable P: Σ -> Prop.
  (*** TODO: Maybe P should be able to depend on list val ***)
  (*** TODO: name it... htree (hoare tree), hktree (hoare ktree)? ***)
  Variable Q: val -> Σ -> Prop.
  Variable fn: fname.

  Let W: Type := (alist mname Σ) * (alist mname Σ).
  Let wf: W -> Prop :=
    fun '(mrs_src0, mrs_tgt0) =>
      exists _mr_caller_src _mr_caller_tgt _mr_callee_src _mr_callee_tgt,
        (<<SRC: mrs_src0 = Maps.add mn_callee _mr_callee_src
                                    (Maps.add mn_caller _mr_caller_src Maps.empty)
                                    >>) /\
        (<<TGT: mrs_tgt0 = Maps.add mn_callee _mr_callee_tgt
                                    (Maps.add mn_caller _mr_caller_tgt Maps.empty)
                                    >>)
  .
  Hypothesis DIF: mn_caller <> mn_callee.

  Goal sim_fsem wf (fun _ => Ret (Vint 0)) (fun _ => (HoareCall mn_caller P Q fn [])).
  Proof.
    ii. clarify. exists 100.
    ss. des. clarify.
    force_r. ii. des_ifs. left. rename c into marg_caller. rename c0 into farg_caller.
    force_r.
    { unfold rel_dec. ss. instantiate (1:=_mr_caller_tgt).
      des_ifs; bsimpl; des; des_sumbool; ss; clarify.
      - unfold rel_dec. ss. des_ifs; bsimpl; des; des_sumbool; ss; clarify.
    }
    ii. left.
    go. rename x into rarg.
    repeat go.
    unfold guarantee. igo.
    go.





    assert(trigger (Call fn []) = HoareFun mn_callee P Q (Ret tt)).
    { admit "call inline". }
    rewrite H. unfold HoareFun. igo.
    replace fr_tgt1 with (URA.unit (t:=Σ)) by admit "push frame".
    force_r.
    exists rarg. left.
    igo.
    force_r. left.
    unfold assume. igo.
    force_r. esplits; et. left.
    force_r. intro vret. left.
    igo.
    force_r. intro tmp. destruct tmp as [mret_callee fret_callee]. left.
    igo. force_r.
    { unfold rel_dec. ss. instantiate (1:=_mr_callee_tgt).
      repeat (unfold rel_dec in *; ss; des_ifs; bsimpl; des; des_sumbool; ss; clarify).
    }
    i. rewrite URA.unit_idl in UPD0.
    left. force_r. intro rret. left.
    igo. unfold guarantee. igo. force_r. i. left.
    force_r. intro fret_garbage; i.
    left.


    replace fret_garbage with fr_tgt1 by admit "pop frame".
    force_r. exists rret. left. force_r. left. igo. force_r.
    esplits; et. left.
  Abort.

End CANCEL.
