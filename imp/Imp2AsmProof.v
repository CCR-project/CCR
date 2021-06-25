From compcert Require Import
     Smallstep AST Events Behaviors Errors Csharpminor Linking Compiler Asm.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.
Require Import Imp2Csharpminor.
Require Import SimSTS2.

Require Import Imp2CsharpminorLink.
Require Import Imp2CsharpminorSepComp.
Require Import Imp2Asm.

Set Implicit Arguments.

Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{builtins : builtinsTy}.

  (* Lemma nlist_list_eq {A} : *)
  (*   forall (nl: @Coqlib.nlist A) (a: A) t *)
  (*     (NLIST: nlist2list nl = a :: t), *)
  (*     (nl = list2nlist a t). *)
  (* Proof. *)
  (*   i. depgen a. depgen t. clear. induction nl; i; ss; clarify. *)
  (* Admitted. *)
  


  Theorem compile_behavior_improves
          (imps : list Imp.program) (asms : Coqlib.nlist Asm.program)
          (COMP: Forall2 (fun imp asm => compile_imp imp = OK asm) imps asms)
          (LINKSRC: exists impl, link_imps imps = Some impl)
    :
      exists asml, ((link_list asms = Some asml) /\
               (improves2 (imps_sem imps) (Asm.semantics asml))).
  Proof.
    assert (CSM: exists csms, Forall2 (fun imp csm => Imp2Csharpminor.compile_imp imp = OK csm) imps (nlist2list csms)).
    { depgen LINKSRC. induction COMP; ss; clarify.
      { i. des. ss. }
      unfold compile_imp, compile in H. des_ifs.
      i. destruct l.
      { unfold link_imps in LINKSRC. ss. des. clarify. exists (Coqlib.nbase p); eauto. econs; eauto. }
      des.
      assert (exists srcl2, link_imps (p0 :: l) = Some srcl2).
      { unfold link_imps in LINKSRC. ss. des_ifs. exists p1. ss. }
      apply IHCOMP in H0. des. exists (Coqlib.ncons p csms). econs; eauto. }
    des. hexploit compile_behavior_improves; eauto. i.
    des. rename tgtl into csml, H into LINKCSM, H0 into IMP2.

    assert (C2A: Coqlib.nlist_forall2 (fun csm asm => transf_csharpminor_program csm = OK asm) csms asms).
    { clear IMP2. depgen asms. depgen csms. clear. depgen csml. induction imps; i; ss; clarify.
      { inv CSM; ss; clarify. sym in H; apply n2l_not_nil in H. clarify. }
      inv CSM. inv COMP.
      admit "". }

    


      (* replace csms with (list2nlist y l'). *)
      (* 2:{ hexploit (n2l_l2n csms). i. des. clarify. sym in H1. apply nlist_list_eq in H1. clarify. } *)
      (* replace asms with (list2nlist y0 l'0). *)
      (* 2:{ hexploit (n2l_l2n asms). i. des. clarify. sym in H4. apply nlist_list_eq in H4. clarify. } *)


      



    
  Qed.

End PROOF.
