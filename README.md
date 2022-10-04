# Conditional Contextual Refinement

This is the artifact for the paper "Conditional Contextual Refinement".

## List of Claims
We claim that the artifact provides Coq development for the results in
the paper (modulo small simplifications for expository purposes) and
compiles without any problem.

## Download, installation, and sanity-testing
The artifact is presented as a Docker image, but we are also
submitting the latest source code just in case. Both of these are also
available [here](https://github.com/alxest/CCR) and [here](TODO).  If
there is a need to update our artifact in the process of the review
process, we will make the latest version available on those links.

### Installing via Docker image
To use Docker, please install [Docker](https://www.docker.com/)
(version 20.10.14 is tested) and TODO.

### Installing manually
TODO

## Evaluation Instructions
To evaluate this artifact, we propose the following steps:
1. Confirm that the Coq development compiles without any problem.  To
   do so, type `git clean -xf .` in the project root directory if you
   have previously built the Coq development or are using the Docker
   image. Check that no `.vo` file remains (e.g., typing `find
   . -iname "*.vo"` in the project root should print nothing). Then,
   run `make -jN` where `N` is the number of cores you wish to use.
2. Check that the source code does not contain any `admit` or
   `Admitted.` (e.g., typing `grep -ri "admit" --include="*.v" .`  in
   the project root should print nothing).
3. Read the Section "Mapping from the paper to the Coq development"
   and check that the Coq development indeed corresponds to the
   paper's presentation
4. Check that the project is hosted in the [public
   repository](https://github.com/alxest/CCR) (including an issue
   tracker) with [open source
   license](https://github.com/alxest/CCR/blob/popl23ae/LICENSE). We
   have also setup [public chat room](https://discord.gg/jQezqzJZ) to
   accommodate collaboration with others. The commit we used in this
   artifact could be found [here](TODO).
5. Check that the development supports extraction of examples to
   OCaml, which can actually be executed. TODO
6. (optional) Check that the development is not using any more axioms
   than the ones specified in Section "Axioms". You can execute `Print
   Assumptions THEOREM` after a theorem. (e.g., try `Print Assumptions
   adequacy_type2` at the end of the `spc/Hoare.v`.)
   
## EMS extraction example
Running extracted examples (abstractions and implementation of MW, Echo, and etc.)
- "cd ./extract; ./run.sh"

## IMP compilation example
Building IMP compiler and compiling the example (IMP implementation of Echo)
- "cd ./imp/compiler_extract; ./run.sh" (please refer to the script for detailed instructions) 

## Mapping from the paper to the Coq development
Fig. 1
(in examples/map directory)
- module I_Map --> MapI.v
- module A_Map --> MapA.v
- pre/post conditions S_Map --> `MapStb` in MapHeader.v
- module M_Map (L200) --> MapM.v

Sec. 2.4 Incremental and modular verification of the running example
(in `examples/map` directory)
- proof of I_Map ⊑_ctx <S0_Map ⊢ M_Map > -> MapIAproof.v
- proof of <S0_Map ⊢ M_Map > ⊑_ctx <S_Map ⊢ A_Map > -> MapMAproof.v
- proof of end-to-end refinement (I_Map ⊑_ctx <S_Map ⊢ A_Map >) -> MapIAproof.v

Fig. 3
(in ems/ directory)
- E_P --> `eventE` in ModSem.v
- E_EMS --> `Es` in ModSem.v
- Mod --> `Mod.t` in ModSem.v
- Mi ≤ctx Ma --> `refines2` in ModSem.v
- Vertical composition of contextual refinements --> `refines2_PreOrder` in ModSem.v
- Horizontal composition of contextual refinements --> `refines2_add` in ModSem.v

Fig. 4
(in ems/ directory)
- Trace --> `Tr.t` in `Behavior.v`
- beh --> `Beh.of_program` in `Behavior.v`
- concat --> `ModL.compile` in `ModSem.v`

Fig. 5
- simulation relation --> `sim_itree` in SimModSem.v

Fig. 6
(in spc/ directory)
- PCM --> `URA.t` in PCM.v
- rProp --> `iProp'` in IProp.v
- Cond --> `fspec` in HoarDef.v
- Conds --> `(alist gname fspec)`
- <S |-a M> --> `Module SMod` in HoareDef.v
- WrapC --> `HoareCall` in HoardDef.v
- WrapF --> `HoareFun` in HoardDef.v

Fig. 7
- 𝜎_Mem --> `SModSem.initial_mr` field of `SMemSem` in mem/Mem1.v
- S_Mem --> `MemStb` in mem/Mem1.v

Fig. 8
(in examples/repeat directory)
- repeat --> `repeatF` in Repeat0.v
- succ, main --> `succF` and `addF` in Add0.v
- H_RP --> `repeat_spec` in Repeat1.v
- S_SC --> `succ_spec` in Add1.v
- end-to-end refinement --> `correct` in RepeatAll.v

Theorem 3.1 (Adequacy)
- `adequacy_local2` in ems/SimModSem.v

Theorem 4.1 (Assumption Cancellation Theorem (ACT))
- `adequacy_type2` in spc/Hoare.v

Theorem 4.2 (Extensionality)
- `adequacy_weaken` in spc/Weakening.v

Lemma 4.3 (Safety)
- `safe_mods_safe` in spc/Safe.v

Theorem 6.1 (Separate Compilation Correctness)
- `compile_behavior_improves` in imp/compiler_proof/Imp2AsmProof.v

## Axioms
The development uses the following non-constructive axioms (most of them are in `lib/Axioms.v`).
- Functional form of the (non extensional) Axiom of Choice.
  (technically, it appears as `relational_choice`
  [here](https://coq.inria.fr/library/Coq.Logic.RelationalChoice.html)
  and `dependent_unique_choice`
  [here](https://coq.inria.fr/library/Coq.Logic.ClassicalUniqueChoice.html).
  However, combination of these two axioms are known to be equivalent
  to Functional form of the (non extensional) Axiom of Choice.
  Specifically, see `Reification of dependent and non dependent
  functional relation are equivalent`, and `AC_rel + AC! = AC_fun`
  [here](https://coq.inria.fr/library/Coq.Logic.ChoiceFacts.html).)
- System call semantics, following the style of [CompCert](https://github.com/AbsInt/CompCert/blob/master/common/Events.v#L1483)
- Propositional Extensionality. (`prop_extensinality` [here](https://coq.inria.fr/library/Coq.Logic.ClassicalFacts.html))
- Proof Irrelevance. (`proof_irrelevance` [here](https://coq.inria.fr/library/Coq.Logic.ClassicalFacts.html))
- Functional Extensionality. (`functional_extensionality_dep` [here](https://coq.inria.fr/library/Coq.Logic.FunctionalExtensionality.html))
- Invariance by Substitution of Reflexive Equality Proofs, UIP. (`eq_rect_eq` [here](https://coq.inria.fr/library/Coq.Logic.Eqdep.html))
- Constructive form of definite description. `constructive_definite_description` [here](https://coq.inria.fr/library/Coq.Logic.Description.html)
- Excluded middle. (`classic` [here](https://coq.inria.fr/library/Coq.Logic.Classical_Prop.html))
- Bisimulation on itree implies Leibniz equality. (`bisimulation_is_eq` [here](https://github.com/DeepSpec/InteractionTrees/blob/master/theories/Eq/EqAxiom.v#L18))

## Chat Room
You can come and chat with us in [CCR-project discord
server](https://discord.gg/jQezqzJZ).







## Delta with paper (and technical report)'s presentation


## Mapping from the Technical Report to the Coq development

Fig. 3
- In examples/cannon directory.

Fig. 4
- mem/MemOpen.v

Fig. 5
- examples/stack directory. I_Stack maps to Stack0.v, Stack1 maps to Stack2.v

Fig. 6
- examples/stack directory. Stack2A/2B maps to Stack3A/B.v

Fig. 7
- examples/echo directory. Composed result is in EchoAll.v

Fig. 8
- examples/repeat directory.

Fig. 9
- Eprim --> `eventE` in ModSem.v
- EEMS --> `Es` in ModSem.v
- EMS --> `ModSem.t` in ModSem.v
- EPAbs --> `hEs` in HoarDef.v
- PAbs --> `KModSem.t` in OpenDef.v
- PCM --> `URA.t` in PCM.v
- rProp --> `iProp'` in IProp.v
- Spec --> `fspec` in HoarDef.v
- Specs --> `(alist gname fspec)`
- s1 ⊒ s0 --> `fspec_weaker` in STB.v
- S1 ⊒ s0 --> `stb_weaker` in STB.v
- Mod --> `Mod.t` in ModSem.v
- Trace --> `Tr.t` in Behavior.v
- Beh --> composition of `Beh.of_program` in Behavior.v and `ModL.compile` in ModSem.v.
- Mi ≤ctx Ma --> `refines2` in ModSem.v

Fig. 9
- `compile_itree` in ModSem.v
- `interp_Es` in ModSemE.v

Fig. 10
- STS.v, Behavior.v

Fig. 11
- toAbs ([A]) --> `KModSem.transl_src` in OpenDef.v
- toAbspec (S_in \rtimes A : S_out) --> `KModSem.transl_tgt` in OpenDef.v
- others are in OpenDef.v/HoareDef.v

Theorem 1
- `adequacy_open` in Open.v

Theorem 2
- `adequacy_type` (`adequacy_type2`) in Hoare.v

Theorem 3
- `adequacy_weaken` in Weakening.v

Theorem 4
- safe --> `safe_itree` in Safe.v
- `safe_mods_safe` in Safe.v

Theorem 6
- `adequacy_local2` in SimModSemHint.v

Theorem 7
- `beh_preserved` in STS2ITree.v

Theorem 8
- `compile_behavior_improves` in Imp2AsmProof.v
