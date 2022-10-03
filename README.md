# Conditional Contextual Refinement

This is the artifact for the paper "Conditional Contextual Refinement".

## List of Claims
The main claim of this artifact is that the description in the paper
corresponds to the Coq development (modulo small simplifications for
presentation purposes).

## Download, installation, and sanity-testing
The artifact is presented as a docker image. The raw source code could
be found [here](https://sf.snu.ac.kr/publications/ccr.tar.gz) and the
docker image -- containing the source-code with all dependencies
already installed -- could be found [here](TODO). We recommend using
the virtual machine unless you are an experienced opam user.

If there is a need
to update our artifact in the process of the review process, we will
make the latest version available on those links.  We are also
submitting the latest source code and docker image, just in case.

### Installing via docker image

### Installing manually


## Overview of the source code

## Evaluation Instructions
To evaluate this artifact, we propose the following steps:
1. Confirm that the Coq development compiles without problems.  To do
   so, run `make clean` if you have previously built the Coq
   development or are using the docker image.  Thereafter, run `make
   -jN` where `N` is the number of cores you wish to use.
2. Search for `admit` or `Admitted.` in the source code files. As you
   will see, the development does not have any admits.
3. Read the Section "Differences to the paper" to familiarize yourself
   with the differences between the on-paper presentation and the Coq
   development.
4. Read through the Coq development and compare the Theorems and
   Definitions with those from the paper. You can find a mapping from
   paper to Coq below in the section "Mapping between the paper and
   the Coq development". You can find the Coq files in the folder
   `dimsum`.
5. Check that the axioms used in the development are only the ones
   listed under "Axioms" below. To do so, you can execute
   `Print Assumptions compiler_correct.` after a theorem (here
   `compiler_correct`).
6. Check that the Gitlab https://gitlab.mpi-sws.org/iris/dimsum
   hosting the project is publicly accessible, includes an issue
   tracker, and the code has an open source license. The commit that
   was used to generate the artifact can be found here:
   https://gitlab.mpi-sws.org/iris/dimsum/-/tree/7d5f0d636030173748e4a9e331e0d03718b8c8a6

## Differences to the paper

## Mapping between the paper and the Coq development

## Axioms



MapIAproof
Print Assumptions correct.

Axioms:
STS.syscall_sem : STS.event → Prop
RelationalChoice.relational_choice
  : ∀ (A B : Type) (R : A → B → Prop),
      (∀ x : A, ∃ y : B, R x y)
      → ∃ R' : A → B → Prop, Logic.subrelation R' R ∧ (∀ x : A, ∃ y, unique (λ y : B, R' x y) y)
Axioms.prop_ext : ClassicalFacts.prop_extensionality
proof_irrelevance : ∀ (P : Prop) (p1 p2 : P), p1 = p2
functional_extensionality_dep : ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x), (∀ x : A, f x = g x) → f = g
Eqdep.Eq_rect_eq.eq_rect_eq : ∀ (U : Type) (p : U) (Q : U → Type) (x : Q p) (h : p = p), x = eq_rect p Q x p h
ClassicalUniqueChoice.dependent_unique_choice
  : ∀ (A : Type) (B : A → Type) (R : ∀ x : A, B x → Prop),
      (∀ x : A, ∃ y, unique (λ y : B x, R x y) y) → ∃ f : ∀ x : A, B x, ∀ x : A, R x (f x)
constructive_definite_description : ∀ (A : Type) (P : A → Prop), (∃ y, unique (λ x : A, P x) y) → {x : A | P x}
classic : ∀ P : Prop, P ∨ ¬ P
bisimulation_is_eq : ∀ (E : Type → Type) (R : Type) (t1 t2 : itree E R), t1 ≅ t2 → t1 = t2


Axioms:
syscall_sem : event → Prop
relational_choice
  : ∀ (A B : Type) (R : A → B → Prop),
      (∀ x : A, ∃ y : B, R x y)
      → ∃ R' : A → B → Prop, Logic.subrelation R' R ∧ (∀ x : A, ∃ y, unique (λ y : B, R' x y) y)
Axioms.prop_ext : ClassicalFacts.prop_extensionality
ProofIrrelevance.proof_irrelevance : ∀ (P : Prop) (p1 p2 : P), p1 = p2
functional_extensionality_dep : ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x), (∀ x : A, f x = g x) → f = g
Eqdep.Eq_rect_eq.eq_rect_eq : ∀ (U : Type) (p : U) (Q : U → Type) (x : Q p) (h : p = p), x = eq_rect p Q x p h
dependent_unique_choice
  : ∀ (A : Type) (B : A → Type) (R : ∀ x : A, B x → Prop),
      (∀ x : A, ∃ y, unique (λ y : B x, R x y) y) → ∃ f : ∀ x : A, B x, ∀ x : A, R x (f x)
constructive_definite_description : ∀ (A : Type) (P : A → Prop), (∃ y, unique (λ x : A, P x) y) → {x : A | P x}
classic : ∀ P : Prop, P ∨ ¬ P
bisimulation_is_eq : ∀ (E : Type → Type) (R : Type) (t1 t2 : itree E R), t1 ≅ t2 → t1 = t2








## Delta with paper (and technical report)'s presentation

- In the paper and technical report, the order of arguments in pre/postconditions are "x -> x_a -> d", but in development it is "x_a -> x -> d".
- In the technical report, we use explicit event GetCaller (using monadic style) but in development we just thread it.

## EMS extraction example
Running extracted examples (abstractions and implementation of MW, Echo, and etc.)
- "cd ./extract; ./run.sh"

## IMP compilation example
Building IMP compiler and compiling the example (IMP implementation of Echo)
- "cd ./imp/compiler_extract; ./run.sh" (please refer to the script for detailed instructions)

## Paper to code mapping

Fig. 1
(examples/map)
- module I_Map --> MapI.v
- module A_Map --> MapA.v
- pre/post conditions S_Map --> `MapStb` in MapHeader.v
- proof of I_Map ⊑_ctx <S0_Map ⊢ M_Map > -> `MapIAproof.v`
- proof of <S0_Map ⊢ M_Map > ⊑_ctx <S_Map ⊢ A_Map > -> `MapMAproof.v` 
 
Sec. 2.4 Incremental and modular verification of the running example
(examples/map)
- proof of I_Map ⊑_ctx <S0_Map ⊢ M_Map > -> `MapIAproof.v`
- proof of <S0_Map ⊢ M_Map > ⊑_ctx <S_Map ⊢ A_Map > -> `MapMAproof.v` 

Fig. 3
(ems/)
- E_P --> `eventE` in ModSem.v
- E_EMS --> `Es` in ModSem.v
- Mod --> `Mod.t` in ModSem.v
- Mi ≤ctx Ma --> `refines2` in ModSem.v

Fig. 4
(ems/)
- Trace --> `Tr.t` in Behavior.v
- Beh --> composition of `Beh.of_program` in Behavior.v and `ModL.compile` in ModSem.v.

Fig. 6
(spc/)
- PCM --> `URA.t` in PCM.v
- rProp --> `iProp'` in IProp.v
- Cond --> `fspec` in HoarDef.v
- Conds --> `(alist gname fspec)`
- <S |-a M> --> `Module SMod` in HoareDef.v
- WrapC --> `HoareCall` in HoardDef.v
- WrapF --> `HoareFun` in HoardDef.v

Fig. 7
- mem/Mem1.v

Theorem 3.1 (Adequaccy)
- `adequacy_local2` in ems/SimModSem.v

Theorem 4.1 (Assumption Cancellation Theorem (ACT))
- `adequacy_type2` in spc/Hoare.v

Theorem 4.2 (Extensionality)
- `adequacy_weaken` in spc/Weakening.v

Lemma 4.3 (Safety)
- `safe_mods_safe` in spc/Safe.v

Theorem 6.1 (Separate Compilation Correctness)
- `compile_behavior_improves` in imp/compiler_proof/Imp2AsmProof.v

## Technical Report to code mapping

Fig. 2
- In examples/cannon directory.

Fig. 3
- mem/MemOpen.v

Fig. 4
- examples/stack directory. I_Stack maps to Stack0.v, Stack1 maps to Stack2.v

Fig. 5
- examples/stack directory. Stack2A/2B maps to Stack3A/B.v

Fig. 6
- examples/echo directory. Composed result is in EchoAll.v

Fig. 7
- examples/repeat directory.

Fig. 8
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
- 
