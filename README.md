# Conditional Contextual Refinement

## Dependencies
Our development successfully compiles with following versions (in Linux, OS X):

- coq (= *8.13.2*)

- coq-ext-lib (= *0.11.3*)
- coq-paco (= *4.1.1*)
- coq-itree (= *3.2.0*)
- coq-ordinal (= *0.5.0*)

- coq-stdpp (= *1.5.0*)
- coq-iris (= *3.4.0*)

- coq-compcert (= *3.9*) and its dependencies:
  + coq-flocq (= *3.4.1*)
  + menhir (= *20210310*)
  + coq-menhirlib (= *20210310*)

- ocamlbuild (= *0.14.0*)

All packages can be installed from [OPAM archive for Coq](https://github.com/coq/opam-coq-archive)

## How to build
- make -j[N] -k

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
