# Abstraction Logic: The Marriage of Contextual Refinement and Separation Logic

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

## Delta with paper (and technical report)'s presentation

- In the paper and technical report, the order of arguments in pre/postconditions are "x -> x_a -> d", but in development it is "x_a -> x -> d".
- In the technical report, we use explicit event GetCaller (using monadic style) but in development we just thread it.

## How to build
- make -j[N] -k

## EMS extraction example
Running extracted examples (abstractions and implementation of MW, Echo, and etc.)
- "cd ./extract; ./run.sh"

## IMP compilation example
Building IMP compiler and compiling the example (IMP implementation of Echo)
- "cd ./imp/compiler_extract; ./run.sh" (please refer to the script for detailed instructions)

## Paper to code mapping

Fig. 1
- P1MW -> MWC0.v
- P2MW -> MWB0.v
- IMW -> MWC1.v
- AMW -> MWC2.v

Fig. 2
- it can be seen as a simplified version of "cannon" example in technical report. (examples/cannon directory)

Fig. 3
- PApp -> MWApp0.v
- IApp -> MWApp1.v
- AApp -> MWApp2.v

Fig. 4
- EEMS --> `Es` in ModSem.v
- EMS --> `ModSem.t` in ModSem.v
- Mod --> `Mod.t` in ModSem.v
- Trace --> `Tr.t` in Behavior.v
- Beh --> composition of `Beh.of_program` in Behavior.v and `ModL.compile` in ModSem.v.
- Mi ≤ctx Ma --> `refines2` in ModSem.v

Fig. 5
- rProp --> `iProp'` in IProp.v
- PCM --> `URA.t` in PCM.v
- Cond --> `fspec` in HoareDef.v
- ESPC --> `hEs` in HoareDef.v
- PAbs --> `SModSem.t` in HoareDef.v
- [] --> `SModSem.to_src` in HoareDef.v
- S_in \rtimes A : S_out --> `SModSem.to_tgt` in HoareDef.v
- CallDef --> `HoareCall` in HoareDef.v
- FunDef --> `HoareFun` in HoareDef.v
- APCiDef --> `_APC` in HoareDef.v
- APCDef --> `APC` in HoareDef.v

Theorem 3.1
- `adequacy_type` (`adequacy_type2`) in Hoare.v

Lemma 3.2
- safe --> `safe_itree` in Safe.v
- `safe_mods_safe` in Safe.v

Theorem 3.4
- `compile_behavior_improves` in Imp2AsmProof.v

Fig. 6
- MemOpen.v, MWHeader.v

Fig. 7
- examples/repeat directory.

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

