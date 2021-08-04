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

- coq-compcert (= *3.8*) and its dependencies:
  + coq-flocq (= *3.4.1*)
  + menhir (= *20210310*)
  + coq-menhirlib (= *20210310*)

- ocamlbuild (= *0.14.0*)

All packages can be installed from [OPAM archive for Coq](https://github.com/coq/opam-coq-archive)

## Figure to code mapping

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
- toAbs --> `KModSem.transl_src` in OpenDef.v
- toAbspec --> `KModSem.transl_tgt` in OpenDef.v
- safe --> `safe_itree` in Safe.v
- others are in OpenDef.v/HoareDef.v

Theorem 3.1
- `adequacy_open` in Open.v

Theorem 4.1 
- `adequacy_local2` in SimModSemHint.v

Theorem 4.2
- `adequacy_weaken` in Weakening.v

Theorem 4.3
- `safe_mods_safe` in Safe.v

Theorem 6.1
- `compile_behavior_improves` in Imp2AsmProof.v

## Delta with paper's presentation

- In the paper, the order of arguments in pre/postconditions are "x -> x_a -> d", but in development it is "x_a -> x -> d".
- In the paper, we use explicit event GetCaller (using monadic style) but in development we just thread it.
- In the paper, the magic number is zero but in development it is -1. (Note also that when running the extracted examples, it stops with -1)

## How to build
- make -j[N] -k

## EMS extraction example
Running extracted examples (abstractions and implementation of Echo)
- "cd ./extract; ./run.sh"

## IMP compilation example
Building IMP compiler and compiling the example (IMP implementation of Echo)
- "cd ./imp/compiler_extract; ./run.sh" (please refer to the script for detailed instructions)
