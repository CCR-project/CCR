# Conditional Contextual Refinement

This is the artifact for the paper "Conditional Contextual Refinement".

## List of Claims
We claim that the artifact provides Coq development for the results in
the paper (modulo small simplifications for expository purposes) and
compiles without any problem.

## Download, installation, and sanity-testing
The artifact is presented as a Docker image ("CCR-docker.tar"), but we
are also submitting the latest source code ("CCR.tar.gz") just in
case. Both of these are also publicly available
[here](https://github.com/alxest/CCR) and
[here](https://hub.docker.com/repository/docker/alxest/popl23ae).  If
there is a need to update our artifact in the middle of the review
process, we will make the latest version available on those links.

### Installing via Docker image
1. Install [Docker](https://www.docker.com/) (version 20.10.14 is
tested).

Now, you can either use the Docker image from the Docker Hub (make
sure you have internet connection):

2. Run `sudo docker run -it alxest/popl23ae /bin/bash`

or, you can use the Docker image that we submitted:

2. Run `sudo docker load < CCR.tar && sudo docker run -it alxest/popl23ae /bin/bash`.


### Installing manually with raw source code
1. Install opam in your system with the version at least 2.1.0.
2. Make a fresh directorcy, install a local opam switch and install the dependencies:
```
mkdir fresh_directory && cd fresh_directory &&
opam switch create . ocaml.4.13.0 &&
eval $(opam env) &&
opam repo add coq-released "https://coq.inria.fr/opam/released" &&
opam config env &&
opam pin add coq 8.15.2 -y &&
opam pin add coq-paco 4.1.2 -y &&
opam pin add coq-itree 4.0.0 -y &&
opam pin add coq-ordinal 0.5.2 -y &&
opam pin add coq-stdpp 1.7.0 -y &&
opam pin add coq-iris 3.6.0 -y &&
opam pin add coq-compcert 3.11 -y &&
opam pin add ocamlbuild 0.14.1 -y
```

Now, you can either use the source code from the Github (make sure you
have internet connection):

3. Run `git clone git@github.com:alxest/CCR.git && cd CCR && make`

or you can use the raw source code that we submitted:

3. Run `mv CCR.tar.gz fresh_directory && tar -xvf CCR.tar.gz && cd CCR && make`.

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
   accommodate collaboration with others.
5. Check that the development supports extraction of examples to
   OCaml, which can actually be executed. The script below runs "echo"
   example (in the tech report) which takes (scanf) integers
   indefinitely, and when you put `-1`, it will print the integers you
   entered so far in a reverse order. You can run the scripts as
   follows in the project root directory.
   - "cd ./extract; ./run.sh; cd .." extracts and runs examples
     written in EMS (abstractions and implementation of Echo, etc)
     using the extraction mechanism of Interaction Trees.
   - "cd ./imp/compiler_extract; ./run.sh; cd .." builds IMP compiler,
     compiles an example down to the assembly using CompCert, and runs
     it.
6. (optional) Check that the development is not using any more axioms
   than the ones specified in Section "Axioms". You can execute `Print
   Assumptions THEOREM` after a theorem. (e.g., try `Print Assumptions
   adequacy_type2` at the end of the `spc/Hoare.v`.)

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

Note: the gap between Coq development and paper's presentation of
Fig. 6 originates from the additional features in Section 5, which are
just briefly mentioned. Specifically, the ordinals comes from the
extension on Section 5.1 and the additional arguments to pre/post
conditions (`varg_src, vret_src`) comes from the extension on Section
5.3.

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

Note: Indeed, we are proving stronger property than a mere
extensionality here. `stb_weaker` in spc/STB.v allows not just
extension of the specs, but also weakening/strengthening of the
pre/post-conditions.

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
If you are involved in this project in any way -- either the user or
the developer -- you are encouraged to join the [CCR-project discord
server](https://discord.gg/jQezqzJZ) for chat.
