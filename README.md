# Coq Formalization Artifact
A Type-Directed Operational Semantics for a Calculus with a Merge Operator

## Building Instructions

Our Coq proofs are verified in **Coq 8.9.1**. We rely on two Coq libraries:
[`metalib`](https://github.com/plclub/metalib) for the locally nameless
representation in our proofs; and
[`LibTactics.v`](http://gallium.inria.fr/~fpottier/ssphs/LibTactics.html),
which is included in the directory.



### Prerequisites

1. Install Coq 8.9.1.
   The recommended way to install Coq is via `OPAM`. Refer to
   [here](https://coq.inria.fr/opam/www/using.html) for detailed steps. Or one could
   download the pre-built packages for Windows and MacOS via
   [here](https://github.com/coq/coq/releases/tag/V8.9.1). Choose a suitable installer
   according to your platform.

2. Make sure `Coq` is installed (type `coqc` in the terminal, if you see "command
   not found" this means you have not properly installed Coq), then install `Metalib`:
   1. Open terminal
   2. `git clone https://github.com/plclub/metalib`
   3. `cd metalib/Metalib`
   4. Make sure the version is correct by `git checkout e15d6a1`
   5. `make install`

3. Note to compile the `variant`, it is necessary to replace `LibLNgen.v` in `Metalib` by the file in the same name provided in the directory.
   1. `cd metalib/Metalib`
   2. copy the `LibLNgen.v` into it for replacement
   3. `make clean && make && make install`

### Build and Compile the Proofs

1. Enter either `main_version/coq` or `variant/coq` directory.

2. Type `make` in the terminal to build and compile the proofs.

3. You should see something like the following (suppose `>` is the prompt):
   ```sh
   coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
   COQDEP VFILES
   COQC LibTactics.v
   COQC syntax_ott.v
   COQC rules_inf.v
   COQC Subtyping_inversion.v
   COQC Infrastructure.v
   COQC Deterministic.v
   COQC Type_Safety.v
   COQC rules_inf2.v
   COQC dunfield.v
   COQC icfp.v
   ```

## Proof Structure

- `main_version` directory contains the definition and proofs of the main calculus
- `variant` directory contains the definition and proofs of the simple variant (discussed in the Appendix). Its subtyping relation is
known to be reflexive and transitive.
- `syntax_ott.v` contains the locally nameless definitions of the calculi and Dunfield's calculus.
- `rules_inf.v` and `rules_inf2.v` contains the `lngen` generated code.
- `Infrastructure.v` contains the type systems of the calculi and some lemmas.
- `Subtyping_inversion.v` contains some properties of the subtyping relation.
- `Deterministic.v` contains the proofs of the determinism property.
- `Type_Safety.v` contains the proofs of the type preservation and progress properties.
- `dunfield.v` contains the proofs of the soundness theorem with respect to Dunfield's calculus.
- `icfp.v`contains the proofs of the completeness theorem with respect to lambdai.
