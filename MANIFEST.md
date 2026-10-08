# Next Slice Manifest: Uniform Rational Query Compiler

**Status:** proposed work plan  
**Repository baseline:** `main`, Lean `leanprover/lean4:v4.35.0-rc4`, mathlib revision pinned in `lakefile.toml` and `lake-manifest.json`.

## Objective

Formalize the generic step that turns one finite existential system of rational polynomial equalities and inequalities into finitely many rational polynomial-solvability queries. Prove that the system has a rational solution exactly when at least one compiled query does.

Then prove that a computable decision procedure for rational polynomial solvability decides these finite systems uniformly from their encoded input. This supplies a concrete, reusable version of the query-compilation part of `FiniteTestInterface.effective`.

This slice does not construct the paper's indexed tests or prove their arithmetic properties. It creates the compiler those later tests can use.

## Why this slice

`FiniteTests.lean` already proves the abstract search argument. Its `FiniteTestInterface.effective` field assumes that a rational-solvability decider uniformly decides every indexed test. The paper explains that each finite test is an existential Boolean combination of polynomial equations and inequations, then reduces that to finitely many rational-solvability queries. Formalizing that translation makes the algorithmic boundary explicit without taking on the elliptic-curve and height arguments yet.

Reference: [Section 2, finite rational tests](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-September-24-2026/build/sections/02-reduction.tex), especially the discussion of finite constraints and rational queries.

## Gate 0: Install and establish the pinned Lean environment

The current workspace shell is Linux x86-64. `git` and `curl` are present; `elan`, `lean`, and `lake` are absent from `PATH`.

1. Install Lean's version manager, [elan](https://github.com/leanprover/elan#installation), using its official installation instructions. Do not select a new global Lean version for this project.
2. Open a new shell (or load elan's environment in the current shell).
3. From the repository root, confirm that elan selects the version in `lean-toolchain`:

   ```sh
   elan show
   lean --version
   lake --version
   ```

4. Establish the source baseline and dependency cache:

   ```sh
   bash verify.sh
   ```

   This script fetches the mathlib cache, builds the project, prints the audit declarations, and runs `leanchecker`. Dependency and toolchain downloads require network access.

**Gate acceptance:** the displayed Lean version is `4.35.0-rc4`, the pinned dependencies resolve without changing their revisions, and `bash verify.sh` exits successfully on the restored checkout before implementation begins. If it fails, record the exact command and error; diagnose that environment issue separately. Do not edit the Lean toolchain, update mathlib, or apply the historical `/proc` adapter unless the same host issue is reproduced and understood.

## Formalization contract

### Input language

Define an effectively encoded finite constraint system with:

- a finite number of existential variables ranging over `ℚ`;
- rational polynomials in those variables;
- a finite Boolean formula built from polynomial equalities and disequalities.

Use mathlib polynomial types and encodings where they fit. If a custom sparse syntax is needed for variable arity or `Primcodable`, give it a denotation as a polynomial over `ℚ` and prove its encoding/evaluation functions computable. Keep the representation small and specific to this contract.

Define satisfaction as existence of a rational assignment making the formula true. The syntax must cover the empty conjunction and disjunction, constants, and negation or an effective normalization of negation to equality/disequality atoms.

### Query compiler

Implement a total, computable compiler from each finite constraint system to a finite list of rational polynomial-solvability instances. A suggested construction is:

1. Put the Boolean formula into a finite disjunction of conjunctions.
2. Replace each disequation `g ≠ 0` by an existential inverse witness `y` and the equation `g * y = 1`.
3. Combine the equations in each conjunction into one equation using a sum of squares over `ℚ`.
4. Include all original and auxiliary variables in that query's arity.

Other constructions are acceptable if they meet the same semantic and computability contract. Preserve the zero-variable and empty-formula cases explicitly.

### Required theorem shapes

Names may differ, but prove equivalents of:

```lean
theorem compile_correct (c : ConstraintSystem) :
  Satisfies c ↔ ∃ q ∈ compile c, RationalPolynomialHasRoot q

theorem constraintSystem_computable
    (oracle : ComputablePred RationalPolynomialHasRoot) :
    ComputablePred Satisfies
```

Also prove the indexed form: if a computable procedure maps an encoded input/index pair to a finite constraint system, then an oracle for rational polynomial solvability decides satisfaction uniformly on that pair. The result should be a real `ComputablePred`, not only a `DecidablePred` obtained classically.

This theorem is a generic compiler result. It does not yet instantiate the paper's complete `effective` field, because the recursive theory, Skolemization, ground-term enumeration, and actual indexed constraint generator are outside this slice.

## Acceptance criteria

- The compiler is total and effective and emits only finitely many queries for every input.
- Its correctness theorem proves both directions of the satisfiability equivalence.
- Computability is uniform over the encoded constraint and, for the indexed theorem, the pair `(input, index)`.
- Include small Lean examples covering an equality, a disequality, a conjunction, a disjunction, and the empty/constant cases.
- Integrate the new module into the Lake build and theorem/axiom audit. Do not introduce `sorry`, custom axioms, `unsafe`, or untracked toolchain changes.
- Once Gate 0 passes and implementation is complete, `bash verify.sh` succeeds from a clean checkout. Report the exact Lean/mathlib versions and any network/cache assumptions.

## Out of scope

- Defining the paper's entire recursive ring theory or generating its indexed tests from a polynomial and natural-number index.
- Proving the integer model, pole-parity formula, compactness step, valuation coarsening, elliptic-curve lemmas, prime-pattern results, or five-point height estimate.
- Proving DPRM or instantiating `passes` and `complete` for H10.
- Changing mathlib revisions, Lean versions, or CI policy to work around a local setup problem.

## Agent coordination

- Treat Gate 0 as a serial prerequisite: one person establishes and records the pinned build before proof work depends on it.
- Before parallel implementation, agree on the constraint/query data types and theorem signatures. Keep a single owner for edits to those shared definitions; parallel work can review mathlib encodings, prove isolated compiler lemmas, or map the paper's test syntax without editing the shared API.
- Each handoff should state changed files, theorem signatures completed, build/audit evidence, and assumptions still left open.
