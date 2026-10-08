# Next Slice Manifest: Integer H10(Q) Query Adapter

**Status:** proposed next implementation slice
**Repository baseline:** the DNF query compiler in `RationalQueryCompiler.lean`; Lean `leanprover/lean4:v4.35.0-rc4`; mathlib revision pinned by `lakefile.toml` and `lake-manifest.json`.

## Current state

The prior compiler slice is complete. It represents finite DNF systems, compiles each clause to a rational polynomial root query, proves `compile_correct`, and proves uniform computability given a root oracle. The implementation and its recorded build are described in [README.md](README.md) and [VALIDATION.md](VALIDATION.md).

The remaining type-level gap at this boundary is that the current oracle, `RationalPolynomialHasRoot`, consumes a rational-coefficient sparse code with variables named by `Nat` and assignments `Nat → ℚ`. The paper's target problem takes integer-coefficient polynomials with finite arity as input. This slice connects those interfaces.

## Objective

Implement a total, computable normalization from the compiler's `PolynomialCode` to an explicitly finite-arity, integer-coefficient polynomial query. Prove that the normalization preserves rational-root existence, then derive the existing finite-system and indexed-system computability results from an oracle for the paper's H10(Q) query type.

Keep the current DNF input unchanged. Do not include the paper's indexed test generator in this slice.

## Environment gate

The recorded compiler build used Lean 4.35.0-rc4 through `/tmp/h10-elan/bin`. Before making changes, confirm the toolchain is available in the agent's shell and run `bash verify.sh` on the unchanged checkout as the baseline. If that path is temporary or missing in a fresh shell, install elan using its [official instructions](https://github.com/leanprover/elan#installation), then let the repository's `lean-toolchain` select the pinned version.

Do not change `lean-toolchain`, mathlib revisions, or CI policy. Record the Lean version, exact command, and whether the mathlib cache was present. Network access may be needed for toolchain, dependencies, and cache files.

## Formalization contract

### Finite-arity integer query

Define an effectively encoded query containing:

- an arity `n : Nat`;
- a finite sparse polynomial with integer coefficients and variables restricted to `Fin n` (or an equivalent code with a proved support bound).

Define its H10(Q) predicate as existence of an assignment `Fin n → ℚ` at which the polynomial, interpreted over `ℚ`, is zero. The query code and its denotation must be effectively encoded. Prefer mathlib encodings where practical; keep the interface independent of any solver implementation.

### Normalization

Implement `normalizeToInteger : PolynomialCode → IntegerPolynomialQuery` (names may differ). It should:

1. enumerate the finite set of variable indices occurring in the sparse code and relabel them densely into a finite arity;
2. compute a positive common denominator for all encoded rational coefficients;
3. multiply by that denominator to produce integer coefficients.

Prove the semantic equivalence:

```lean
theorem normalizeToInteger_preserves_roots (p : PolynomialCode) :
  RationalPolynomialHasRoot p ↔ IntegerPolynomialHasRationalRoot (normalizeToInteger p)
```

The normalization must be computable (primitive recursive if the chosen encodings support that proof). Include the zero polynomial, nonzero constants, repeated variable occurrences, duplicate terms, and a sparse variable label such as `37` in small Lean examples.

### Oracle composition

For a hypothesis giving a real computable H10(Q) oracle over the new finite-arity integer query type, prove:

```lean
theorem rationalRoot_computable_of_h10Q
    (oracle : ComputablePred IntegerPolynomialHasRationalRoot) :
    ComputablePred RationalPolynomialHasRoot

theorem constraintSystem_computable_of_h10Q
    (oracle : ComputablePred IntegerPolynomialHasRationalRoot) :
    ComputablePred H10RationalCompiler.Satisfies
```

Also derive the indexed form for any computable generator of DNF constraint systems from `(input, index)`. These are conditional computability theorems: do not assert that the H10(Q) oracle exists.

## Acceptance criteria

- The normalization is total and computable on every `PolynomialCode`.
- The root-preservation theorem proves both directions, including finite-support extension and restriction between `Nat → ℚ` and `Fin n → ℚ` assignments.
- Clearing denominators uses a provably nonzero common denominator and preserves zero sets over `ℚ`.
- The new oracle corollary composes with the existing `constraintSystem_computable` and indexed theorem without classical decidability standing in for computability.
- The query type has a `Primcodable` encoding, and its arity/support invariant is checked by construction or proved.
- Add the new module to the Lake build, `Audit.lean`, and `verify.sh`. The audit should display theorem types and axioms for the normalization and oracle-composition results.
- No `sorry`, custom axioms, `unsafe`, or toolchain/dependency revision changes.
- After implementation, `bash verify.sh` succeeds from the pinned baseline; record the exact toolchain, cache/network assumptions, and `leanchecker` scope in `VALIDATION.md`.

## Out of scope

- A syntax tree for arbitrary quantifier-free Boolean formulas and its conversion to DNF. The current compiler's DNF representation remains the input contract for this slice.
- Constructing the paper's indexed constraint generator from `(f, n)`, Skolemizing its ring theory, or proving that the generated tests are equivalent to integer solvability.
- Proving `passes` or `complete` in `FiniteTestInterface`, integer undecidability via DPRM, compactness, pole parity, valuation coarsening, elliptic-curve results, prime patterns, or the height estimate.
- Implementing or assuming an actual H10(Q) decision algorithm.

## Coordination and handoff

- Agree on the finite-arity query encoding and normalization theorem signature before parallel proof work. Keep one owner for shared syntax and normalization definitions.
- Independent tasks may review finite-support relabeling, denominator clearing, or mathlib computability encodings against the agreed API.
- The handoff should report changed files, theorem signatures completed, build and audit evidence, and the exact remaining gap before the paper's test generator can instantiate `FiniteTestInterface.effective`.
