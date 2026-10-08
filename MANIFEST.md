# Next Slice Manifest: Finite Ground-Test Compiler

**Status:** next proposed implementation slice

**Repository baseline:** abstract finite-test reduction in `FiniteTests.lean`,
rational DNF compiler in `RationalQueryCompiler.lean`, finite-arity integer
query adapter in `IntegerQueryAdapter.lean`, and Boolean formula front end in
`BooleanFormula.lean`.

**Pinned toolchain:** `leanprover/lean4:v4.35.0-rc4`; mathlib revisions are
recorded in `lakefile.toml` and `lake-manifest.json`.

## Current state

The generic final computability argument is formalized conditionally on an
abstract `FiniteTestInterface`. The rational compiler handles finite DNF
systems, and the integer-query adapter preserves rational roots while
normalizing to finite-arity integer queries. `BooleanFormula.lean` adds
postfix-coded Boolean formulas over the existing equation and disequation
atoms, with total semantics, a primitive-recursive conversion to DNF, a
correctness proof, and conditional formula-oracle composition theorems.

The recorded verification for this baseline is in [VALIDATION.md](VALIDATION.md).
It passed on 2026-10-08 with the pinned toolchain available through
`/tmp/h10-elan/bin`. In a fresh environment, check toolchain availability and
run `bash verify.sh` before editing. Do not change Lean or mathlib pins to make
setup easier.

The paper's particular recursive ring theory, Skolemization, ground-term
enumeration, and finite-test generator are not formalized. The abstract
interface's `effective`, `passes`, and `complete` fields therefore remain
uninstantiated for the paper.

## Objective

Build the effective finite-test pipeline from the paper's recursive
first-order construction to the existing formula language. For an encoded
nonconstant integer polynomial `f` and finite-test index `n`, generate a
`H10RationalFormula.ConstraintFormula` whose satisfiability is the `n`th
finite rational test from Section 2 of the paper.

The generated constraint should encode the relevant finite ground instances,
including the ring-operation and functionality constraints, universal axiom
instances, and auxiliary witnesses required by the positive-existential
condition. Use fresh natural-number variable names for term values and
existential witnesses. Keep all polynomial semantics in the existing sparse
code and atom representation.

This slice should establish effective, uniform test generation and connect it
to the existing conditional H10(Q) oracle theorem. It should not try to prove
the arithmetic truth of the tests.

## Formalization contract

### Effective syntax and enumeration

Choose explicit effectively encoded types for the paper's required ring
signature, terms, and quantifier-free formulas, or use a generic encoded
signature if that keeps the construction reusable. Formalize the recursive
axiom scheme and its Skolemized universal form. Make the coding of function
symbols, arities, terms, and formulas explicit; avoid treating an informal
enumeration or Skolemization procedure as an oracle.

Define a computable enumeration of ground terms and of the finite constraints
attached to each index. State the convention precisely: for example, whether
test `n` is the first `n` constraints or the first `n` ground instances, and
ensure the convention covers every required constraint as `n` varies.

### Translation to rational polynomial formulas

Translate each finite constraint fragment to the existing Boolean formula
code over polynomial equations and disequations. Handle equal-input
functionality conditions, fixed rational coefficients, and existential
witnesses by assigning fresh variable labels. Prove that satisfiability of
the generated formula is equivalent to solvability of the corresponding
finite rational constraint fragment.

The key computability result should have this shape (names may differ):

```lean
def makeFiniteTestFormula : IntegerPolynomialQuery → Nat → ConstraintFormula

theorem makeFiniteTestFormula_computable :
    Computable₂ makeFiniteTestFormula

theorem makeFiniteTestFormula_correct (f : IntegerPolynomialQuery) (n : Nat) :
    FormulaSatisfies (makeFiniteTestFormula f n) ↔
      PaperFiniteTestSolvable f n
```

Then derive the uniform conditional decision result using
`H10RationalFormula.indexed_formulaSatisfies_computable_of_h10Q`. Keep the
integer root oracle as an explicit hypothesis.

Handle constant polynomials explicitly or restrict the generator's input to
nonconstant polynomials with that restriction stated in its type. The paper
dispatches constant polynomials separately.

## Acceptance criteria

- Signature, term, formula, axiom, and ground-instance codes have explicit
  effective encodings.
- The Skolemized theory and finite ground-constraint enumeration are produced
  by a computable procedure, uniformly in `f` and `n`.
- Every generated variable label is fresh where needed and all witnesses are
  included in the existential rational assignment represented by
  `FormulaSatisfies`.
- Translation correctness proves both directions between the generated
  formula and the specified finite rational test.
- The generator is `Computable₂`; prove `Primrec` when the selected coding
  supports it without distorting the syntax.
- The existing indexed formula-oracle theorem decides the generated tests
  conditionally on the finite-arity integer H10(Q) oracle.
- Add the module to the Lake build, `Audit.lean`, and `verify.sh`; audit theorem
  types and axioms. Include small examples for term evaluation, function
  congruence, an axiom instance, and fresh existential witnesses.
- No `sorry`, custom axioms, `unsafe`, or toolchain/dependency revision
  changes. Run `bash verify.sh` after implementation and update
  `VALIDATION.md` with exact evidence and limits.

## Out of scope

- Proving that integer solutions pass every test (`FiniteTestInterface.passes`).
- Proving that success of all tests forces an integer solution
  (`FiniteTestInterface.complete`). This contains the compactness, pole
  parity, valuation, elliptic-curve, and height arguments.
- Formalizing the arithmetic inputs from the paper's later sections, including
  prime patterns, elliptic rank and local comparisons, pole parity, or the
  five-point height estimate.
- Proving integer undecidability via DPRM or constructing an actual H10(Q)
  decision algorithm.
- Optimizing DNF expansion or changing the established polynomial encodings.

## Coordination and handoff

- Keep the next slice on effective syntax, finite-instance generation, and
  translation correctness. Leave the arithmetic `passes` and `complete`
  proofs as explicit later milestones.
- Settle term, formula, and fresh-variable conventions before parallel work;
  keep one owner for their shared encodings.
- Report changed files, completed theorem signatures, validation evidence,
  and the remaining gap before `FiniteTestInterface` can be instantiated for
  the paper.
