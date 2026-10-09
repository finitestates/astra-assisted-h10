# Next Slice Manifest: Proof-Risk Checkpoint Before Further H10(Q) Formalization

**Status:** the formalization progress below remains in place: generated
formulas are proved correct for the coded finite-test semantics, while the
Skolemization bridge to original prenex axioms and the paper-specific inputs
and effective instantiation remain open. Given uncertainty about the new
paper's arithmetic proof, the immediate next slice is a read-only review of
its highest-leverage mathematical dependencies. Defer further routine compiler
lemmas until that review gives a useful continue-or-redirect signal.

**Repository baseline:** the abstract reduction in `FiniteTests.lean`, rational
DNF compiler in `RationalQueryCompiler.lean`, finite-arity integer query
adapter in `IntegerQueryAdapter.lean`, Boolean formula front end in
`BooleanFormula.lean`, and generic ground-test scaffold in
`FiniteGroundTests.lean`.

**Pinned toolchain:** `leanprover/lean4:v4.35.0-rc4`; mathlib revisions are
recorded in `lakefile.toml` and `lake-manifest.json`.

## Current state

`FiniteGroundTests.lean` has postfix term and quantifier-free formula codes,
validity predicates, a total term evaluator, generic prenex Skolemization,
fresh labels for positive-existential witnesses, a decoder that enumerates
every constraint item, and translations for the finite constraint families.
It now defines assignment-based semantics independently of the generated DNF
and proves pointwise correctness for the root and every item tag, including
ring operations, function congruence, universal instances of the coded
Skolemized theory, and positive-existential witnesses. Consequently,
`makeFiniteTestFormula_correct` proves equivalence with the independent
`PaperFiniteTestSolvable` predicate without a translator-correctness premise.
The finite-prefix stream includes the root equation and the first `n` decoded
items. The validity predicates are defined, but no theorem yet proves that the
paper's proposed input codes satisfy them. The universal-item semantics checks
the coded Skolemized matrix; equivalence between that and the original prenex
axiom's quantified meaning remains to be proved.

The term evaluator, item decoder, root formula translator, ring-operation
formula translator, Skolem-term and prefix builders, and term and QF-token
substitution steps are primitive recursive. The complete `skolemizeAxiom`, QF
formula translator, function-congruence and witness translators, and one-item
formula translator still lack primitive-recursiveness proofs. The root
translation expands the natural scale of each integer coefficient by
repeating its polynomial term, and its semantic equivalence to the finite-arity
integer polynomial is preserved. The recursive ring theory has not been
instantiated. `poleParityFormula choices` compiles the paper's Section 3
positive-existential formula for a supplied finite list of rational coefficient
pairs `(m, m_d)`. The pinned paper does not provide numerical entries for
`M` or `D_m`; Section 3 proves their existence by weak approximation and says
to fix those lists independently of the input. The code does not yet formalize
their local coverage properties, prove finite choices exist, or instantiate
`poleParityFormula` with certified choices. See the pinned [Section 3
argument](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-September-24-2026/build/sections/03-parity.tex#L106-L132)
and [Section 2](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-September-24-2026/build/sections/02-reduction.tex#L423-L429).
The coverage statement to encode is: for every nonzero rational `b`, some
`m ∈ M` has `m*b > 0`, is a square in `Q₂`, and has even 3-adic valuation
with nonsquare 3-adic unit part; for each such fixed `m`, with
`S(m) = {2, 3} ∪ Supp(m)`, every nonzero `b` has some `m_d ∈ D_m` such that
`m_d*b > 0` and `m_d*b` is a square in `Q_q` for every `q ∈ S(m)`. These
properties choose a disjunct for an integer input; they are not extra
conjuncts of the positive-existential formula.

The indexed H10(Q)-oracle result therefore still takes formula-generator
computability as a premise. The paper-facing theory, complete computability
proof, constant-polynomial dispatch, and the arithmetic `passes` and
`complete` obligations remain open. On 2026-10-08, `bash verify.sh` and
`bash ci/audit-modules.sh` both passed with the pinned toolchain. Do not change
the pinned Lean or mathlib revisions.

## Immediate objective: targeted mathematical risk review

Review the cited Section 3 dependency and the central Section 2 arithmetic
chain before investing further effort in lower-risk compiler details. This is
a bounded triage review, not a claim that the H10(Q) theorem has been fully
verified.

### Gate 1: Section 3's Selmer-to-point step

- Read the H10 paper's `par:global-point` argument and Theorem 1.1 of the
  cited *Pointwise 2-converse* paper. Confirm the exact theorem version and
  hypotheses used.
- Check the H10 paper's derivation of full 2-power Selmer corank at most one
  for `E_l`, and trace how finite `Sha`, the Cassels--Tate pairing, and the
  Selmer class `gamma = (beta, 1)` yield the required rational point.
- Distinguish a correct application of the cited theorem from an independent
  check of that theorem's proof. Record the latter as unresolved unless it is
  actually reviewed; do not treat citation or Lean encoding as validation.

Sources: [pinned H10 Section 3](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-September-24-2026/build/sections/03-parity.tex#L2410-L2530)
and [Pointwise 2-converse](https://github.com/openai/math/blob/main/preprints/A-pointwise-2-converse-for-elliptic-curves-with-rational-two-torsion-September-24-2026/paper.pdf).

### Gate 2: Section 2's all-tests-to-integer-root implication

- Trace the paper's `complete` argument from success of every finite test to
  an integer root, following its compactness and nonstandard-model step,
  local elliptic/logarithm comparisons, uniform height bound, and final
  ordinary-integer conclusion.
- Identify the first substantive lemma or dependency whose hypotheses,
  uniformity, or conclusion cannot be independently checked from the stated
  argument. Record a concrete gap or counterexample if one is found; otherwise
  state precisely which parts were checked and which remain open.

Source: [pinned Section 2 reduction](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-September-24-2026/build/sections/02-reduction.tex).

The missing numerical entries for `M` and `D_m` in Section 3 are not by
themselves a risk gate: the paper gives an existence argument by weak
approximation, and any fixed lists satisfying the coverage conditions can
serve. Constructing and formalizing certified choices remains follow-on work.

### Review handoff

Produce a concise dependency map with each gate marked checked, discrepancy
found, or unresolved, and give a recommendation to continue the formalization
as scoped below or redirect effort to a proof gap. Keep manuscript assertions,
the correctness of their use, and independently verified results distinct.

## Follow-on compiler objective (if the risk review supports continuing)

Finish the effective finite-test compiler as a paper-facing construction.
Specify the meaning of a finite test independently of its generated formula,
prove both directions of the translation, and instantiate the generic input
with the recursive theory from Section 2 and the positive-existential formula
from Section 3 used by that reduction.
Derive computability of the resulting `(query, test-index)` generator rather
than leaving it as a premise. Keep the H10(Q) oracle explicit and do not try to
prove the arithmetic truth of the tests in this slice.

## Follow-on formalization contract

### Syntax and semantics

- State validity conditions for term, formula, prenex-axiom, and
  positive-existential codes. Total fallback behavior may remain for malformed
  codes, but paper-facing correctness claims must be restricted to valid
  encodings.
- Give an independent semantic definition of each finite constraint item:
  zero and one, ring operations, function congruence, universal axiom
  instances, and positive-existential witnesses. Keep witness variables
  separate from the ground-term values, as in the paper.
- Prove semantic correctness for term evaluation, quantifier-free translation,
  Skolemization, and each constraint-item translator. The finite-test theorem
  must be about this independent semantic definition, not a predicate defined
  as satisfiability of `finiteTestDNF`.
- Prove the finite-prefix convention precisely: test `n` contains the root
  equation and the first `n` enumerated constraints, and every required paper
  constraint occurs in some prefix.

### Paper inputs and computability

- Encode the paper's recursive ring-theory axiom scheme in the selected
  syntax, and prove it composes with the existing query-specific root
  constraint. Encode the positive-existential formula with its fixed rational
  coefficients cleared or represented effectively.
- Prove the input encodings valid and their generators primitive recursive (or
  computable if primitive recursiveness is a poor fit).
- Prove the actual root and one-item translators primitive recursive for
  these inputs, then derive a uniform theorem of the form:

  ```lean
  theorem makeFiniteTestFormula_computable :
      Computable₂ makeFiniteTestFormula
  ```

- Prove that the generated formula is satisfiable exactly when the
  independently specified Section 2 finite rational test is solvable. Use
  that theorem to derive the indexed decision result conditionally on
  `IntegerPolynomialHasRationalRoot` being computable.
- Handle constant polynomial inputs explicitly or state and enforce a
  nonconstant-input restriction in the formal type, matching the paper's
  dispatch.

## Acceptance criteria for follow-on compiler work

- The semantic finite-test predicate is independent of the generated DNF and
  formula.
- Translation correctness covers the root constraint and every finite-test
  item, including both directions and the fresh auxiliary witnesses.
- The paper-specific theory and positive-existential input are encoded and
  shown effective; no opaque axiom-scheme or formula-computability premise is
  left in the final generator theorem.
- Every valid required constraint appears in some finite prefix.
- The generated formula is uniformly computable in the polynomial query and
  test index, and the existing indexed formula-oracle theorem gives the
  conditional decision result with the H10(Q) oracle explicit.
- Add the necessary examples and theorem-type/axiom audit entries. No `sorry`,
  custom axioms, `unsafe`, or toolchain/dependency revision changes. Run
  `bash verify.sh` and update `VALIDATION.md` with exact evidence and limits.

## Out of scope for the review and compiler milestone

- Formalizing or proving in Lean that integer solutions pass every test
  (`FiniteTestInterface.passes`) or that success of all tests forces an
  integer solution (`FiniteTestInterface.complete`). The review may inspect
  the manuscript's latter argument, but it does not formalize or reprove it.
- Proving the integer undecidability result via DPRM or constructing an actual
  H10(Q) decision algorithm.
- Optimizing DNF expansion or changing the established polynomial encodings.

## Coordination and handoff

Keep one owner for the shared syntax and its validity/semantic conventions.
First report the risk-review findings and the checked-versus-unresolved
boundary. If work continues, report changed files, completed theorem
signatures, validation evidence, and the remaining gap before formalizing the
arithmetic `passes` and `complete` obligations. The present generic scaffold
is useful progress, but it does not validate the paper's number-theoretic
claims.
