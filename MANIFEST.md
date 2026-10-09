# Next Slice Manifest: Proof-Risk Checkpoint Before Further H10(Q) Formalization

**Status:** the formalization progress below remains in place: generated
formulas are proved correct for the coded finite-test semantics, while the
Skolemization bridge to original prenex axioms and the paper-specific inputs
and effective instantiation remain open. The targeted mathematical review
below was completed on 2026-10-09. It found no concrete discrepancy in the
Section 2 reduction from successful finite tests to an integer root, conditional
on its arithmetic inputs. The Section 3 Selmer-to-point deduction is also
correct conditional on its descent lemma and the cited pointwise 2-converse.
Those external theorem proofs and the Section 4 five-point height estimate
remain independently unverified. Defer routine compiler work while the next
slice audits these proof dependencies.

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

## Completed checkpoint: targeted mathematical risk review (2026-10-09)

This was a read-only triage review, not a claim that the H10(Q) theorem has
been fully verified. No concrete counterexample or internal discrepancy was
found in the inspected reduction chain. The conditional and unresolved
boundaries are recorded below.

### Gate 1: Section 3's Selmer-to-point step

**Finding: checked conditionally; cited proof unresolved.** The cited
September 24, 2026 *Pointwise 2-converse* Theorem 1.1 assumes nonzero rational
2-torsion and full `2^∞`-Selmer corank in `{0, 1}`. These hypotheses match
`E_l`. Given the descent lemma's `dim_F2 Sel_2(E_l) = 3`, the Kummer sequence
gives `rank(E_l) + dim_F2 Sha(E_l)[2] = 1`. If `t` is the corank of
`Sha(E_l)[2^∞]`, then `t ≤ dim_F2 Sha(E_l)[2]`, so the full Selmer corank is
at most one. The cited theorem then gives finite `Sha`; the perfect alternating
Cassels--Tate pairing makes `dim_F2 Sha[2]` even. The displayed equality
therefore forces rank one and `Sha[2] = 0`, so `gamma = (beta, 1)` comes from
a rational point with the required `x`-coordinate square class.

This verifies the use of the theorem statement conditional on the descent
lemma. The proof of the cited theorem has not been independently reviewed, nor
has every step constructing a parameter satisfying the descent lemma been
re-proved. A citation or Lean encoding is not validation of those results.

Sources: [pinned H10 Section 3](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-September-24-2026/build/sections/03-parity.tex#L2410-L2530)
and [Pointwise 2-converse](https://github.com/openai/math/blob/main/preprints/A-pointwise-2-converse-for-elliptic-curves-with-rational-two-torsion-September-24-2026/paper.pdf).

### Gate 2: Section 2's all-tests-to-integer-root implication

**Finding: conditional reduction inspected; principal arithmetic input
unresolved.** The compactness construction, valuation coarsening, paired
elliptic/logarithm comparison, divisibility of the fixed error by the contact
radical, and final height contradiction are internally consistent on the
stated inputs. The fixed root error `delta` is reused for every ring element;
choosing `K` relative to `deg(f)` then gives the uniform linear-in-`B` height
bound needed to force the root indices into an ordinary finite interval. The
final use of additivity and injectivity does not require the index map to
preserve multiplication. No concrete discrepancy was found in this chain.

The first major unresolved dependency in the core reduction is the five-point
height estimate in Section 4, which Section 2 needs with constants and
exponent uniform in the rational point. Its non-CM proof invokes a separate
result claiming odd-regular Fontaine--Mazur modularity at 2. The H10 paper
checks the stated representation hypotheses for that invocation, but this
review did not audit that theorem's proof or the full height argument. The
prime-pattern sieve supplying the
ordinary integer model is another required input whose full proof was not
independently audited. Thus the reduction's conditional logic is not an
independent verification of the arithmetic theorem.

**Recommendation:** redirect the next effort to an independent review of the
Section 4 height estimate, beginning with its dyadic modularity dependency,
and the cited pointwise 2-converse proof. If those checks support continuing,
the compiler slice below remains appropriately scoped as syntax and finite-test
semantics work; it must not be presented as validation of the arithmetic
claims.

Sources: [pinned Section 2 reduction](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-September-24-2026/build/sections/02-reduction.tex),
[pinned Section 4 height argument](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-September-24-2026/build/sections/04-height.tex),
and [Fontaine--Mazur modularity at 2](https://github.com/openai/math/blob/main/preprints/Fontaine-Mazur-modularity-at-the-prime-2-September-23-2026/paper.pdf).

The missing numerical entries for `M` and `D_m` in Section 3 are not by
themselves a risk gate: the paper gives an existence argument by weak
approximation, and any fixed lists satisfying the coverage conditions can
serve. Constructing and formalizing certified choices remains follow-on work.

### Next-step handoff

The targeted risk review is complete. Before resuming compiler work,
independently review the cited pointwise 2-converse proof and the Section 4
five-point height argument, starting with its dyadic modularity dependency.
Keep the prime-pattern sieve as a separate unresolved input unless it is also
audited. Record each result as checked, discrepancy found, or unresolved, and
give a continue-or-redirect recommendation. Keep manuscript assertions, the
correctness of their use, and independently verified results distinct.

## Follow-on compiler objective (deferred pending external proof review)

Do not resume this work until the proof-risk review above gives a continue
signal. The compiler milestone remains independent of the truth of the
arithmetic `passes` and `complete` obligations, but its completion would not
resolve the currently unverified theorem dependencies.

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
