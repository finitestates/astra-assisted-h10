# A checked final reduction for the H10(Q) project

**Status: six Lean theorems compiled successfully. The final conditional logical
implication is checked; the paper's arithmetic construction is not formalized
here.**

This is a small formalization of the concluding argument in the September 24,
2026 paper *Hilbert's tenth problem over the rational numbers*, hosted in
[openai/math](https://github.com/openai/math). It does not establish Hilbert's
tenth problem over the rationals on its own, and it does not certify the
correctness of the paper.

## The argument in ordinary language

Write `P(f)` for “the polynomial f has an integer solution.” Suppose a proposed
family of tests has these properties:

1. If f has an integer solution, every test passes.
2. If every test passes, f has an integer solution.
3. Given a rational-solvability algorithm, one algorithm can decide test n for
   any input f and any natural number n.

Now imagine that rational-solvability algorithm exists. Search for an integer
solution while also searching for a failed test. Give each search successive
finite amounts of running time. If an integer solution exists, the first search
eventually finds it. If there is none, property 2 implies that some test fails,
so the second search eventually finds a failure. Property 1 ensures that a
failed test is a valid negative answer.

Together these searches decide integer solvability. If integer solvability is
undecidable, the assumed rational algorithm cannot exist.

The Lean proof uses mathlib's existing Post theorem to combine the two searches.
It proves the failed-test search is a legitimate semidecision procedure. There
is no required computable bound on the first failing index.

## What Lean checks

The file [FiniteTests.lean](FiniteTests.lean) works with abstract encoded inputs.

| Lean declaration | Meaning |
| --- | --- |
| `re_exists_nat_of_computable` | Search over natural-number witnesses to a computable relation recognizes exactly the inputs that have a witness. |
| `failure_iff_not` | Some test fails exactly when the source property is false, assuming both directions of the test characterization. |
| `complement_re_of_tests` | Uniformly decidable tests give a search recognizing negative source instances. |
| `computable_of_re_and_tests` | Searches recognizing positive and negative instances give a total decision algorithm. |
| `decision_transfer` | The interface transfers target decidability to source decidability. |
| `undecidable_target` | If the source is also undecidable, the target is undecidable. |

`ComputablePred` means that an actual computable decision function exists.
`REPred` means that a search halts exactly on positive instances; it may run
forever on negative ones. `Primcodable` supplies the effective encodings used
by mathlib's computability framework. These notions are stronger than simply
asking Lean to assign a truth value using classical logic.

The main theorem has this shape; its parameters are essential:

```lean
theorem undecidable_target
    (P : α → Prop) (Q : β → Prop)
    (positive_re : REPred P)
    (source_undecidable : ¬ ComputablePred P)
    (interface : FiniteTestInterface P Q) :
    ¬ ComputablePred Q
```

## What remains to connect this to the paper

The record `FiniteTestInterface` collects obligations; this project does **not**
construct a value of that record for integer and rational polynomial solvability.

| Required ingredient | Status here |
| --- | --- |
| Effective encodings of integer- and rational-solvability instances | Not supplied; `α` and `β` are abstract. |
| Integer-solvability witness search (`positive_re`) | A hypothesis. The generic witness-search lemma is proved, but polynomial evaluation and tuple enumeration are not instantiated. |
| Integer undecidability (`source_undecidable`, intended to come from DPRM) | A hypothesis, not a formalized use of the DPRM theorem. |
| The paper's indexed tests (`interface.test`) | An input to the interface; no polynomial systems or query syntax are built here. |
| Effective test generation and evaluation (`interface.effective`) | A hypothesis that target computability implies uniform computability of the tests. No rational-query compiler or oracle machine is constructed. |
| Integer solutions pass every test (`interface.passes`) | A hypothesis; its arithmetic proof remains to be formalized. |
| Passing all tests yields an integer solution (`interface.complete`) | A hypothesis; the compactness, valuation, elliptic-curve, and height arguments remain to be formalized. |

Although the interface is named “finite tests,” its definition permits any
natural-number-indexed predicate family with the stated properties. Finiteness
of the paper's individual constraint systems belongs to the missing arithmetic
and compiler implementation.

Uniformity matters: one effective procedure must handle the pair `(f, n)`.
Separate decision procedures for each fixed n are insufficient. The paper
handles constant polynomials separately; a concrete instantiation must include
that case or justify restricting to nonconstant polynomials.

These are missing formalizations, not claims that the corresponding informal
mathematics is wrong. Completing them could require substantial additional work.

## Reproduce the check

Install Lean's usual `elan` toolchain manager, unzip this directory, and run:

```sh
bash verify.sh
```

The script downloads the relevant mathlib cache, builds both Lean files,
prints theorem types and axiom dependencies, and replays this project's proof
declarations through Lean's kernel. It requires network access for dependencies.

Pinned versions:

- Lean: `leanprover/lean4:v4.35.0-rc4`
- mathlib: `62bf13aabd0db1bf4cbe2a6ec087c6f7a677f448`
- Transitive dependency revisions: `lake-manifest.json`

See [VALIDATION.md](VALIDATION.md) for successful checks, their scope, and the
restoration of these files after workspace maintenance. No toolchain, dependency
cache, or generated `.olean` files are bundled.

## Source and credit

The mathematical reduction comes from the paper and standard computability
theory. No new number-theoretic result is claimed. See
[CONTRIBUTIONS.md](CONTRIBUTIONS.md) for the division of work.

Paper snapshot:
[section 2 at commit fd4aeeb](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-September-24-2026/build/sections/02-reduction.tex).
The relevant conclusion follows `red:finite-test-success` and is the final
proof of the main theorem. Arithmetic effectiveness and integer-model claims
occur earlier in that section.

Existing search-combination theorem:
[`ComputablePred.computable_iff_re_compl_re'`](https://github.com/leanprover-community/mathlib4/blob/62bf13aabd0db1bf4cbe2a6ec087c6f7a677f448/Mathlib/Computability/RE.lean).
