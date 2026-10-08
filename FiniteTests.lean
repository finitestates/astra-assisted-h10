module

public import Mathlib.Computability.RE

/-!
# The final computability argument for Hilbert's tenth problem over Q

This file formalizes the FINAL LOGICAL REDUCTION ONLY. It does not construct the
paper's arithmetic tests and does not prove undecidability over Q unconditionally.

`ComputablePred` is mathlib's actual computability predicate, not merely
`DecidablePred`. The distinction is essential: classical decidability alone
does not provide an algorithm.

Inputs are abstract, effectively encoded objects. They can later be instantiated
with codes for polynomials once those encodings and the arithmetic interface
have been formalized. All outstanding ingredients are theorem parameters.

Reference: OpenAI, "Hilbert's tenth problem over the rational numbers",
September 24, 2026, section 2, final proof of the main theorem.
Project initiated by the user; Lean development by the OpenAI assistant.
-/

@[expose] public section

namespace H10FiniteTests

variable {α : Type*} [Primcodable α]

/-- Searching natural-number witnesses to a computable relation is a
semidecision procedure. The search may diverge exactly when no witness exists. -/
theorem re_exists_nat_of_computable
    (p : α → ℕ → Prop)
    (hp : ComputablePred (fun z : α × ℕ => p z.1 z.2)) :
    REPred (fun a => ∃ n, p a n) := by
  obtain ⟨inst, hcomp⟩ := hp
  let : DecidablePred (fun z : α × ℕ => p z.1 z.2) := inst
  let : DecidableRel p := fun a n => inst (a, n)
  have hsearch : Partrec (fun a => Nat.rfind (fun n => Part.some (decide (p a n)))) :=
    Partrec.rfind hcomp.partrec
  apply hsearch.dom_re.of_eq
  intro a
  constructor
  · intro h
    obtain ⟨n, hn, _⟩ := Nat.rfind_dom.mp h
    exact ⟨n, by simpa using hn⟩
  · rintro ⟨n, hn⟩
    exact Nat.rfind_dom.mpr ⟨n, by simpa using hn, fun {_} _ => trivial⟩

omit [Primcodable α] in
/-- If membership in `P` implies that all tests pass, while passing all tests
implies membership, nonmembership is equivalent to a finite failed test.
No bound on the index of the failed test is assumed. -/
theorem failure_iff_not
    (P : α → Prop) (test : α → ℕ → Prop)
    (passes : ∀ a, P a → ∀ n, test a n)
    (complete : ∀ a, (∀ n, test a n) → P a)
    (a : α) :
    (∃ n, ¬ test a n) ↔ ¬ P a := by
  classical
  constructor
  · rintro ⟨n, hn⟩ ha
    exact hn (passes a ha n)
  · intro ha
    by_contra h
    apply ha
    apply complete a
    intro n
    by_contra hn
    exact h ⟨n, hn⟩

/-- A computable family of tests with the stated equivalence semidecides the
complement of `P`: search for a test that fails. -/
theorem complement_re_of_tests
    (P : α → Prop) (test : α → ℕ → Prop)
    (test_comp : ComputablePred (fun z : α × ℕ => test z.1 z.2))
    (passes : ∀ a, P a → ∀ n, test a n)
    (complete : ∀ a, (∀ n, test a n) → P a) :
    REPred (fun a => ¬ P a) := by
  have hfail := re_exists_nat_of_computable (fun a n => ¬ test a n) test_comp.not
  exact hfail.of_eq (failure_iff_not P test passes complete)

/-- The two-search argument: a semidecision procedure for membership and
a computable finite-test family together give a total computable decision
procedure. Mathlib's Post theorem supplies the dovetailing of the two searches. -/
theorem computable_of_re_and_tests
    (P : α → Prop) (test : α → ℕ → Prop)
    (positive_re : REPred P)
    (test_comp : ComputablePred (fun z : α × ℕ => test z.1 z.2))
    (passes : ∀ a, P a → ∀ n, test a n)
    (complete : ∀ a, (∀ n, test a n) → P a) :
    ComputablePred P := by
  exact ComputablePred.computable_iff_re_compl_re'.2
    ⟨positive_re, complement_re_of_tests P test test_comp passes complete⟩

variable {β : Type*} [Primcodable β]

/-- Explicit boundary between the arithmetic paper and this formalized logical
argument. `effective` says a genuine decision algorithm for `Q` would decide
the tests UNIFORMLY in both the input and the test index. It is an assumption
about a compiler/query interface, not an assertion that `Q` is computable. -/
structure FiniteTestInterface (P : α → Prop) (Q : β → Prop) where
  test : α → ℕ → Prop
  effective : ComputablePred Q → ComputablePred (fun z : α × ℕ => test z.1 z.2)
  passes : ∀ a, P a → ∀ n, test a n
  complete : ∀ a, (∀ n, test a n) → P a

/-- Conditional decision transfer. The arithmetic interface is not supplied
by this project; it remains an explicit input to the theorem. -/
theorem decision_transfer
    (P : α → Prop) (Q : β → Prop)
    (positive_re : REPred P)
    (interface : FiniteTestInterface P Q) :
    ComputablePred Q → ComputablePred P := by
  intro hQ
  exact computable_of_re_and_tests P interface.test positive_re
    (interface.effective hQ) interface.passes interface.complete

/-- Final contradiction: an undecidable, semidecidable source problem and
the stated finite-test interface force the target problem to be undecidable.
This is a conditional theorem, not an unconditional proof of H10(Q). -/
theorem undecidable_target
    (P : α → Prop) (Q : β → Prop)
    (positive_re : REPred P)
    (source_undecidable : ¬ ComputablePred P)
    (interface : FiniteTestInterface P Q) :
    ¬ ComputablePred Q := by
  intro hQ
  exact source_undecidable (decision_transfer P Q positive_re interface hQ)

end H10FiniteTests
