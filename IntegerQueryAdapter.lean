module

public import RationalQueryCompiler
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Finite-arity integer queries for the rational constraint compiler

The source compiler uses sparse rational coefficients and variables named by
`Nat`.  This file turns that syntax into a sparse integer polynomial whose
variables are indexed by a finite arity.  Integer coefficients are stored in
factored form: a list of integer numerator factors and one natural scale.  The
denotation of each such code is an integer, while keeping normalization purely
primitive recursive on the existing coefficient encoding.
-/

@[expose] public section

namespace H10RationalQueryAdapter

open H10RationalCompiler

abbrev IntegerCoefficientCode := List Int × Nat
abbrev IntegerTermCode := IntegerCoefficientCode × MonomialCode
abbrev IntegerPolynomialCode := List IntegerTermCode
abbrev IntegerPolynomialQuery := Nat × IntegerPolynomialCode

/-- The rational value of the integer represented by a factored coefficient. -/
def integerCoefficientValue (c : IntegerCoefficientCode) : ℚ :=
  (c.1.map (Int.cast : Int → ℚ)).prod * c.2

def integerCoefficientAsInt (c : IntegerCoefficientCode) : Int :=
  c.1.prod * c.2

theorem intListProduct_cast (xs : List Int) :
    (xs.map (Int.cast : Int → ℚ)).prod = (xs.prod : ℚ) :=
  (Int.cast_list_prod xs).symm

theorem integerCoefficientValue_eq_intCast (c : IntegerCoefficientCode) :
    integerCoefficientValue c = (integerCoefficientAsInt c : ℚ) := by
  simp only [integerCoefficientValue, integerCoefficientAsInt]
  rw [intListProduct_cast]
  push_cast
  ring

def finiteVariableValue (arity : Nat) (x : Fin arity → ℚ) (index : Nat) : ℚ :=
  if h : index < arity then x ⟨index, h⟩ else 0

def integerMonomialValue (arity : Nat) (x : Fin arity → ℚ)
    (m : MonomialCode) : ℚ :=
  (m.map fun ie => finiteVariableValue arity x ie.1 ^ ie.2).prod

def integerTermValue (arity : Nat) (x : Fin arity → ℚ)
    (t : IntegerTermCode) : ℚ :=
  integerCoefficientValue t.1 * integerMonomialValue arity x t.2

def integerPolynomialValue (arity : Nat) (x : Fin arity → ℚ)
    (p : IntegerPolynomialCode) : ℚ :=
  (p.map (integerTermValue arity x)).sum

/-- An integer polynomial query consists of a finite arity and sparse terms.
Every variable code is interpreted as a `Fin arity` variable when it is below
the arity, and as zero otherwise.  Normalized queries prove that every label
is in range; this total interpretation also gives malformed codes a denotation.
-/
def IntegerPolynomialHasRationalRoot (q : IntegerPolynomialQuery) : Prop :=
  ∃ x : Fin q.1 → ℚ, integerPolynomialValue q.1 x q.2 = 0

example : Primcodable IntegerPolynomialQuery := inferInstance

def allVariables (p : PolynomialCode) : List Nat :=
  p.flatMap fun t => t.2.map Prod.fst

/-- Add a variable to a list only when it has not already appeared. -/
def insertVariable (seen : List Nat) (i : Nat) : List Nat :=
  if decide (seen.idxOf i < seen.length) then seen else seen ++ [i]

/-- Collect used variable labels in first-occurrence order. -/
def uniqueVariables (xs : List Nat) : List Nat :=
  xs.foldl insertVariable []

def variableSupport (p : PolynomialCode) : List Nat :=
  uniqueVariables (allVariables p)

def coefficientDenominator (c : CoeffCode) : Nat :=
  (c.map fun a => a.2 + 1).prod

def globalDenominator (p : PolynomialCode) : Nat :=
  (p.map fun t => coefficientDenominator t.1).prod

def scaledIntegerCoefficientCode (denom : Nat) (c : CoeffCode) : IntegerCoefficientCode :=
  (c.map Prod.fst, denom / coefficientDenominator c)

def integerCoefficientCode (p : PolynomialCode) (c : CoeffCode) : IntegerCoefficientCode :=
  scaledIntegerCoefficientCode (globalDenominator p) c

def denseMonomial (support : List Nat) (m : MonomialCode) : MonomialCode :=
  m.map fun ie => (support.idxOf ie.1, ie.2)

/-- Normalize each coefficient by the product of all encoded denominators,
and relabel the finite support by first-occurrence indices.
-/
def normalizeToInteger (p : PolynomialCode) : IntegerPolynomialQuery :=
  let support := variableSupport p
  (support.length,
    p.map fun t => (integerCoefficientCode p t.1, denseMonomial support t.2))

theorem mem_insertVariable (seen : List Nat) (i a : Nat) :
    a ∈ insertVariable seen i ↔ a ∈ seen ∨ a = i := by
  by_cases h : i ∈ seen
  · have hi : seen.idxOf i < seen.length := List.idxOf_lt_length_iff.mpr h
    rw [insertVariable]
    simp only [hi]
    constructor
    · exact Or.inl
    · intro hmem
      rcases hmem with hmem | hmem
      · exact hmem
      · subst a
        exact h
  · have hi : ¬ seen.idxOf i < seen.length := by
      simpa [List.idxOf_lt_length_iff] using h
    have hdec : decide (seen.idxOf i < seen.length) = false := by simp [hi]
    have hresult : insertVariable seen i = seen ++ [i] := by
      simp [insertVariable, hdec]
    rw [hresult]
    simp [List.mem_append]

theorem mem_foldl_insertVariable (xs initial : List Nat) (a : Nat) :
    a ∈ xs.foldl insertVariable initial ↔ a ∈ initial ∨ a ∈ xs := by
  induction xs generalizing initial with
  | nil => simp
  | cons i xs ih =>
      rw [List.foldl_cons, ih, mem_insertVariable]
      simp [or_assoc, or_left_comm, or_comm]

@[simp]
theorem mem_uniqueVariables {xs : List Nat} {a : Nat} :
    a ∈ uniqueVariables xs ↔ a ∈ xs := by
  simp [uniqueVariables, mem_foldl_insertVariable]

theorem variableSupport_mem_iff (p : PolynomialCode) (i : Nat) :
    i ∈ variableSupport p ↔ i ∈ allVariables p := by
  simp [variableSupport]

theorem insertVariable_nodup {seen : List Nat} (i : Nat)
    (hseen : seen.Nodup) : (insertVariable seen i).Nodup := by
  by_cases hi : i ∈ seen
  · have hidx : seen.idxOf i < seen.length := List.idxOf_lt_length_iff.mpr hi
    simpa [insertVariable, hidx] using hseen
  · have hidx : ¬ seen.idxOf i < seen.length := by
      simpa [List.idxOf_lt_length_iff] using hi
    have hdec : decide (seen.idxOf i < seen.length) = false := by simp [hidx]
    have hresult : insertVariable seen i = seen ++ [i] := by
      simp [insertVariable, hdec]
    rw [hresult]
    rw [List.nodup_append]
    refine ⟨hseen, List.nodup_singleton i, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    intro hab
    exact hi (hab ▸ ha)

theorem nodup_foldl_insertVariable (xs initial : List Nat)
    (hinitial : initial.Nodup) : (xs.foldl insertVariable initial).Nodup := by
  induction xs generalizing initial with
  | nil => simpa using hinitial
  | cons i xs ih =>
      apply ih
      exact insertVariable_nodup i hinitial

theorem variableSupport_nodup (p : PolynomialCode) :
    (variableSupport p).Nodup := by
  exact nodup_foldl_insertVariable (allVariables p) [] (by simp [List.nodup_nil])

theorem variableSupport_index_lt (p : PolynomialCode) (i : Nat)
    (hi : i ∈ variableSupport p) :
    (variableSupport p).idxOf i < (variableSupport p).length := by
  exact List.idxOf_lt_length_iff.mpr hi

theorem variableSupport_index_mem (p : PolynomialCode) (i : Nat)
    (hi : i ∈ variableSupport p) :
    (variableSupport p)[(variableSupport p).idxOf i]'(variableSupport_index_lt p i hi) = i := by
  have hidx := variableSupport_index_lt p i hi
  exact List.getElem_idxOf hidx

theorem variableSupport_index_dense (p : PolynomialCode)
    (j : Fin (variableSupport p).length) :
    ∃ i, i ∈ variableSupport p ∧ (variableSupport p).idxOf i = j.val := by
  let support := variableSupport p
  let i := support.get j
  have hi : i ∈ support := List.get_mem support j
  have hidx : support.idxOf i < support.length := List.idxOf_lt_length_iff.mpr hi
  have hval : support[support.idxOf i]'hidx = support[j.val]'j.isLt := by
    calc
      support[support.idxOf i]'hidx = i := List.getElem_idxOf hidx
      _ = support.get j := rfl
      _ = support[j.val]'j.isLt := List.get_eq_getElem
  have hpos := (variableSupport_nodup p).getElem_inj.mp hval
  exact ⟨i, hi, hpos⟩

theorem coefficientDenominator_pos (c : CoeffCode) :
    0 < coefficientDenominator c := by
  induction c with
  | nil => simp [coefficientDenominator]
  | cons a c ih =>
      simp only [coefficientDenominator, List.map_cons, List.prod_cons]
      exact Nat.mul_pos (Nat.succ_pos _) ih

theorem globalDenominator_pos (p : PolynomialCode) :
    0 < globalDenominator p := by
  induction p with
  | nil => simp [globalDenominator]
  | cons t p ih =>
      simp only [globalDenominator, List.map_cons, List.prod_cons]
      exact Nat.mul_pos (coefficientDenominator_pos t.1) ih

theorem nat_dvd_prod_of_mem (values : List Nat) (n : Nat)
    (hn : n ∈ values) : n ∣ values.prod := by
  induction values with
  | nil => simp at hn
  | cons a values ih =>
      simp only [List.mem_cons] at hn
      simp only [List.prod_cons]
      rcases hn with h | h
      · subst n
        exact ⟨values.prod, rfl⟩
      · rcases ih h with ⟨k, hk⟩
        refine ⟨a * k, ?_⟩
        calc
          a * values.prod = a * (n * k) := by rw [hk]
          _ = n * (a * k) := by ac_rfl

theorem coefficientDenominator_dvd_global (p : PolynomialCode) (t : TermCode)
    (ht : t ∈ p) : coefficientDenominator t.1 ∣ globalDenominator p := by
  apply nat_dvd_prod_of_mem
  exact List.mem_map.mpr ⟨t, ht, rfl⟩

def finiteToNatAssignment (support : List Nat) (y : Fin support.length → ℚ) : Nat → ℚ :=
  fun i => finiteVariableValue support.length y (support.idxOf i)

def natToFiniteAssignment (support : List Nat) (x : Nat → ℚ) :
    Fin support.length → ℚ := fun j => x (support.get j)

theorem finiteToNat_natToFinite (support : List Nat) (x : Nat → ℚ) (i : Nat)
    (hi : i ∈ support) :
    finiteToNatAssignment support (natToFiniteAssignment support x) i = x i := by
  have hidx := List.idxOf_lt_length_of_mem hi
  have hget : support[support.idxOf i] = i := List.getElem_idxOf hidx
  simp [finiteToNatAssignment, natToFiniteAssignment, finiteVariableValue, hidx, hget]

theorem monomialValue_congr {x y : Nat → ℚ} (m : MonomialCode)
    (h : ∀ i e, (i, e) ∈ m → x i = y i) :
    monomialValue x m = monomialValue y m := by
  induction m with
  | nil => rfl
  | cons ie m ih =>
      have hie : x ie.1 = y ie.1 := h ie.1 ie.2 (by simp)
      have htail : ∀ i e, (i, e) ∈ m → x i = y i := by
        intro i e he
        exact h i e (by simp [he])
      simp only [monomialValue, List.map_cons, List.prod_cons]
      rw [hie]
      congr 1
      exact ih htail

theorem termValue_congr {x y : Nat → ℚ} (t : TermCode)
    (h : ∀ i e, (i, e) ∈ t.2 → x i = y i) :
    termValue x t = termValue y t := by
  simp [termValue, monomialValue_congr t.2 h]

theorem polynomialValue_congr_on_support {p : PolynomialCode} {x y : Nat → ℚ}
    (h : ∀ i, i ∈ variableSupport p → x i = y i) :
    polynomialValue x p = polynomialValue y p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      have ht : ∀ i e, (i, e) ∈ t.2 → x i = y i := by
        intro i e hie
        apply h i
        apply (variableSupport_mem_iff (t :: p) i).2
        simp only [allVariables, List.flatMap_cons, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨(i, e), hie, rfl⟩)
      have hp : ∀ i, i ∈ variableSupport p → x i = y i := by
        intro i hi
        apply h i
        apply (variableSupport_mem_iff (t :: p) i).2
        have hip := (variableSupport_mem_iff p i).mp hi
        simp only [allVariables, List.flatMap_cons, List.mem_append]
        exact Or.inr hip
      simp only [polynomialValue, List.map_cons, List.sum_cons]
      rw [termValue_congr t ht]
      congr 1
      exact ih hp

def rationalNumeratorValue (c : CoeffCode) : ℚ :=
  (c.map fun a => (a.1 : ℚ)).prod

theorem coeffValue_eq_numerator_div_denominator (c : CoeffCode) :
    coeffValue c = rationalNumeratorValue c / coefficientDenominator c := by
  induction c with
  | nil => simp [coeffValue, rationalNumeratorValue, coefficientDenominator]
  | cons a c ih =>
      have hden : (a.2 : ℚ) + 1 ≠ 0 := by positivity
      have htail : (coefficientDenominator c : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (coefficientDenominator_pos c))
      have hcoeff : coeffValue (a :: c) = coeffAtomValue a * coeffValue c := by
        simp [coeffValue, List.map_cons, List.prod_cons]
      have hnum : rationalNumeratorValue (a :: c) =
          (a.1 : ℚ) * rationalNumeratorValue c := by
        simp [rationalNumeratorValue]
      have hdenom : coefficientDenominator (a :: c) =
          (a.2 + 1) * coefficientDenominator c := by
        simp [coefficientDenominator]
      rw [hcoeff, coeffAtomValue, ih, hnum, hdenom]
      push_cast
      field_simp [hden, htail]

theorem integerCoefficientValue_scaled (denom : Nat) (c : CoeffCode)
    (hdiv : coefficientDenominator c ∣ denom) :
    integerCoefficientValue (scaledIntegerCoefficientCode denom c) =
      (denom : ℚ) * coeffValue c := by
  have hquotient' :
      ((denom / coefficientDenominator c : Nat) : ℚ) *
        (coefficientDenominator c : ℚ) = (denom : ℚ) := by
    have hn := Nat.div_mul_cancel hdiv
    exact_mod_cast hn
  have hden : (coefficientDenominator c : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (coefficientDenominator_pos c))
  have hcode : integerCoefficientValue (scaledIntegerCoefficientCode denom c) =
      rationalNumeratorValue c * (denom / coefficientDenominator c : Nat) := by
    have hnum_all : ∀ c : CoeffCode,
        ((c.map Prod.fst).map (Int.cast : Int → ℚ)).prod = rationalNumeratorValue c := by
      intro c
      induction c with
      | nil => rfl
      | cons a c ih =>
          change (a.1 : ℚ) * ((c.map Prod.fst).map (Int.cast : Int → ℚ)).prod =
            (a.1 : ℚ) * (c.map fun a => (a.1 : ℚ)).prod
          rw [ih]
          simp [rationalNumeratorValue]
    have hnum := hnum_all c
    change ((c.map Prod.fst).map (Int.cast : Int → ℚ)).prod *
      (denom / coefficientDenominator c : Nat) = _
    rw [hnum]
  rw [hcode, coeffValue_eq_numerator_div_denominator]
  calc
    rationalNumeratorValue c * (denom / coefficientDenominator c : Nat) =
        ((denom / coefficientDenominator c : Nat) : ℚ) *
          (coefficientDenominator c : ℚ) *
            (rationalNumeratorValue c / (coefficientDenominator c : ℚ)) := by
          field_simp [hden]
    _ = (denom : ℚ) *
        (rationalNumeratorValue c / (coefficientDenominator c : ℚ)) := by rw [hquotient']

theorem denseMonomialValue (support : List Nat) (arity : Nat)
    (x : Fin arity → ℚ) (m : MonomialCode) :
    integerMonomialValue arity x (denseMonomial support m) =
      monomialValue (fun i => finiteVariableValue arity x (support.idxOf i)) m := by
  simp only [integerMonomialValue, denseMonomial, monomialValue, List.map_map,
    Function.comp_def]

theorem normalizedValueWithDenominator (p : PolynomialCode) (support : List Nat)
    (denom : Nat) (hdiv : ∀ t ∈ p, coefficientDenominator t.1 ∣ denom)
    (y : Fin support.length → ℚ) :
    integerPolynomialValue support.length y
        (p.map fun t =>
          (scaledIntegerCoefficientCode denom t.1, denseMonomial support t.2)) =
      (denom : ℚ) * polynomialValue (finiteToNatAssignment support y) p := by
  induction p with
  | nil => simp [integerPolynomialValue, polynomialValue]
  | cons t p ih =>
      have hdivt : coefficientDenominator t.1 ∣ denom := hdiv t (by simp)
      have hcoef := integerCoefficientValue_scaled denom t.1 hdivt
      have hdivTail : ∀ u ∈ p, coefficientDenominator u.1 ∣ denom := by
        intro u hu
        exact hdiv u (by simp [hu])
      change integerTermValue support.length y
          (scaledIntegerCoefficientCode denom t.1, denseMonomial support t.2) +
          integerPolynomialValue support.length y
            (p.map fun u =>
              (scaledIntegerCoefficientCode denom u.1, denseMonomial support u.2)) =
        (denom : ℚ) *
          (termValue (finiteToNatAssignment support y) t +
            polynomialValue (finiteToNatAssignment support y) p)
      simp only [integerTermValue, termValue]
      rw [hcoef, denseMonomialValue, ih hdivTail]
      have hmono : monomialValue
          (fun i => finiteVariableValue support.length y (support.idxOf i)) t.2 =
          monomialValue (finiteToNatAssignment support y) t.2 := rfl
      rw [hmono]
      ring

theorem normalizedValue (p : PolynomialCode) (y : Fin (variableSupport p).length → ℚ) :
    integerPolynomialValue (variableSupport p).length y (normalizeToInteger p).2 =
      (globalDenominator p : ℚ) *
        polynomialValue (finiteToNatAssignment (variableSupport p) y) p := by
  have hdiv : ∀ t ∈ p, coefficientDenominator t.1 ∣ globalDenominator p := by
    intro t ht
    exact coefficientDenominator_dvd_global p t ht
  have h := normalizedValueWithDenominator p (variableSupport p)
    (globalDenominator p) hdiv y
  simpa [normalizeToInteger, integerCoefficientCode, scaledIntegerCoefficientCode] using h

theorem rationalPolynomialHasRoot_iff_value (p : PolynomialCode) :
    RationalPolynomialHasRoot p ↔ ∃ x : Nat → ℚ, polynomialValue x p = 0 :=
  rationalPolynomialHasRoot_iff p

/-- Normalization preserves rational root existence.  The forward direction
extends an arbitrary natural-indexed assignment to the finite support; the
reverse direction extends any finite assignment to a natural-indexed one.
-/
theorem normalizeToInteger_preserves_roots (p : PolynomialCode) :
    RationalPolynomialHasRoot p ↔
      IntegerPolynomialHasRationalRoot (normalizeToInteger p) := by
  rw [rationalPolynomialHasRoot_iff_value]
  change (∃ x : Nat → ℚ, polynomialValue x p = 0) ↔
    ∃ y : Fin (variableSupport p).length → ℚ,
      integerPolynomialValue (variableSupport p).length y (normalizeToInteger p).2 = 0
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨natToFiniteAssignment (variableSupport p) x, ?_⟩
    have heval := normalizedValue p (natToFiniteAssignment (variableSupport p) x)
    have hround :
        polynomialValue
          (finiteToNatAssignment (variableSupport p)
            (natToFiniteAssignment (variableSupport p) x)) p = polynomialValue x p := by
      apply polynomialValue_congr_on_support
      intro i hi
      exact finiteToNat_natToFinite (variableSupport p) x i hi
    rw [heval, hround, hx]
    simp
  · rintro ⟨y, hy⟩
    refine ⟨finiteToNatAssignment (variableSupport p) y, ?_⟩
    have heval := normalizedValue p y
    rw [heval] at hy
    have hD : (globalDenominator p : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (globalDenominator_pos p))
    exact (mul_eq_zero.mp hy).resolve_left hD

theorem normalizeToInteger_support_bounded (p : PolynomialCode) :
    ∀ t ∈ (normalizeToInteger p).2, ∀ ie ∈ t.2, ie.1 < (normalizeToInteger p).1 := by
  intro t ht ie hie
  simp only [normalizeToInteger, List.mem_map] at ht
  rcases ht with ⟨source, hsource, rfl⟩
  simp only [denseMonomial, List.mem_map] at hie
  rcases hie with ⟨sourceVar, hsourceVar, rfl⟩
  have hmem : sourceVar.1 ∈ variableSupport p := by
    apply (variableSupport_mem_iff p sourceVar.1).2
    unfold allVariables
    exact List.mem_flatMap.mpr ⟨source, hsource,
      List.mem_map.mpr ⟨sourceVar, hsourceVar, rfl⟩⟩
  exact variableSupport_index_lt p sourceVar.1 hmem

theorem primrec_allVariables : Primrec allVariables := by
  unfold allVariables
  have hmap : Primrec (fun t : TermCode => t.2.map Prod.fst) := by
    exact Primrec.list_map Primrec.snd (Primrec.fst.comp Primrec.snd)
  have hmap₂ : Primrec₂ (fun (_ : PolynomialCode) (t : TermCode) => t.2.map Prod.fst) := by
    apply Primrec₂.mk
    exact hmap.comp Primrec.snd
  exact Primrec.list_flatMap Primrec.id hmap₂

theorem primrec_insertVariable : Primrec₂ insertVariable := by
  apply Primrec₂.mk
  unfold insertVariable
  have hidx : Primrec₂ (fun (seen : List Nat) (i : Nat) => seen.idxOf i) := by
    apply Primrec₂.mk
    exact Primrec₂.comp Primrec.list_idxOf Primrec.snd Primrec.fst
  have hlen : Primrec₂ (fun (seen : List Nat) (_ : Nat) => seen.length) := by
    apply Primrec₂.mk
    exact Primrec.list_length.comp Primrec.fst
  have hcond₂ : Primrec₂ (fun (seen : List Nat) (i : Nat) =>
      decide (seen.idxOf i < seen.length)) :=
    (Primrec.nat_lt.comp₂ hidx hlen).decide
  have hcond : Primrec (fun z : List Nat × Nat => decide (z.1.idxOf z.2 < z.1.length)) :=
    Primrec₂.uncurry.mpr hcond₂
  have hsingleton : Primrec (fun z : List Nat × Nat => [z.2]) := by
    exact Primrec₂.comp Primrec.list_cons Primrec.snd (Primrec.const [])
  have happend : Primrec (fun z : List Nat × Nat => z.1 ++ [z.2]) := by
    exact Primrec₂.comp Primrec.list_append Primrec.fst hsingleton
  exact (Primrec.cond hcond Primrec.fst happend).of_eq fun z => by
    cases h : decide (z.1.idxOf z.2 < z.1.length) <;> rfl

theorem primrec_uniqueVariables : Primrec uniqueVariables := by
  unfold uniqueVariables
  have hstep : Primrec₂ (fun (xs : List Nat) (s : List Nat × Nat) =>
      insertVariable s.1 s.2) := by
    apply Primrec₂.mk
    exact Primrec₂.comp primrec_insertVariable
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldl Primrec.id (Primrec.const []) hstep

theorem primrec_variableSupport : Primrec variableSupport := by
  unfold variableSupport
  exact primrec_uniqueVariables.comp primrec_allVariables

theorem primrec_natProduct : Primrec fun xs : List Nat => xs.prod := by
  have hstep : Primrec₂ (fun (_ : List Nat) (ab : Nat × Nat) => ab.1 * ab.2) := by
    apply Primrec₂.mk
    exact Primrec₂.comp Primrec.nat_mul
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  simpa [List.prod] using
    (Primrec.list_foldr Primrec.id (Primrec.const 1) hstep)

theorem primrec_coefficientDenominator : Primrec coefficientDenominator := by
  unfold coefficientDenominator
  have hentry : Primrec₂ (fun (_ : CoeffCode) (a : CoeffAtomCode) => a.2 + 1) := by
    apply Primrec₂.mk
    exact Primrec.succ.comp (Primrec.snd.comp Primrec.snd)
  have hmap : Primrec fun c : CoeffCode => c.map fun a => a.2 + 1 :=
    Primrec.list_map Primrec.id hentry
  exact primrec_natProduct.comp hmap

theorem primrec_globalDenominator : Primrec globalDenominator := by
  unfold globalDenominator
  have hentry : Primrec₂ (fun (_ : PolynomialCode) (t : TermCode) =>
      coefficientDenominator t.1) := by
    apply Primrec₂.mk
    exact primrec_coefficientDenominator.comp (Primrec.fst.comp Primrec.snd)
  have hmap : Primrec fun p : PolynomialCode => p.map fun t => coefficientDenominator t.1 :=
    Primrec.list_map Primrec.id hentry
  exact primrec_natProduct.comp hmap

theorem primrec_integerCoefficientCode :
    Primrec (fun z : PolynomialCode × CoeffCode => integerCoefficientCode z.1 z.2) := by
  unfold integerCoefficientCode
  have hnums : Primrec fun z : PolynomialCode × CoeffCode => z.2.map Prod.fst := by
    exact Primrec.list_map Primrec.snd
      (Primrec.fst.comp Primrec.snd)
  have hquot : Primrec fun z : PolynomialCode × CoeffCode =>
      globalDenominator z.1 / coefficientDenominator z.2 := by
    exact Primrec₂.comp Primrec.nat_div
      (primrec_globalDenominator.comp Primrec.fst)
      (primrec_coefficientDenominator.comp Primrec.snd)
  exact Primrec.pair hnums hquot

theorem primrec_denseMonomial :
    Primrec (fun z : List Nat × MonomialCode => denseMonomial z.1 z.2) := by
  unfold denseMonomial
  have hentryWithContext : Primrec₂ (fun (z : List Nat × MonomialCode) (ie : Nat × Nat) =>
      (z.1.idxOf ie.1, ie.2)) := by
    apply Primrec₂.mk
    have hidx : Primrec (fun w : (List Nat × MonomialCode) × (Nat × Nat) =>
        w.1.1.idxOf w.2.1) :=
      Primrec₂.comp Primrec.list_idxOf
        (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)
    exact Primrec.pair hidx (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_map Primrec.snd hentryWithContext

theorem primrec_normalizeToInteger : Primrec normalizeToInteger := by
  unfold normalizeToInteger
  have hsupport : Primrec fun p : PolynomialCode => variableSupport p := primrec_variableSupport
  have harity : Primrec fun p : PolynomialCode => (variableSupport p).length :=
    Primrec.list_length.comp hsupport
  have hterms : Primrec fun p : PolynomialCode =>
      p.map fun t => (integerCoefficientCode p t.1, denseMonomial (variableSupport p) t.2) := by
    have hterm : Primrec (fun z : PolynomialCode × TermCode =>
        (integerCoefficientCode z.1 z.2.1, denseMonomial (variableSupport z.1) z.2.2)) := by
      have hcoeff : Primrec (fun z : PolynomialCode × TermCode =>
          integerCoefficientCode z.1 z.2.1) :=
        primrec_integerCoefficientCode.comp (Primrec.pair Primrec.fst
          (Primrec.fst.comp Primrec.snd))
      have hmonomial : Primrec (fun z : PolynomialCode × TermCode =>
          denseMonomial (variableSupport z.1) z.2.2) :=
        primrec_denseMonomial.comp (Primrec.pair
          (primrec_variableSupport.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd))
      exact Primrec.pair hcoeff hmonomial
    exact Primrec.list_map Primrec.id (Primrec₂.mk hterm)
  exact Primrec.pair harity hterms

theorem rationalRoot_computable_of_h10Q
    (oracle : ComputablePred IntegerPolynomialHasRationalRoot) :
    ComputablePred RationalPolynomialHasRoot := by
  classical
  let rootDecision : PolynomialCode → Bool :=
    fun p => decide (RationalPolynomialHasRoot p)
  have hnormalize : Computable normalizeToInteger := primrec_normalizeToInteger.to_comp
  have hquery : Computable (fun p : PolynomialCode =>
      decide (IntegerPolynomialHasRationalRoot (normalizeToInteger p))) :=
    oracle.decide.comp hnormalize
  have hroot : Computable rootDecision := hquery.of_eq fun p => by
    apply Bool.eq_iff_iff.mpr
    simpa [rootDecision] using (normalizeToInteger_preserves_roots p).symm
  exact hroot.computablePred

theorem constraintSystem_computable_of_h10Q
    (oracle : ComputablePred IntegerPolynomialHasRationalRoot) :
    ComputablePred H10RationalCompiler.Satisfies :=
  H10RationalCompiler.constraintSystem_computable
    (rationalRoot_computable_of_h10Q oracle)

theorem indexed_constraintSystem_computable_of_h10Q
    {α : Type*} [Primcodable α]
    (makeConstraints : α → Nat → H10RationalCompiler.ConstraintSystem)
    (hmake : Computable₂ makeConstraints)
    (oracle : ComputablePred IntegerPolynomialHasRationalRoot) :
    ComputablePred (fun p : α × Nat =>
      H10RationalCompiler.Satisfies (makeConstraints p.1 p.2)) :=
  H10RationalCompiler.indexed_constraintSystem_computable makeConstraints hmake
    (rationalRoot_computable_of_h10Q oracle)

example : normalizeToInteger ([] : PolynomialCode) = (0, []) := by decide

example : normalizeToInteger (polyConst [(7, 2)]) =
    (0, [(([7], 1), [])]) := by decide

example : normalizeToInteger
    ([( [(5, 1)], [(37, 2), (37, 3)] )] : PolynomialCode) =
      (1, [(([5], 1), [(0, 2), (0, 3)])]) := by decide

example : normalizeToInteger
    ([( [(5, 1)], [(37, 1)] ), ([(5, 1)], [(37, 1)])] : PolynomialCode) =
      (1, [(([5], 2), [(0, 1)]), (([5], 2), [(0, 1)])]) := by decide

end H10RationalQueryAdapter

