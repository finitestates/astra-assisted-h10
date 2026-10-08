module

public import Mathlib.Computability.RE
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A finite rational constraint compiler

The input language is finite disjunctive normal form.  Polynomial coefficients
are encoded as an integer numerator and a positive denominator (`den + 1`),
so the syntax itself has a primitive recursive encoding even though `ℚ` does
not have a `Primcodable` instance in mathlib.  Monomials are finite lists of
variable/exponent pairs; repeated variable entries are allowed.
-/

@[expose] public section

namespace H10RationalCompiler

abbrev CoeffAtomCode := Int × Nat
abbrev CoeffCode := List CoeffAtomCode
abbrev MonomialCode := List (Nat × Nat)
abbrev TermCode := CoeffCode × MonomialCode
abbrev PolynomialCode := List TermCode
abbrev Atom := Bool × PolynomialCode
abbrev ConstraintSystem := List (List Atom)

/-- Interpret `(a, b)` as the rational `a / (b + 1)`. -/
def coeffAtomValue (c : CoeffAtomCode) : ℚ := (c.1 : ℚ) / (c.2 + 1)

def coeffValue (c : CoeffCode) : ℚ := (c.map coeffAtomValue).prod

/-- Multiplication of rational coefficient codes, without normalizing. -/
def coeffMul (a b : CoeffCode) : CoeffCode :=
  a ++ b

def monomialValue (x : Nat → ℚ) (m : MonomialCode) : ℚ :=
  (m.map fun ie => x ie.1 ^ ie.2).prod

def termValue (x : Nat → ℚ) (t : TermCode) : ℚ :=
  coeffValue t.1 * monomialValue x t.2

def polynomialValue (x : Nat → ℚ) (p : PolynomialCode) : ℚ :=
  (p.map (termValue x)).sum

noncomputable def monomialPolynomial (m : MonomialCode) : MvPolynomial Nat ℚ :=
  (m.map fun ie => MvPolynomial.X ie.1 ^ ie.2).prod

noncomputable def termPolynomial (t : TermCode) : MvPolynomial Nat ℚ :=
  MvPolynomial.C (coeffValue t.1) * monomialPolynomial t.2

noncomputable def polynomialDenote (p : PolynomialCode) : MvPolynomial Nat ℚ :=
  (p.map termPolynomial).sum

def polyAdd (p q : PolynomialCode) : PolynomialCode := p ++ q

def termMul (a b : TermCode) : TermCode :=
  (coeffMul a.1 b.1, a.2 ++ b.2)

def mapTermMul (a : TermCode) (q : PolynomialCode) : PolynomialCode :=
  q.map (termMul a)

def polyMul (p q : PolynomialCode) : PolynomialCode :=
  p.flatMap (mapTermMul · q)

def polyConst (c : CoeffCode) : PolynomialCode := [(c, [])]

def polyVar (i : Nat) : PolynomialCode := [([], [(i, 1)])]

def liftMonomial (m : MonomialCode) : MonomialCode :=
  m.map fun ie => (Nat.pair 0 ie.1, ie.2)

def liftTerm (t : TermCode) : TermCode := (t.1, liftMonomial t.2)

def mapVars (f : Nat → Nat) (p : PolynomialCode) : PolynomialCode :=
  p.map fun t => (t.1, t.2.map fun ie => (f ie.1, ie.2))

def liftOriginal (p : PolynomialCode) : PolynomialCode :=
  p.map liftTerm

def equationOfAtom (a : Atom) : PolynomialCode :=
  if a.1 then
    polyAdd
      (polyMul (liftOriginal a.2) (polyVar (Nat.pair 1 (Encodable.encode a.2))))
      (polyConst [(-1, 0)])
  else liftOriginal a.2

def sumSquares (equations : List PolynomialCode) : PolynomialCode :=
  equations.foldr (fun p acc => polyAdd (polyMul p p) acc) []

def compileClause (clause : List Atom) : PolynomialCode :=
  sumSquares (clause.map equationOfAtom)

/-- Compile each disjunct to one polynomial equation. -/
def compile (c : ConstraintSystem) : List PolynomialCode := c.map compileClause

def atomSatisfied (x : Nat → ℚ) (a : Atom) : Prop :=
  if a.1 then polynomialValue x a.2 ≠ 0 else polynomialValue x a.2 = 0

def clauseSatisfied (x : Nat → ℚ) (clause : List Atom) : Prop :=
  ∀ a ∈ clause, atomSatisfied x a

/-- A finite DNF constraint system has a rational solution.  The empty
disjunction is false and an empty conjunction is true. -/
def Satisfies (c : ConstraintSystem) : Prop :=
  ∃ x : Nat → ℚ, ∃ clause ∈ c, clauseSatisfied x clause

/-- Rational-polynomial solvability for the explicit finite polynomial code. -/
noncomputable def RationalPolynomialHasRoot (p : PolynomialCode) : Prop :=
  ∃ x : Nat → ℚ, (polynomialDenote p).eval x = 0

def originalAssignment (x : Nat → ℚ) : Nat → ℚ := fun i => x (Nat.pair 0 i)

def witnessVariable (p : PolynomialCode) : Nat := Nat.pair 1 (Encodable.encode p)

def equationValue (x : Nat → ℚ) (a : Atom) : ℚ :=
  if a.1 then
    polynomialValue (originalAssignment x) a.2 * x (witnessVariable a.2) - 1
  else polynomialValue (originalAssignment x) a.2

/-- Extend an assignment by assigning each tagged witness variable the inverse
of the polynomial named by its code. -/
def extendAssignment (x : Nat → ℚ) : Nat → ℚ := fun v =>
  let (tag, code) := Nat.unpair v
  if tag = 0 then x code
  else if tag = 1 then
    match Encodable.decode code with
    | some p => (polynomialValue x p)⁻¹
    | none => 0
  else 0

theorem monomialPolynomial_eval (x : Nat → ℚ) (m : MonomialCode) :
    (monomialPolynomial m).eval x = monomialValue x m := by
  induction m with
  | nil => simp [monomialPolynomial, monomialValue]
  | cons ie m ih =>
      change (MvPolynomial.X ie.1 ^ ie.2 * monomialPolynomial m).eval x =
        x ie.1 ^ ie.2 * monomialValue x m
      simp [ih]

theorem termPolynomial_eval (x : Nat → ℚ) (t : TermCode) :
    (termPolynomial t).eval x = termValue x t := by
  simp [termPolynomial, termValue, monomialPolynomial_eval]

theorem polynomialDenote_eval (x : Nat → ℚ) (p : PolynomialCode) :
    (polynomialDenote p).eval x = polynomialValue x p := by
  induction p with
  | nil => simp [polynomialDenote, polynomialValue]
  | cons t p ih =>
      change (termPolynomial t + polynomialDenote p).eval x =
        termValue x t + polynomialValue x p
      rw [MvPolynomial.eval_add, termPolynomial_eval, ih]

theorem rationalPolynomialHasRoot_iff (p : PolynomialCode) :
    RationalPolynomialHasRoot p ↔ ∃ x : Nat → ℚ, polynomialValue x p = 0 := by
  simp [RationalPolynomialHasRoot, polynomialDenote_eval]

theorem coeffAtomValue_surjective : Function.Surjective coeffAtomValue := by
  intro q
  refine ⟨(q.num, q.den - 1), ?_⟩
  have hden : q.den - 1 + 1 = q.den :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr q.den_ne_zero)
  simp only [coeffAtomValue]
  have hdenQ : ((q.den - 1 : Nat) : ℚ) + 1 = (q.den : ℚ) := by
    exact_mod_cast hden
  rw [hdenQ]
  rw [show (q.den : ℚ) = (Int.ofNat q.den : ℚ) by rfl]
  rw [← Rat.divInt_eq_div]
  exact Rat.num_divInt_den q

@[simp]
theorem polynomialValue_polyConst (x : Nat → ℚ) (c : CoeffCode) :
    polynomialValue x (polyConst c) = coeffValue c := by
  simp [polynomialValue, polyConst, termValue, monomialValue]

@[simp]
theorem polynomialValue_polyVar (x : Nat → ℚ) (i : Nat) :
    polynomialValue x (polyVar i) = x i := by
  simp [polynomialValue, polyVar, termValue, monomialValue, coeffValue]

theorem coeffValue_mul (a b : CoeffCode) :
    coeffValue (coeffMul a b) = coeffValue a * coeffValue b := by
  simp [coeffValue, coeffMul, List.map_append, List.prod_append]

theorem monomialValue_append (x : Nat → ℚ) (m n : MonomialCode) :
    monomialValue x (m ++ n) = monomialValue x m * monomialValue x n := by
  simp [monomialValue, List.map_append]

theorem monomialValue_map (x : Nat → ℚ) (f : Nat → Nat) (m : MonomialCode) :
    monomialValue x (m.map fun ie => (f ie.1, ie.2)) =
      monomialValue (fun i => x (f i)) m := by
  simp [monomialValue, List.map_map, Function.comp_def]

theorem termValue_mul (x : Nat → ℚ) (a b : TermCode) :
    termValue x (termMul a b) = termValue x a * termValue x b := by
  simp [termValue, termMul, coeffValue_mul, monomialValue_append]
  ring

theorem polynomialValue_add (x : Nat → ℚ) (p q : PolynomialCode) :
    polynomialValue x (polyAdd p q) = polynomialValue x p + polynomialValue x q := by
  simp [polynomialValue, polyAdd, List.map_append, List.sum_append]

theorem polynomialValue_mapVars (x : Nat → ℚ) (f : Nat → Nat)
    (p : PolynomialCode) :
    polynomialValue x (mapVars f p) = polynomialValue (fun i => x (f i)) p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      simp only [polynomialValue, mapVars, List.map_cons, List.sum_cons]
      congr 1
      simp [termValue, monomialValue_map]

theorem polynomialValue_liftOriginal (x : Nat → ℚ) (p : PolynomialCode) :
    polynomialValue x (liftOriginal p) = polynomialValue (originalAssignment x) p := by
  change polynomialValue x (mapVars (Nat.pair 0) p) =
    polynomialValue (originalAssignment x) p
  rw [polynomialValue_mapVars]
  rfl

theorem sum_termMul_left (x : Nat → ℚ) (a : TermCode) (q : PolynomialCode) :
    (q.map (termValue x ∘ termMul a)).sum =
      termValue x a * polynomialValue x q := by
  induction q with
  | nil => simp [polynomialValue]
  | cons b q ih =>
      simp only [List.map_cons, List.sum_cons, polynomialValue, Function.comp_apply]
      change (q.map (termValue x ∘ termMul a)).sum =
        termValue x a * (q.map (termValue x)).sum at ih
      rw [termValue_mul, ih]
      ring

theorem polynomialValue_mul (x : Nat → ℚ) (p q : PolynomialCode) :
    polynomialValue x (polyMul p q) = polynomialValue x p * polynomialValue x q := by
  induction p with
  | nil => simp [polyMul, mapTermMul, polynomialValue]
  | cons a p ih =>
      calc
        polynomialValue x (polyMul (a :: p) q) =
            (q.map (termValue x ∘ termMul a)).sum +
              polynomialValue x (polyMul p q) := by
                simp [polyMul, mapTermMul, polynomialValue, List.flatMap_cons, List.map_append,
                  List.sum_append]
        _ = termValue x a * polynomialValue x q +
              polynomialValue x p * polynomialValue x q := by
                rw [ih]
                rw [sum_termMul_left]
        _ = polynomialValue x (a :: p) * polynomialValue x q := by
              simp [polynomialValue, add_mul]

theorem polynomialValue_sumSquares (x : Nat → ℚ) (equations : List PolynomialCode) :
    polynomialValue x (sumSquares equations) =
      (equations.map fun p => polynomialValue x p * polynomialValue x p).sum := by
  induction equations with
  | nil => simp [sumSquares, polynomialValue]
  | cons p equations ih =>
      change polynomialValue x (polyAdd (polyMul p p) (sumSquares equations)) = _
      rw [polynomialValue_add, polynomialValue_mul, ih]
      simp

theorem list_sum_squares_nonneg (values : List ℚ) :
    0 ≤ (values.map fun a => a * a).sum := by
  induction values with
  | nil => simp
  | cons a values ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (mul_self_nonneg a) ih

theorem list_sum_squares_eq_zero_iff (values : List ℚ) :
    (values.map fun a => a * a).sum = 0 ↔ ∀ a ∈ values, a = 0 := by
  induction values with
  | nil => simp
  | cons a values ih =>
      simp only [List.map_cons, List.sum_cons]
      constructor
      · intro h b hb
        have htail : 0 ≤ (values.map fun z => z * z).sum :=
          list_sum_squares_nonneg values
        have ha2 : a * a = 0 := by nlinarith [mul_self_nonneg a]
        have ha : a = 0 := (mul_self_eq_zero.mp ha2)
        have hrest : (values.map fun z => z * z).sum = 0 := by nlinarith
        rcases List.mem_cons.mp hb with hba | hb
        · subst b
          exact ha
        · exact ih.mp hrest b hb
      · intro h
        have ha : a = 0 := h a (by simp)
        have htail : ∀ z ∈ values, z = 0 := by
          intro z hz
          exact h z (by simp [hz])
        have hrest : (values.map fun z => z * z).sum = 0 := ih.mpr htail
        simp [ha, hrest]

@[simp]
theorem extendAssignment_original (x : Nat → ℚ) (i : Nat) :
    originalAssignment (extendAssignment x) i = x i := by
  simp [originalAssignment, extendAssignment, Nat.unpair_pair]

@[simp]
theorem extendAssignment_witness (x : Nat → ℚ) (p : PolynomialCode) :
    extendAssignment x (witnessVariable p) = (polynomialValue x p)⁻¹ := by
  simp [witnessVariable, extendAssignment, Nat.unpair_pair]

theorem polynomialValue_equationOfAtom (x : Nat → ℚ) (a : Atom) :
    polynomialValue x (equationOfAtom a) = equationValue x a := by
  rcases a with ⟨diseq, p⟩
  cases diseq
  · change polynomialValue x (mapVars (Nat.pair 0) p) =
      polynomialValue (originalAssignment x) p
    rw [polynomialValue_mapVars]
    rfl
  · change polynomialValue x
      (polyAdd (polyMul (liftOriginal p) (polyVar (witnessVariable p)))
        (polyConst [(-1, 0)])) =
      polynomialValue (originalAssignment x) p * x (witnessVariable p) - 1
    rw [polynomialValue_add, polynomialValue_mul, polynomialValue_liftOriginal]
    rw [polynomialValue_polyVar, polynomialValue_polyConst]
    simp [coeffValue, coeffAtomValue]
    ring

theorem compileClause_correct (clause : List Atom) :
    (∃ x : Nat → ℚ, clauseSatisfied x clause) ↔
      RationalPolynomialHasRoot (compileClause clause) := by
  constructor
  · rintro ⟨x, hclause⟩
    rw [rationalPolynomialHasRoot_iff]
    let y := extendAssignment x
    have hOrig : originalAssignment y = x := by
      funext i
      simp [y]
    have hEq : ∀ a ∈ clause, polynomialValue y (equationOfAtom a) = 0 := by
      intro a ha
      rw [polynomialValue_equationOfAtom, equationValue, hOrig]
      cases h : a.1 with
      | false => simpa [atomSatisfied, h] using hclause a ha
      | true =>
          have hne : polynomialValue x a.2 ≠ 0 := by
            simpa [atomSatisfied, h] using hclause a ha
          have hwit : y (witnessVariable a.2) =
              (polynomialValue x a.2)⁻¹ := by
            simp [y]
          rw [hwit, mul_inv_cancel₀ hne]
          simp
    refine ⟨y, ?_⟩
    change polynomialValue y (sumSquares (clause.map equationOfAtom)) = 0
    rw [polynomialValue_sumSquares]
    let values := (clause.map equationOfAtom).map (polynomialValue y)
    have hall : ∀ value ∈ values, value = 0 := by
      intro value hvalue
      rcases List.mem_map.mp hvalue with ⟨p, hp, rfl⟩
      rcases List.mem_map.mp hp with ⟨a, ha, rfl⟩
      exact hEq a ha
    have hsquares := (list_sum_squares_eq_zero_iff values).mpr hall
    simpa [values, List.map_map, Function.comp_def] using hsquares
  · intro hroot
    rcases (rationalPolynomialHasRoot_iff _).mp hroot with ⟨y, hy⟩
    let x := originalAssignment y
    have hvalues :
        ((clause.map equationOfAtom).map fun p =>
          polynomialValue y p * polynomialValue y p).sum = 0 := by
      rw [← polynomialValue_sumSquares]
      simpa [compileClause] using hy
    let values := (clause.map equationOfAtom).map (polynomialValue y)
    have hsum : (values.map fun v => v * v).sum = 0 := by
      simpa [values, List.map_map, Function.comp_def] using hvalues
    have hall : ∀ q ∈ values, q = 0 :=
      (list_sum_squares_eq_zero_iff values).mp hsum
    refine ⟨x, ?_⟩
    intro a ha
    have heq : polynomialValue y (equationOfAtom a) = 0 :=
      hall _ (List.mem_map.mpr ⟨equationOfAtom a,
        List.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩)
    rw [polynomialValue_equationOfAtom] at heq
    cases h : a.1 with
    | false =>
        simpa [atomSatisfied, equationValue, x, h] using heq
    | true =>
        have hne : polynomialValue x a.2 ≠ 0 := by
          intro hz
          have hval :
              polynomialValue x a.2 * y (witnessVariable a.2) - 1 = 0 := by
            simpa [equationValue, x, h] using heq
          simp [hz] at hval
        simpa [atomSatisfied, h] using hne

/-- The finite DNF system is solvable exactly when one compiled equation has a
rational root.  The two empty-list cases are included in this equivalence. -/
theorem compile_correct (c : ConstraintSystem) :
    Satisfies c ↔ ∃ q ∈ compile c, RationalPolynomialHasRoot q := by
  constructor
  · rintro ⟨x, clause, hclause, hsat⟩
    exact ⟨compileClause clause, List.mem_map.mpr ⟨clause, hclause, rfl⟩,
      (compileClause_correct clause).mp ⟨x, hsat⟩⟩
  · rintro ⟨q, hq, hroot⟩
    rcases List.mem_map.mp hq with ⟨clause, hclause, rfl⟩
    rcases (compileClause_correct clause).mpr hroot with ⟨x, hsat⟩
    exact ⟨x, clause, hclause, hsat⟩

example : Primcodable CoeffCode := inferInstance

example : Primcodable PolynomialCode := inferInstance

example : Primcodable ConstraintSystem := inferInstance

theorem primrec_coeffMul : Primrec₂ coeffMul := by
  exact Primrec.list_append

theorem primrec_termMul_uncurried :
    Primrec (fun z : TermCode × TermCode => termMul z.1 z.2) := by
  unfold termMul coeffMul
  change Primrec (fun z : TermCode × TermCode =>
    (z.1.1 ++ z.2.1, z.1.2 ++ z.2.2))
  exact Primrec.pair
    (Primrec₂.comp Primrec.list_append (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
    (Primrec₂.comp Primrec.list_append (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

theorem primrec_termMul : Primrec₂ termMul := Primrec₂.mk primrec_termMul_uncurried

theorem primrec_mapTermMul :
    Primrec (fun z : TermCode × PolynomialCode => mapTermMul z.1 z.2) := by
  unfold mapTermMul
  exact Primrec.list_map Primrec.snd
    (Primrec₂.comp₂ primrec_termMul
      (Primrec.comp₂ Primrec.fst Primrec₂.left) Primrec₂.right)

theorem primrec_polyMul_uncurried :
    Primrec (fun z : PolynomialCode × PolynomialCode => polyMul z.1 z.2) := by
  unfold polyMul
  have hmap :
      Primrec (fun z : (PolynomialCode × PolynomialCode) × TermCode =>
        mapTermMul z.2 z.1.2) := by
    exact primrec_mapTermMul.comp
      (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))
  exact Primrec.list_flatMap Primrec.fst (Primrec₂.mk hmap)

theorem primrec_polyMul : Primrec₂ polyMul := Primrec₂.mk primrec_polyMul_uncurried

theorem primrec_liftMonomialEntry :
    Primrec (fun ie : Nat × Nat => (Nat.pair 0 ie.1, ie.2)) := by
  exact Primrec.pair
    (Primrec₂.comp Primrec₂.natPair (Primrec.const 0) Primrec.fst)
    Primrec.snd

theorem primrec_liftMonomial : Primrec liftMonomial := by
  unfold liftMonomial
  exact Primrec.list_map Primrec.id
    (Primrec₂.mk (primrec_liftMonomialEntry.comp Primrec.snd))

theorem primrec_liftTerm : Primrec liftTerm := by
  unfold liftTerm
  exact Primrec.pair Primrec.fst (primrec_liftMonomial.comp Primrec.snd)

theorem primrec_liftOriginal : Primrec liftOriginal := by
  unfold liftOriginal
  exact Primrec.list_map Primrec.id
    (Primrec₂.mk (primrec_liftTerm.comp Primrec.snd))

theorem primrec_polyAdd : Primrec₂ polyAdd := by
  exact Primrec.list_append

theorem primrec_polyConst : Primrec polyConst := by
  unfold polyConst
  exact Primrec₂.comp Primrec.list_cons
    (Primrec.pair Primrec.id (Primrec.const [])) (Primrec.const [])

theorem primrec_polyVar : Primrec polyVar := by
  unfold polyVar
  exact Primrec₂.comp Primrec.list_cons
    (Primrec.pair (Primrec.const [])
      (Primrec₂.comp Primrec.list_cons
        (Primrec.pair Primrec.id (Primrec.const 1)) (Primrec.const [])))
    (Primrec.const [])

theorem primrec_witnessVariable : Primrec witnessVariable := by
  unfold witnessVariable
  exact Primrec₂.comp Primrec₂.natPair (Primrec.const 1) Primrec.encode

theorem primrec_equationOfAtom : Primrec equationOfAtom := by
  unfold equationOfAtom
  have hbranches : Primrec (fun a : Atom =>
      bif a.1 then
        polyAdd
          (polyMul (liftOriginal a.2) (polyVar (Nat.pair 1 (Encodable.encode a.2))))
          (polyConst [(-1, 0)])
      else liftOriginal a.2) := by
    exact Primrec.cond Primrec.fst
      (Primrec₂.comp primrec_polyAdd
      (Primrec₂.comp primrec_polyMul
        (primrec_liftOriginal.comp Primrec.snd)
        (primrec_polyVar.comp
          (Primrec₂.comp Primrec₂.natPair (Primrec.const 1)
            (Primrec.encode.comp Primrec.snd))))
        (primrec_polyConst.comp (Primrec.const [(-1, 0)])))
      (primrec_liftOriginal.comp Primrec.snd)
  exact hbranches.of_eq fun a => by cases a.1 <;> rfl

theorem primrec_sumSquares : Primrec sumSquares := by
  unfold sumSquares
  have hstep : Primrec₂ (fun (_ : List PolynomialCode)
      (pair : PolynomialCode × PolynomialCode) =>
        polyAdd (polyMul pair.1 pair.1) pair.2) := by
    apply Primrec₂.mk
    exact Primrec₂.comp primrec_polyAdd
      (Primrec₂.comp primrec_polyMul (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.id (Primrec.const []) hstep

theorem primrec_compileClause : Primrec compileClause := by
  unfold compileClause
  exact primrec_sumSquares.comp <|
    Primrec.list_map Primrec.id
      (Primrec₂.mk (primrec_equationOfAtom.comp Primrec.snd))

theorem primrec_compile : Primrec compile := by
  unfold compile
  exact Primrec.list_map Primrec.id
    (Primrec₂.mk (primrec_compileClause.comp Primrec.snd))

def rootSearchStep (root : PolynomialCode → Bool)
    (queries : List PolynomialCode) : Part (Bool ⊕ List PolynomialCode) :=
  match queries.head? with
  | none => Part.some (Sum.inl false)
  | some query =>
      if root query then Part.some (Sum.inl true) else Part.some (Sum.inr queries.tail)

theorem computable_list_any_of (root : PolynomialCode → Bool)
    (hroot : Computable root) :
    Computable (fun queries : List PolynomialCode => queries.any root) := by
  let step : List PolynomialCode →. Bool ⊕ List PolynomialCode := rootSearchStep root
  have hbranchFn : Computable (fun z : List PolynomialCode × PolynomialCode =>
      if root z.2 then (Sum.inl true : Bool ⊕ List PolynomialCode)
      else (Sum.inr z.1.tail : Bool ⊕ List PolynomialCode)) := by
    exact (Computable.cond (hroot.comp Computable.snd)
      (Computable.const (Sum.inl true : Bool ⊕ List PolynomialCode))
      (Computable.sumInr.comp (Primrec.list_tail.to_comp.comp Computable.fst))).of_eq fun z => by
        cases root z.2 <;> rfl
  have hbranch : Computable₂ (fun (queries : List PolynomialCode) (query : PolynomialCode) =>
      if root query then (Sum.inl true : Bool ⊕ List PolynomialCode)
      else (Sum.inr queries.tail : Bool ⊕ List PolynomialCode)) := hbranchFn.to₂
  have hstep : Partrec step := by
    exact (Partrec.optionCasesOn_right Primrec.list_head?.to_comp
      (Computable.const (Sum.inl false)) hbranch.partrec₂).of_eq fun queries => by
        cases h : queries.head? with
        | none => simp [step, rootSearchStep, h]
        | some query =>
            simp only [step, rootSearchStep, h]
            cases hq : root query <;> simp [hq]
  have hmem : ∀ queries, queries.any root ∈ step.fix queries := by
    intro queries
    induction queries with
    | nil =>
        rw [PFun.mem_fix_iff]
        left
        simp [step, rootSearchStep]
    | cons query tail ih =>
        rw [PFun.mem_fix_iff]
        by_cases hrootQuery : root query
        · left
          have hAny : (query :: tail).any root = true := by
            simp [List.any_cons, hrootQuery]
          rw [hAny]
          simp [step, rootSearchStep, hrootQuery]
        · right
          have hAny : (query :: tail).any root = tail.any root := by
            simp [List.any_cons, hrootQuery]
          rw [hAny]
          refine ⟨tail, ?_, ih⟩
          simp [step, rootSearchStep, hrootQuery]
  exact (Partrec.fix hstep).of_eq_tot hmem

theorem constraintSystem_computable
    (oracle : ComputablePred RationalPolynomialHasRoot) :
    ComputablePred Satisfies := by
  classical
  let rootDecision : PolynomialCode → Bool := fun q => decide (RationalPolynomialHasRoot q)
  have hroot : Computable rootDecision := oracle.decide
  have hqueries : Computable (fun queries : List PolynomialCode => queries.any rootDecision) :=
    computable_list_any_of rootDecision hroot
  have hcompile : Computable compile := primrec_compile.to_comp
  have hdecide : Computable (fun c : ConstraintSystem => decide (Satisfies c)) := by
    have hcompiled := hqueries.comp hcompile
    refine hcompiled.of_eq ?_
    intro c
    apply Bool.eq_iff_iff.mpr
    simpa only [List.any_eq_true, rootDecision, decide_eq_true_eq] using
      (compile_correct c).symm
  exact hdecide.computablePred

theorem constraintSystem_computable_of_compiler
    {α : Type*} [Primcodable α] (makeConstraints : α → ConstraintSystem)
    (hmake : Computable makeConstraints)
    (oracle : ComputablePred RationalPolynomialHasRoot) :
    ComputablePred (fun a => Satisfies (makeConstraints a)) := by
  classical
  exact (constraintSystem_computable oracle).decide.comp hmake |>.computablePred

/-- Indexed constraint generators are handled uniformly on the encoded pair
of an input and a natural-number test index. -/
theorem indexed_constraintSystem_computable
    {α : Type*} [Primcodable α] (makeConstraints : α → Nat → ConstraintSystem)
    (hmake : Computable₂ makeConstraints)
    (oracle : ComputablePred RationalPolynomialHasRoot) :
    ComputablePred (fun p : α × Nat => Satisfies (makeConstraints p.1 p.2)) := by
  have hmakePair : Computable (fun p : α × Nat => makeConstraints p.1 p.2) := hmake
  exact constraintSystem_computable_of_compiler
    (fun p : α × Nat => makeConstraints p.1 p.2) hmakePair oracle

example : compileClause [] = [] := by rfl

example : ¬ Satisfies ([] : ConstraintSystem) := by
  simp [Satisfies]

example : Satisfies ([[]] : ConstraintSystem) := by
  refine ⟨fun _ => 0, [], by simp, ?_⟩
  simp [clauseSatisfied]

example :
    Satisfies ([[(false, polyVar 0)]] : ConstraintSystem) := by
  refine ⟨fun _ => 0, [(false, polyVar 0)], by simp, ?_⟩
  simp [clauseSatisfied, atomSatisfied, polynomialValue_polyVar]

example :
    ¬ Satisfies ([[(false, polyConst [(1, 0)])]] : ConstraintSystem) := by
  simp [Satisfies, clauseSatisfied, atomSatisfied, polynomialValue_polyConst, coeffValue,
    coeffAtomValue]

example :
    Satisfies ([[(true, polyConst [(1, 0)])]] : ConstraintSystem) := by
  refine ⟨fun _ => 0, [(true, polyConst [(1, 0)])], by simp, ?_⟩
  norm_num [clauseSatisfied, atomSatisfied, polynomialValue_polyConst, coeffValue,
    coeffAtomValue]

example :
    Satisfies ([[(false, polyConst [(0, 0)])]] : ConstraintSystem) := by
  refine ⟨fun _ => 0, [(false, polyConst [(0, 0)])], by simp, ?_⟩
  norm_num [clauseSatisfied, atomSatisfied, polynomialValue_polyConst, coeffValue,
    coeffAtomValue]

example :
    Satisfies ([[(false, polyVar 0), (true, polyVar 1)]] : ConstraintSystem) := by
  refine ⟨(fun i => if i = 1 then 1 else 0),
    [(false, polyVar 0), (true, polyVar 1)], by simp, ?_⟩
  simp [clauseSatisfied, atomSatisfied, polynomialValue_polyVar]

example :
    Satisfies ([[(false, polyConst [(1, 0)])],
      [(false, polyVar 0)]] : ConstraintSystem) := by
  refine ⟨fun _ => 0, [(false, polyVar 0)], by simp, ?_⟩
  simp [clauseSatisfied, atomSatisfied, polynomialValue_polyVar]

end H10RationalCompiler
