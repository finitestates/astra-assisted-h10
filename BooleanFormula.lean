module

public import IntegerQueryAdapter

/-!
# Boolean formulas over rational polynomial constraints

Formulas use postfix syntax.  The token stream is an effective encoding built
from the existing atom code and the computable list encoding.  The
`ConstraintFormula` namespace provides the usual formula builder functions; for
example, `conjoin p q` encodes `p ∧ q`. Postfix codes with missing operands
have a fixed interpretation (a missing operand is `false`), and the final
stack's top entry is the result (or `false` for an empty stack). This makes the
semantics and compiler total on every encoded input.
-/

@[expose] public section

namespace H10RationalFormula

open H10RationalCompiler

/-- `none` is true, `some (inl a)` is an atom, and the four pairs on the right
encode false, negation, conjunction, and disjunction. -/
abbrev FormulaToken := Option (Sum Atom (Bool × Bool))

abbrev ConstraintFormula := List FormulaToken

namespace FormulaToken

def truth : FormulaToken := none
def atom (a : Atom) : FormulaToken := some (.inl a)
def falsity : FormulaToken := some (.inr (false, false))
def negation : FormulaToken := some (.inr (false, true))
def conjunction : FormulaToken := some (.inr (true, false))
def disjunction : FormulaToken := some (.inr (true, true))

end FormulaToken

namespace ConstraintFormula

def truth : ConstraintFormula := [FormulaToken.truth]
def falsity : ConstraintFormula := [FormulaToken.falsity]
def atom (a : Atom) : ConstraintFormula := [FormulaToken.atom a]
def negate (φ : ConstraintFormula) : ConstraintFormula := φ ++ [FormulaToken.negation]
def conjoin (φ ψ : ConstraintFormula) : ConstraintFormula :=
  φ ++ ψ ++ [FormulaToken.conjunction]
def disjoin (φ ψ : ConstraintFormula) : ConstraintFormula :=
  φ ++ ψ ++ [FormulaToken.disjunction]

end ConstraintFormula

def FormulaMeaning := (Nat → ℚ) → Prop

def popStack {α : Type*} (default : α) : List α → α × List α
  | [] => (default, [])
  | value :: rest => (value, rest)

theorem popStack_fst_eq_headD {α : Type*} (default : α) (stack : List α) :
    (popStack default stack).1 = stack.headD default := by
  cases stack <;> rfl

def complementAtom (a : Atom) : Atom := (!a.1, a.2)

def clauseSatisfied (x : Nat → ℚ) (clause : List Atom) : Prop :=
  ∀ a ∈ clause, atomSatisfied x a

def satisfiesAt (x : Nat → ℚ) (dnf : ConstraintSystem) : Prop :=
  ∃ clause ∈ dnf, clauseSatisfied x clause

def andDNF (left right : ConstraintSystem) : ConstraintSystem :=
  left.flatMap fun lhs => right.map fun rhs => lhs ++ rhs

def orDNF (left right : ConstraintSystem) : ConstraintSystem := left ++ right

def negateClause (clause : List Atom) : ConstraintSystem :=
  clause.map fun a => [complementAtom a]

/-- Negate a DNF by De Morgan's laws. -/
def negateDNF : ConstraintSystem → ConstraintSystem
  | [] => [[]]
  | clause :: rest => andDNF (negateClause clause) (negateDNF rest)

theorem mem_andDNF (left right : ConstraintSystem) (clause : List Atom) :
    clause ∈ andDNF left right ↔
      ∃ lhs ∈ left, ∃ rhs ∈ right, lhs ++ rhs = clause := by
  simp [andDNF, List.mem_flatMap, List.mem_map]

theorem satisfiesAt_append (x : Nat → ℚ) (left right : ConstraintSystem) :
    satisfiesAt x (left ++ right) ↔ satisfiesAt x left ∨ satisfiesAt x right := by
  unfold satisfiesAt
  constructor
  · rintro ⟨clause, hclause, hsat⟩
    rcases List.mem_append.mp hclause with hleft | hright
    · exact Or.inl ⟨clause, hleft, hsat⟩
    · exact Or.inr ⟨clause, hright, hsat⟩
  · rintro (⟨clause, hclause, hsat⟩ | ⟨clause, hclause, hsat⟩)
    · exact ⟨clause, List.mem_append_left _ hclause, hsat⟩
    · exact ⟨clause, List.mem_append_right _ hclause, hsat⟩

theorem clauseSatisfied_append (x : Nat → ℚ) (left right : List Atom) :
    clauseSatisfied x (left ++ right) ↔ clauseSatisfied x left ∧ clauseSatisfied x right := by
  unfold clauseSatisfied
  constructor
  · intro h
    constructor
    · intro a ha
      exact h a (List.mem_append_left _ ha)
    · intro a ha
      exact h a (List.mem_append_right _ ha)
  · rintro ⟨hleft, hright⟩ a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hleft a ha
    · exact hright a ha

theorem satisfiesAt_atom (x : Nat → ℚ) (a : Atom) :
    satisfiesAt x [[a]] ↔ atomSatisfied x a := by
  unfold satisfiesAt clauseSatisfied
  constructor
  · rintro ⟨clause, hclause, hsat⟩
    have hEq : clause = [a] := by simpa using hclause
    subst clause
    exact hsat a (by simp)
  · intro ha
    refine ⟨[a], by simp, ?_⟩
    intro b hb
    have : b = a := by simpa using hb
    subst b
    exact ha

theorem satisfiesAt_andDNF (x : Nat → ℚ) (left right : ConstraintSystem) :
    satisfiesAt x (andDNF left right) ↔
      satisfiesAt x left ∧ satisfiesAt x right := by
  constructor
  · rintro ⟨clause, hclause, hsat⟩
    rcases (mem_andDNF left right clause).mp hclause with
      ⟨lhs, hlhs, rhs, hrhs, hEq⟩
    subst clause
    have hparts : clauseSatisfied x lhs ∧ clauseSatisfied x rhs := by
      simpa [clauseSatisfied_append] using hsat
    exact ⟨⟨lhs, hlhs, hparts.1⟩, ⟨rhs, hrhs, hparts.2⟩⟩
  · rintro ⟨⟨lhs, hlhs, hleft⟩, ⟨rhs, hrhs, hright⟩⟩
    refine ⟨lhs ++ rhs, ?_, ?_⟩
    · exact (mem_andDNF left right (lhs ++ rhs)).2 ⟨lhs, hlhs, rhs, hrhs, rfl⟩
    · exact (clauseSatisfied_append x lhs rhs).2 ⟨hleft, hright⟩

theorem complementAtom_satisfied (x : Nat → ℚ) (a : Atom) :
    atomSatisfied x (complementAtom a) ↔ ¬ atomSatisfied x a := by
  cases a with
  | mk polarity polynomial =>
    cases polarity <;> simp [complementAtom, atomSatisfied]

theorem satisfiesAt_cons (x : Nat → ℚ) (clause : List Atom)
    (rest : ConstraintSystem) :
    satisfiesAt x (clause :: rest) ↔
      clauseSatisfied x clause ∨ satisfiesAt x rest := by
  unfold satisfiesAt
  constructor
  · rintro ⟨candidate, hmem, hsat⟩
    rcases List.mem_cons.mp hmem with hEq | htail
    · subst candidate
      exact Or.inl hsat
    · exact Or.inr ⟨candidate, htail, hsat⟩
  · rintro (hclause | ⟨candidate, hmem, hsat⟩)
    · exact ⟨clause, by simp, hclause⟩
    · exact ⟨candidate, List.mem_cons_of_mem _ hmem, hsat⟩

theorem clauseSatisfied_cons (x : Nat → ℚ) (a : Atom) (rest : List Atom) :
    clauseSatisfied x (a :: rest) ↔
      atomSatisfied x a ∧ clauseSatisfied x rest := by
  unfold clauseSatisfied
  constructor
  · intro h
    constructor
    · exact h a (by simp)
    · intro b hb
      exact h b (by simp [hb])
  · rintro ⟨ha, hr⟩ b hb
    rcases List.mem_cons.mp hb with hEq | htail
    · subst b
      exact ha
    · exact hr b htail

theorem satisfiesAt_negateClause (x : Nat → ℚ) (clause : List Atom) :
    satisfiesAt x (negateClause clause) ↔ ¬ clauseSatisfied x clause := by
  induction clause with
  | nil => simp [negateClause, satisfiesAt, clauseSatisfied]
  | cons a rest ih =>
    rw [show negateClause (a :: rest) = [complementAtom a] :: negateClause rest by rfl]
    rw [show [complementAtom a] :: negateClause rest =
      [[complementAtom a]] ++ negateClause rest by rfl]
    rw [satisfiesAt_append, satisfiesAt_atom, ih]
    rw [clauseSatisfied_cons]
    rw [complementAtom_satisfied]
    constructor
    · intro h hsat
      rcases hsat with ⟨ha, hrest⟩
      rcases h with hnot | hnotRest
      · exact hnot ha
      · exact hnotRest hrest
    · intro h
      by_cases ha : atomSatisfied x a
      · exact Or.inr (fun hrest => h ⟨ha, hrest⟩)
      · exact Or.inl ha

theorem satisfiesAt_negateDNF (x : Nat → ℚ) (dnf : ConstraintSystem) :
    satisfiesAt x (negateDNF dnf) ↔ ¬ satisfiesAt x dnf := by
  induction dnf with
  | nil => simp [negateDNF, satisfiesAt, clauseSatisfied]
  | cons clause rest ih =>
    rw [negateDNF, satisfiesAt_andDNF, satisfiesAt_negateClause, ih,
      satisfiesAt_cons]
    simp

def formulaStep (stack : List FormulaMeaning) (token : FormulaToken) :
    List FormulaMeaning :=
  match token with
  | none => (fun _ => True) :: stack
  | some (.inl a) => (fun x => atomSatisfied x a) :: stack
  | some (.inr (false, false)) => (fun _ => False) :: stack
  | some (.inr (false, true)) =>
      let popped := popStack (fun _ => False) stack
      (fun x => ¬ popped.1 x) :: popped.2
  | some (.inr (true, false)) =>
      let right := popStack (fun _ => False) stack
      let left := popStack (fun _ => False) right.2
      (fun x => left.1 x ∧ right.1 x) :: left.2
  | some (.inr (true, true)) =>
      let right := popStack (fun _ => False) stack
      let left := popStack (fun _ => False) right.2
      (fun x => left.1 x ∨ right.1 x) :: left.2

def dnfStep (stack : List ConstraintSystem) (token : FormulaToken) :
    List ConstraintSystem :=
  match token with
  | none => [[]] :: stack
  | some (.inl a) => [[a]] :: stack
  | some (.inr (false, false)) => [] :: stack
  | some (.inr (false, true)) =>
      let popped := popStack ([] : ConstraintSystem) stack
      negateDNF popped.1 :: popped.2
  | some (.inr (true, false)) =>
      let right := popStack ([] : ConstraintSystem) stack
      let left := popStack ([] : ConstraintSystem) right.2
      andDNF left.1 right.1 :: left.2
  | some (.inr (true, true)) =>
      let right := popStack ([] : ConstraintSystem) stack
      let left := popStack ([] : ConstraintSystem) right.2
      orDNF left.1 right.1 :: left.2

/-- Interpret a postfix formula code pointwise. Operators use `false` when an
operand is absent from the stack. -/
def FormulaHolds (x : Nat → ℚ) (φ : ConstraintFormula) : Prop :=
  ((φ.foldl formulaStep []).headD (fun _ => False)) x

def toDNF (φ : ConstraintFormula) : ConstraintSystem :=
  (φ.foldl dnfStep []).headD []

def FormulaSatisfies (φ : ConstraintFormula) : Prop :=
  ∃ x : Nat → ℚ, FormulaHolds x φ

def FormulaDNFRelation (meaning : FormulaMeaning) (dnf : ConstraintSystem) : Prop :=
  ∀ x, meaning x ↔ satisfiesAt x dnf

theorem popStack_forall₂ {α β : Type*} {R : α → β → Prop}
    (leftDefault : α) (rightDefault : β) {left : List α} {right : List β}
    (hDefault : R leftDefault rightDefault) (h : List.Forall₂ R left right) :
    R (popStack leftDefault left).1 (popStack rightDefault right).1 ∧
      List.Forall₂ R (popStack leftDefault left).2 (popStack rightDefault right).2 := by
  cases left with
  | nil =>
    cases right with
    | nil =>
      simpa [popStack] using
        And.intro hDefault (List.Forall₂.nil (R := R) : List.Forall₂ R [] [])
    | cons r rs => cases h
  | cons l ls =>
    cases right with
    | nil => cases h
    | cons r rs =>
      cases h with
      | cons hHead hTail => exact ⟨hHead, hTail⟩

theorem forall₂_headD {α β : Type*} {R : α → β → Prop}
    (leftDefault : α) (rightDefault : β) {left : List α} {right : List β}
    (hDefault : R leftDefault rightDefault) (h : List.Forall₂ R left right) :
    R (left.headD leftDefault) (right.headD rightDefault) := by
  cases left with
  | nil =>
    cases right with
    | nil => exact hDefault
    | cons r rs => cases h
  | cons l ls =>
    cases right with
    | nil => cases h
    | cons r rs =>
      cases h with
      | cons hHead hTail => exact hHead

theorem formulaStep_preserves (token : FormulaToken)
    (meanings : List FormulaMeaning) (dnfs : List ConstraintSystem)
    (h : List.Forall₂ FormulaDNFRelation meanings dnfs) :
    List.Forall₂ FormulaDNFRelation (formulaStep meanings token) (dnfStep dnfs token) := by
  cases token with
  | none =>
    change List.Forall₂ FormulaDNFRelation ((fun _ => True) :: meanings) ([[]] :: dnfs)
    exact .cons (by intro x; simp [satisfiesAt, clauseSatisfied]) h
  | some rest =>
    cases rest with
    | inl a =>
      change List.Forall₂ FormulaDNFRelation
        ((fun x => atomSatisfied x a) :: meanings) ([[a]] :: dnfs)
      exact .cons (by intro x; exact (satisfiesAt_atom x a).symm) h
    | inr op =>
      rcases op with ⟨b₁, b₂⟩
      cases b₁ with
      | false =>
        cases b₂ with
        | false =>
          change List.Forall₂ FormulaDNFRelation ((fun _ => False) :: meanings) ([] :: dnfs)
          exact .cons (by intro x; simp [satisfiesAt]) h
        | true =>
          have hDefault : FormulaDNFRelation (fun _ => False) ([] : ConstraintSystem) := by
            intro x
            simp [satisfiesAt]
          rcases popStack_forall₂ (fun _ => False) ([] : ConstraintSystem) hDefault h with
            ⟨hHead, hTail⟩
          change List.Forall₂ FormulaDNFRelation
            ((fun x => ¬ (popStack (fun _ => False) meanings).1 x) ::
              (popStack (fun _ => False) meanings).2)
            (negateDNF (popStack ([] : ConstraintSystem) dnfs).1 ::
              (popStack ([] : ConstraintSystem) dnfs).2)
          apply List.Forall₂.cons
          · intro x
            change (¬ (popStack (fun _ => False) meanings).1 x) ↔
              satisfiesAt x (negateDNF (popStack ([] : ConstraintSystem) dnfs).1)
            rw [satisfiesAt_negateDNF]
            exact not_congr (hHead x)
          · exact hTail
      | true =>
        cases b₂ with
        | false =>
          have hDefault : FormulaDNFRelation (fun _ => False) ([] : ConstraintSystem) := by
            intro x
            simp [satisfiesAt]
          let rightMeanings := popStack (fun _ => False) meanings
          let rightDnfs := popStack ([] : ConstraintSystem) dnfs
          rcases popStack_forall₂ (fun _ => False) ([] : ConstraintSystem) hDefault h with
            ⟨hRight, hRest⟩
          let leftMeanings := popStack (fun _ => False) rightMeanings.2
          let leftDnfs := popStack ([] : ConstraintSystem) rightDnfs.2
          rcases popStack_forall₂ (fun _ => False) ([] : ConstraintSystem) hDefault hRest with
            ⟨hLeft, hTail⟩
          change List.Forall₂ FormulaDNFRelation
            ((fun x => leftMeanings.1 x ∧ rightMeanings.1 x) :: leftMeanings.2)
            (andDNF leftDnfs.1 rightDnfs.1 :: leftDnfs.2)
          apply List.Forall₂.cons
          · intro x
            change (leftMeanings.1 x ∧ rightMeanings.1 x) ↔
              satisfiesAt x (andDNF leftDnfs.1 rightDnfs.1)
            rw [satisfiesAt_andDNF]
            exact and_congr (hLeft x) (hRight x)
          · exact hTail
        | true =>
          have hDefault : FormulaDNFRelation (fun _ => False) ([] : ConstraintSystem) := by
            intro x
            simp [satisfiesAt]
          let rightMeanings := popStack (fun _ => False) meanings
          let rightDnfs := popStack ([] : ConstraintSystem) dnfs
          rcases popStack_forall₂ (fun _ => False) ([] : ConstraintSystem) hDefault h with
            ⟨hRight, hRest⟩
          let leftMeanings := popStack (fun _ => False) rightMeanings.2
          let leftDnfs := popStack ([] : ConstraintSystem) rightDnfs.2
          rcases popStack_forall₂ (fun _ => False) ([] : ConstraintSystem) hDefault hRest with
            ⟨hLeft, hTail⟩
          change List.Forall₂ FormulaDNFRelation
            ((fun x => leftMeanings.1 x ∨ rightMeanings.1 x) :: leftMeanings.2)
            (orDNF leftDnfs.1 rightDnfs.1 :: leftDnfs.2)
          apply List.Forall₂.cons
          · intro x
            change (leftMeanings.1 x ∨ rightMeanings.1 x) ↔
              satisfiesAt x (orDNF leftDnfs.1 rightDnfs.1)
            rw [orDNF, satisfiesAt_append]
            exact or_congr (hLeft x) (hRight x)
          · exact hTail

theorem formulaCode_machine_correct (φ : ConstraintFormula)
    (meanings : List FormulaMeaning) (dnfs : List ConstraintSystem)
    (h : List.Forall₂ FormulaDNFRelation meanings dnfs) :
    List.Forall₂ FormulaDNFRelation (φ.foldl formulaStep meanings) (φ.foldl dnfStep dnfs) := by
  induction φ generalizing meanings dnfs with
  | nil => exact h
  | cons token rest ih =>
    simp only [List.foldl_cons]
    exact ih (formulaStep meanings token) (dnfStep dnfs token)
      (formulaStep_preserves token meanings dnfs h)

theorem formulaHolds_iff_toDNF (φ : ConstraintFormula) (x : Nat → ℚ) :
    FormulaHolds x φ ↔ satisfiesAt x (toDNF φ) := by
  have hDefault : FormulaDNFRelation (fun _ => False) ([] : ConstraintSystem) := by
    intro y
    simp [satisfiesAt]
  have h := formulaCode_machine_correct φ [] [] List.Forall₂.nil
  have hFinal := forall₂_headD (fun _ => False) ([] : ConstraintSystem) hDefault h
  change ((φ.foldl formulaStep []).headD (fun _ => False)) x ↔
    satisfiesAt x ((φ.foldl dnfStep []).headD [])
  exact hFinal x

theorem formula_to_dnf_correct (φ : ConstraintFormula) :
    FormulaSatisfies φ ↔ H10RationalCompiler.Satisfies (toDNF φ) := by
  change (∃ x : Nat → ℚ, FormulaHolds x φ) ↔
    ∃ x : Nat → ℚ, satisfiesAt x (toDNF φ)
  exact exists_congr fun x => formulaHolds_iff_toDNF φ x

example : Primcodable FormulaToken := inferInstance

example : Primcodable ConstraintFormula := inferInstance

theorem primrec_complementAtom : Primrec complementAtom := by
  unfold complementAtom
  exact Primrec.pair (Primrec.not.comp Primrec.fst) Primrec.snd

theorem primrec_negateClause : Primrec negateClause := by
  unfold negateClause
  have hentry : Primrec₂ (fun (_ : List Atom) (a : Atom) => [complementAtom a]) := by
    apply Primrec₂.mk
    exact Primrec₂.comp Primrec.list_cons
      (primrec_complementAtom.comp Primrec.snd) (Primrec.const [])
  exact Primrec.list_map Primrec.id hentry

theorem primrec_andDNF_uncurried :
    Primrec (fun p : ConstraintSystem × ConstraintSystem => andDNF p.1 p.2) := by
  unfold andDNF
  have happend : Primrec (fun z : ((ConstraintSystem × ConstraintSystem) × List Atom) × List Atom =>
      z.1.2 ++ z.2) := by
    exact Primrec₂.comp Primrec.list_append
      (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hmap : Primrec (fun z : (ConstraintSystem × ConstraintSystem) × List Atom =>
      z.1.2.map fun rhs => z.2 ++ rhs) := by
    exact Primrec.list_map (Primrec.snd.comp Primrec.fst) (Primrec₂.mk happend)
  exact Primrec.list_flatMap Primrec.fst (Primrec₂.mk hmap)

theorem primrec_andDNF : Primrec₂ andDNF :=
  Primrec₂.mk primrec_andDNF_uncurried

theorem primrec_orDNF : Primrec₂ orDNF := by
  unfold orDNF
  exact Primrec.list_append

def negateDNFFold (dnf : ConstraintSystem) : ConstraintSystem :=
  dnf.foldr (fun clause result => andDNF (negateClause clause) result) [[]]

theorem negateDNF_eq_negateDNFFold (dnf : ConstraintSystem) :
    negateDNF dnf = negateDNFFold dnf := by
  induction dnf with
  | nil => rfl
  | cons clause rest ih => simp [negateDNF, negateDNFFold, ih]

theorem primrec_negateDNFFold : Primrec negateDNFFold := by
  unfold negateDNFFold
  have hstepUncurried :
      Primrec (fun z : ConstraintSystem × (List Atom × ConstraintSystem) =>
        andDNF (negateClause z.2.1) z.2.2) := by
    exact Primrec₂.comp primrec_andDNF
      (primrec_negateClause.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.id))
  have hstep : Primrec₂ (fun (_ : ConstraintSystem) (p : List Atom × ConstraintSystem) =>
      andDNF (negateClause p.1) p.2) := Primrec₂.mk hstepUncurried
  exact Primrec.list_foldr Primrec.id (Primrec.const [[]]) hstep

theorem primrec_negateDNF : Primrec negateDNF :=
  Primrec.of_eq primrec_negateDNFFold fun dnf => (negateDNF_eq_negateDNFFold dnf).symm

theorem primrec_popStack (default : ConstraintSystem) :
    Primrec (popStack default) := by
  have hhead : Primrec fun stack : List ConstraintSystem =>
      (stack.head?).getD default := by
    exact Primrec₂.comp Primrec.option_getD Primrec.list_head?
      (Primrec.const default)
  exact (Primrec.pair hhead Primrec.list_tail).of_eq fun stack => by
    cases stack <;> rfl

def dnfNegStep (stack : List ConstraintSystem) : List ConstraintSystem :=
  let popped := popStack ([] : ConstraintSystem) stack
  negateDNF popped.1 :: popped.2

def dnfAndStep (stack : List ConstraintSystem) : List ConstraintSystem :=
  let right := popStack ([] : ConstraintSystem) stack
  let left := popStack ([] : ConstraintSystem) right.2
  andDNF left.1 right.1 :: left.2

def dnfOrStep (stack : List ConstraintSystem) : List ConstraintSystem :=
  let right := popStack ([] : ConstraintSystem) stack
  let left := popStack ([] : ConstraintSystem) right.2
  orDNF left.1 right.1 :: left.2

def dnfTruthStep (stack : List ConstraintSystem) : List ConstraintSystem :=
  ([[]] : ConstraintSystem) :: stack

def dnfFalseStep (stack : List ConstraintSystem) : List ConstraintSystem :=
  ([] : ConstraintSystem) :: stack

def dnfAtomStep (stack : List ConstraintSystem) (a : Atom) :
    List ConstraintSystem := [[a]] :: stack

theorem primrec_dnfNegStep : Primrec dnfNegStep := by
  unfold dnfNegStep
  have hpop := primrec_popStack ([] : ConstraintSystem)
  exact Primrec₂.comp Primrec.list_cons
    (primrec_negateDNF.comp (Primrec.fst.comp hpop))
    (Primrec.snd.comp hpop)

theorem primrec_dnfAndStep : Primrec dnfAndStep := by
  unfold dnfAndStep
  have hpop := primrec_popStack ([] : ConstraintSystem)
  have hrightHead := Primrec.fst.comp hpop
  have hrightTail := Primrec.snd.comp hpop
  have hleft := hpop.comp hrightTail
  have hhead := primrec_andDNF_uncurried.comp
    (Primrec.pair (Primrec.fst.comp hleft) hrightHead)
  exact Primrec₂.comp Primrec.list_cons hhead (Primrec.snd.comp hleft)

theorem primrec_dnfOrStep : Primrec dnfOrStep := by
  unfold dnfOrStep
  have hpop := primrec_popStack ([] : ConstraintSystem)
  have hrightHead := Primrec.fst.comp hpop
  have hrightTail := Primrec.snd.comp hpop
  have hleft := hpop.comp hrightTail
  have hhead := Primrec₂.comp Primrec.list_append
    (Primrec.fst.comp hleft) hrightHead
  exact Primrec₂.comp Primrec.list_cons hhead (Primrec.snd.comp hleft)

theorem primrec_dnfTruthStep : Primrec dnfTruthStep := by
  unfold dnfTruthStep
  exact Primrec₂.comp Primrec.list_cons (Primrec.const ([[]] : ConstraintSystem)) Primrec.id

theorem primrec_dnfFalseStep : Primrec dnfFalseStep := by
  unfold dnfFalseStep
  exact Primrec₂.comp Primrec.list_cons (Primrec.const ([] : ConstraintSystem)) Primrec.id

theorem primrec_dnfAtomStep : Primrec₂ dnfAtomStep := by
  unfold dnfAtomStep
  apply Primrec₂.mk
  have hSingleton : Primrec (fun a : Atom => [a]) :=
    Primrec₂.comp Primrec.list_cons Primrec.id (Primrec.const [])
  have hDoubleton : Primrec (fun a : Atom => [ [a] ]) :=
    Primrec₂.comp Primrec.list_cons hSingleton (Primrec.const [])
  exact Primrec₂.comp Primrec.list_cons
    (hDoubleton.comp Primrec.snd) Primrec.fst

theorem primrec_dnfStep_uncurried :
    Primrec (fun p : List ConstraintSystem × FormulaToken => dnfStep p.1 p.2) := by
  have hTruth : Primrec fun p : List ConstraintSystem × FormulaToken => dnfTruthStep p.1 :=
    primrec_dnfTruthStep.comp Primrec.fst
  have hFalse : Primrec fun p : List ConstraintSystem × FormulaToken => dnfFalseStep p.1 :=
    primrec_dnfFalseStep.comp Primrec.fst
  have hSome : Primrec (fun p : List ConstraintSystem × (Atom ⊕ (Bool × Bool)) =>
      Sum.elim (γ := List ConstraintSystem) (fun a : Atom => dnfAtomStep p.1 a)
        (fun op : Bool × Bool => bif op.1 then
          bif op.2 then dnfOrStep p.1 else dnfAndStep p.1
        else bif op.2 then dnfNegStep p.1 else dnfFalseStep p.1) p.2) := by
    have hAtom : Primrec₂ (fun (p : List ConstraintSystem) (a : Atom) => dnfAtomStep p a) :=
      primrec_dnfAtomStep
    have hOpFunction : Primrec (fun p : List ConstraintSystem × (Bool × Bool) =>
        bif p.2.1 then
          bif p.2.2 then dnfOrStep p.1 else dnfAndStep p.1
        else bif p.2.2 then dnfNegStep p.1 else dnfFalseStep p.1) := by
      have hFirst : Primrec (fun p : List ConstraintSystem × (Bool × Bool) => p.2.1) :=
        Primrec.fst.comp Primrec.snd
      have hSecond : Primrec (fun p : List ConstraintSystem × (Bool × Bool) => p.2.2) :=
        Primrec.snd.comp Primrec.snd
      exact Primrec.cond hFirst
        (Primrec.cond hSecond
          (primrec_dnfOrStep.comp Primrec.fst)
          (primrec_dnfAndStep.comp Primrec.fst))
        (Primrec.cond hSecond
          (primrec_dnfNegStep.comp Primrec.fst)
          (primrec_dnfFalseStep.comp Primrec.fst))
    have hAtomBranch : Primrec₂
        (fun (p : List ConstraintSystem × (Atom ⊕ (Bool × Bool))) (a : Atom) =>
          dnfAtomStep p.1 a) := by
      apply Primrec₂.mk
      exact Primrec₂.comp primrec_dnfAtomStep
        (Primrec.fst.comp Primrec.fst) Primrec.snd
    have hOpBranch : Primrec₂
        (fun (p : List ConstraintSystem × (Atom ⊕ (Bool × Bool))) (op : Bool × Bool) =>
          bif op.1 then
            bif op.2 then dnfOrStep p.1 else dnfAndStep p.1
          else bif op.2 then dnfNegStep p.1 else dnfFalseStep p.1) := by
      apply Primrec₂.mk
      exact hOpFunction.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
    exact Primrec.sumCasesOn Primrec.snd hAtomBranch hOpBranch
  have hSomeBranch : Primrec₂
      (fun (p : List ConstraintSystem × FormulaToken)
        (tag : Atom ⊕ (Bool × Bool)) =>
          Sum.elim (γ := List ConstraintSystem) (fun a : Atom => dnfAtomStep p.1 a)
            (fun op : Bool × Bool => bif op.1 then
              bif op.2 then dnfOrStep p.1 else dnfAndStep p.1
            else bif op.2 then dnfNegStep p.1 else dnfFalseStep p.1) tag) := by
    apply Primrec₂.mk
    exact hSome.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hAll : Primrec (fun p : List ConstraintSystem × FormulaToken =>
      Option.casesOn (motive := fun _ : Option (Atom ⊕ (Bool × Bool)) =>
        List ConstraintSystem) p.2 (dnfTruthStep p.1) (fun tag =>
        Sum.elim (γ := List ConstraintSystem) (fun a : Atom => dnfAtomStep p.1 a)
          (fun op : Bool × Bool => bif op.1 then
            bif op.2 then dnfOrStep p.1 else dnfAndStep p.1
          else bif op.2 then dnfNegStep p.1 else dnfFalseStep p.1) tag)) :=
    Primrec.option_casesOn Primrec.snd hTruth hSomeBranch
  exact hAll.of_eq fun ⟨stack, token⟩ => by
    cases token with
    | none => rfl
    | some tag =>
      cases tag with
      | inl a => rfl
      | inr op => cases op with | mk b₁ b₂ => cases b₁ <;> cases b₂ <;> rfl

theorem primrec_fold_dnfStep : Primrec (fun φ : ConstraintFormula => φ.foldl dnfStep []) := by
  have hstepUncurried :
      Primrec (fun z : ConstraintFormula × (List ConstraintSystem × FormulaToken) =>
        dnfStep z.2.1 z.2.2) := by
    exact primrec_dnfStep_uncurried.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  have hstep : Primrec₂ (fun (_ : ConstraintFormula) (p : List ConstraintSystem × FormulaToken) =>
      dnfStep p.1 p.2) := Primrec₂.mk hstepUncurried
  exact Primrec.list_foldl Primrec.id (Primrec.const []) hstep

theorem primrec_toDNF : Primrec toDNF := by
  exact (Primrec.list_headI.comp primrec_fold_dnfStep).of_eq fun φ => by
    unfold toDNF
    cases φ.foldl dnfStep [] <;> rfl

theorem formulaSatisfies_computable_of_h10Q
    (oracle : ComputablePred H10RationalQueryAdapter.IntegerPolynomialHasRationalRoot) :
    ComputablePred FormulaSatisfies := by
  classical
  have hsystem := H10RationalQueryAdapter.constraintSystem_computable_of_h10Q oracle
  have htoDNF : Computable toDNF := primrec_toDNF.to_comp
  have hcompiled : Computable (fun φ : ConstraintFormula =>
      decide (H10RationalCompiler.Satisfies (toDNF φ))) :=
    hsystem.decide.comp htoDNF
  have hformula : Computable (fun φ : ConstraintFormula => decide (FormulaSatisfies φ)) := by
    refine hcompiled.of_eq fun φ => ?_
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using (formula_to_dnf_correct φ).symm
  exact hformula.computablePred

theorem indexed_formulaSatisfies_computable_of_h10Q
    {α : Type*} [Primcodable α]
    (makeFormula : α → Nat → ConstraintFormula)
    (hmake : Computable₂ makeFormula)
    (oracle : ComputablePred H10RationalQueryAdapter.IntegerPolynomialHasRationalRoot) :
    ComputablePred (fun p : α × Nat =>
      FormulaSatisfies (makeFormula p.1 p.2)) := by
  classical
  have hmakePair : Computable (fun p : α × Nat => makeFormula p.1 p.2) := hmake
  exact (formulaSatisfies_computable_of_h10Q oracle).decide.comp hmakePair |>.computablePred

example : toDNF ConstraintFormula.truth = [[]] := by rfl

example : toDNF ConstraintFormula.falsity = [] := by rfl

example : toDNF (ConstraintFormula.atom (false, polyVar 3)) =
    [[(false, polyVar 3)]] := by rfl

example : toDNF (ConstraintFormula.atom (true, polyVar 3)) =
    [[(true, polyVar 3)]] := by rfl

example : toDNF (ConstraintFormula.negate (ConstraintFormula.atom (false, polyVar 3))) =
    [[(true, polyVar 3)]] := by rfl

example : toDNF (ConstraintFormula.negate (ConstraintFormula.negate
    (ConstraintFormula.atom (true, polyVar 3)))) =
    [[(true, polyVar 3)]] := by rfl

example : toDNF (ConstraintFormula.negate (ConstraintFormula.conjoin
    (ConstraintFormula.atom (false, polyVar 1))
    (ConstraintFormula.atom (true, polyVar 2)))) =
      toDNF (ConstraintFormula.disjoin
        (ConstraintFormula.negate (ConstraintFormula.atom (false, polyVar 1)))
        (ConstraintFormula.negate (ConstraintFormula.atom (true, polyVar 2)))) := by rfl

example : toDNF (ConstraintFormula.conjoin
    (ConstraintFormula.atom (false, polyVar 0))
    (ConstraintFormula.disjoin
      (ConstraintFormula.atom (true, polyVar 1))
      (ConstraintFormula.atom (false, polyVar 2)))) =
      [[(false, polyVar 0), (true, polyVar 1)],
        [(false, polyVar 0), (false, polyVar 2)]] := by rfl

example (x : Nat → ℚ) :
    FormulaHolds x (ConstraintFormula.atom (false, polyVar 0)) ↔ x 0 = 0 := by
  simp [FormulaHolds, ConstraintFormula.atom, FormulaToken.atom, formulaStep,
    atomSatisfied, List.headD]

example (x : Nat → ℚ) :
    FormulaHolds x (ConstraintFormula.atom (true, polyVar 0)) ↔ x 0 ≠ 0 := by
  simp [FormulaHolds, ConstraintFormula.atom, FormulaToken.atom, formulaStep,
    atomSatisfied, List.headD]

example (x : Nat → ℚ) :
    FormulaHolds x (ConstraintFormula.negate (ConstraintFormula.atom (true, polyVar 0))) ↔
      x 0 = 0 := by
  simp [FormulaHolds, ConstraintFormula.negate, ConstraintFormula.atom,
    FormulaToken.atom, FormulaToken.negation, formulaStep, atomSatisfied, popStack,
    List.headD]

end H10RationalFormula
