module

public import BooleanFormula

/-!
# Effective finite ground-test syntax

This module formalizes the finite, effective compiler layer described in
Section 2 of the project paper.  It uses a generic recursively presented
prenex theory: a concrete presentation of the paper's full elliptic and
valuation axiom scheme can be supplied as the `axioms` input.  The compiler
itself produces the four finite constraint families (ring operations,
function congruence, Skolemized universal instances, and positive-existential
witnesses) over the existing rational polynomial atom language.

Terms and formulas are serialized as postfix lists rather than Lean recursive
inductives.  This keeps the syntax primitive-recursive and gives each function
symbol an explicit namespace, name, and arity.
-/

@[expose] public section

namespace H10RationalGroundTests

open H10RationalCompiler H10RationalQueryAdapter H10RationalFormula

/-! ## Postfix syntax codes -/

/-- A term token is a pair `(tag, payload)`.  Tags `0` through `7` mean zero,
one, addition, multiplication, negation, bound variable, named input constant,
and function application. -/
abbrev TermToken := Nat × Nat
abbrev TermCode := List TermToken

/-- A formula token stores a tag and two term codes.  Tags `0` through `6`
mean truth, falsehood, equality, disequality, negation, conjunction, and
disjunction. -/
abbrev QFToken := Nat × (TermCode × TermCode)
abbrev QFCode := List QFToken
abbrev GroundTermCode := Nat

/-- A prenex axiom is a quantifier prefix (`true` means universal) and a
quantifier-free matrix.  Matrix variables are numbered in prefix order. -/
abbrev PrenexAxiom := List Bool × QFCode

/-- A positive-existential condition is an effective Boolean formula over
the existing rational polynomial atoms. Variable `0` is its input and
variables `1` through `witnessCount` are existential witnesses. Keeping the
matrix in `ConstraintFormula` also lets fixed rational coefficients be
represented directly by the existing coefficient codes. -/
abbrev PositiveExistential := Nat × ConstraintFormula

def functionSymbolArity (symbol : Nat) : Nat := (Nat.unpair symbol).2

/-! ## Well-formedness conditions -/

/-- The postfix term reader's stack-depth transition. `none` means that the
prefix is malformed. -/
def termCodeDepthStep (variableCount : Nat) (depth : Option Nat)
    (part : TermToken) : Option Nat := by
  cases depth with
  | none => exact none
  | some d =>
    exact if part.1 == 0 || part.1 == 1 || part.1 == 6 then some (d + 1)
      else if part.1 == 2 || part.1 == 3 then
        if 2 ≤ d then some (d - 1) else none
      else if part.1 == 4 then
        if 1 ≤ d then some d else none
      else if part.1 == 5 then
        if part.2 < variableCount then some (d + 1) else none
      else if part.1 == 7 then
        let arity := functionSymbolArity part.2
        if arity ≤ d then some (d - arity + 1) else none
      else none

def validTermCode (variableCount : Nat) (code : TermCode) : Bool :=
  code.foldl (termCodeDepthStep variableCount) (some 0) == some 1

/-- A term code is valid when it parses to exactly one stack value, and every
variable reference is below `variableCount`. -/
def ValidTermCode (variableCount : Nat) (code : TermCode) : Prop :=
  validTermCode variableCount code = true

def qfTokenTermsValid (variableCount : Nat) (part : QFToken) : Bool :=
  if part.1 == 2 || part.1 == 3 then
    validTermCode variableCount part.2.1 &&
      validTermCode variableCount part.2.2
  else part.1 ≤ 6

def qfCodeDepthStep (variableCount : Nat) (depth : Option Nat)
    (part : QFToken) : Option Nat := by
  cases depth with
  | none => exact none
  | some d =>
    exact if part.1 == 0 || part.1 == 1 then some (d + 1)
      else if part.1 == 2 || part.1 == 3 then
        if qfTokenTermsValid variableCount part then some (d + 1) else none
      else if part.1 == 4 then
        if 1 ≤ d then some d else none
      else if part.1 == 5 || part.1 == 6 then
        if 2 ≤ d then some (d - 1) else none
      else none

/-- A quantifier-free formula is valid when its postfix parse ends with one
formula and every embedded term is valid for the supplied variable range. -/
def ValidQFCode (variableCount : Nat) (code : QFCode) : Prop :=
  code.foldl (qfCodeDepthStep variableCount) (some 0) = some 1

def ValidPrenexAxiom (sentence : PrenexAxiom) : Prop :=
  ValidQFCode sentence.1.length sentence.2

def positiveFormulaDepthStep (variableCount : Nat) (depth : Option Nat)
    (part : FormulaToken) : Option Nat := by
  cases depth with
  | none => exact none
  | some d =>
    exact match part with
      | none => some (d + 1)
      | some (.inl atom) =>
        if atom.1 then none else
        if ∀ i ∈ allVariables atom.2, i < variableCount then some (d + 1) else none
      | some (.inr (false, false)) => some (d + 1)
      | some (.inr (false, true)) => none
      | some (.inr (true, false)) => if 2 ≤ d then some (d - 1) else none
      | some (.inr (true, true)) => if 2 ≤ d then some (d - 1) else none

/-- Positive existential matrices use only equations and positive Boolean
connectives. The distinguished input variable is `0`; the remaining declared
variables are existential witnesses. -/
def ValidPositiveExistential (phi : PositiveExistential) : Prop :=
  phi.2.foldl (positiveFormulaDepthStep (phi.1 + 1)) (some 0) = some 1

/-- Function symbols are encoded as `(namespace, name, arity)`.  Namespace
zero is reserved for ring operations, one for functions in the recursive
theory, and two for generated Skolem functions. -/
def functionSymbolCode (ns name arity : Nat) : Nat :=
  Nat.pair (Nat.pair ns name) arity

def token (tag payload : Nat) : TermToken := (tag, payload)

def zeroToken : TermToken := token 0 0
def oneToken : TermToken := token 1 0
def addToken : TermToken := token 2 0
def mulToken : TermToken := token 3 0
def negToken : TermToken := token 4 0
def variableToken (i : Nat) : TermToken := token 5 i
def inputToken (i : Nat) : TermToken := token 6 i
def functionToken (symbol : Nat) : TermToken := token 7 symbol

def zeroOpenTerm : TermCode := [zeroToken]
def oneOpenTerm : TermCode := [oneToken]
def inputOpenTerm (i : Nat) : TermCode := [inputToken i]

def zeroTerm : GroundTermCode := Nat.pair 0 0
def oneTerm : GroundTermCode := Nat.pair 0 1
def inputTerm (i : Nat) : GroundTermCode := Nat.pair 0 (i + 2)

def termLabel (t : GroundTermCode) : Nat := Nat.pair 0 t

def witnessLabel (t : GroundTermCode) (i : Nat) : Nat :=
  Nat.pair 1 (Nat.pair t i)

theorem witnessLabel_fresh (t u : GroundTermCode) (i : Nat) :
    witnessLabel t i ≠ termLabel u := by
  intro h
  have h' := Nat.pair_eq_pair.mp h
  omega

theorem witnessLabel_injective :
    Function.Injective fun p : GroundTermCode × Nat => witnessLabel p.1 p.2 := by
  intro p q h
  have h' := Nat.pair_eq_pair.mp h
  have h'' := Nat.pair_eq_pair.mp h'.2
  exact Prod.ext h''.1 h''.2

theorem termLabel_injective : Function.Injective termLabel := by
  intro t u h
  exact (Nat.pair_eq_pair.mp h).2

/-! ## Total postfix term reader -/

def builtinAddSymbol : Nat := functionSymbolCode 0 2 2
def builtinMulSymbol : Nat := functionSymbolCode 0 3 2
def builtinNegSymbol : Nat := functionSymbolCode 0 4 1

/-- Applications use an injective paired descriptor.  The second component is
above every argument code, so a generated application cannot alias an
argument.  Unused natural codes serve as extra named constants; this total
extension keeps the ground-term enumeration simple and effective. -/
def applicationTerm (symbol : Nat) (arguments : List GroundTermCode) :
    GroundTermCode :=
  let descriptor := Encodable.encode (symbol, arguments)
  let bound := arguments.foldl max 0 + 1
  Nat.pair 1 (Nat.pair descriptor bound)

theorem applicationTerm_injective :
    Function.Injective fun p : Nat × List GroundTermCode =>
      applicationTerm p.1 p.2 := by
  intro p q h
  have houter := Nat.pair_eq_pair.mp h
  have hinner := Nat.pair_eq_pair.mp houter.2
  have hdescriptor :
      Encodable.encode (p.1, p.2) = Encodable.encode (q.1, q.2) := hinner.1
  have hpair : (p.1, p.2) = (q.1, q.2) :=
    Encodable.encode_injective hdescriptor
  exact hpair

theorem natPair_second_le (a b : Nat) : b ≤ Nat.pair a b := by
  by_cases h : a < b
  · rw [Nat.pair, ite_eq_left h]
    have hbb := Nat.le_mul_self b
    omega
  · rw [Nat.pair, ite_eq_right h]
    omega

theorem natPair_one_gt (n : Nat) : n < Nat.pair 1 n := by
  by_cases h : 1 < n
  · rw [Nat.pair, ite_eq_left h]
    have hn : 2 ≤ n := by omega
    have hnn := Nat.le_mul_self n
    omega
  · rw [Nat.pair, ite_eq_right h]
    omega

theorem foldl_max_self (xs : List Nat) (n : Nat) :
    n ≤ xs.foldl max n := by
  induction xs generalizing n with
  | nil => simp
  | cons head tail ih =>
    change n ≤ tail.foldl max (max n head)
    exact le_trans (Nat.le_max_left n head) (ih (max n head))

theorem foldl_max_mono (xs : List Nat) {m n : Nat} (h : m ≤ n) :
    xs.foldl max m ≤ xs.foldl max n := by
  induction xs generalizing m n with
  | nil => exact h
  | cons head tail ih =>
    change tail.foldl max (max m head) ≤ tail.foldl max (max n head)
    apply ih
    exact max_le_max h (le_refl head)

theorem mem_le_foldl_max (xs : List Nat) (a : Nat) (ha : a ∈ xs) :
    a ≤ xs.foldl max 0 := by
  induction xs with
  | nil => simp at ha
  | cons head tail ih =>
    rcases List.mem_cons.mp ha with hhead | htail
    · subst a
      change head ≤ tail.foldl max (max 0 head)
      exact le_trans (Nat.le_max_right 0 head) (foldl_max_self tail (max 0 head))
    · change a ≤ tail.foldl max (max 0 head)
      exact le_trans (ih htail)
        (foldl_max_mono tail (Nat.le_max_left 0 head))

theorem applicationTerm_gt_arg (symbol : Nat) (arguments : List GroundTermCode)
    (arg : GroundTermCode) (harg : arg ∈ arguments) :
    arg < applicationTerm symbol arguments := by
  unfold applicationTerm
  have hargBound : arg < arguments.foldl max 0 + 1 := by
    have h := mem_le_foldl_max arguments arg harg
    exact Nat.lt_succ_of_le h
  have hbound : arguments.foldl max 0 + 1 ≤
      Nat.pair (Encodable.encode (symbol, arguments))
        (arguments.foldl max 0 + 1) :=
    natPair_second_le _ _
  have houter := natPair_one_gt
    (Nat.pair (Encodable.encode (symbol, arguments))
      (arguments.foldl max 0 + 1))
  exact lt_of_lt_of_le hargBound (le_trans hbound (Nat.le_of_lt houter))

theorem applicationTerm_not_arg (symbol : Nat) (arguments : List GroundTermCode)
    (arg : GroundTermCode) (harg : arg ∈ arguments) :
    applicationTerm symbol arguments ≠ arg := by
  intro h
  have hlt := applicationTerm_gt_arg symbol arguments arg harg
  exact Nat.ne_of_gt hlt h

theorem primrec_functionSymbolCode : Primrec fun p : Nat × (Nat × Nat) =>
    functionSymbolCode p.1 p.2.1 p.2.2 := by
  unfold functionSymbolCode
  have hleft : Primrec fun p : Nat × (Nat × Nat) => Nat.pair p.1 p.2.1 :=
    Primrec₂.comp Primrec₂.natPair Primrec.fst (Primrec.fst.comp Primrec.snd)
  exact Primrec₂.comp Primrec₂.natPair hleft (Primrec.snd.comp Primrec.snd)

theorem primrec_functionSymbolArity : Primrec functionSymbolArity := by
  exact Primrec.snd.comp Primrec.unpair

theorem primrec_applicationTerm : Primrec fun p : Nat × List GroundTermCode =>
    applicationTerm p.1 p.2 := by
  unfold applicationTerm
  have hdescriptor : Primrec fun p : Nat × List GroundTermCode =>
      Encodable.encode (p.1, p.2) :=
    Primrec.encode.comp (Primrec.pair Primrec.fst Primrec.snd)
  have hmaxStep : Primrec₂ (fun (_ : List Nat) (p : Nat × Nat) => max p.1 p.2) := by
    apply Primrec₂.mk
    exact Primrec.nat_max.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hmaxFold : Primrec fun xs : List Nat => xs.foldl max 0 :=
    Primrec.list_foldl Primrec.id (Primrec.const 0) hmaxStep
  have hbound : Primrec fun p : Nat × List GroundTermCode =>
      (p.2.foldl max 0) + 1 := by
    have hfold : Primrec fun p : Nat × List GroundTermCode => p.2.foldl max 0 :=
      hmaxFold.comp Primrec.snd
    exact Primrec₂.comp Primrec.nat_add hfold (Primrec.const 1)
  have hinner : Primrec fun p : Nat × List GroundTermCode =>
      Nat.pair (Encodable.encode (p.1, p.2)) ((p.2.foldl max 0) + 1) :=
    Primrec₂.comp Primrec₂.natPair hdescriptor hbound
  exact Primrec₂.comp Primrec₂.natPair (Primrec.const 1) hinner

theorem primrec_termLabel : Primrec termLabel := by
  unfold termLabel
  exact Primrec₂.comp Primrec₂.natPair (Primrec.const 0) Primrec.id

theorem primrec_witnessLabel : Primrec fun p : GroundTermCode × Nat =>
    witnessLabel p.1 p.2 := by
  unfold witnessLabel
  have hinner : Primrec fun p : GroundTermCode × Nat => Nat.pair p.1 p.2 :=
    Primrec₂.comp Primrec₂.natPair Primrec.fst Primrec.snd
  exact Primrec₂.comp Primrec₂.natPair (Primrec.const 1) hinner

def popGroundTerm (stack : List GroundTermCode) : GroundTermCode × List GroundTermCode :=
  popStack zeroTerm stack

theorem primrec_popGroundTerm : Primrec popGroundTerm := by
  unfold popGroundTerm popStack
  have hhead : Primrec fun stack : List GroundTermCode =>
      (stack.head?).getD zeroTerm :=
    Primrec₂.comp Primrec.option_getD Primrec.list_head?
      (Primrec.const zeroTerm)
  exact (Primrec.pair hhead Primrec.list_tail).of_eq fun stack => by
    cases stack <;> rfl

def binaryOperationStep (symbol : Nat) (stack : List GroundTermCode) :
    List GroundTermCode :=
  let right := popGroundTerm stack
  let left := popGroundTerm right.2
  applicationTerm symbol [left.1, right.1] :: left.2

def unaryOperationStep (symbol : Nat) (stack : List GroundTermCode) :
    List GroundTermCode :=
  let value := popGroundTerm stack
  applicationTerm symbol [value.1] :: value.2

def functionApplicationStep (symbol : Nat) (stack : List GroundTermCode) :
    List GroundTermCode :=
  let arity := functionSymbolArity symbol
  if arity ≤ stack.length then
    applicationTerm symbol (stack.take arity).reverse :: stack.drop arity
  else zeroTerm :: stack

def variableStep (arguments stack : List GroundTermCode) (index : Nat) :
    List GroundTermCode :=
  ((arguments[index]?).getD zeroTerm) :: stack

def evaluateTermStep (arguments : List GroundTermCode)
    (stack : List GroundTermCode) (part : TermToken) : List GroundTermCode :=
  if part.1 = 0 then zeroTerm :: stack
  else if part.1 = 1 then oneTerm :: stack
  else if part.1 = 2 then binaryOperationStep builtinAddSymbol stack
  else if part.1 = 3 then binaryOperationStep builtinMulSymbol stack
  else if part.1 = 4 then unaryOperationStep builtinNegSymbol stack
  else if part.1 = 5 then variableStep arguments stack part.2
  else if part.1 = 6 then inputTerm part.2 :: stack
  else if part.1 = 7 then functionApplicationStep part.2 stack
  else zeroTerm :: stack

/-- Evaluate a postfix first-order term after replacing its free variables by
the supplied ground-term codes.  Missing operands and out-of-range variables
have a fixed zero meaning, so this reader is total on every syntax code. -/
def evaluateTermCode (arguments : List GroundTermCode) (code : TermCode) :
    GroundTermCode :=
  (code.foldl (evaluateTermStep arguments) []).headD zeroTerm

theorem primrec_binaryOperationStep : Primrec fun p : Nat × List Nat =>
    binaryOperationStep p.1 p.2 := by
  unfold binaryOperationStep
  have hright : Primrec fun p : Nat × List Nat => popGroundTerm p.2 :=
    primrec_popGroundTerm.comp Primrec.snd
  have hleft : Primrec fun p : Nat × List Nat =>
      popGroundTerm ((popGroundTerm p.2).2) :=
    primrec_popGroundTerm.comp (Primrec.snd.comp hright)
  have htail : Primrec fun p : Nat × List Nat => [(popGroundTerm p.2).1] :=
    Primrec₂.comp Primrec.list_cons (Primrec.fst.comp hright) (Primrec.const [])
  have hargs : Primrec fun p : Nat × List Nat =>
      [(popGroundTerm ((popGroundTerm p.2).2)).1, (popGroundTerm p.2).1] :=
    Primrec₂.comp Primrec.list_cons (Primrec.fst.comp hleft) htail
  have happ : Primrec fun p : Nat × List Nat =>
      applicationTerm p.1 [(popGroundTerm ((popGroundTerm p.2).2)).1,
        (popGroundTerm p.2).1] :=
    primrec_applicationTerm.comp (Primrec.pair Primrec.fst hargs)
  exact Primrec₂.comp Primrec.list_cons happ (Primrec.snd.comp hleft)

theorem primrec_unaryOperationStep : Primrec fun p : Nat × List Nat =>
    unaryOperationStep p.1 p.2 := by
  unfold unaryOperationStep
  have hvalue : Primrec fun p : Nat × List Nat => popGroundTerm p.2 :=
    primrec_popGroundTerm.comp Primrec.snd
  have hargs : Primrec fun p : Nat × List Nat => [(popGroundTerm p.2).1] :=
    Primrec₂.comp Primrec.list_cons (Primrec.fst.comp hvalue) (Primrec.const [])
  have happ : Primrec fun p : Nat × List Nat =>
      applicationTerm p.1 [(popGroundTerm p.2).1] :=
    primrec_applicationTerm.comp (Primrec.pair Primrec.fst hargs)
  exact Primrec₂.comp Primrec.list_cons happ (Primrec.snd.comp hvalue)

theorem primrec_functionApplicationStep : Primrec fun p : Nat × List Nat =>
    functionApplicationStep p.1 p.2 := by
  unfold functionApplicationStep
  have hEnough : PrimrecPred fun p : Nat × List Nat =>
      functionSymbolArity p.1 ≤ p.2.length := by
    exact PrimrecRel.comp Primrec.nat_le
      (primrec_functionSymbolArity.comp Primrec.fst)
      (Primrec.list_length.comp Primrec.snd)
  have hTake : Primrec fun p : Nat × List Nat =>
      (p.2.take (functionSymbolArity p.1)).reverse := by
    have hTakeRaw : Primrec fun p : Nat × List Nat =>
        p.2.take (functionSymbolArity p.1) := by
      exact Primrec₂.comp Primrec.list_take
        (primrec_functionSymbolArity.comp Primrec.fst) Primrec.snd
    exact Primrec.list_reverse.comp hTakeRaw
  have hDrop : Primrec fun p : Nat × List Nat =>
      p.2.drop (functionSymbolArity p.1) := by
    exact Primrec₂.comp Primrec.list_drop
      (primrec_functionSymbolArity.comp Primrec.fst) Primrec.snd
  have happ : Primrec fun p : Nat × List Nat =>
      applicationTerm p.1 ((p.2.take (functionSymbolArity p.1)).reverse) :=
    primrec_applicationTerm.comp (Primrec.pair Primrec.fst hTake)
  have hgood : Primrec fun p : Nat × List Nat =>
      applicationTerm p.1 ((p.2.take (functionSymbolArity p.1)).reverse) ::
        p.2.drop (functionSymbolArity p.1) :=
    Primrec₂.comp Primrec.list_cons happ hDrop
  have hbad : Primrec fun p : Nat × List Nat => zeroTerm :: p.2 :=
    Primrec₂.comp Primrec.list_cons (Primrec.const zeroTerm) Primrec.snd
  exact Primrec.ite hEnough hgood hbad

theorem primrec_variableStep : Primrec fun p : (List Nat × List Nat) × Nat =>
    variableStep p.1.1 p.1.2 p.2 := by
  unfold variableStep
  have hget : Primrec fun p : (List Nat × List Nat) × Nat =>
      (p.1.1[p.2]?).getD zeroTerm :=
    Primrec₂.comp Primrec.option_getD
      (Primrec₂.comp Primrec.list_getElem? (Primrec.fst.comp Primrec.fst)
        Primrec.snd) (Primrec.const zeroTerm)
  exact Primrec₂.comp Primrec.list_cons hget (Primrec.snd.comp Primrec.fst)

set_option maxHeartbeats 1000000 in
theorem primrec_evaluateTermStep : Primrec fun p : (List Nat × List Nat) × TermToken =>
    evaluateTermStep p.1.1 p.1.2 p.2 := by
  unfold evaluateTermStep
  have htag : Primrec fun p : (List Nat × List Nat) × TermToken => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hpayload : Primrec fun p : (List Nat × List Nat) × TermToken => p.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hEq (n : Nat) : PrimrecPred fun p : (List Nat × List Nat) × TermToken =>
      p.2.1 = n := by
    exact PrimrecRel.comp Primrec.eq htag (Primrec.const n)
  have hZero : Primrec fun p : (List Nat × List Nat) × TermToken => zeroTerm :: p.1.2 :=
    Primrec₂.comp Primrec.list_cons (Primrec.const zeroTerm)
      (Primrec.snd.comp Primrec.fst)
  have hOne : Primrec fun p : (List Nat × List Nat) × TermToken => oneTerm :: p.1.2 :=
    Primrec₂.comp Primrec.list_cons (Primrec.const oneTerm)
      (Primrec.snd.comp Primrec.fst)
  have hAdd : Primrec fun p : (List Nat × List Nat) × TermToken =>
      binaryOperationStep builtinAddSymbol p.1.2 := by
    exact primrec_binaryOperationStep.comp
      (Primrec.pair (Primrec.const builtinAddSymbol)
        (Primrec.snd.comp Primrec.fst))
  have hMul : Primrec fun p : (List Nat × List Nat) × TermToken =>
      binaryOperationStep builtinMulSymbol p.1.2 := by
    exact primrec_binaryOperationStep.comp
      (Primrec.pair (Primrec.const builtinMulSymbol)
        (Primrec.snd.comp Primrec.fst))
  have hNeg : Primrec fun p : (List Nat × List Nat) × TermToken =>
      unaryOperationStep builtinNegSymbol p.1.2 := by
    exact primrec_unaryOperationStep.comp
      (Primrec.pair (Primrec.const builtinNegSymbol)
        (Primrec.snd.comp Primrec.fst))
  have hVariable : Primrec fun p : (List Nat × List Nat) × TermToken =>
      variableStep p.1.1 p.1.2 p.2.2 := by
    exact primrec_variableStep.comp
      (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))
  have hInput : Primrec fun p : (List Nat × List Nat) × TermToken =>
      inputTerm p.2.2 :: p.1.2 := by
    have hinput : Primrec fun p : (List Nat × List Nat) × TermToken => inputTerm p.2.2 := by
      unfold inputTerm
      exact Primrec₂.comp Primrec₂.natPair (Primrec.const 0)
        (Primrec₂.comp Primrec.nat_add (Primrec.snd.comp Primrec.snd)
          (Primrec.const 2))
    exact Primrec₂.comp Primrec.list_cons hinput (Primrec.snd.comp Primrec.fst)
  have hFunction : Primrec fun p : (List Nat × List Nat) × TermToken =>
      functionApplicationStep p.2.2 p.1.2 := by
    exact primrec_functionApplicationStep.comp
      (Primrec.pair (Primrec.snd.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  exact Primrec.ite (hEq 0) hZero <| Primrec.ite (hEq 1) hOne <|
    Primrec.ite (hEq 2) hAdd <| Primrec.ite (hEq 3) hMul <|
    Primrec.ite (hEq 4) hNeg <| Primrec.ite (hEq 5) hVariable <|
    Primrec.ite (hEq 6) hInput <| Primrec.ite (hEq 7) hFunction hZero

set_option maxHeartbeats 1000000 in
theorem primrec_evaluateTermCode : Primrec fun p : List GroundTermCode × TermCode =>
    evaluateTermCode p.1 p.2 := by
  unfold evaluateTermCode
  have hStep : Primrec₂ fun p : List GroundTermCode × TermCode =>
      fun state : List GroundTermCode × TermToken =>
        evaluateTermStep p.1 state.1 state.2 := by
    apply Primrec₂.mk
    exact primrec_evaluateTermStep.comp <| Primrec.pair
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hFold : Primrec fun p : List GroundTermCode × TermCode =>
      p.2.foldl (evaluateTermStep p.1) [] :=
    Primrec.list_foldl Primrec.snd (Primrec.const []) hStep
  have hHead : Primrec fun p : List GroundTermCode × TermCode =>
      (p.2.foldl (evaluateTermStep p.1) []).headD zeroTerm := by
    have hGet : Primrec fun o : Option GroundTermCode => o.getD zeroTerm :=
      Primrec₂.comp Primrec.option_getD Primrec.id (Primrec.const zeroTerm)
    exact (hGet.comp (Primrec.list_head?.comp hFold)).of_eq fun p => by
      cases p.2.foldl (evaluateTermStep p.1) [] <;> rfl
  exact hHead

theorem evaluateTermCode_zero : evaluateTermCode [] zeroOpenTerm = zeroTerm := by
  rfl

theorem evaluateTermCode_input (i : Nat) :
    evaluateTermCode [] (inputOpenTerm i) = inputTerm i := by
  rfl

example : evaluateTermCode [zeroTerm, oneTerm]
    [variableToken 0, variableToken 1, addToken] =
      applicationTerm builtinAddSymbol [zeroTerm, oneTerm] := by
  decide

/-! ## Skolemization -/

def skolemTerm (axiomIndex binderIndex universalCount : Nat) : TermCode :=
  (List.range universalCount).map (fun i => variableToken i) ++
    [functionToken (functionSymbolCode 2 (Nat.pair axiomIndex binderIndex)
      universalCount)]

def skolemPrefixStep (axiomIndex : Nat) (state : List TermCode × Nat)
    (isUniversal : Bool) : List TermCode × Nat :=
  let binderIndex := state.1.length
  if isUniversal then
    (state.1 ++ [[variableToken state.2]], state.2 + 1)
  else
    (state.1 ++ [skolemTerm axiomIndex binderIndex state.2], state.2)

def skolemPrefix (axiomIndex : Nat) (quantifiers : List Bool) :
    List TermCode × Nat :=
  quantifiers.foldl (skolemPrefixStep axiomIndex) ([], 0)

def substituteTerm (replacements : List TermCode) (t : TermCode) : TermCode :=
  t.flatMap fun part =>
    if part.1 == 5 then (replacements[part.2]?).getD zeroOpenTerm else [part]

def substituteQFToken (replacements : List TermCode) (q : QFToken) : QFToken :=
  if q.1 == 2 || q.1 == 3 then
    (q.1, (substituteTerm replacements q.2.1,
      substituteTerm replacements q.2.2))
  else q

def skolemizeAxiom (axiomIndex : Nat) (sentence : PrenexAxiom) : Nat × QFCode :=
  let state := skolemPrefix axiomIndex sentence.1
  (state.2, sentence.2.map (substituteQFToken state.1))

theorem primrec_variableToken : Primrec variableToken := by
  unfold variableToken token
  exact Primrec.pair (Primrec.const 5) Primrec.id

theorem primrec_functionToken : Primrec functionToken := by
  unfold functionToken token
  exact Primrec.pair (Primrec.const 7) Primrec.id

theorem primrec_skolemTerm :
    Primrec fun p : Nat × (Nat × Nat) =>
      skolemTerm p.1 p.2.1 p.2.2 := by
  unfold skolemTerm
  have hrange : Primrec fun p : Nat × (Nat × Nat) => List.range p.2.2 :=
    Primrec.list_range.comp (Primrec.snd.comp Primrec.snd)
  have hvariable : Primrec₂ (fun (_ : Nat × (Nat × Nat)) (i : Nat) => variableToken i) := by
    apply Primrec₂.mk
    exact primrec_variableToken.comp Primrec.snd
  have hvariables : Primrec fun p : Nat × (Nat × Nat) =>
      (List.range p.2.2).map (fun i => variableToken i) :=
    Primrec.list_map hrange hvariable
  have hname : Primrec fun p : Nat × (Nat × Nat) => Nat.pair p.1 p.2.1 :=
    Primrec₂.comp Primrec₂.natPair Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hsymbolInput : Primrec fun p : Nat × (Nat × Nat) =>
      (2, (Nat.pair p.1 p.2.1, p.2.2)) :=
    Primrec.pair (Primrec.const 2) (Primrec.pair hname (Primrec.snd.comp Primrec.snd))
  have hsymbol : Primrec fun p : Nat × (Nat × Nat) =>
      functionSymbolCode 2 (Nat.pair p.1 p.2.1) p.2.2 :=
    primrec_functionSymbolCode.comp hsymbolInput
  have htoken : Primrec fun p : Nat × (Nat × Nat) => functionToken
      (functionSymbolCode 2 (Nat.pair p.1 p.2.1) p.2.2) :=
    primrec_functionToken.comp hsymbol
  have hsingleton : Primrec fun p : Nat × (Nat × Nat) =>
      [functionToken (functionSymbolCode 2 (Nat.pair p.1 p.2.1) p.2.2)] :=
    Primrec₂.comp Primrec.list_cons htoken (Primrec.const [])
  have hbody : Primrec fun p : Nat × (Nat × Nat) =>
      (List.range p.2.2).map (fun i => variableToken i) ++
        [functionToken (functionSymbolCode 2 (Nat.pair p.1 p.2.1) p.2.2)] :=
    Primrec₂.comp Primrec.list_append hvariables hsingleton
  exact hbody.of_eq fun p => by cases p with | mk a bc => cases bc; rfl

theorem primrec_skolemPrefixStep :
    Primrec fun p : Nat × ((List TermCode × Nat) × Bool) =>
      skolemPrefixStep p.1 p.2.1 p.2.2 := by
  unfold skolemPrefixStep
  let state := fun p : Nat × ((List TermCode × Nat) × Bool) => p.2.1
  let terms := fun p : Nat × ((List TermCode × Nat) × Bool) => p.2.1.1
  let counter := fun p : Nat × ((List TermCode × Nat) × Bool) => p.2.1.2
  have hstate : Primrec state := Primrec.fst.comp Primrec.snd
  have hterms : Primrec terms := Primrec.fst.comp hstate
  have hcounter : Primrec counter := Primrec.snd.comp hstate
  have hbinder : Primrec fun p : Nat × ((List TermCode × Nat) × Bool) =>
      p.2.1.1.length := Primrec.list_length.comp hterms
  have htoken : Primrec fun p : Nat × ((List TermCode × Nat) × Bool) =>
      variableToken p.2.1.2 := primrec_variableToken.comp hcounter
  have hnested : Primrec fun p : Nat × ((List TermCode × Nat) × Bool) =>
      [[variableToken p.2.1.2]] := by
    have hinner : Primrec fun p : Nat × ((List TermCode × Nat) × Bool) =>
        [variableToken p.2.1.2] := Primrec₂.comp Primrec.list_cons htoken (Primrec.const [])
    exact Primrec₂.comp Primrec.list_cons hinner (Primrec.const [])
  have htrueTerms : Primrec fun p : Nat × ((List TermCode × Nat) × Bool) =>
      p.2.1.1 ++ [[variableToken p.2.1.2]] := Primrec₂.comp Primrec.list_append hterms hnested
  have htrueCount : Primrec fun p : Nat × ((List TermCode × Nat) × Bool) =>
      p.2.1.2 + 1 := Primrec.succ.comp hcounter
  have htrue : Primrec fun p : Nat × ((List TermCode × Nat) × Bool) =>
      (p.2.1.1 ++ [[variableToken p.2.1.2]], p.2.1.2 + 1) :=
    Primrec.pair htrueTerms htrueCount
  have hskolemInput : Primrec fun p : Nat × ((List TermCode × Nat) × Bool) =>
      (p.1, (p.2.1.1.length, p.2.1.2)) :=
    Primrec.pair Primrec.fst (Primrec.pair hbinder hcounter)
  have hskolem : Primrec fun p : Nat × ((List TermCode × Nat) × Bool) =>
      skolemTerm p.1 p.2.1.1.length p.2.1.2 :=
    primrec_skolemTerm.comp hskolemInput
  have hskolemSingleton : Primrec fun p : Nat × ((List TermCode × Nat) × Bool) =>
      [skolemTerm p.1 p.2.1.1.length p.2.1.2] :=
    Primrec₂.comp Primrec.list_cons hskolem (Primrec.const [])
  have hfalseTerms : Primrec fun p : Nat × ((List TermCode × Nat) × Bool) =>
      p.2.1.1 ++ [skolemTerm p.1 p.2.1.1.length p.2.1.2] :=
    Primrec₂.comp Primrec.list_append hterms hskolemSingleton
  have hfalse : Primrec fun p : Nat × ((List TermCode × Nat) × Bool) =>
      (p.2.1.1 ++ [skolemTerm p.1 p.2.1.1.length p.2.1.2], p.2.1.2) :=
    Primrec.pair hfalseTerms hcounter
  have hcondition : Primrec fun p : Nat × ((List TermCode × Nat) × Bool) => p.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.id)
  exact (Primrec.cond hcondition htrue hfalse).of_eq fun p => by
    simp [state, terms, counter]

theorem primrec_skolemPrefix :
    Primrec fun p : Nat × List Bool => skolemPrefix p.1 p.2 := by
  unfold skolemPrefix
  have hstepInput : Primrec fun z : (Nat × List Bool) × ((List TermCode × Nat) × Bool) =>
      (z.1.1, z.2) := Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.id)) Primrec.snd
  have hstep : Primrec₂ (fun (p : Nat × List Bool)
      (stateBool : (List TermCode × Nat) × Bool) =>
        skolemPrefixStep p.1 stateBool.1 stateBool.2) :=
    Primrec₂.mk (primrec_skolemPrefixStep.comp hstepInput)
  have hfold : Primrec fun p : Nat × List Bool =>
      (p.2.foldl (skolemPrefixStep p.1) ([], 0)) :=
    Primrec.list_foldl Primrec.snd (Primrec.const ([], 0)) hstep
  exact hfold.of_eq fun _ => rfl

theorem primrec_substituteTerm :
    Primrec fun p : List TermCode × TermCode => substituteTerm p.1 p.2 := by
  unfold substituteTerm
  have hpartTag : Primrec₂ (fun (_ : List TermCode × TermCode)
      (part : TermToken) => part.1) := by
    apply Primrec₂.mk
    exact Primrec.fst.comp Primrec.snd
  have htag₂ : Primrec₂ (fun (p : List TermCode × TermCode) (part : TermToken) =>
      decide (part.1 = 5)) := (Primrec.eq.comp₂ hpartTag (Primrec₂.const 5)).decide
  have htag : Primrec fun p : (List TermCode × TermCode) × TermToken =>
      decide (p.2.1 = 5) := Primrec₂.uncurry.mpr htag₂
  have hget : Primrec fun p : (List TermCode × TermCode) × TermToken =>
      (p.1.1[p.2.2]?).getD zeroOpenTerm := by
    have hlistGetD : Primrec₂ (fun (l : List TermCode) (i : Nat) =>
        l.getD i zeroOpenTerm) := Primrec.list_getD zeroOpenTerm
    have hlookup : Primrec fun p : (List TermCode × TermCode) × TermToken =>
        List.getD p.1.1 p.2.2 zeroOpenTerm :=
      Primrec₂.comp (f := fun (l : List TermCode) (i : Nat) =>
          List.getD l i zeroOpenTerm) hlistGetD
        (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
    exact hlookup.of_eq fun _ => by
      simp [List.getD_eq_getElem?_getD]
  have hkeep : Primrec fun p : (List TermCode × TermCode) × TermToken => [p.2] := by
    exact Primrec₂.comp Primrec.list_cons Primrec.snd (Primrec.const [])
  have hstep : Primrec₂ (fun (p : List TermCode × TermCode) (part : TermToken) =>
      if part.1 == 5 then (p.1[part.2]?).getD zeroOpenTerm else [part]) := by
    apply Primrec₂.mk
    have hcondition₂ : Primrec₂ (fun (_ : List TermCode × TermCode)
        (part : TermToken) => decide (part.1 = 5)) :=
      (Primrec.eq.comp₂ hpartTag (Primrec₂.const 5)).decide
    have hcondition : Primrec fun z : (List TermCode × TermCode) × TermToken =>
        decide (z.2.1 = 5) := Primrec₂.uncurry.mpr hcondition₂
    exact (Primrec.cond hcondition hget hkeep).of_eq fun _ => by simp
  exact Primrec.list_flatMap Primrec.snd hstep

theorem primrec_substituteQFToken :
    Primrec fun p : List TermCode × QFToken => substituteQFToken p.1 p.2 := by
  unfold substituteQFToken
  have htag : Primrec₂ (fun (p : List TermCode) (q : QFToken) => q.1) := by
    apply Primrec₂.mk
    exact Primrec.fst.comp Primrec.snd
  have hEq₂ : Primrec₂ (fun (p : List TermCode) (q : QFToken) => decide (q.1 = 2)) :=
    (Primrec.eq.comp₂ htag (Primrec₂.const 2)).decide
  have hEq₃ : Primrec₂ (fun (p : List TermCode) (q : QFToken) => decide (q.1 = 3)) :=
    (Primrec.eq.comp₂ htag (Primrec₂.const 3)).decide
  have hEq2 : Primrec fun p : List TermCode × QFToken => decide (p.2.1 = 2) :=
    Primrec₂.uncurry.mpr hEq₂
  have hEq3 : Primrec fun p : List TermCode × QFToken => decide (p.2.1 = 3) :=
    Primrec₂.uncurry.mpr hEq₃
  have hcondition : Primrec fun p : List TermCode × QFToken =>
      p.2.1 == 2 || p.2.1 == 3 := by
    exact (Primrec.cond hEq2 (Primrec.const true) hEq3).of_eq fun p => by
      cases h2 : p.2.1 == 2 <;> cases h3 : p.2.1 == 3 <;>
        simp_all [beq_iff_eq]
  have hleftInput : Primrec fun p : List TermCode × QFToken =>
      (p.1, p.2.2.1) :=
    Primrec.pair Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hleft : Primrec fun p : List TermCode × QFToken =>
      substituteTerm p.1 p.2.2.1 := primrec_substituteTerm.comp hleftInput
  have hrightInput : Primrec fun p : List TermCode × QFToken =>
      (p.1, p.2.2.2) :=
    Primrec.pair Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hright : Primrec fun p : List TermCode × QFToken =>
      substituteTerm p.1 p.2.2.2 := primrec_substituteTerm.comp hrightInput
  have hsub : Primrec fun p : List TermCode × QFToken =>
      (p.2.1, (substituteTerm p.1 p.2.2.1, substituteTerm p.1 p.2.2.2)) :=
    Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.pair hleft hright)
  exact (Primrec.cond hcondition hsub Primrec.snd).of_eq fun _ => by simp

/-! ## Quantifier-free translation -/

def polynomialNeg (p : PolynomialCode) : PolynomialCode :=
  polyMul (polyConst [(-1, 0)]) p

def polynomialDifference (left right : PolynomialCode) : PolynomialCode :=
  polyAdd left (polynomialNeg right)

def equalityAtom (left right : PolynomialCode) : Atom :=
  (false, polynomialDifference left right)

def disequalityAtom (left right : PolynomialCode) : Atom :=
  (true, polynomialDifference left right)

def ringPolynomialStep (variableLabel : Nat → Option Nat)
    (stack : List PolynomialCode) (part : TermToken) : List PolynomialCode :=
  match part.1 with
  | 0 => [] :: stack
  | 1 => polyConst [(1, 0)] :: stack
  | 2 =>
      let right := popStack ([] : PolynomialCode) stack
      let left := popStack ([] : PolynomialCode) right.2
      polyAdd left.1 right.1 :: left.2
  | 3 =>
      let right := popStack ([] : PolynomialCode) stack
      let left := popStack ([] : PolynomialCode) right.2
      polyMul left.1 right.1 :: left.2
  | 4 =>
      let popped := popStack ([] : PolynomialCode) stack
      polynomialNeg popped.1 :: popped.2
  | 5 =>
      match variableLabel part.2 with
      | some i => polyVar i :: stack
      | none => [] :: stack
  | _ => [] :: stack

def ringPolynomial (variableLabel : Nat → Option Nat) (t : TermCode) :
    PolynomialCode :=
  ((t.foldl (ringPolynomialStep variableLabel) []).headD [])

def groundValuePolynomial (t : GroundTermCode) : PolynomialCode :=
  polyVar (termLabel t)

def rationalTokenOfQF (atomPolynomial : TermCode → PolynomialCode)
    (q : QFToken) : FormulaToken :=
  match q.1 with
  | 0 => FormulaToken.truth
  | 1 => FormulaToken.falsity
  | 2 => FormulaToken.atom (equalityAtom (atomPolynomial q.2.1)
      (atomPolynomial q.2.2))
  | 3 => FormulaToken.atom (disequalityAtom (atomPolynomial q.2.1)
      (atomPolynomial q.2.2))
  | 4 => FormulaToken.negation
  | 5 => FormulaToken.conjunction
  | 6 => FormulaToken.disjunction
  | _ => FormulaToken.falsity

def qfToFormula (atomPolynomial : TermCode → PolynomialCode) (q : QFCode) :
    ConstraintFormula :=
  q.map (rationalTokenOfQF atomPolynomial)

def rootVariableLabel (q : IntegerPolynomialQuery) (i : Nat) : Nat :=
  if i < q.1 then termLabel (inputTerm i) else termLabel zeroTerm

/-- Expand the natural scale in an integer coefficient as a finite sum of
identical rational-polynomial terms. This keeps the root translation
primitive recursive without multiplying encoded `Int` values. -/
def rootPolynomialTerm (q : IntegerPolynomialQuery) (t : IntegerTermCode) :
    PolynomialCode :=
  (List.range t.1.2).map fun _ =>
    (t.1.1.map fun factor => (factor, 0),
      t.2.map fun ie => (rootVariableLabel q ie.1, ie.2))

def rootPolynomial (q : IntegerPolynomialQuery) : PolynomialCode :=
  q.2.flatMap (rootPolynomialTerm q)

def rootQueryFormula (q : IntegerPolynomialQuery) : ConstraintFormula :=
  ConstraintFormula.conjoin
    (ConstraintFormula.atom (false, rootPolynomial q))
    (ConstraintFormula.atom (false, polyVar (termLabel zeroTerm)))

def rootAssignment (arity : Nat) (values : Fin arity → ℚ) (variableCode : Nat) : ℚ :=
  let label := Nat.unpair variableCode
  if label.1 = 0 then
    let ground := Nat.unpair label.2
    if ground.1 = 0 ∧ 2 ≤ ground.2 then
      H10RationalQueryAdapter.finiteVariableValue arity values (ground.2 - 2)
    else 0
  else 0

theorem rootAssignment_zero (arity : Nat) (values : Fin arity → ℚ) :
    rootAssignment arity values (termLabel zeroTerm) = 0 := by
  simp [rootAssignment, termLabel, zeroTerm, Nat.unpair_pair]

theorem rootAssignment_rootVariableLabel (q : IntegerPolynomialQuery)
    (values : Fin q.1 → ℚ) (i : Nat) :
    rootAssignment q.1 values (rootVariableLabel q i) =
      H10RationalQueryAdapter.finiteVariableValue q.1 values i := by
  by_cases hi : i < q.1
  · simp [rootAssignment, rootVariableLabel, hi, termLabel, inputTerm,
      Nat.unpair_pair, H10RationalQueryAdapter.finiteVariableValue]
  · simp [rootAssignment, rootVariableLabel, hi, termLabel, zeroTerm,
      Nat.unpair_pair, H10RationalQueryAdapter.finiteVariableValue]

theorem rootPolynomialValue_eq_integerPolynomialValue
    (q : IntegerPolynomialQuery) (x : Nat → ℚ)
    (values : Fin q.1 → ℚ)
    (hvars : ∀ i, x (rootVariableLabel q i) =
      H10RationalQueryAdapter.finiteVariableValue q.1 values i) :
    polynomialValue x (rootPolynomial q) =
      H10RationalQueryAdapter.integerPolynomialValue q.1 values q.2 := by
  have hmonomial : ∀ m : MonomialCode,
      monomialValue x (m.map fun ie => (rootVariableLabel q ie.1, ie.2)) =
        H10RationalQueryAdapter.integerMonomialValue q.1 values m := by
    intro m
    induction m with
    | nil => rfl
    | cons ie rest ih =>
      change x (rootVariableLabel q ie.1) ^ ie.2 *
          monomialValue x (rest.map fun ie => (rootVariableLabel q ie.1, ie.2)) =
        H10RationalQueryAdapter.finiteVariableValue q.1 values ie.1 ^ ie.2 *
          H10RationalQueryAdapter.integerMonomialValue q.1 values rest
      rw [hvars ie.1, ih]
  have hcoeff (factors : List Int) :
      coeffValue (factors.map fun factor => (factor, 0)) =
        (factors.map (Int.cast : Int → ℚ)).prod := by
    simp only [coeffValue, List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro factor _
    simp [coeffAtomValue]
  have hterm (t : IntegerTermCode) :
      ((rootPolynomialTerm q t).map (termValue x)).sum =
        H10RationalQueryAdapter.integerTermValue q.1 values t := by
    simp only [rootPolynomialTerm, List.map_map]
    change (List.map (fun (_ : Nat) =>
      termValue x
        (t.1.1.map (fun factor => (factor, 0)),
          t.2.map (fun ie => (rootVariableLabel q ie.1, ie.2))))
        (List.range t.1.2)).sum =
      H10RationalQueryAdapter.integerTermValue q.1 values t
    rw [List.map_const']
    simp only [List.length_range, List.sum_replicate, termValue]
    rw [hcoeff t.1.1, hmonomial t.2]
    simp only [H10RationalQueryAdapter.integerTermValue,
      H10RationalQueryAdapter.integerCoefficientValue,
      H10RationalQueryAdapter.integerMonomialValue]
    ring
  unfold rootPolynomial
  change ((q.2.flatMap (rootPolynomialTerm q)).map (termValue x)).sum =
    (q.2.map (H10RationalQueryAdapter.integerTermValue q.1 values)).sum
  induction q.2 with
  | nil => rfl
  | cons t rest ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons]
    rw [hterm t, ih]

theorem rootQueryFormula_toDNF (q : IntegerPolynomialQuery) :
    toDNF (rootQueryFormula q) =
      [[(false, rootPolynomial q), (false, polyVar (termLabel zeroTerm))]] := by
  rfl

theorem rootQueryFormula_correct (q : IntegerPolynomialQuery) :
    FormulaSatisfies (rootQueryFormula q) ↔
      H10RationalQueryAdapter.IntegerPolynomialHasRationalRoot q := by
  rw [formula_to_dnf_correct, rootQueryFormula_toDNF]
  change (∃ x : Nat → ℚ, ∃ clause ∈
      [[(false, rootPolynomial q), (false, polyVar (termLabel zeroTerm))]],
      H10RationalCompiler.clauseSatisfied x clause) ↔ _
  constructor
  · rintro ⟨x, clause, hmem, hsat⟩
    have hclause : clause =
        [(false, rootPolynomial q), (false, polyVar (termLabel zeroTerm))] := by
      simpa using hmem
    subst clause
    have hroot : polynomialValue x (rootPolynomial q) = 0 := by
      have h := hsat (false, rootPolynomial q) (by simp)
      simpa [H10RationalCompiler.atomSatisfied] using h
    have hzero : x (termLabel zeroTerm) = 0 := by
      have h := hsat (false, polyVar (termLabel zeroTerm)) (by simp)
      simpa [H10RationalCompiler.atomSatisfied, polynomialValue_polyVar] using h
    let values : Fin q.1 → ℚ := fun i =>
      x (termLabel (inputTerm i.1))
    have hvars : ∀ i, x (rootVariableLabel q i) =
        H10RationalQueryAdapter.finiteVariableValue q.1 values i := by
      intro i
      by_cases hi : i < q.1
      · simp [rootVariableLabel, hi, values,
          H10RationalQueryAdapter.finiteVariableValue]
      · simp [rootVariableLabel, hi,
          H10RationalQueryAdapter.finiteVariableValue, hzero]
    refine ⟨values, ?_⟩
    rw [← rootPolynomialValue_eq_integerPolynomialValue q x values hvars]
    exact hroot
  · rintro ⟨values, hroot⟩
    let x : Nat → ℚ := rootAssignment q.1 values
    have hzero : x (termLabel zeroTerm) = 0 := by
      exact rootAssignment_zero q.1 values
    have hvars : ∀ i, x (rootVariableLabel q i) =
        H10RationalQueryAdapter.finiteVariableValue q.1 values i := by
      intro i
      exact rootAssignment_rootVariableLabel q values i
    have hpoly := rootPolynomialValue_eq_integerPolynomialValue q x values hvars
    refine ⟨x, [(false, rootPolynomial q),
      (false, polyVar (termLabel zeroTerm))], ?_, ?_⟩
    · simp
    · intro atom hatom
      simp only [List.mem_cons] at hatom
      rcases hatom with hatom | hatom
      · subst atom
        simpa [H10RationalCompiler.atomSatisfied] using (by rw [hpoly]; exact hroot)
      · rcases hatom with hatom | hatom
        · subst atom
          simpa [H10RationalCompiler.atomSatisfied, polynomialValue_polyVar] using hzero
        · simp at hatom

def phiVariableLabel (witnessCount : Nat) (t : GroundTermCode) (i : Nat) :
    Option Nat :=
  if i == 0 then some (termLabel t)
  else if i ≤ witnessCount then some (witnessLabel t (i - 1))
  else none

def renameFormulaToken (rename : Nat → Nat) : FormulaToken → FormulaToken
  | none => FormulaToken.truth
  | some (.inl atom) =>
      FormulaToken.atom (atom.1, mapVars rename atom.2)
  | some (.inr op) => some (.inr op)

def renameFormulaVariables (rename : Nat → Nat)
    (formula : ConstraintFormula) : ConstraintFormula :=
  formula.map (renameFormulaToken rename)

def positiveExistentialFormula (phi : PositiveExistential) (t : GroundTermCode) :
    ConstraintFormula :=
  renameFormulaVariables (fun i => (phiVariableLabel phi.1 t i).getD 0) phi.2

/-! ## Effective encoding of the pole-parity formula -/

def integerConstantPolynomial (n : Int) : PolynomialCode :=
  polyConst [(n, 0)]

def squarePolynomial (p : PolynomialCode) : PolynomialCode := polyMul p p

def positiveEquation (p : PolynomialCode) : ConstraintFormula :=
  ConstraintFormula.atom (false, p)

def conjunctionOfEquations (equations : List PolynomialCode) : ConstraintFormula :=
  equations.foldl (fun formula equation =>
    ConstraintFormula.conjoin formula (positiveEquation equation))
    ConstraintFormula.truth

def ellipticFamilyEquation (x y parameter : PolynomialCode) : PolynomialCode :=
  polynomialDifference (squarePolynomial y)
    (polyMul (polyMul x (polynomialDifference x parameter))
      (polyAdd x (polyMul (integerConstantPolynomial 3) parameter)))

/-- One finite-disjunction branch in the paper's positive-existential
condition. The 16 witness slots are: an inverse for the input, `t`, `e`,
`U`, `H'`, inverses for the denominator, `e`, and `eH'`, then point and
square-root witnesses for each of the two curves. `m` and `m_d` are fixed
rational coefficient codes. -/
def poleParityBranchMatrix (m mD : CoeffCode) : ConstraintFormula := Id.run do
  let b := polyVar 0
  let bInverse := polyVar 1
  let t := polyVar 2
  let e := polyVar 3
  let u := polyVar 4
  let h := polyVar 5
  let denominatorInverse := polyVar 6
  let eInverse := polyVar 7
  let ehInverse := polyVar 8
  let x1 := polyVar 9
  let y1 := polyVar 10
  let z1 := polyVar 11
  let z1Inverse := polyVar 12
  let x2 := polyVar 13
  let y2 := polyVar 14
  let z2 := polyVar 15
  let z2Inverse := polyVar 16
  let one := integerConstantPolynomial 1
  let mPolynomial := polyConst m
  let mDPolynomial := polyConst mD
  let bPrime := polyMul mPolynomial b
  let d := polyMul mDPolynomial b
  let tSquared := squarePolynomial t
  let denominator := polyAdd one (polyMul d tSquared)
  let numerator := polyMul b (polynomialDifference one (polyMul d tSquared))
  let hExpected := polyMul bPrime (polynomialDifference bPrime (squarePolynomial u))
  let eh := polyMul e h
  let curve1 := ellipticFamilyEquation x1 y1 e
  let curve2 := ellipticFamilyEquation x2 y2 eh
  let xSquare1 := polynomialDifference x1 (polyMul bPrime (squarePolynomial z1))
  let xSquare2 := polynomialDifference x2 (polyMul bPrime (squarePolynomial z2))
  let equations := [
    polynomialDifference (polyMul b bInverse) one,
    polynomialDifference (polyMul u denominator) numerator,
    polynomialDifference h hExpected,
    polynomialDifference (polyMul denominator denominatorInverse) one,
    polynomialDifference (polyMul e eInverse) one,
    polynomialDifference (polyMul eh ehInverse) one,
    curve1,
    xSquare1,
    polynomialDifference (polyMul z1 z1Inverse) one,
    curve2,
    xSquare2,
    polynomialDifference (polyMul z2 z2Inverse) one]
  return conjunctionOfEquations equations

/-- The Section 3 formula is compiled from the finite rational multipliers
`(m,m_d)`. The zero case is the first disjunct; each remaining disjunct
chooses one pair and existentially supplies the 16 witnesses in
`poleParityBranchMatrix`. Coefficients are the same exact rational codes used
by the polynomial compiler. -/
def poleParityFormula (choices : List (CoeffCode × CoeffCode)) :
    PositiveExistential :=
  (16, choices.foldl (fun formula choice =>
    ConstraintFormula.disjoin formula (poleParityBranchMatrix choice.1 choice.2))
    (positiveEquation (polyVar 0)))

/-! ## The four finite constraint families -/

/-- A finite-test item is an explicitly primitive-codable tuple.  Its tag is
`0` dummy, `1` zero, `2` one, `3` addition, `4` multiplication, `5` negation,
`6` function congruence, `7` universal axiom instance, or `8` positive
existential condition.  The tuple fields hold the function/axiom code and the
relevant argument-term lists. -/
abbrev TestItem := Nat × (Nat × (List GroundTermCode ×
  (List GroundTermCode × List GroundTermCode)))

def dummyItem : TestItem := (0, (0, ([], [], [])))

def itemTag (item : TestItem) : Nat := item.1
def itemPayload (item : TestItem) : Nat := item.2.1
def itemTerms (item : TestItem) : List GroundTermCode := item.2.2.1
def itemLeftArgs (item : TestItem) : List GroundTermCode := item.2.2.2.1
def itemRightArgs (item : TestItem) : List GroundTermCode := item.2.2.2.2

def equalTermFormula (left right : GroundTermCode) : ConstraintFormula :=
  ConstraintFormula.atom (equalityAtom (groundValuePolynomial left)
    (groundValuePolynomial right))

def termFormulaList (terms : List GroundTermCode) : ConstraintFormula :=
  terms.foldl (fun result t =>
    ConstraintFormula.conjoin result
      (ConstraintFormula.atom (false, groundValuePolynomial t)))
    ConstraintFormula.truth

def functionApplication (symbol : Nat) (args : List GroundTermCode) : GroundTermCode :=
  applicationTerm symbol args

def additionTerm (left right : GroundTermCode) : GroundTermCode :=
  applicationTerm builtinAddSymbol [left, right]

def multiplicationTerm (left right : GroundTermCode) : GroundTermCode :=
  applicationTerm builtinMulSymbol [left, right]

def negationTerm (arg : GroundTermCode) : GroundTermCode :=
  applicationTerm builtinNegSymbol [arg]

def functionInputsEqualFormula (left right : List GroundTermCode) :
    ConstraintFormula :=
  (List.zip left right).foldl
    (fun result pair => ConstraintFormula.conjoin result
      (equalTermFormula pair.1 pair.2)) ConstraintFormula.truth

def operationFormula (tag : Nat) (terms : List GroundTermCode) : ConstraintFormula :=
  if tag == 3 && terms.length == 2 then
    let leftTerm := terms.getD 0 zeroTerm
    let rightTerm := terms.getD 1 zeroTerm
    let left := groundValuePolynomial leftTerm
    let right := groundValuePolynomial rightTerm
    let result := groundValuePolynomial (additionTerm leftTerm rightTerm)
    ConstraintFormula.atom (false, polynomialDifference result (polyAdd left right))
  else if tag == 4 && terms.length == 2 then
    let leftTerm := terms.getD 0 zeroTerm
    let rightTerm := terms.getD 1 zeroTerm
    let left := groundValuePolynomial leftTerm
    let right := groundValuePolynomial rightTerm
    let result := groundValuePolynomial (multiplicationTerm leftTerm rightTerm)
    ConstraintFormula.atom (false, polynomialDifference result (polyMul left right))
  else if tag == 5 && terms.length == 1 then
    let argument := terms.getD 0 zeroTerm
    let value := groundValuePolynomial argument
    let result := groundValuePolynomial (negationTerm argument)
    ConstraintFormula.atom (false, polyAdd result value)
  else ConstraintFormula.truth

def functionCongruenceFormula (symbol : Nat)
    (left right : List GroundTermCode) :
    ConstraintFormula :=
  if functionSymbolArity symbol != left.length || left.length != right.length then
    ConstraintFormula.truth
  else
    ConstraintFormula.disjoin
      (ConstraintFormula.negate (functionInputsEqualFormula left right))
      (equalTermFormula (functionApplication symbol left)
        (functionApplication symbol right))

def universalInstanceFormula (axioms : Nat → PrenexAxiom) (index : Nat)
    (arguments : List GroundTermCode) : ConstraintFormula :=
  let skolemized := skolemizeAxiom index (axioms index)
  if skolemized.1 != arguments.length then ConstraintFormula.truth
  else
    qfToFormula (fun term => groundValuePolynomial
      (evaluateTermCode arguments term)) skolemized.2

def testItemFormula (axioms : Nat → PrenexAxiom) (phi : PositiveExistential)
    (item : TestItem) : ConstraintFormula :=
  match itemTag item with
  | 1 => ConstraintFormula.atom (false, polyVar (termLabel zeroTerm))
  | 2 => ConstraintFormula.atom (false, polynomialDifference
      (polyVar (termLabel oneTerm)) (polyConst [(1, 0)]))
  | 3 | 4 | 5 => operationFormula (itemTag item) (itemTerms item)
  | 6 => functionCongruenceFormula (itemPayload item)
      (itemLeftArgs item) (itemRightArgs item)
  | 7 => universalInstanceFormula axioms (itemPayload item) (itemTerms item)
  | 8 =>
      if (itemTerms item).length == 1 then
        positiveExistentialFormula phi (itemTerms item).head!
      else ConstraintFormula.truth
  | _ => ConstraintFormula.truth

/-! ## Independent semantics of a finite-test item -/

def groundTermValue (x : Nat → ℚ) (term : GroundTermCode) : ℚ :=
  x (termLabel term)

def qfGroundMeaningStep (arguments : List GroundTermCode)
    (stack : List FormulaMeaning) (part : QFToken) : List FormulaMeaning :=
  match part.1 with
  | 0 => (fun _ => True) :: stack
  | 1 => (fun _ => False) :: stack
  | 2 => (fun y => groundTermValue y (evaluateTermCode arguments part.2.1) =
      groundTermValue y (evaluateTermCode arguments part.2.2)) :: stack
  | 3 => (fun y => groundTermValue y (evaluateTermCode arguments part.2.1) ≠
      groundTermValue y (evaluateTermCode arguments part.2.2)) :: stack
  | 4 =>
      let popped := popStack (fun _ => False) stack
      (fun y => ¬ popped.1 y) :: popped.2
  | 5 =>
      let right := popStack (fun _ => False) stack
      let left := popStack (fun _ => False) right.2
      (fun y => left.1 y ∧ right.1 y) :: left.2
  | 6 =>
      let right := popStack (fun _ => False) stack
      let left := popStack (fun _ => False) right.2
      (fun y => left.1 y ∨ right.1 y) :: left.2
  | _ => (fun _ => False) :: stack

/-- Direct interpretation of a quantifier-free matrix over values assigned to
ground terms. It is defined by reading the input syntax and does not refer to
`qfToFormula` or the generated DNF. -/
def qfGroundHolds (x : Nat → ℚ) (arguments : List GroundTermCode)
    (matrix : QFCode) : Prop :=
  ((matrix.foldl (qfGroundMeaningStep arguments) []).headD (fun _ => False)) x

def QFMeaningRelation (left right : FormulaMeaning) : Prop :=
  ∀ x, left x ↔ right x

theorem polynomialValue_polynomialNeg (x : Nat → ℚ) (p : PolynomialCode) :
    polynomialValue x (polynomialNeg p) = -polynomialValue x p := by
  simp [polynomialNeg, polynomialValue_mul, polynomialValue_polyConst,
    coeffValue, coeffAtomValue]

theorem polynomialValue_polynomialDifference (x : Nat → ℚ)
    (left right : PolynomialCode) :
    polynomialValue x (polynomialDifference left right) =
      polynomialValue x left - polynomialValue x right := by
  simp [polynomialDifference, polynomialValue_add,
    polynomialValue_polynomialNeg]
  ring

@[simp]
theorem atomSatisfied_equalityAtom (x : Nat → ℚ)
    (left right : PolynomialCode) :
    atomSatisfied x (equalityAtom left right) ↔
      polynomialValue x left = polynomialValue x right := by
  simp [atomSatisfied, equalityAtom, polynomialValue_polynomialDifference]
  constructor <;> intro h <;> linarith

@[simp]
theorem atomSatisfied_disequalityAtom (x : Nat → ℚ)
    (left right : PolynomialCode) :
    atomSatisfied x (disequalityAtom left right) ↔
      polynomialValue x left ≠ polynomialValue x right := by
  simp [atomSatisfied, disequalityAtom, polynomialValue_polynomialDifference]
  constructor
  · intro h heq
    apply h
    rw [heq]
    simp
  · intro h heq
    exact h (sub_eq_zero.mp heq)

theorem groundValuePolynomial_correct (x : Nat → ℚ) (term : GroundTermCode) :
    polynomialValue x (groundValuePolynomial term) = groundTermValue x term := by
  simp [groundValuePolynomial, groundTermValue]

theorem formulaHolds_equation (x : Nat → ℚ) (p : PolynomialCode) :
    FormulaHolds x (ConstraintFormula.atom (false, p)) ↔
      polynomialValue x p = 0 := by
  simp [FormulaHolds, ConstraintFormula.atom, FormulaToken.atom, formulaStep,
    List.headD, H10RationalCompiler.atomSatisfied]

@[simp]
theorem formulaHolds_truth (x : Nat → ℚ) :
    FormulaHolds x ConstraintFormula.truth := by
  simp [FormulaHolds, ConstraintFormula.truth, FormulaToken.truth, formulaStep,
    List.headD]

theorem formulaHolds_negate (x : Nat → ℚ) (formula : ConstraintFormula) :
    FormulaHolds x (ConstraintFormula.negate formula) ↔
      ¬ FormulaHolds x formula := by
  unfold FormulaHolds ConstraintFormula.negate
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
    FormulaToken.negation, formulaStep]
  cases h : formula.foldl formulaStep [] with
  | nil => simp [h, popStack, List.headD]
  | cons head rest => simp [h, popStack, List.headD]

theorem formulaHolds_conjoin_right_atom (x : Nat → ℚ)
    (formula : ConstraintFormula) (atom : Atom) :
    FormulaHolds x (ConstraintFormula.conjoin formula
      (ConstraintFormula.atom atom)) ↔
      FormulaHolds x formula ∧ atomSatisfied x atom := by
  unfold FormulaHolds ConstraintFormula.conjoin ConstraintFormula.atom
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
    FormulaToken.atom, FormulaToken.conjunction, formulaStep]
  cases h : formula.foldl formulaStep [] with
  | nil => simp [h, popStack, List.headD]
  | cons head rest => simp [h, popStack, List.headD]

theorem formulaHolds_disjoin_right_atom (x : Nat → ℚ)
    (formula : ConstraintFormula) (atom : Atom) :
    FormulaHolds x (ConstraintFormula.disjoin formula
      (ConstraintFormula.atom atom)) ↔
      FormulaHolds x formula ∨ atomSatisfied x atom := by
  unfold FormulaHolds ConstraintFormula.disjoin ConstraintFormula.atom
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
    FormulaToken.atom, FormulaToken.disjunction, formulaStep]
  cases h : formula.foldl formulaStep [] with
  | nil => simp [h, popStack, List.headD]
  | cons head rest => simp [h, popStack, List.headD]

theorem formulaHolds_equalTermFormula (x : Nat → ℚ)
    (left right : GroundTermCode) :
    FormulaHolds x (equalTermFormula left right) ↔
      groundTermValue x left = groundTermValue x right := by
  simp [equalTermFormula, formulaHolds_equation, equalityAtom,
    polynomialValue_polynomialDifference, groundValuePolynomial_correct,
    sub_eq_zero]

theorem functionInputsEqualFormula_fold_correct (x : Nat → ℚ)
    (pairs : List (GroundTermCode × GroundTermCode))
    (initial : ConstraintFormula) :
    FormulaHolds x (pairs.foldl
      (fun result pair => ConstraintFormula.conjoin result
        (equalTermFormula pair.1 pair.2)) initial) ↔
      FormulaHolds x initial ∧
        ∀ pair ∈ pairs, groundTermValue x pair.1 = groundTermValue x pair.2 := by
  induction pairs generalizing initial with
  | nil => simp
  | cons pair rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    dsimp only [equalTermFormula]
    rw [formulaHolds_conjoin_right_atom]
    rw [atomSatisfied_equalityAtom, groundValuePolynomial_correct,
      groundValuePolynomial_correct]
    simp [equalityAtom, polynomialValue_polynomialDifference,
      groundValuePolynomial_correct, sub_eq_zero, List.mem_cons,
      and_assoc, and_left_comm, and_comm]

theorem functionInputsEqualFormula_correct (x : Nat → ℚ)
    (left right : List GroundTermCode) :
    FormulaHolds x (functionInputsEqualFormula left right) ↔
      ∀ pair ∈ List.zip left right,
        groundTermValue x pair.1 = groundTermValue x pair.2 := by
  unfold functionInputsEqualFormula
  simpa using functionInputsEqualFormula_fold_correct x (List.zip left right)
    ConstraintFormula.truth

theorem operationFormula_addition_semantics (x : Nat → ℚ)
    (terms : List GroundTermCode) (hLength : terms.length = 2) :
    FormulaHolds x (operationFormula 3 terms) ↔
      groundTermValue x (additionTerm terms[0]! terms[1]!) =
        groundTermValue x terms[0]! + groundTermValue x terms[1]! := by
  have hParts : ∃ left right, terms = [left, right] := by
    cases terms with
    | nil => simp at hLength
    | cons left tail =>
      cases tail with
      | nil => simp at hLength
      | cons right rest =>
        have hRestLength : rest.length = 0 := by
          simp only [List.length_cons] at hLength
          omega
        have hRest : rest = [] := by
          cases rest with
          | nil => rfl
          | cons head tail => simp at hRestLength
        subst rest
        exact ⟨left, right, rfl⟩
  rcases hParts with ⟨left, right, hTerms⟩
  rw [hTerms]
  change FormulaHolds x (ConstraintFormula.atom (false,
    polynomialDifference (groundValuePolynomial (additionTerm left right))
      (polyAdd (groundValuePolynomial left) (groundValuePolynomial right)))) ↔
      groundTermValue x (additionTerm left right) =
        groundTermValue x left + groundTermValue x right
  rw [formulaHolds_equation]
  simp [polynomialValue_polynomialDifference, groundValuePolynomial_correct,
    polynomialValue_add, sub_eq_zero]

theorem operationFormula_multiplication_semantics (x : Nat → ℚ)
    (terms : List GroundTermCode) (hLength : terms.length = 2) :
    FormulaHolds x (operationFormula 4 terms) ↔
      groundTermValue x (multiplicationTerm terms[0]! terms[1]!) =
        groundTermValue x terms[0]! * groundTermValue x terms[1]! := by
  have hParts : ∃ left right, terms = [left, right] := by
    cases terms with
    | nil => simp at hLength
    | cons left tail =>
      cases tail with
      | nil => simp at hLength
      | cons right rest =>
        have hRestLength : rest.length = 0 := by
          simp only [List.length_cons] at hLength
          omega
        have hRest : rest = [] := by
          cases rest with
          | nil => rfl
          | cons head tail => simp at hRestLength
        subst rest
        exact ⟨left, right, rfl⟩
  rcases hParts with ⟨left, right, hTerms⟩
  rw [hTerms]
  change FormulaHolds x (ConstraintFormula.atom (false,
    polynomialDifference (groundValuePolynomial (multiplicationTerm left right))
      (polyMul (groundValuePolynomial left) (groundValuePolynomial right)))) ↔
      groundTermValue x (multiplicationTerm left right) =
        groundTermValue x left * groundTermValue x right
  rw [formulaHolds_equation]
  simp [polynomialValue_polynomialDifference, groundValuePolynomial_correct,
    polynomialValue_mul, sub_eq_zero]

theorem operationFormula_negation_semantics (x : Nat → ℚ)
    (terms : List GroundTermCode) (hLength : terms.length = 1) :
    FormulaHolds x (operationFormula 5 terms) ↔
      groundTermValue x (negationTerm terms.head!) = -groundTermValue x terms.head! := by
  have hParts : ∃ argument, terms = [argument] := by
    cases terms with
    | nil => simp at hLength
    | cons argument rest =>
      have hRestLength : rest.length = 0 := by
        simp only [List.length_cons] at hLength
        omega
      have hRest : rest = [] := by
        cases rest with
        | nil => rfl
        | cons head tail => simp at hRestLength
      subst rest
      exact ⟨argument, rfl⟩
  rcases hParts with ⟨argument, hTerms⟩
  rw [hTerms]
  change FormulaHolds x (ConstraintFormula.atom (false,
    polyAdd (groundValuePolynomial (negationTerm argument))
      (groundValuePolynomial argument))) ↔
      groundTermValue x (negationTerm argument) = -groundTermValue x argument
  rw [formulaHolds_equation]
  simp only [polynomialValue_add, groundValuePolynomial_correct]
  constructor <;> intro h <;> linarith

def FormulaRenameRelation (rename : Nat → Nat)
    (translated original : FormulaMeaning) : Prop :=
  ∀ x, translated x ↔ original (fun i => x (rename i))

theorem formulaStep_rename_preserves (rename : Nat → Nat) (part : FormulaToken)
    (translatedStack originalStack : List FormulaMeaning)
    (h : List.Forall₂ (FormulaRenameRelation rename) translatedStack originalStack) :
    List.Forall₂ (FormulaRenameRelation rename)
      (formulaStep translatedStack (renameFormulaToken rename part))
      (formulaStep originalStack part) := by
  cases part with
  | none =>
    apply List.Forall₂.cons
    · intro x
      rfl
    · exact h
  | some part =>
    cases part with
    | inl atom =>
      apply List.Forall₂.cons
      · intro x
        cases atom with
        | mk polarity polynomial =>
          cases polarity <;>
            simp [FormulaRenameRelation, formulaStep, renameFormulaToken,
              H10RationalCompiler.atomSatisfied, polynomialValue_mapVars]
      · exact h
    | inr op =>
      rcases op with ⟨leftOp, rightOp⟩
      cases leftOp with
      | false =>
        cases rightOp with
        | false =>
          apply List.Forall₂.cons
          · intro x
            rfl
          · exact h
        | true =>
          have hDefault : FormulaRenameRelation rename
              (fun _ => False) (fun _ => False) := by
            intro x
            rfl
          rcases popStack_forall₂ (fun _ => False) (fun _ => False)
              hDefault h with ⟨hHead, hTail⟩
          apply List.Forall₂.cons
          · intro x
            exact not_congr (hHead x)
          · exact hTail
      | true =>
        cases rightOp with
        | false =>
          have hDefault : FormulaRenameRelation rename
              (fun _ => False) (fun _ => False) := by
            intro x
            rfl
          let translatedRight := popStack (fun _ => False) translatedStack
          let originalRight := popStack (fun _ => False) originalStack
          rcases popStack_forall₂ (fun _ => False) (fun _ => False)
              hDefault h with ⟨hRight, hRest⟩
          let translatedLeft := popStack (fun _ => False) translatedRight.2
          let originalLeft := popStack (fun _ => False) originalRight.2
          rcases popStack_forall₂ (fun _ => False) (fun _ => False)
              hDefault hRest with ⟨hLeft, hTail⟩
          apply List.Forall₂.cons
          · intro x
            exact and_congr (hLeft x) (hRight x)
          · exact hTail
        | true =>
          have hDefault : FormulaRenameRelation rename
              (fun _ => False) (fun _ => False) := by
            intro x
            rfl
          let translatedRight := popStack (fun _ => False) translatedStack
          let originalRight := popStack (fun _ => False) originalStack
          rcases popStack_forall₂ (fun _ => False) (fun _ => False)
              hDefault h with ⟨hRight, hRest⟩
          let translatedLeft := popStack (fun _ => False) translatedRight.2
          let originalLeft := popStack (fun _ => False) originalRight.2
          rcases popStack_forall₂ (fun _ => False) (fun _ => False)
              hDefault hRest with ⟨hLeft, hTail⟩
          apply List.Forall₂.cons
          · intro x
            exact or_congr (hLeft x) (hRight x)
          · exact hTail

theorem formulaRename_correct_aux (rename : Nat → Nat)
    (formula : ConstraintFormula) (translatedStack originalStack : List FormulaMeaning)
    (h : List.Forall₂ (FormulaRenameRelation rename) translatedStack originalStack) :
    List.Forall₂ (FormulaRenameRelation rename)
      ((formula.map (renameFormulaToken rename)).foldl formulaStep translatedStack)
      (formula.foldl formulaStep originalStack) := by
  induction formula generalizing translatedStack originalStack with
  | nil => exact h
  | cons part rest ih =>
    simp only [List.map_cons, List.foldl_cons]
    exact ih _ _ (formulaStep_rename_preserves rename part translatedStack originalStack h)

theorem formulaHolds_rename_correct (rename : Nat → Nat)
    (formula : ConstraintFormula) (x : Nat → ℚ) :
    FormulaHolds x (renameFormulaVariables rename formula) ↔
      FormulaHolds (fun i => x (rename i)) formula := by
  have hDefault : FormulaRenameRelation rename (fun _ => False) (fun _ => False) := by
    intro y
    rfl
  have h := formulaRename_correct_aux rename formula [] [] List.Forall₂.nil
  have hHead := forall₂_headD (fun _ => False) (fun _ => False) hDefault h
  exact hHead x

theorem qfGroundMeaningStep_preserves (arguments : List GroundTermCode)
    (part : QFToken) (groundStack formulaStack : List FormulaMeaning)
    (h : List.Forall₂ QFMeaningRelation groundStack formulaStack) :
    List.Forall₂ QFMeaningRelation
      (qfGroundMeaningStep arguments groundStack part)
      (formulaStep formulaStack (rationalTokenOfQF
        (fun term => groundValuePolynomial (evaluateTermCode arguments term)) part)) := by
  cases part with
  | mk tag operands =>
    cases tag with
    | zero =>
      apply List.Forall₂.cons
      · intro x
        simp [QFMeaningRelation, qfGroundMeaningStep, rationalTokenOfQF, formulaStep]
      · exact h
    | succ tag =>
      cases tag with
      | zero =>
        apply List.Forall₂.cons
        · intro x
          simp [QFMeaningRelation, qfGroundMeaningStep, rationalTokenOfQF, formulaStep]
        · exact h
      | succ tag =>
        cases tag with
        | zero =>
          apply List.Forall₂.cons
          · intro x
            simp only [QFMeaningRelation, qfGroundMeaningStep, rationalTokenOfQF,
              formulaStep]
            rw [atomSatisfied_equalityAtom, groundValuePolynomial_correct,
              groundValuePolynomial_correct]
          · exact h
        | succ tag =>
          cases tag with
          | zero =>
            apply List.Forall₂.cons
            · intro x
              simp only [QFMeaningRelation, qfGroundMeaningStep, rationalTokenOfQF,
                formulaStep]
              rw [atomSatisfied_disequalityAtom, groundValuePolynomial_correct,
                groundValuePolynomial_correct]
            · exact h
          | succ tag =>
            cases tag with
            | zero =>
              have hDefault : QFMeaningRelation (fun _ => False) (fun _ => False) := by
                intro x
                rfl
              rcases popStack_forall₂ (fun _ => False) (fun _ => False) hDefault h with
                ⟨hHead, hTail⟩
              apply List.Forall₂.cons
              · intro x
                exact not_congr (hHead x)
              · exact hTail
            | succ tag =>
              cases tag with
              | zero =>
                have hDefault : QFMeaningRelation (fun _ => False) (fun _ => False) := by
                  intro x
                  rfl
                let groundRight := popStack (fun _ => False) groundStack
                let formulaRight := popStack (fun _ => False) formulaStack
                rcases popStack_forall₂ (fun _ => False) (fun _ => False) hDefault h with
                  ⟨hRight, hRest⟩
                let groundLeft := popStack (fun _ => False) groundRight.2
                let formulaLeft := popStack (fun _ => False) formulaRight.2
                rcases popStack_forall₂ (fun _ => False) (fun _ => False) hDefault hRest with
                  ⟨hLeft, hTail⟩
                apply List.Forall₂.cons
                · intro x
                  exact and_congr (hLeft x) (hRight x)
                · exact hTail
              | succ tag =>
                cases tag with
                | zero =>
                  have hDefault : QFMeaningRelation (fun _ => False) (fun _ => False) := by
                    intro x
                    rfl
                  let groundRight := popStack (fun _ => False) groundStack
                  let formulaRight := popStack (fun _ => False) formulaStack
                  rcases popStack_forall₂ (fun _ => False) (fun _ => False) hDefault h with
                    ⟨hRight, hRest⟩
                  let groundLeft := popStack (fun _ => False) groundRight.2
                  let formulaLeft := popStack (fun _ => False) formulaRight.2
                  rcases popStack_forall₂ (fun _ => False) (fun _ => False) hDefault hRest with
                    ⟨hLeft, hTail⟩
                  apply List.Forall₂.cons
                  · intro x
                    exact or_congr (hLeft x) (hRight x)
                  · exact hTail
                | succ _ =>
                  apply List.Forall₂.cons
                  · intro x
                    simp [QFMeaningRelation, qfGroundMeaningStep, rationalTokenOfQF,
                      formulaStep]
                  · exact h

theorem qfGroundMeaningCode_correct_aux (arguments : List GroundTermCode)
    (matrix : QFCode) (groundStack formulaStack : List FormulaMeaning)
    (h : List.Forall₂ QFMeaningRelation groundStack formulaStack) :
    List.Forall₂ QFMeaningRelation
      (matrix.foldl (qfGroundMeaningStep arguments) groundStack)
      (List.foldl formulaStep formulaStack (matrix.map (rationalTokenOfQF
        (fun term => groundValuePolynomial (evaluateTermCode arguments term))))) := by
  induction matrix generalizing groundStack formulaStack with
  | nil => exact h
  | cons part rest ih =>
    simp only [List.foldl_cons, List.map_cons]
    exact ih _ _ (qfGroundMeaningStep_preserves arguments part groundStack formulaStack h)

theorem qfGroundMeaningCode_correct (x : Nat → ℚ)
    (arguments : List GroundTermCode) (matrix : QFCode) :
    FormulaHolds x (qfToFormula
      (fun term => groundValuePolynomial (evaluateTermCode arguments term)) matrix) ↔
      qfGroundHolds x arguments matrix := by
  have hDefault : QFMeaningRelation (fun _ => False) (fun _ => False) := by
    intro y
    rfl
  have h := qfGroundMeaningCode_correct_aux arguments matrix [] [] List.Forall₂.nil
  have hHead := forall₂_headD (fun _ => False) (fun _ => False) hDefault h
  exact (hHead x).symm

def positiveExistentialEnvironment (x : Nat → ℚ) (term : GroundTermCode)
    (phi : PositiveExistential) : Nat → ℚ :=
  fun i => if h0 : i = 0 then groundTermValue x term
    else if h : i ≤ phi.1 then x (witnessLabel term (i - 1)) else x 0

/-- The input term's value is fixed by `x`; each witness ranges independently
over `Q`, and its index is disjoint from every ground-term label. -/
def positiveExistentialHolds (x : Nat → ℚ) (phi : PositiveExistential)
    (term : GroundTermCode) : Prop :=
  FormulaHolds (positiveExistentialEnvironment x term phi) phi.2

theorem positiveExistentialFormula_semantics (x : Nat → ℚ)
    (phi : PositiveExistential) (term : GroundTermCode) :
    FormulaHolds x (positiveExistentialFormula phi term) ↔
      positiveExistentialHolds x phi term := by
  unfold positiveExistentialFormula positiveExistentialHolds
  rw [formulaHolds_rename_correct]
  have hAssignment :
      (fun i => x ((phiVariableLabel phi.1 term i).getD 0)) =
        positiveExistentialEnvironment x term phi := by
    funext i
    by_cases hZero : i = 0
    · subst i
      simp [positiveExistentialEnvironment, phiVariableLabel, groundTermValue]
    · by_cases hWitness : i ≤ phi.1
      · simp [positiveExistentialEnvironment, phiVariableLabel, hZero, hWitness]
      · simp [positiveExistentialEnvironment, phiVariableLabel, hZero, hWitness]
  rw [hAssignment]

/-- Meaning of one code in the paper's finite constraint stream. Malformed
payloads retain the same harmless-true convention as the total translator;
paper-facing use is restricted to valid syntax. -/
def testItemSemantics (x : Nat → ℚ) (axioms : Nat → PrenexAxiom)
    (phi : PositiveExistential) (item : TestItem) : Prop :=
  match itemTag item with
  | 1 => groundTermValue x zeroTerm = 0
  | 2 => groundTermValue x oneTerm = 1
  | 3 => if (itemTerms item).length == 2 then
      let left := (itemTerms item)[0]!
      let right := (itemTerms item)[1]!
      groundTermValue x (additionTerm left right) =
        groundTermValue x left + groundTermValue x right
    else True
  | 4 => if (itemTerms item).length == 2 then
      let left := (itemTerms item)[0]!
      let right := (itemTerms item)[1]!
      groundTermValue x (multiplicationTerm left right) =
        groundTermValue x left * groundTermValue x right
    else True
  | 5 => if (itemTerms item).length == 1 then
      let argument := (itemTerms item).head!
      groundTermValue x (negationTerm argument) = -groundTermValue x argument
    else True
  | 6 =>
      let left := itemLeftArgs item
      let right := itemRightArgs item
      if functionSymbolArity (itemPayload item) != left.length ||
          left.length != right.length then True else
        (∀ pair ∈ List.zip left right,
          groundTermValue x pair.1 = groundTermValue x pair.2) →
          groundTermValue x (functionApplication (itemPayload item) left) =
            groundTermValue x (functionApplication (itemPayload item) right)
  | 7 =>
      let skolemized := skolemizeAxiom (itemPayload item)
        (axioms (itemPayload item))
      if skolemized.1 != (itemTerms item).length then True
      else qfGroundHolds x (itemTerms item) skolemized.2
  | 8 => if (itemTerms item).length == 1 then
      positiveExistentialHolds x phi (itemTerms item).head!
    else True
  | _ => True

theorem functionCongruenceFormula_semantics (x : Nat → ℚ) (symbol : Nat)
    (left right : List GroundTermCode) :
    FormulaHolds x (functionCongruenceFormula symbol left right) ↔
      (if functionSymbolArity symbol != left.length || left.length != right.length
       then True else
        (∀ pair ∈ List.zip left right,
          groundTermValue x pair.1 = groundTermValue x pair.2) →
        groundTermValue x (functionApplication symbol left) =
          groundTermValue x (functionApplication symbol right)) := by
  by_cases hMalformed :
      functionSymbolArity symbol != left.length || left.length != right.length
  · simp [functionCongruenceFormula, hMalformed]
  · have hFormula : functionCongruenceFormula symbol left right =
        ConstraintFormula.disjoin
          (ConstraintFormula.negate (functionInputsEqualFormula left right))
          (equalTermFormula (functionApplication symbol left)
            (functionApplication symbol right)) := by
      simp [functionCongruenceFormula, hMalformed]
    rw [hFormula]
    dsimp only [equalTermFormula]
    rw [formulaHolds_disjoin_right_atom, formulaHolds_negate,
      functionInputsEqualFormula_correct, atomSatisfied_equalityAtom,
      groundValuePolynomial_correct, groundValuePolynomial_correct]
    have hValid : functionSymbolArity symbol = left.length ∧
        left.length = right.length := by
      simpa [ne_eq] using hMalformed
    simp [hValid.1, hValid.2, imp_iff_not_or]

theorem testItemFormula_zero_semantics (x : Nat → ℚ)
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential) (item : TestItem)
    (hTag : itemTag item = 1) :
    FormulaHolds x (testItemFormula axioms phi item) ↔
      testItemSemantics x axioms phi item := by
  have hTag' : item.1 = 1 := by simpa [itemTag] using hTag
  have hEquation := formulaHolds_equation x (polyVar (termLabel zeroTerm))
  simpa [testItemFormula, testItemSemantics, itemTag, itemTerms, hTag',
    groundTermValue, groundValuePolynomial, polynomialValue_polyVar, zeroTerm,
    termLabel] using hEquation

theorem testItemFormula_one_semantics (x : Nat → ℚ)
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential) (item : TestItem)
    (hTag : itemTag item = 2) :
    FormulaHolds x (testItemFormula axioms phi item) ↔
      testItemSemantics x axioms phi item := by
  have hTag' : item.1 = 2 := by simpa [itemTag] using hTag
  have hCoefficient : coeffValue [(1, 0)] = (1 : ℚ) := by
    norm_num [coeffValue, coeffAtomValue]
  have hEquation := formulaHolds_equation x
    (polynomialDifference (polyVar (termLabel oneTerm))
      (polyConst [(1, 0)]))
  rw [polynomialValue_polynomialDifference, polynomialValue_polyVar,
    polynomialValue_polyConst, hCoefficient] at hEquation
  have hExpected : x (termLabel oneTerm) - 1 = 0 ↔
      groundTermValue x oneTerm = 1 := by
    simp [groundTermValue, oneTerm, termLabel]
    constructor <;> intro h <;> linarith
  rw [hExpected] at hEquation
  simpa [testItemFormula, testItemSemantics, itemTag, itemTerms, hTag',
    groundTermValue, groundValuePolynomial, polynomialValue_polyVar,
    polynomialValue_polynomialDifference, polynomialValue_polyConst,
    coeffValue, coeffAtomValue, oneTerm, termLabel] using hEquation

theorem testItemFormula_addition_semantics (x : Nat → ℚ)
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential) (item : TestItem)
    (hTag : itemTag item = 3) :
    FormulaHolds x (testItemFormula axioms phi item) ↔
      testItemSemantics x axioms phi item := by
  have hTag' : item.1 = 3 := by simpa [itemTag] using hTag
  by_cases hLength : item.2.2.1.length == 2
  · have hLength' : item.2.2.1.length = 2 := of_decide_eq_true hLength
    simpa [testItemFormula, testItemSemantics, itemTag, itemTerms, hTag', hLength]
      using operationFormula_addition_semantics x item.2.2.1 hLength'
  · simp [testItemFormula, testItemSemantics, operationFormula, itemTag,
      itemTerms, hTag', hLength]

theorem testItemFormula_multiplication_semantics (x : Nat → ℚ)
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential) (item : TestItem)
    (hTag : itemTag item = 4) :
    FormulaHolds x (testItemFormula axioms phi item) ↔
      testItemSemantics x axioms phi item := by
  have hTag' : item.1 = 4 := by simpa [itemTag] using hTag
  by_cases hLength : item.2.2.1.length == 2
  · have hLength' : item.2.2.1.length = 2 := of_decide_eq_true hLength
    simpa [testItemFormula, testItemSemantics, itemTag, itemTerms, hTag', hLength]
      using operationFormula_multiplication_semantics x item.2.2.1 hLength'
  · simp [testItemFormula, testItemSemantics, operationFormula, itemTag,
      itemTerms, hTag', hLength]

theorem testItemFormula_negation_semantics (x : Nat → ℚ)
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential) (item : TestItem)
    (hTag : itemTag item = 5) :
    FormulaHolds x (testItemFormula axioms phi item) ↔
      testItemSemantics x axioms phi item := by
  have hTag' : item.1 = 5 := by simpa [itemTag] using hTag
  by_cases hLength : item.2.2.1.length == 1
  · have hLength' : item.2.2.1.length = 1 := of_decide_eq_true hLength
    simpa [testItemFormula, testItemSemantics, itemTag, itemTerms, hTag', hLength]
      using operationFormula_negation_semantics x item.2.2.1 hLength'
  · simp [testItemFormula, testItemSemantics, operationFormula, itemTag,
      itemTerms, hTag', hLength]

theorem testItemFormula_congruence_semantics (x : Nat → ℚ)
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential) (item : TestItem)
    (hTag : itemTag item = 6) :
    FormulaHolds x (testItemFormula axioms phi item) ↔
      testItemSemantics x axioms phi item := by
  have hTag' : item.1 = 6 := by simpa [itemTag] using hTag
  simpa [testItemFormula, testItemSemantics, itemTag, itemPayload,
    itemLeftArgs, itemRightArgs, hTag'] using
      (functionCongruenceFormula_semantics x (itemPayload item)
        (itemLeftArgs item) (itemRightArgs item))

theorem testItemFormula_universal_semantics (x : Nat → ℚ)
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential) (item : TestItem)
    (hTag : itemTag item = 7) :
    FormulaHolds x (testItemFormula axioms phi item) ↔
      testItemSemantics x axioms phi item := by
  have hTag' : item.1 = 7 := by simpa [itemTag] using hTag
  let skolemized := skolemizeAxiom item.2.1 (axioms item.2.1)
  by_cases hMismatch : skolemized.1 != item.2.2.1.length
  · simp [testItemFormula, testItemSemantics, itemTag, itemPayload, itemTerms,
      hTag', universalInstanceFormula, skolemized, hMismatch]
  · simpa [testItemFormula, testItemSemantics, itemTag, itemPayload, itemTerms,
      hTag', universalInstanceFormula, skolemized, hMismatch] using
        (qfGroundMeaningCode_correct x item.2.2.1 skolemized.2)

theorem testItemFormula_positiveExistential_semantics (x : Nat → ℚ)
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential) (item : TestItem)
    (hTag : itemTag item = 8) :
    FormulaHolds x (testItemFormula axioms phi item) ↔
      testItemSemantics x axioms phi item := by
  have hTag' : item.1 = 8 := by simpa [itemTag] using hTag
  by_cases hLength : item.2.2.1.length == 1
  · simpa [testItemFormula, testItemSemantics, itemTag, itemTerms, hTag',
      hLength, positiveExistentialFormula_semantics]
  · simp [testItemFormula, testItemSemantics, itemTag, itemTerms, hTag', hLength]

theorem testItemFormula_semantics (x : Nat → ℚ)
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential) (item : TestItem) :
    FormulaHolds x (testItemFormula axioms phi item) ↔
      testItemSemantics x axioms phi item := by
  rcases item with ⟨tag, rest⟩
  cases tag with
  | zero =>
    simp [testItemFormula, testItemSemantics, itemTag]
  | succ n =>
    cases n with
    | zero =>
      exact testItemFormula_zero_semantics x axioms phi (1, rest) rfl
    | succ n =>
      cases n with
      | zero =>
        exact testItemFormula_one_semantics x axioms phi (2, rest) rfl
      | succ n =>
        cases n with
        | zero =>
          exact testItemFormula_addition_semantics x axioms phi (3, rest) rfl
        | succ n =>
          cases n with
          | zero =>
            exact testItemFormula_multiplication_semantics x axioms phi
              (4, rest) rfl
          | succ n =>
            cases n with
            | zero =>
              exact testItemFormula_negation_semantics x axioms phi (5, rest) rfl
            | succ n =>
              cases n with
              | zero =>
                exact testItemFormula_congruence_semantics x axioms phi
                  (6, rest) rfl
              | succ n =>
                cases n with
                | zero =>
                  exact testItemFormula_universal_semantics x axioms phi
                    (7, rest) rfl
                | succ n =>
                  cases n with
                  | zero =>
                    exact testItemFormula_positiveExistential_semantics x
                      axioms phi (8, rest) rfl
                  | succ n =>
                    simp [testItemFormula, testItemSemantics, itemTag]

def rootQuerySemantics (x : Nat → ℚ) (q : IntegerPolynomialQuery) : Prop :=
  polynomialValue x (rootPolynomial q) = 0 ∧
    x (termLabel zeroTerm) = 0

theorem rootQueryFormula_semantics (q : IntegerPolynomialQuery) (x : Nat → ℚ) :
    FormulaHolds x (rootQueryFormula q) ↔ rootQuerySemantics x q := by
  rw [formulaHolds_iff_toDNF, rootQueryFormula_toDNF]
  simp [rootQuerySemantics, H10RationalFormula.satisfiesAt,
    H10RationalFormula.clauseSatisfied, H10RationalCompiler.atomSatisfied,
    polynomialValue_polyVar]

def decodeTestItem (index : Nat) : TestItem :=
  (Encodable.decode (α := TestItem) index).getD dummyItem

theorem primrec_decodeTestItem : Primrec decodeTestItem := by
  unfold decodeTestItem
  have hget : Primrec fun item : Option TestItem => item.getD dummyItem :=
    Primrec₂.comp Primrec.option_getD Primrec.id (Primrec.const dummyItem)
  exact hget.comp Primrec.decode

def finiteTestSemantics (axioms : Nat → PrenexAxiom)
    (phi : PositiveExistential) (q : IntegerPolynomialQuery) (n : Nat) : Prop :=
  ∃ x : Nat → ℚ,
    rootQuerySemantics x q ∧
      ∀ i, i < n → testItemSemantics x axioms phi (decodeTestItem i)

def finiteTestDNF (axioms : Nat → PrenexAxiom) (phi : PositiveExistential)
    (q : IntegerPolynomialQuery) (n : Nat) : ConstraintSystem :=
  (List.range n).foldl (fun system i =>
    andDNF system (toDNF (testItemFormula axioms phi (decodeTestItem i))))
    (toDNF (rootQueryFormula q))

def dnfClauseFormula (clause : List Atom) : ConstraintFormula :=
  clause.foldr (fun atom rest => ConstraintFormula.conjoin
    (ConstraintFormula.atom atom) rest) ConstraintFormula.truth

def dnfFormula : ConstraintSystem → ConstraintFormula
  | [] => ConstraintFormula.falsity
  | clause :: rest => ConstraintFormula.disjoin (dnfClauseFormula clause)
      (dnfFormula rest)

def dnfFormulaFold (dnf : ConstraintSystem) : ConstraintFormula :=
  dnf.foldr (fun clause rest =>
    ConstraintFormula.disjoin (dnfClauseFormula clause) rest)
    ConstraintFormula.falsity

theorem dnfFormula_eq_fold (dnf : ConstraintSystem) :
    dnfFormula dnf = dnfFormulaFold dnf := by
  induction dnf with
  | nil => rfl
  | cons clause rest ih => simp [dnfFormula, dnfFormulaFold, ih]

theorem primrec_formulaAtom : Primrec fun atom : Atom =>
    ConstraintFormula.atom atom := by
  unfold ConstraintFormula.atom FormulaToken.atom
  have htoken : Primrec fun atom : Atom =>
      (some (Sum.inl atom : Atom ⊕ (Bool × Bool)) : FormulaToken) :=
    Primrec.option_some.comp (Primrec.sumInl.comp Primrec.id)
  exact Primrec₂.comp Primrec.list_cons htoken (Primrec.const [])

theorem primrec_formulaConjoin : Primrec₂ ConstraintFormula.conjoin := by
  unfold ConstraintFormula.conjoin
  apply Primrec₂.mk
  have hfirst : Primrec fun p : ConstraintFormula × ConstraintFormula =>
      p.1 ++ p.2 :=
    Primrec₂.comp Primrec.list_append Primrec.fst Primrec.snd
  exact Primrec₂.comp Primrec.list_append hfirst
    (Primrec.const [FormulaToken.conjunction])

theorem primrec_formulaDisjoin : Primrec₂ ConstraintFormula.disjoin := by
  unfold ConstraintFormula.disjoin
  apply Primrec₂.mk
  have hfirst : Primrec fun p : ConstraintFormula × ConstraintFormula =>
      p.1 ++ p.2 :=
    Primrec₂.comp Primrec.list_append Primrec.fst Primrec.snd
  exact Primrec₂.comp Primrec.list_append hfirst
    (Primrec.const [FormulaToken.disjunction])

theorem primrec_groundValuePolynomial : Primrec groundValuePolynomial := by
  unfold groundValuePolynomial
  exact primrec_polyVar.comp primrec_termLabel

theorem primrec_polynomialDifference : Primrec₂ polynomialDifference := by
  apply Primrec₂.mk
  unfold polynomialDifference polynomialNeg
  have hneg : Primrec fun p : PolynomialCode × PolynomialCode =>
      polyMul (polyConst [(-1, 0)]) p.2 :=
    Primrec₂.comp primrec_polyMul (Primrec.const (polyConst [(-1, 0)])) Primrec.snd
  exact Primrec₂.comp primrec_polyAdd Primrec.fst hneg

theorem primrec_additionTerm : Primrec₂ additionTerm := by
  unfold additionTerm
  have hargs : Primrec fun p : GroundTermCode × GroundTermCode => [p.1, p.2] := by
    exact Primrec₂.comp Primrec.list_cons Primrec.fst
      (Primrec₂.comp Primrec.list_cons Primrec.snd (Primrec.const []))
  have hinput : Primrec fun p : GroundTermCode × GroundTermCode =>
      (builtinAddSymbol, [p.1, p.2]) :=
    Primrec.pair (Primrec.const builtinAddSymbol) hargs
  exact (Primrec₂.uncurry.mpr primrec_applicationTerm).comp hinput

theorem primrec_multiplicationTerm : Primrec₂ multiplicationTerm := by
  unfold multiplicationTerm
  have hargs : Primrec fun p : GroundTermCode × GroundTermCode => [p.1, p.2] := by
    exact Primrec₂.comp Primrec.list_cons Primrec.fst
      (Primrec₂.comp Primrec.list_cons Primrec.snd (Primrec.const []))
  have hinput : Primrec fun p : GroundTermCode × GroundTermCode =>
      (builtinMulSymbol, [p.1, p.2]) :=
    Primrec.pair (Primrec.const builtinMulSymbol) hargs
  exact (Primrec₂.uncurry.mpr primrec_applicationTerm).comp hinput

theorem primrec_negationTerm : Primrec negationTerm := by
  unfold negationTerm
  have hargs : Primrec fun t : GroundTermCode => [t] :=
    Primrec₂.comp Primrec.list_cons Primrec.id (Primrec.const [])
  have hinput : Primrec fun t : GroundTermCode => (builtinNegSymbol, [t]) :=
    Primrec.pair (Primrec.const builtinNegSymbol) hargs
  exact (Primrec₂.uncurry.mpr primrec_applicationTerm).comp hinput

set_option maxHeartbeats 1000000 in
theorem primrec_operationFormula : Primrec₂ operationFormula := by
  apply Primrec₂.uncurry.mp
  unfold operationFormula
  let P := Nat × List GroundTermCode
  have htagEq (n : Nat) : PrimrecPred fun p : P => p.1 = n :=
    PrimrecRel.comp Primrec.eq Primrec.fst (Primrec.const n)
  have hlengthEq (n : Nat) : PrimrecPred fun p : P => p.2.length = n :=
    PrimrecRel.comp Primrec.eq (Primrec.list_length.comp Primrec.snd)
      (Primrec.const n)
  have hleft : Primrec fun p : P => p.2.getD 0 zeroTerm :=
    Primrec₂.comp (f := fun (terms : List GroundTermCode) (i : Nat) =>
      terms.getD i zeroTerm) (Primrec.list_getD zeroTerm) Primrec.snd
      (Primrec.const 0)
  have hright : Primrec fun p : P => p.2.getD 1 zeroTerm :=
    Primrec₂.comp (f := fun (terms : List GroundTermCode) (i : Nat) =>
      terms.getD i zeroTerm) (Primrec.list_getD zeroTerm) Primrec.snd
      (Primrec.const 1)
  have hleftValue : Primrec fun p : P => groundValuePolynomial (p.2.getD 0 zeroTerm) :=
    primrec_groundValuePolynomial.comp hleft
  have hrightValue : Primrec fun p : P => groundValuePolynomial (p.2.getD 1 zeroTerm) :=
    primrec_groundValuePolynomial.comp hright
  have hargs : Primrec fun p : P => [p.2.getD 0 zeroTerm, p.2.getD 1 zeroTerm] := by
    exact Primrec₂.comp Primrec.list_cons hleft
      (Primrec₂.comp Primrec.list_cons hright (Primrec.const []))
  have haddTerm : Primrec fun p : P =>
      additionTerm (p.2.getD 0 zeroTerm) (p.2.getD 1 zeroTerm) := by
    unfold additionTerm
    exact primrec_applicationTerm.comp
      (Primrec.pair (Primrec.const builtinAddSymbol) hargs)
  have hmulTerm : Primrec fun p : P =>
      multiplicationTerm (p.2.getD 0 zeroTerm) (p.2.getD 1 zeroTerm) := by
    unfold multiplicationTerm
    exact primrec_applicationTerm.comp
      (Primrec.pair (Primrec.const builtinMulSymbol) hargs)
  have hnegTerm : Primrec fun p : P => negationTerm (p.2.getD 0 zeroTerm) :=
    primrec_negationTerm.comp hleft
  have haddResult : Primrec fun p : P =>
      groundValuePolynomial (additionTerm (p.2.getD 0 zeroTerm)
        (p.2.getD 1 zeroTerm)) := primrec_groundValuePolynomial.comp haddTerm
  have hmulResult : Primrec fun p : P =>
      groundValuePolynomial (multiplicationTerm (p.2.getD 0 zeroTerm)
        (p.2.getD 1 zeroTerm)) := primrec_groundValuePolynomial.comp hmulTerm
  have hnegResult : Primrec fun p : P =>
      groundValuePolynomial (negationTerm (p.2.getD 0 zeroTerm)) :=
    primrec_groundValuePolynomial.comp hnegTerm
  have haddPolynomial : Primrec fun p : P =>
      polyAdd (groundValuePolynomial (p.2.getD 0 zeroTerm))
        (groundValuePolynomial (p.2.getD 1 zeroTerm)) :=
    Primrec₂.comp primrec_polyAdd hleftValue hrightValue
  have hmulPolynomial : Primrec fun p : P =>
      polyMul (groundValuePolynomial (p.2.getD 0 zeroTerm))
        (groundValuePolynomial (p.2.getD 1 zeroTerm)) :=
    Primrec₂.comp primrec_polyMul hleftValue hrightValue
  have haddDiff : Primrec fun p : P =>
      polynomialDifference
        (groundValuePolynomial (additionTerm (p.2.getD 0 zeroTerm)
          (p.2.getD 1 zeroTerm)))
        (polyAdd (groundValuePolynomial (p.2.getD 0 zeroTerm))
          (groundValuePolynomial (p.2.getD 1 zeroTerm))) :=
    Primrec₂.comp primrec_polynomialDifference haddResult haddPolynomial
  have hmulDiff : Primrec fun p : P =>
      polynomialDifference
        (groundValuePolynomial (multiplicationTerm (p.2.getD 0 zeroTerm)
          (p.2.getD 1 zeroTerm)))
        (polyMul (groundValuePolynomial (p.2.getD 0 zeroTerm))
          (groundValuePolynomial (p.2.getD 1 zeroTerm))) :=
    Primrec₂.comp primrec_polynomialDifference hmulResult hmulPolynomial
  have hnegSum : Primrec fun p : P =>
      polyAdd (groundValuePolynomial (negationTerm (p.2.getD 0 zeroTerm)))
        (groundValuePolynomial (p.2.getD 0 zeroTerm)) :=
    Primrec₂.comp primrec_polyAdd hnegResult hleftValue
  let plusFormula : P → ConstraintFormula := fun p => ConstraintFormula.atom (false,
      polynomialDifference
        (groundValuePolynomial (additionTerm (p.2.getD 0 zeroTerm)
          (p.2.getD 1 zeroTerm)))
        (polyAdd (groundValuePolynomial (p.2.getD 0 zeroTerm))
          (groundValuePolynomial (p.2.getD 1 zeroTerm))))
  have hplus : Primrec plusFormula := by
    unfold plusFormula
    exact primrec_formulaAtom.comp (Primrec.pair (Primrec.const false) haddDiff)
  let timesFormula : P → ConstraintFormula := fun p => ConstraintFormula.atom (false,
      polynomialDifference
        (groundValuePolynomial (multiplicationTerm (p.2.getD 0 zeroTerm)
          (p.2.getD 1 zeroTerm)))
        (polyMul (groundValuePolynomial (p.2.getD 0 zeroTerm))
          (groundValuePolynomial (p.2.getD 1 zeroTerm))))
  have htimes : Primrec timesFormula := by
    unfold timesFormula
    exact primrec_formulaAtom.comp (Primrec.pair (Primrec.const false) hmulDiff)
  let minusFormula : P → ConstraintFormula := fun p => ConstraintFormula.atom (false,
      polyAdd (groundValuePolynomial (negationTerm (p.2.getD 0 zeroTerm)))
        (groundValuePolynomial (p.2.getD 0 zeroTerm)))
  have hminus : Primrec minusFormula := by
    unfold minusFormula
    exact primrec_formulaAtom.comp (Primrec.pair (Primrec.const false) hnegSum)
  have htruth : Primrec fun _ : P => ConstraintFormula.truth := Primrec.const _
  let negBranch : P → ConstraintFormula := fun p =>
      if p.1 = 5 then
        (if p.2.length = 1 then minusFormula p
          else ConstraintFormula.truth)
      else ConstraintFormula.truth
  have hnegBranch : Primrec negBranch := by
    unfold negBranch
    exact Primrec.ite (htagEq 5) (Primrec.ite (hlengthEq 1) hminus htruth) htruth
  let mulBranch : P → ConstraintFormula := fun p =>
      if p.1 = 4 then
        (if p.2.length = 2 then timesFormula p else negBranch p)
      else negBranch p
  have hmulBranch : Primrec mulBranch := by
    unfold mulBranch
    exact Primrec.ite (htagEq 4) (Primrec.ite (hlengthEq 2) htimes hnegBranch) hnegBranch
  let plusBranch : P → ConstraintFormula := fun p =>
      if p.2.length = 2 then plusFormula p else mulBranch p
  have hplusBranch : Primrec plusBranch := by
    unfold plusBranch
    exact Primrec.ite (hlengthEq 2) hplus hmulBranch
  let result : P → ConstraintFormula := fun p =>
      if p.1 = 3 then plusBranch p else mulBranch p
  have hresult : Primrec result := by
    unfold result
    exact Primrec.ite (htagEq 3) hplusBranch hmulBranch
  exact hresult.of_eq fun p => by
    rcases p with ⟨tag, terms⟩
    by_cases htag3 : tag = 3
    · subst tag
      by_cases hlength2 : terms.length = 2
      · simp [result, plusBranch, mulBranch, negBranch, plusFormula, timesFormula,
          minusFormula, hlength2, beq_iff_eq]
      · simp [result, plusBranch, mulBranch, negBranch, plusFormula, timesFormula,
          minusFormula, hlength2, beq_iff_eq]
    · by_cases htag4 : tag = 4
      · subst tag
        by_cases hlength2 : terms.length = 2
        · simp [result, plusBranch, mulBranch, negBranch, plusFormula, timesFormula,
            minusFormula, hlength2, beq_iff_eq]
        · simp [result, plusBranch, mulBranch, negBranch, plusFormula, timesFormula,
            minusFormula, hlength2, beq_iff_eq]
      · by_cases htag5 : tag = 5
        · subst tag
          by_cases hlength1 : terms.length = 1
          · simp [result, plusBranch, mulBranch, negBranch, plusFormula, timesFormula,
              minusFormula, hlength1, beq_iff_eq]
          · simp [result, plusBranch, mulBranch, negBranch, plusFormula, timesFormula,
              minusFormula, hlength1, beq_iff_eq]
        · simp [result, plusBranch, mulBranch, negBranch, plusFormula, timesFormula,
            minusFormula, htag3, htag4, htag5, beq_iff_eq]

theorem primrec_rootVariableLabel :
    Primrec fun p : IntegerPolynomialQuery × Nat =>
      rootVariableLabel p.1 p.2 := by
  unfold rootVariableLabel
  have hindex : Primrec₂ (fun (_ : IntegerPolynomialQuery) (i : Nat) => i) := by
    apply Primrec₂.mk
    exact Primrec.snd
  have harity : Primrec₂ (fun (q : IntegerPolynomialQuery) (_ : Nat) => q.1) := by
    apply Primrec₂.mk
    exact Primrec.fst.comp Primrec.fst
  have hcondition₂ : Primrec₂ (fun (q : IntegerPolynomialQuery) (i : Nat) =>
      decide (i < q.1)) :=
    (Primrec.nat_lt.comp₂ hindex harity).decide
  have hcondition : Primrec fun p : IntegerPolynomialQuery × Nat =>
      decide (p.2 < p.1.1) := Primrec₂.uncurry.mpr hcondition₂
  have hinput : Primrec fun p : IntegerPolynomialQuery × Nat =>
      inputTerm p.2 := by
    unfold inputTerm
    exact Primrec₂.comp Primrec₂.natPair (Primrec.const 0)
      (Primrec.succ.comp (Primrec.succ.comp Primrec.snd))
  have htrue : Primrec fun p : IntegerPolynomialQuery × Nat =>
      termLabel (inputTerm p.2) := primrec_termLabel.comp hinput
  exact (Primrec.cond hcondition htrue
    (Primrec.const (termLabel zeroTerm))).of_eq fun p => by
      simp

theorem primrec_rootPolynomialTerm :
    Primrec fun p : IntegerPolynomialQuery × IntegerTermCode =>
      rootPolynomialTerm p.1 p.2 := by
  unfold rootPolynomialTerm
  have hcoefficientEntry :
      Primrec₂ (fun (_ : IntegerPolynomialQuery × IntegerTermCode)
        (factor : Int) => (factor, (0 : Nat))) := by
    apply Primrec₂.mk
    exact Primrec.pair Primrec.snd (Primrec.const 0)
  have hcoefficients : Primrec fun p : IntegerPolynomialQuery × IntegerTermCode =>
      p.2.1.1.map (fun factor => (factor, (0 : Nat))) :=
    Primrec.list_map
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) hcoefficientEntry
  have hmonomialEntry :
      Primrec₂ (fun (p : IntegerPolynomialQuery × IntegerTermCode)
        (ie : Nat × Nat) =>
          (rootVariableLabel p.1 ie.1, ie.2)) := by
    apply Primrec₂.mk
    exact Primrec.pair
      (primrec_rootVariableLabel.comp <| Primrec.pair
        (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hmonomial : Primrec fun p : IntegerPolynomialQuery × IntegerTermCode =>
      p.2.2.map (fun ie => (rootVariableLabel p.1 ie.1, ie.2)) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd) hmonomialEntry
  have hterm : Primrec fun p : IntegerPolynomialQuery × IntegerTermCode =>
      (p.2.1.1.map (fun factor => (factor, (0 : Nat))),
        p.2.2.map (fun ie => (rootVariableLabel p.1 ie.1, ie.2))) :=
    Primrec.pair hcoefficients hmonomial
  have hscale : Primrec fun p : IntegerPolynomialQuery × IntegerTermCode =>
      List.range p.2.1.2 :=
    Primrec.list_range.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hcopy : Primrec₂ (fun (p : IntegerPolynomialQuery × IntegerTermCode)
      (_ : Nat) =>
        (p.2.1.1.map (fun factor => (factor, (0 : Nat))),
          p.2.2.map (fun ie => (rootVariableLabel p.1 ie.1, ie.2)))) := by
    apply Primrec₂.mk
    exact hterm.comp Primrec.fst
  exact Primrec.list_map hscale hcopy

theorem primrec_rootPolynomial : Primrec rootPolynomial := by
  unfold rootPolynomial
  exact Primrec.list_flatMap Primrec.snd primrec_rootPolynomialTerm

theorem primrec_rootQueryFormula : Primrec rootQueryFormula := by
  unfold rootQueryFormula
  have hroot : Primrec fun q : IntegerPolynomialQuery =>
      ConstraintFormula.atom (false, rootPolynomial q) := by
    exact primrec_formulaAtom.comp
      (Primrec.pair (Primrec.const false) primrec_rootPolynomial)
  exact Primrec₂.comp primrec_formulaConjoin hroot
    (Primrec.const (ConstraintFormula.atom
      (false, polyVar (termLabel zeroTerm))))

theorem primrec_dnfClauseFormula : Primrec dnfClauseFormula := by
  unfold dnfClauseFormula
  have hstepFn : Primrec fun z : List Atom × (Atom × ConstraintFormula) =>
      ConstraintFormula.conjoin (ConstraintFormula.atom z.2.1) z.2.2 :=
    Primrec₂.comp primrec_formulaConjoin
      (primrec_formulaAtom.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec₂ (fun (_ : List Atom) (pair : Atom × ConstraintFormula) =>
      ConstraintFormula.conjoin (ConstraintFormula.atom pair.1) pair.2) :=
    Primrec₂.mk hstepFn
  exact Primrec.list_foldr Primrec.id
    (Primrec.const ConstraintFormula.truth) hstep

theorem primrec_dnfFormula : Primrec dnfFormula := by
  have hstepFn : Primrec fun z : ConstraintSystem ×
      (List Atom × ConstraintFormula) =>
        ConstraintFormula.disjoin (dnfClauseFormula z.2.1) z.2.2 :=
    Primrec₂.comp primrec_formulaDisjoin
      (primrec_dnfClauseFormula.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec₂ (fun (_ : ConstraintSystem)
      (pair : List Atom × ConstraintFormula) =>
        ConstraintFormula.disjoin (dnfClauseFormula pair.1) pair.2) :=
    Primrec₂.mk hstepFn
  have hfold : Primrec dnfFormulaFold := by
    unfold dnfFormulaFold
    exact Primrec.list_foldr Primrec.id
      (Primrec.const ConstraintFormula.falsity) hstep
  exact hfold.of_eq fun dnf => (dnfFormula_eq_fold dnf).symm

def makeFiniteTestFormula (axioms : Nat → PrenexAxiom)
    (phi : PositiveExistential) (q : IntegerPolynomialQuery) (n : Nat) :
    ConstraintFormula := dnfFormula (finiteTestDNF axioms phi q n)

/-- Once the one-item translator is primitive recursive, the root formula,
finite stream, and DNF serialization give a primitive-recursive prefix
compiler. -/
theorem primrec_finiteTestDNF_of_itemTranslator
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential)
    (hitem : Primrec fun item : TestItem => testItemFormula axioms phi item) :
    Primrec fun p : IntegerPolynomialQuery × Nat =>
      finiteTestDNF axioms phi p.1 p.2 := by
  unfold finiteTestDNF
  have hitemAt : Primrec fun index : Nat =>
      toDNF (testItemFormula axioms phi (decodeTestItem index)) :=
    primrec_toDNF.comp (hitem.comp primrec_decodeTestItem)
  have hindices : Primrec fun p : IntegerPolynomialQuery × Nat => List.range p.2 :=
    Primrec.list_range.comp (Primrec.snd.comp Primrec.id)
  have hrootDnf : Primrec fun p : IntegerPolynomialQuery × Nat =>
      toDNF (rootQueryFormula p.1) :=
    primrec_toDNF.comp (primrec_rootQueryFormula.comp Primrec.fst)
  have hstepFn : Primrec fun z : (IntegerPolynomialQuery × Nat) ×
      (ConstraintSystem × Nat) => andDNF z.2.1
        (toDNF (testItemFormula axioms phi (decodeTestItem z.2.2))) :=
    primrec_andDNF.comp (Primrec.fst.comp Primrec.snd)
      (hitemAt.comp (Primrec.snd.comp Primrec.snd))
  have hstep : Primrec₂ (fun (_ : IntegerPolynomialQuery × Nat)
      (state : ConstraintSystem × Nat) => andDNF state.1
        (toDNF (testItemFormula axioms phi (decodeTestItem state.2)))) :=
    Primrec₂.mk hstepFn
  have hfold : Primrec fun p : IntegerPolynomialQuery × Nat =>
      (List.range p.2).foldl
        (fun system index => andDNF system
          (toDNF (testItemFormula axioms phi (decodeTestItem index))))
        (toDNF (rootQueryFormula p.1)) :=
    Primrec.list_foldl hindices hrootDnf hstep
  exact hfold.of_eq fun _ => rfl

theorem primrec_makeFiniteTestFormula_of_itemTranslator
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential)
    (hitem : Primrec fun item : TestItem => testItemFormula axioms phi item) :
    Primrec fun p : IntegerPolynomialQuery × Nat =>
      makeFiniteTestFormula axioms phi p.1 p.2 := by
  unfold makeFiniteTestFormula
  exact primrec_dnfFormula.comp
    (primrec_finiteTestDNF_of_itemTranslator axioms phi hitem)

theorem makeFiniteTestFormula_computable_of_itemTranslator
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential)
    (hitem : Primrec fun item : TestItem => testItemFormula axioms phi item) :
    Computable₂ fun q n => makeFiniteTestFormula axioms phi q n :=
  (primrec_makeFiniteTestFormula_of_itemTranslator axioms phi hitem).to_comp.to₂

/-- The `n`th finite test means the first `n` decoded constraint codes, in
addition to the root equation.  Invalid codes decode to the dummy true
constraint.  Since every code is eventually decoded, every ring, function,
universal-instance, and witness constraint occurs in some test. -/
def PaperFiniteTestSolvable (axioms : Nat → PrenexAxiom)
    (phi : PositiveExistential) (q : IntegerPolynomialQuery) (n : Nat) : Prop :=
  finiteTestSemantics axioms phi q n

theorem foldTestItems_satisfies (indices : List Nat) (x : Nat → ℚ)
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential)
    (initial : ConstraintSystem) :
    satisfiesAt x (indices.foldl (fun system i =>
      andDNF system (toDNF (testItemFormula axioms phi (decodeTestItem i)))) initial) ↔
      satisfiesAt x initial ∧
        ∀ i, i ∈ indices →
          FormulaHolds x (testItemFormula axioms phi (decodeTestItem i)) := by
  induction indices generalizing initial with
  | nil => simp
  | cons index rest ih =>
    simp only [List.foldl_cons, ih, satisfiesAt_andDNF, formulaHolds_iff_toDNF]
    simp [List.mem_cons, and_assoc, and_left_comm, and_comm]

theorem finiteTestDNF_satisfies_iff_of_semantic_translators
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential)
    (q : IntegerPolynomialQuery) (n : Nat)
    (hroot : ∀ x, FormulaHolds x (rootQueryFormula q) ↔ rootQuerySemantics x q)
    (hitem : ∀ x i, FormulaHolds x
      (testItemFormula axioms phi (decodeTestItem i)) ↔
        testItemSemantics x axioms phi (decodeTestItem i)) :
    H10RationalCompiler.Satisfies (finiteTestDNF axioms phi q n) ↔
      finiteTestSemantics axioms phi q n := by
  unfold H10RationalCompiler.Satisfies finiteTestSemantics finiteTestDNF
  constructor
  · rintro ⟨x, h⟩
    have hfold := (foldTestItems_satisfies (List.range n) x axioms phi
      (toDNF (rootQueryFormula q))).mp h
    rcases hfold with ⟨hrootDNF, hitems⟩
    refine ⟨x, ?_, ?_⟩
    · exact (hroot x).mp ((formulaHolds_iff_toDNF _ _).mpr hrootDNF)
    · intro i hi
      exact (hitem x i).mp (hitems i (List.mem_range.mpr hi))
  · rintro ⟨x, hrootSem, hitems⟩
    refine ⟨x, ?_⟩
    apply (foldTestItems_satisfies (List.range n) x axioms phi
      (toDNF (rootQueryFormula q))).mpr
    refine ⟨(formulaHolds_iff_toDNF _ _).mp ((hroot x).mpr hrootSem), ?_⟩
    intro i hi
    exact (hitem x i).mpr (hitems i (List.mem_range.mp hi))

theorem dnfClauseFormula_fold (clause : List Atom) (stack : List ConstraintSystem) :
    (dnfClauseFormula clause).foldl dnfStep stack = [clause] :: stack := by
  induction clause generalizing stack with
  | nil => simp [dnfClauseFormula, ConstraintFormula.truth, FormulaToken.truth, dnfStep]
  | cons atom rest ih =>
      change (ConstraintFormula.atom atom ++ dnfClauseFormula rest ++
        [FormulaToken.conjunction]).foldl dnfStep stack = _
      rw [List.foldl_append, List.foldl_append]
      simp only [ConstraintFormula.atom, List.foldl_cons, List.foldl_nil,
        FormulaToken.atom, dnfStep]
      rw [ih]
      simp [FormulaToken.conjunction, popStack, andDNF]

theorem dnfFormula_fold (dnf : ConstraintSystem) (stack : List ConstraintSystem) :
    (dnfFormula dnf).foldl dnfStep stack = dnf :: stack := by
  induction dnf generalizing stack with
  | nil => simp [dnfFormula, ConstraintFormula.falsity, FormulaToken.falsity, dnfStep]
  | cons clause rest ih =>
      change (dnfClauseFormula clause ++ dnfFormula rest ++
        [FormulaToken.disjunction]).foldl dnfStep stack = _
      rw [List.foldl_append, List.foldl_append]
      rw [dnfClauseFormula_fold clause, ih]
      simp [FormulaToken.disjunction, dnfStep, popStack, orDNF]

theorem dnfClauseFormula_toDNF (clause : List Atom) :
    toDNF (dnfClauseFormula clause) = [clause] := by
  change ((dnfClauseFormula clause).foldl dnfStep []).headD [] = [clause]
  have h := dnfClauseFormula_fold clause []
  simpa using congrArg (fun stack : List ConstraintSystem => stack.headD []) h

theorem dnfFormula_toDNF (dnf : ConstraintSystem) :
    toDNF (dnfFormula dnf) = dnf := by
  change ((dnfFormula dnf).foldl dnfStep []).headD [] = dnf
  have h := dnfFormula_fold dnf []
  simpa using congrArg (fun stack : List ConstraintSystem => stack.headD []) h

theorem makeFiniteTestFormula_correct (axioms : Nat → PrenexAxiom)
    (phi : PositiveExistential) (q : IntegerPolynomialQuery) (n : Nat) :
    FormulaSatisfies (makeFiniteTestFormula axioms phi q n) ↔
      PaperFiniteTestSolvable axioms phi q n := by
  rw [formula_to_dnf_correct]
  simpa [makeFiniteTestFormula, PaperFiniteTestSolvable, dnfFormula_toDNF] using
    (finiteTestDNF_satisfies_iff_of_semantic_translators axioms phi q n
      (rootQueryFormula_semantics q)
      (fun x i => testItemFormula_semantics x axioms phi (decodeTestItem i)))

/-- If the instantiated compiler is computable, its indexed finite-test
solvability predicate is decidable relative to the finite-arity H10(Q) root
oracle.  The theorem keeps that oracle explicit. -/
theorem finiteTestSolvable_computable_of_h10Q
    (axioms : Nat → PrenexAxiom) (phi : PositiveExistential)
    (hmake : Computable₂ fun q n => makeFiniteTestFormula axioms phi q n)
    (oracle : ComputablePred H10RationalQueryAdapter.IntegerPolynomialHasRationalRoot) :
    ComputablePred fun p : IntegerPolynomialQuery × Nat =>
      PaperFiniteTestSolvable axioms phi p.1 p.2 := by
  have hformula := indexed_formulaSatisfies_computable_of_h10Q
    (fun q n => makeFiniteTestFormula axioms phi q n) hmake oracle
  exact ComputablePred.of_eq hformula fun p =>
    makeFiniteTestFormula_correct axioms phi p.1 p.2

theorem decodeTestItem_encode (item : TestItem) :
    decodeTestItem (Encodable.encode item) = item := by
  unfold decodeTestItem
  rw [Encodable.encodek]
  rfl

theorem everyTestItem_isEnumerated (item : TestItem) :
    ∃ index, decodeTestItem index = item :=
  ⟨Encodable.encode item, decodeTestItem_encode item⟩

/-! ## Fresh witness and syntax examples -/

example (t : GroundTermCode) (i : Nat) : witnessLabel t i ≠ termLabel t := by
  exact witnessLabel_fresh t t i

example (i : Nat) : evaluateTermCode [] (inputOpenTerm i) = inputTerm i :=
  evaluateTermCode_input i

example (left right : GroundTermCode) :
    functionApplication (functionSymbolCode 1 7 2) [left, right] =
      applicationTerm (functionSymbolCode 1 7 2) [left, right] := rfl

example (left right : GroundTermCode) :
    functionCongruenceFormula (functionSymbolCode 1 7 1) [left] [right] =
      ConstraintFormula.disjoin
        (ConstraintFormula.negate (ConstraintFormula.conjoin ConstraintFormula.truth
          (equalTermFormula left right)))
        (equalTermFormula (functionApplication (functionSymbolCode 1 7 1) [left])
          (functionApplication (functionSymbolCode 1 7 1) [right])) := by
  simp [functionCongruenceFormula, functionInputsEqualFormula,
    functionSymbolArity, functionSymbolCode]

example (t : GroundTermCode) :
    universalInstanceFormula
      (fun _ => ([true, false],
        [(2, ([variableToken 0], [variableToken 1]))])) 4 [t] =
      ConstraintFormula.atom (equalityAtom (groundValuePolynomial t)
        (groundValuePolynomial
          (applicationTerm (functionSymbolCode 2 (Nat.pair 4 1) 1) [t]))) := by
  simp [universalInstanceFormula, skolemizeAxiom, skolemPrefix, skolemPrefixStep,
    skolemTerm, substituteQFToken, substituteTerm, qfToFormula, rationalTokenOfQF,
    token, variableToken, functionToken, evaluateTermCode, evaluateTermStep,
    variableStep, functionApplicationStep, functionSymbolArity, functionSymbolCode,
    Nat.unpair_pair, ConstraintFormula.atom]

example (q : IntegerPolynomialQuery) (n : Nat) :
    FormulaSatisfies (makeFiniteTestFormula (fun _ => ([], [])) (0, []) q n) ↔
      H10RationalCompiler.Satisfies
        (finiteTestDNF (fun _ => ([], [])) (0, []) q n) := by
  rw [formula_to_dnf_correct]
  simp [makeFiniteTestFormula, dnfFormula_toDNF]

end H10RationalGroundTests
