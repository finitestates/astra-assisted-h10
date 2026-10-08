module

import FiniteTests
import RationalQueryCompiler

/- Inspect theorem types as well as axioms: hypotheses remain hypotheses even
when the axiom report contains only Lean's standard foundational axioms. -/
#check @H10FiniteTests.re_exists_nat_of_computable
#check @H10FiniteTests.decision_transfer
#check @H10FiniteTests.undecidable_target
#check @H10RationalCompiler.compile_correct
#check @H10RationalCompiler.constraintSystem_computable
#check @H10RationalCompiler.indexed_constraintSystem_computable
#print axioms H10FiniteTests.re_exists_nat_of_computable
#print axioms H10FiniteTests.failure_iff_not
#print axioms H10FiniteTests.complement_re_of_tests
#print axioms H10FiniteTests.computable_of_re_and_tests
#print axioms H10FiniteTests.decision_transfer
#print axioms H10FiniteTests.undecidable_target
#print axioms H10RationalCompiler.compile_correct
#print axioms H10RationalCompiler.constraintSystem_computable
#print axioms H10RationalCompiler.indexed_constraintSystem_computable
