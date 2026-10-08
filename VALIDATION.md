# Validation record

The current verification was run locally on 2026-10-08 after adding the
rational-query compiler.

## Current checks

- `PATH=/tmp/h10-elan/bin:$PATH bash verify.sh`: exit code 0.
- The successful run followed `lake clean`, so the project modules were rebuilt
  from clean project outputs.
- The mathlib cache command found the cache already populated: 841 files were
decompressed and no files needed downloading.
- `lake build`: exit code 0; Lake completed 1378 jobs, including cached
  dependencies, and emitted no warnings in the final run.
- `Audit.lean` printed the theorem types and axiom dependencies for the original
  final-reduction results and the new compiler results.
- `lake env leanchecker FiniteTests` and
  `lake env leanchecker RationalQueryCompiler`: both exit code 0 with empty
  output. These checks replay project declarations through Lean's kernel; they
  are not independent proof checkers and were not run with `--fresh` over all
  imported declarations.
- No project Lean file contains a `sorry`, custom `axiom`, or `unsafe`
  declaration. The audited theorems depend on
  `[propext, Classical.choice, Quot.sound]`, mathlib's standard foundational
  axioms.

The theorem audit leaves its assumptions visible. In particular,
`constraintSystem_computable` and `indexed_constraintSystem_computable` take a
`ComputablePred RationalPolynomialHasRoot` oracle as a hypothesis. The compiler
formalizes finite constraint translation; it does not construct the paper's
indexed tests or prove an unconditional H10(Q) theorem.

## Pinned software

- Lean: `leanprover/lean4:v4.35.0-rc4`
- Lean release commit: `c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`
- Lake: `5.0.0-src+c29b6dd`
- mathlib commit: `62bf13aabd0db1bf4cbe2a6ec087c6f7a677f448`
- Transitive dependency revisions: `lake-manifest.json`

`elan`, `lean`, and `lake` were available through `/tmp/h10-elan/bin`; the
project's `lean-toolchain` selected the pinned Lean version. The current check
did not use the historical `/proc` compatibility adapter or modify Lean,
mathlib, the toolchain pin, or dependency revisions. A populated dependency
checkout and mathlib cache were available for this run; `verify.sh` downloads
the cache when needed.

## Earlier validation artifacts

`validation/previous-build-output.txt` preserves the earlier baseline build
transcript. It covers only the original `FiniteTests` module and `Audit`; the
current check above recompiles the updated project including
`RationalQueryCompiler`. The old host compatibility note described a prior
execution environment. `host-compat/proc_self_compat.c` remains in the project
for that historical record and was not needed for this verification.
