# Validation record

The current validation was run locally on 2026-10-08 after adding the finite-
arity integer-query adapter. Before implementation, `bash verify.sh` also
passed on the pre-adapter checkout under the same pinned Lean toolchain.

## Current checks

- `PATH=/tmp/h10-elan/bin:$PATH bash verify.sh`: exit code 0.
- The mathlib cache was already populated: no files needed downloading, and
  841 files were already decompressed.
- `lake build`: exit code 0; Lake completed 1380 jobs, including
  `IntegerQueryAdapter` and the updated `Audit`, with no warnings in the run.
- `Audit.lean` printed the coefficient-to-integer denotation, positive global
  denominator, root-preservation equivalence, finite-support bounds, primitive
  recursive normalization, and conditional root, finite-system, and indexed
  system oracle-composition theorem types. It also printed their axiom
  dependencies.
- `lake env leanchecker FiniteTests`,
  `lake env leanchecker RationalQueryCompiler`, and
  `lake env leanchecker IntegerQueryAdapter`: all exited 0 with empty output.
  These replay project declarations through Lean's kernel; they are not
  independent proof checkers and were not run with `--fresh` over all imported
  declarations.
- No project Lean file contains a `sorry`, custom `axiom`, or `unsafe`
  declaration. The audited results depend on `[propext, Classical.choice,
  Quot.sound]`, mathlib's standard foundational axioms.

The new oracle theorems retain `ComputablePred IntegerPolynomialHasRationalRoot`
as an explicit hypothesis. The adapter does not construct an H10(Q) decision
algorithm, nor does this slice construct the paper's indexed test generator.
The full verification used the existing Lake outputs; it did not run `lake
clean` first.

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
checkout and mathlib cache were available. `verify.sh` fetches the cache when
needed.

## Earlier validation artifacts

`validation/previous-build-output.txt` preserves an earlier baseline build
transcript. It covers only the original `FiniteTests` module and `Audit`; the
current check above builds and checks the project including
`RationalQueryCompiler` and `IntegerQueryAdapter`. The old host compatibility
note described a prior execution environment. `host-compat/proc_self_compat.c`
remains in the project for that historical record and was not needed for this
verification.
