# Validation record

The current validation was run locally on 2026-10-08 after adding the Boolean
formula front end. Before implementation, the same verification command passed
on the original Lean sources under the same pinned Lean toolchain; the supplied
`MANIFEST.md` edit was already present in the working tree.

## Current checks

- Exact command: `PATH=/tmp/h10-elan/bin:$PATH bash verify.sh` (exit code 0).
- The mathlib cache was already populated: the cache command downloaded no
  files, and 841 files were already decompressed. This run therefore needed no
  network transfer; a fresh environment may need network access for Lean,
  dependencies, or cache files.
- `lake build`: exit code 0; Lake completed 1382 jobs, including
  `BooleanFormula` and the updated `Audit`.
- `Audit.lean` printed the coefficient-to-integer denotation, positive global
  denominator, root-preservation equivalence, finite-support bounds, primitive
  recursive normalization, formula-to-DNF correctness, primitive recursive
  formula conversion, and conditional formula and indexed-formula oracle
  theorem types. It also printed their axiom dependencies.
- `lake env leanchecker FiniteTests`,
  `lake env leanchecker RationalQueryCompiler`,
  `lake env leanchecker IntegerQueryAdapter`, and
  `lake env leanchecker BooleanFormula`: all exited 0 with empty output. These
  replay the named project modules through Lean's kernel; they are not
  independent proof checkers and were not run with `--fresh` over all imported
  declarations.
- No project Lean file contains a `sorry`, custom `axiom`, or `unsafe`
  declaration. The audited results depend on `[propext, Classical.choice,
  Quot.sound]`, mathlib's standard foundational axioms.

The formula oracle theorems retain
`ComputablePred IntegerPolynomialHasRationalRoot` as an explicit hypothesis.
The adapter does not construct an H10(Q) decision algorithm, nor does this
slice construct the paper's indexed test generator. The full verification used
the existing Lake outputs; it did not run `lake clean` first.

## GitHub Actions coverage

`.github/workflows/lean.yml` builds the project, runs `leanchecker` on
`FiniteTests`, `RationalQueryCompiler`, `IntegerQueryAdapter`, and
`BooleanFormula`, then displays the theorem and axiom report from `Audit.lean`.
`ci/audit-modules.sh` runs the pinned `axiom-audit` tool once for each of those
four top-level proof modules. Each run allows only `propext`,
`Classical.choice`, and `Quot.sound`. `Audit` is built and executed as a report
module; it contains no proof declarations of its own.

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
`RationalQueryCompiler`, `IntegerQueryAdapter`, and `BooleanFormula`. The old
host compatibility note described a prior execution environment.
`host-compat/proc_self_compat.c` remains in the project for that historical
record and was not needed for this verification.
