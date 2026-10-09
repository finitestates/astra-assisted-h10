# Validation record

The current validation was run locally on 2026-10-08 after proving the
independent finite-test semantics and adding the associated theorem and axiom
audit entries. The supplied `MANIFEST.md` changes were already in the working
tree before validation.

## Current checks

- Exact command: `PATH=/tmp/h10-elan/bin:$PATH bash verify.sh` (exit code 0,
  2026-10-08). The mathlib cache was populated: no files were downloaded and
  841 files were already decompressed. `lake build` completed all 1,384 jobs;
  the script then ran `Audit.lean` and `leanchecker` on all five proof modules.
- `Audit.lean` printed theorem types and axiom dependencies for the independent
  QF interpreter, positive-existential assignment semantics, root semantics,
  each ring operation, function congruence, the all-tags item semantics
  theorem, the finite-DNF semantic equivalence, and
  `makeFiniteTestFormula_correct`. It also confirms that
  `finiteTestSolvable_computable_of_h10Q` still assumes computability of the
  instantiated formula generator and the integer H10(Q) root oracle.
- `lake env leanchecker FiniteTests`, `RationalQueryCompiler`,
  `IntegerQueryAdapter`, `BooleanFormula`, and `FiniteGroundTests` all exited 0
  through `verify.sh`. These replay the named project modules through Lean's
  kernel; they are not independent proof checkers and were not run with
  `--fresh` over all imported declarations.
- Exact command: `PATH=/tmp/h10-elan/bin:$PATH bash ci/audit-modules.sh` (exit
  code 0). The pinned `axiom-audit` tool audited 25, 114, 111, 101, and 322
  declarations in `FiniteTests`, `RationalQueryCompiler`,
  `IntegerQueryAdapter`, `BooleanFormula`, and `FiniteGroundTests`,
  respectively. All stayed within `[propext, Classical.choice, Quot.sound]`.
- `rg -n '\bsorry\b|^\s*axiom\b|\bunsafe\b' --glob '*.lean' .` found no
  matches. `git diff --check` exited 0.
- Lean emitted unused-simp-argument and unused-variable warnings in
  `FiniteGroundTests.lean`; there were no build or kernel-check errors.

The finite-test correctness theorem now targets an independent semantic
predicate, and no longer assumes a per-item translator theorem. The generic
root and item translator primitive-recursiveness proofs are still missing, as
are the recursive ring-theory input and the proof that finite multiplier lists
with the Section 3 coverage properties exist. The pinned paper lists no
numerical multiplier table. No H10(Q) decision algorithm or arithmetic
`passes`/`complete` proof is claimed. Verification used the existing Lake
outputs; it did not run `lake clean` first.

## GitHub Actions coverage

`.github/workflows/lean.yml` builds the project, runs `leanchecker` on
`FiniteTests`, `RationalQueryCompiler`, `IntegerQueryAdapter`,
`BooleanFormula`, and `FiniteGroundTests`, then displays the theorem and axiom
report from `Audit.lean`. `ci/audit-modules.sh` runs the pinned `axiom-audit`
tool once for each of those five top-level proof modules. Each run allows only
`propext`, `Classical.choice`, and `Quot.sound`. `Audit` is built and executed as a report
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
