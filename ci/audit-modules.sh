#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

# Keep this pin synchronized with leanprover/lean-action's axiom-audit runner.
h10_audit_ref="v0.1.2"
h10_audit_sha="46024e005996495c65ef609368e11ab39c4222e3"
h10_audit_dir="$(mktemp -d "${RUNNER_TEMP:-/tmp}/h10-axiom-audit.XXXXXX")"
trap 'rm -rf "$h10_audit_dir"' EXIT

git clone --depth 1 --branch "$h10_audit_ref" \
  https://github.com/leanprover-community/axiom-audit.git "$h10_audit_dir/tool"

h10_actual_sha="$(git -C "$h10_audit_dir/tool" rev-parse HEAD)"
if [[ "$h10_actual_sha" != "$h10_audit_sha" ]]; then
  printf 'axiom-audit %s resolved to %s, expected %s\n' \
    "$h10_audit_ref" "$h10_actual_sha" "$h10_audit_sha" >&2
  exit 1
fi

cp lean-toolchain "$h10_audit_dir/tool/lean-toolchain"
(
  cd "$h10_audit_dir/tool"
  lake build
)

h10_audit_bin="$h10_audit_dir/tool/.lake/build/bin/axiom-audit"
h10_allowed_axioms="propext,Classical.choice,Quot.sound"

# axiom-audit accepts one module root per invocation. These module names are
# intentionally top-level, so audit each proof module separately.
for h10_module in FiniteTests RationalQueryCompiler IntegerQueryAdapter BooleanFormula; do
  echo "::group::Axiom audit: $h10_module"
  lake env "$h10_audit_bin" --root "$h10_module" --allow "$h10_allowed_axioms"
  echo "::endgroup::"
done
