#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

lake exe cache get Mathlib/Computability/RE.lean
lake build
lake env lean Audit.lean
lake env leanchecker FiniteTests
