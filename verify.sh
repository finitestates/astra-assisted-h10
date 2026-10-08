#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

lake exe cache get Mathlib.Computability.RE
lake build
lake env lean Audit.lean
lake env leanchecker FiniteTests
lake env leanchecker RationalQueryCompiler
