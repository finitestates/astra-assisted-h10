# Contributions and provenance

Date: 2026-10-08.

- The user proposed attempting the final logical argument in Lean, chose the
  scope, and initiated this experiment.
- The OpenAI assistant (Codex) chose the abstractions, wrote and revised the
  Lean files and documentation, installed a pinned environment, and ran the
  recorded validation commands.
- The mathematical argument comes from the cited paper and standard
  computability theory. The theorem combining positive and negative searches
  is already proved in mathlib; it was not newly proved from first principles
  in this project.
- Lean and mathlib contributors provide the foundational software and imported
  results. Their upstream licenses and attribution remain applicable.

No independent human mathematical review has been performed. The user has not
been represented as the author of the paper, the discoverer of its arithmetic
results, or the manual author of this Lean code. No pull request has been
submitted as part of this experiment.

## Reviewed source snapshot

Repository: https://github.com/openai/math

Commit: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`

Path:
`preprints/Hilberts-tenth-problem-over-the-rational-numbers-September-24-2026/build/sections/02-reduction.tex`

The concluding logical reduction and a generic finite DNF-to-root-query
compiler are formalized. The paper's arithmetic arguments and its particular
indexed test generator are not formalized. Reading the arithmetic arguments
does not amount to verifying them. The source paper is not included in this
archive.
