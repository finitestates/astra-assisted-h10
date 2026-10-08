# Validation record

The checks below were actually executed in this conversation on 2026-10-08,
before a subsequent workspace cleanup removed the temporary project and
toolchain. The source was then restored from the complete source text retained
in the conversation. No proof changes were made during restoration. The
restored files have not been compiled again in the replacement environment.

## Successful checks

- `lake build`: exit code 0. Both `FiniteTests` and `Audit` built successfully,
  without warnings in the final run. Lake reported 860 jobs, including cached
  dependencies; this does not mean 860 new mathematical results were proved.
- `Audit.lean` printed the main theorem types, exposing the mathematical
  assumptions as explicit arguments.
- `#print axioms` for all six project theorems reported exactly
  `[propext, Classical.choice, Quot.sound]`.
- `lake env leanchecker FiniteTests`: exit code 0, with empty stdout/stderr.
  This replays this module's declarations through Lean's kernel. It is not an
  independent proof checker and was not run with `--fresh` over all imports.

There are no `sorry` proofs, custom `axiom` declarations, or `unsafe`
declarations in the two project Lean files. An axiom audit does not discharge
the assumptions in a theorem's type: `positive_re`, `source_undecidable`, and
all fields of `FiniteTestInterface` remain required inputs.

`validation/previous-build-output.txt` reproduces the final build output
preserved in the conversation. It is a recovered transcript, not a newly
generated post-restoration log. `SHA256SUMS` identifies the delivered source and
documentation; these hashes were generated after restoration.

## Pinned software

- Official Linux Lean release: `lean-4.35.0-rc4-linux.tar.zst`
- Lean version: `4.35.0-rc4`
- Lean release commit: `c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`
- mathlib commit: `62bf13aabd0db1bf4cbe2a6ec087c6f7a677f448`
- mathlib and transitive dependencies were fetched at their pinned commits;
  compiled imports came from the mathlib cache.

No modifications were made to Lean's compiler, logical kernel, or mathlib
theorems. No Lean or mathlib binaries are distributed with this project.

## Host compatibility during the original check

On the original execution host, Lean could not find its executable because
numeric process IDs and the mounted `/proc` filesystem used different PID
namespaces. Reading `/proc/self/exe` worked. The included
`host-compat/proc_self_compat.c` redirects only a `readlink` request for the
current process's `/proc/<pid>/exe` to `/proc/self/exe`; other paths are unchanged.

The original commands used this adapter via `LD_PRELOAD` and put the downloaded
Lean `bin` directory on `PATH`. The adapter changes executable-path discovery,
not parsing, elaboration, proof terms, axioms, or kernel validation. It is
included for transparency and should not be necessary on an ordinary host.

For the same specific host issue, it can be compiled with:

```sh
cc -shared -fPIC host-compat/proc_self_compat.c -o host-compat/proc_self_compat.so -ldl
```

Do not mistake the host adapter for part of the mathematical proof.
