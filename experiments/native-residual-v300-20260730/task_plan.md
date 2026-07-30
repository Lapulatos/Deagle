# Task Plan: V300 Native Residual

## Goal

Add one generic native Deagle optimization that increases Exact725 coverage
without wrapper changes, old-correct losses, new wrong results, or material
resource regression.

## Gates

- [x] Base exactly on accepted V299 commit `869464b7`.
- [x] Select the three residual comparator scan-law timeouts as one semantic
  family.
- [x] Implement only generic production logic; no task names, paths, hashes,
  labels, or source-line constants.
- [x] Keep `svcomp_stuff/deagle` and `svcomp_stuff/deagle.py` byte-identical.
- [x] Pass direct target checks and all 14 negative mutation tests.
- [x] Pass paired Prior90 with only the three intended timeout-to-correct
  changes, zero old-correct losses, and zero new wrong.
- [x] Pass paired Exact725 with zero old-correct losses and zero new wrong.
- [x] Bound CPU, wall time, and memory deltas.
- [x] Generate and check three native correctness witnesses.
- [x] Reproduce the source binary in two independent object-free builds.
- [x] Update and browser-verify the dashboard through V300.
- [x] Pass final repository review and authorize the scoped commit/push.

## Status

All native correctness, performance, witness, mutation, and reproducibility
gates pass. The scoped evaluated candidate SHA-256
`549ce2ac77fe8d726d40fc7efb3b64027d017df8b16aa673e5a18d1ecc06a03f`
passes Prior90 and Exact725 with only the three intended timeout-to-correct
changes, zero losses, and zero new wrong results. All three final witnesses
pass WitnessLint's format gate. Two independent object-free builds produce
the byte-identical SHA-256
`8b96d184c37d85105ad30619b412ea21704468c96f7f40ded0c4190d236f90fe`.
The V300 dashboard has 301 embedded records (Baseline plus V1-V300), 302
ledger rows including the header, 589 chart points, and zero browser console
errors. Final review confirms byte-identical wrappers, no forbidden benchmark
literals in production, `git diff --check`, and a remote base still at V299.
The scoped V300 commit is ready to push.

## Errors Encountered

- `make -C src deagle_exe` failed because the executable target belongs to
  `src/cbmc/Makefile`; corrected to `make -C src/cbmc`.
- The first `src/cbmc` link found transferred thin archives whose referenced
  object files were absent. Rebuild all recursive `src` targets before
  relinking; keep generated parser sources because the server lacks `flex`.
- The recursive target retained some apparently up-to-date transferred thin
  archives, so a second link still found a missing `ansi-c` member. Build each
  linked archive directory normally (without `-B` or cleaning generated
  parsers), then relink.
- The first scan-law compile used the wrong `find_symbols` container type and
  protected generic subtype accessor. Replaced them with the existing
  static-symbol collector and `to_pointer_type(...).base_type()`.
- The first Prior90 launch used the system BenchExec module path and could not
  import `deagle_benchexec`. Relaunch with
  `PYTHONPATH=/data3/sujie/tmp/benchexec`, matching the prior accepted gates.
- The first V300 Prior90 gate incorrectly changed `fibonacci.wvr` and
  `test-easy1.wvr` from false to true. The cause was that unresolved standard
  `abort` and verified assume wrappers had been admitted in the shared
  relational-bisimulation effect checker. Scope both permissions exclusively
  to the new fully audited comparator-scan path; direct checks now restore both
  negative controls to `VERIFICATION FAILED` while preserving all three target
  proofs. The failed gate is retained and must not be used for publication.
