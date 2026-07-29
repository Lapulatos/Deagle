# Task Plan: V288 Single-Worker Initialization Prefix

## Goal

Native Deagle should expose the real task91 counterexample by retaining a
complete inner initialization and materializing one structurally selected
worker, without wrapper verdict logic, old-correct losses, new wrong results,
or a material resource regression.

## Acceptance Gates

- One unified `deagle_exe`; wrapper hashes remain identical to V287.
- Admission and transformation are transactional and task-independent.
- The native transform derives initialization loops, worker class, worker
  selector, and unwind loop from the GOTO model.
- Premise-breaking mutations reject.
- Task91 produces a native violation witness with a semantically valid
  nonzero initialized datum.
- Task93 is either independently justified or remains inconclusive.
- Prior90 remains 90/90.
- Exact725 loses zero V287-correct tasks and adds no new wrong result.
- Resource metrics have no material regression.
- Commit, push, and dashboard publication occur only after all gates pass.

## Phases

- [x] Recheck the preserved candidate in the accepted container.
- [x] Identify the invalid host-direct conclusion (missing pthread bodies and
  zero generated VCCs).
- [x] Migrate the transactional native code onto accepted V287.
- [x] Compile and rerun task91/task93 plus natural and mutation controls.
- [x] Run Prior90 and Exact725 if the target gate passes.
- [x] Audit the native witness path and implementation boundary.
- [x] Publish experiment documentation and dashboard after every release gate
  passes.

## Errors Encountered

- The isolated worktree resolved `python3` to the Xcode Python 3.9 runtime,
  which lacks Playwright. Re-running the verifier with the repository's
  established `/opt/anaconda3/bin/python3` environment passed.

## Status

The migrated V288 binary finds only the task91 violation, leaves task93
unknown, preserves all V287 statuses otherwise, rejects all mutations, and
keeps Prior90 at 90/90. WitnessLint passes as a format gate, and the ordered
V288 is accepted. Native source commit
`4264197e57b726050c2d363108ade0b9dec78775` is pushed and confirmed on
`origin/deagle-dev`. The V1--V288 dashboard passes browser verification with
565 chart points, 290 ledger rows including the header, and zero console
errors. The documentation and dashboard artifact set is complete.
