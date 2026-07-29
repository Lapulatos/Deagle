# V297 Native Residual Plan

## Objective

Increase coverage beyond accepted V296 using one unified native
`deagle_exe`, with no wrapper analysis, no old-correct loss, no new wrong
result, and no material aggregate resource regression.

## P0 Actions

- [completed] Audit phase-boundary nondeterministic termination in the
  remaining alternating recurrence family.
- [completed] Derive a generic fail-closed transition-word summary.
- [completed] Implement without benchmark names, paths, expected labels, or
  source-line conditions.
- [completed] Rerun all gates after final alias and exit-phase identity review.

## Release Gates

- [completed] Prior90 remains 90/90.
- [completed] Paired V296/V297 Exact725 has zero old-correct losses and zero new
  wrong results.
- [completed] Aggregate CPU, wall, and summed memory do not materially regress.
- [completed] Wrapper entry files remain byte-identical.
- [completed] Native witness and reproducible-build checks pass.
- [completed] Commit and push immediately only after every gate passes.

## Current Status

The final alias and exit-phase checks and all release gates pass. The accepted
source and evidence are committed and pushed to `origin/deagle-dev`.

## Errors Encountered

- The first Prior90 BenchExec launch omitted `--tool-directory tool` and
  stopped before running tasks.
- The second launch was outside a delegated systemd scope and stopped before
  running tasks because required cgroups were unavailable.
- The final launch used both requirements and completed 90/90.
- Final review found an implicit static-zero premise in the first candidate.
  The release was paused, the premise was made explicit in native admission,
  and a nonzero-static-initializer mutation was added.
- A second review found that the parsed exit-phase identifier was not compared
  explicitly with the update-phase identifier, and that pre-spawn private
  aliases needed a direct-assignment-only rule. Both are tightened before
  release.
- A local evidence-listing command used GNU `find -printf`, which macOS `find`
  does not support. It made no changes; the listing was rerun with `stat`.
