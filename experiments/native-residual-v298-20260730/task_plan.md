# V298 Native Residual Plan

## Objective

Increase coverage beyond accepted V297 using one unified native `deagle_exe`,
with no wrapper analysis, no old-correct loss, no new wrong result, and no
material aggregate resource regression.

## P0 Actions

- [completed] Classify all 22 V297 Exact725 unfinished tasks by front-end
  rejection, solver bottleneck, and reusable program structure.
- [completed] Select one general native direction with explicit fail-closed
  premises and natural negative controls.
- [completed] Implement without benchmark names, paths, expected labels, or
  source-line conditions.
- [completed] Run target, mutation, Prior90, paired Exact725, witness, and
  reproducible-build gates.

## Release Gates

- [completed] Prior90 remains 90/90.
- [completed] Paired V297/V298 Exact725 has zero old-correct losses and zero new
  wrong results.
- [completed] Aggregate CPU, wall, and summed memory do not materially regress.
- [completed] Wrapper entry files remain byte-identical.
- [completed] Native verdict and witness generation stay inside `deagle_exe`.
- [completed] Commit and push immediately only after every gate passes.

## Current Status

All semantic, resource, source-boundary, witness, and reproducible-build gates
pass. This accepted experiment is committed and pushed to `origin/deagle-dev`.

## Errors Encountered

- The first remote build command assumed per-component CMake build
  directories. This tree uses the existing component Makefiles directly, so
  no compilation or verification task ran; the command was replaced.
- The first Makefile deployment excluded existing object files. The analyses
  source compiled, but CBMC's thin archives could not resolve untouched
  objects at link time. V298-r2 starts from the complete verified V297 build
  tree and overlays only the three candidate source files.
- The first V297 dashboard verification used the default Python, which lacked
  Playwright. A disposable `/private/tmp` environment was used instead.
- The V297 dashboard data generator still capped discovered versions at V296.
  The cap was advanced to V297.
- V295's end epoch and V296's start/end epochs disagreed with their ISO strings
  and artifact timestamps by 380 seconds. The epoch values were corrected;
  displayed evidence times were not changed.
