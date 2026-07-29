# Task Plan: V291 Native Guided Short-Schedule Search

## Goal

Add a task-independent native Deagle search that can discover a short
violation execution in one or more remaining timeout tasks, while requiring a
second solve over the untransformed original GOTO model before verdict and
witness generation.

## Acceptance Gates

- One unified `deagle_exe`; no wrapper analysis or verdict logic.
- No task path, benchmark name, expected label, source identifier, fixed
  worker role/count, known schedule, or target source-line dispatch.
- Every reduction is counterexample-only and can never return safe.
- Final violation result and GraphML come from an original-GOTO replay.
- Replay fails closed on missing guide, infeasibility, timeout, or property
  mismatch.
- Target mutations and natural controls reject or retain their expected result.
- Prior90 remains 90/90.
- Exact725 has zero V290-correct losses and zero new genuine wrong results.
- Aggregate CPU, wall, and summed memory do not materially regress.
- Commit and push immediately only after all gates pass.

## Phases

- [x] Freeze V290 as the accepted baseline and enumerate its 21 unresolved
  tasks.
- [x] Re-read the V275--V277 failure boundaries.
- [x] Attribute the current V290 target bottleneck and inspect native worker
  lifecycle/model structure.
- [x] State a reusable admission rule and bounded search strategy.
- [x] Implement only if the strategy does not encode the known schedule.
- [x] Run target, mutation, natural-control, Prior90, Exact725, and resource
  gates.
- [x] Commit and push only after every release gate passes.
- [x] Publish the accepted V291 dashboard row and verify the standalone HTML.

## Current Decision

Prior V276 correctly rejected a hard-coded ABA schedule. V291 may proceed only
if Deagle derives a bounded schedule search space from generic GOTO lifecycle,
atomic, alias, and property structure. The reduced search is a guide only;
V290's original-model replay remains the semantic release boundary.

The viable V291 gain came from a smaller generic correction to
the existing native pure-spin admission proof: retain prefix branch facts and
prune prefix CFG branches that cannot reach the marked loop. Target diagnosis
passes. Natural controls, mutations, Prior90, the paired Exact725 task diff,
resource comparison, and WitnessLint now pass.

## Status

All release gates passed. Accepted native commit
`c3031379673085b40f7b34e3d485ef4ddb3e854b` is pushed to
`origin/deagle-dev`. The V291 dashboard row is generated with an explicit N8
paired-protocol boundary; standalone-page verification reports 293 ledger
rows including the header and zero console errors.

## Errors Encountered

- The first diagnostic passed wrapper-only portfolio-selection flags directly
  to `deagle_exe`; the native parser rejected
  `--deagle-experiment-direct` before analysis. Those three usage-error logs
  are excluded. The corrected diagnostic uses only native parse options.
- On 2026-07-30 the recorded server build workspace
  `/data3/sujie/workspaces/deagle-v291-guided-short-schedule-r1-20260730`
  was no longer present when the rebuild resumed. No build or experiment
  result is inferred from that missing path; V291 must recreate an isolated
  workspace from the verified V290 baseline before testing the candidate.
- A source archive of accepted V290 retained Git-tracked thin `.a` archives
  whose referenced object files are not tracked. The first link therefore
  failed at `analyses.a(../analyses/ai.o): No such file or directory`.
  This is a stale-build-artifact failure, not a candidate compile failure;
  the newly created isolated workspace must be cleaned with the project
  Makefiles and rebuilt completely.
- The first Prior90 BenchExec launch executed 0/90 tasks because Ubuntu's
  AppArmor configuration forbids the unprivileged user namespace used by
  BenchExec's default container mode. The rerun uses BenchExec
  `--no-container`; runexec still enforces the declared CPU, memory, and wall
  limits, and all tool/dataset paths are explicit.
- The stock BenchExec `benchexec.tools.deagle` module drops every XML
  `<option>` for Deagle versions at least 2.2. The first two eight-worker
  Prior90 attempts therefore invoked the wrapper with only `--32`; both were
  stopped and excluded after inherited tasks timed out. The V291 benchmark
  uses an experiment-local tool-info module that only forwards the declared
  options. It performs no source/property inspection, verdict logic, or
  verification.
- The restarted server exposes 8 physical cores to the delegated user slice,
  while the historical dashboard run used 48 workers. V291 is therefore
  compared against a contemporaneous V290 run with the same binary package,
  tool-info module, 8 workers, task order, and resource limits. Historical
  N48 totals are not used as the release performance comparison.
- The first remote V290 clean build outlived its SSH output session. A second
  incremental `make` was briefly started against the same isolated tree, then
  its exact process group was stopped while the original build continued.
  The completed baseline binary was hash-checked before use.
