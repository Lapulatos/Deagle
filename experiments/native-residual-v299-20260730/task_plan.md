# V299 Native Residual Plan

## Objective

Increase coverage beyond accepted V298 using one unified native `deagle_exe`,
with no wrapper analysis, no old-correct loss, no new wrong result, and no
material aggregate resource regression.

## P0 Actions

- [completed] Reject unsigned subtractive tiled-loop equivalence because the
  small-bound wraparound case is not semantically equivalent.
- [completed] Derive a generic fail-closed relational array-scan
  bisimulation for two fully joined workers.
- [completed] Implement without benchmark names, paths, expected labels, or
  source-line conditions.
- [completed] Run target, mutation, Prior90, paired Exact725, and witness
  gates.
- [completed] Complete the independent reproducible build and
  reproducible-build gates.
- [completed] Publish dashboard and run final repository checks.
- [completed] Commit
  and push the accepted version.

## Release Gates

- [completed] Paired final Prior90 has zero status changes against V298 in
  the currently available server dataset.
- [completed] Paired V298/V299 Exact725 has zero old-correct losses and zero new
  wrong results.
- [completed] Aggregate CPU, wall, and summed memory do not materially regress.
- [completed] Wrapper entry files remain byte-identical.
- [completed] Native verdict and witness generation stay inside `deagle_exe`.
- [completed] Commit and push immediately only after every gate passes.

## Current Status

V299 starts from accepted commit
`b90ef66cb871963fd7c52b614347b008416ca27e` in an isolated worktree.
The target and 12 rejection mutations pass. The final Prior90 candidate has
zero status changes against a V298 control binary under the same server
environment. Paired Exact725 changes only the target from a wrong verdict to
correct true. The final correctness witness passes WitnessLint's format gate.
Two independent clean builds are byte-identical. The dashboard renders
V1-V299 with 300 rows including baseline and zero browser console errors.
All release gates pass.

## Errors Encountered

- The archived V298 paths under `/home/lapulatos` are absent on the current
  server. The available `/data3/sujie/svcomp2026-caat` tree produces very
  different absolute counts, so current gates use paired V298/V299 runs and
  do not overwrite accepted archival totals.
- The default BenchExec adapter did not forward XML options. Re-runs use the
  previously accepted `deagle_benchexec.py` adapter that appends options.
- The first independent `make clean` rebuild stopped because the server lacks
  `flex` and cleaning removes checked-in generated lexer sources. Copying only
  the generated lexer/parser C++ files from the other source tree allowed two
  independent clean object builds. Their final binaries are byte-identical.
- The evaluated incremental binary and clean-build binary differ because
  static-library member/link order changes function addresses. Release
  reproducibility therefore compares the two independent clean builds, while
  preserving the separately identified evaluated binary.
- Local Python Playwright is unavailable. Chrome rendering verifies 300 DOM
  rows including baseline, the complete V299 row, one SVG chart, and zero
  console errors.
