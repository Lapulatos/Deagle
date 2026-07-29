# V295 Native Residual Plan

## Objective

Increase coverage beyond accepted V294 using one unified native
`deagle_exe`, with no wrapper analysis, no old-correct loss, no new wrong
result, and no material aggregate resource regression.

## P0 Actions

- [completed] Classify the nine remaining Weaver timeouts by GOTO and solver
  mechanism.
- [completed] Select one generic, fail-closed native mechanism with at least one
  plausible target.
- [completed] Implement it without benchmark names, paths, expected labels, or
  source-line conditions.
- [completed] Run target, premise-breaking mutation, and natural-control gates.

## Release Gates

- [completed] Prior90 remains 90/90.
- [completed] Paired V294/V295 Exact725 has zero old-correct losses and zero new
  wrong results.
- [completed] Aggregate CPU, wall, and summed memory do not materially regress.
- [completed] Wrapper entry files remain byte-identical.
- [completed] Native witness and reproducible-build checks pass.
- [completed] Commit and push immediately only after every gate passes.

## Residual Boundary

V292 already rejected broad libvsync pure-read admission and bounded SafeStack
progress. V293 rejected the elimination-backoff RF-selector direction. V295
therefore begins with the remaining Weaver timeout family; it will not reopen
those rejected mechanisms without new evidence.
