# V296 Native Residual Plan

## Objective

Increase coverage beyond accepted V295 using one unified native
`deagle_exe`, with no wrapper analysis, no old-correct loss, no new wrong
result, and no material aggregate resource regression.

## P0 Actions

- [completed] Reclassify the 25 V295-unfinished tasks after removing the
  solved local-clamp target.
- [completed] Select one generic, fail-closed native mechanism with a precise
  semantic argument.
- [completed] Implement it without benchmark names, paths, expected labels, or
  source-line conditions.
- [completed] Run target, premise-breaking mutation, and natural-control gates.

## Release Gates

- [completed] Prior90 remains 90/90.
- [completed] Paired V295/V296 Exact725 has zero old-correct losses and zero new
  wrong results.
- [completed] Aggregate CPU, wall, and summed memory do not materially regress.
- [completed] Wrapper entry files remain byte-identical.
- [completed] Native witness and reproducible-build checks pass.
- [completed] Commit and push immediately only after every gate passes.
