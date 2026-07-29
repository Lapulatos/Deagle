# Task Plan: V287 Pointer-Exception Scope

## Goal

Preserve V285 `ticketlock` while admitting the single pointer-valued
reservation-free spin loop in `cnalock`, without wrapper proof logic, old
correct losses, new wrong results, or a material resource regression.

## Acceptance Gates

- One unified `deagle_exe`; the accepted V285 wrapper remains byte-identical.
- Existing reservation and stuttering-retry proofs retain their V285 scope.
- Only the reservation-free pointer exception requires exactly one marked loop.
- Pointer-specific semantic mutations reject.
- Prior90 remains 90/90.
- Exact725 gains `cnalock`, loses zero V285-correct tasks, and adds no wrong.
- Resource metrics remain within the accepted regression bound.
- WitnessLint, build, diff, and source-boundary checks pass.

## Phases

- [x] Freeze V286 as a failed version and identify its global-gate regression.
- [x] Implement V287 from accepted V285 in an isolated worktree.
- [x] Pass natural, mutation, and Prior90 gates.
- [x] Pass Exact725, resource, witness, build, and source-boundary gates.
- [x] Commit, push, and publish the accepted result.

## Status

All release gates pass. V287 reaches 701 official / 702 adjudicated correct
with only `cnalock` newly covered and zero old-correct losses. Native commit
`3b02c2e0ed7854ba9d91971965dd84e77f3b2dcf` is pushed to `deagle-dev`; the
V1–V287 dashboard records both failed V286 and accepted V287.
