# Task Plan: V286 Single Pointer-Spin Collapse

## Goal

Extend the native pure-spin theorem to one pointer-valued read-only spin loop,
adding `libvsync/cnalock` without wrapper proof logic, old-correct losses, new
wrong results, or a material resource regression.

## Acceptance Gates

- The wrapper remains byte-identical and only passes the existing native flag.
- Deagle admits exactly one marked loop with one recursively checked atomic
  load, local-only bookkeeping, and an exit.
- A missing reservation is allowed only for a pointer-valued atomic load.
- Pointer-specific mutations reject and the local-only control remains admitted.
- Prior90 remains 90/90.
- Exact725 has zero V285-correct losses and no new wrong result.
- Commit and push only after every gate passes.

## Phases

- [x] Reconstruct the V285 libvsync residual and prior V278 failure.
- [x] Implement in an isolated worktree based on accepted V285.
- [x] Run mutations, natural controls, Prior90, and Exact725.
- [x] Reject publication because Exact725 loses one V285-correct task.

## Status

V286 gains `cnalock` but loses V285-correct `ticketlock`; the official total
remains 700. The candidate is rejected and its source is not committed or
pushed. The failed experimental version remains recorded in the dashboard.
