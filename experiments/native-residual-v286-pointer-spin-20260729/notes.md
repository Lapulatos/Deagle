# Notes: V286 Single Pointer-Spin Collapse

## Candidate

- Baseline: accepted V285, 700 official / 701 adjudicated correct.
- Source worktree:
  `/private/tmp/deagle-v286-single-pointer-spin.20260729`.
- Server workspace:
  `/data3/sujie/workspaces/deagle-v286-single-pointer-spin-r1-20260729`.
- Unified binary SHA-256:
  `3185092399c7a082567d86a4ea3eece128880eeb7ed9c3ad356d0ee5635e4cf6`.
- Changed source: `src/analyses/pure_spin_wait_analysis.cpp`.
- Wrapper: byte-identical to accepted V285.

## Gates

- `cnalock`: native success.
- `rec_mcslock` and scalar-spin controls: native inconclusive.
- Five negative mutations reject; the local-only positive control admits.
- Prior90: 90/90 correct.
- Invalid libvsync r1 is excluded because image `deagle:sujie` dropped the
  benchmark XML options. Formal runs use `deagle-rvf-p1:sujie`.

## Exact725 Result

- Run:
  `/data3/sujie/experiments/v286-single-pointer-spin-exact725-r1`.
- XML:
  `/data3/sujie/experiments/v286-single-pointer-spin-exact725-r1/results/exact725.2026-07-29_12-35-01.results.accepted-native-integration-exact725.Concurrency.xml.bz2`.
- Official/adjudicated correct: 700/701.
- `libvsync/cnalock.yml`: unknown -> correct true.
- `libvsync/ticketlock.yml`: correct true -> unknown.
- Net coverage change: zero.
- Decision: rejected for one V285-correct loss. No source commit or push.
