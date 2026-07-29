# Conclusion: V293 Affine and RF Selector Feasibility

## Decision

Reject V293. It is a counted failed optimization version with zero coverage
gain and no production source change.

The affine nontermination direction is unsound without a proof excluding
signed wraparound. The independent high-fan-in RF selector direction builds
and runs, but the corrected target run still exhausts 4 GB and is marginally
slower and larger than the identical V291 baseline.

## Safety Boundary

- No wrapper analysis, verification, or verdict behavior was added.
- No Deagle production code remains changed.
- No accepted V291 behavior was replaced.
- Prior90 and Exact725 were intentionally not run because both candidates
  failed before the release gates.
- No candidate source code is authorized for commit or push.

## Timing

- Start: `2026-07-29T19:59:21Z`
  (`2026-07-30 03:59:21 +0800`).
- End: `2026-07-29T20:10:12Z`
  (`2026-07-30 04:10:12 +0800`).
- Duration: 10.85 minutes.

The interval starts after V292 ended at `2026-07-29T19:55:13Z`.
