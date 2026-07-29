# Results: V293 Affine and RF Selector Feasibility

## Candidate 1

The affine nontermination proof was rejected on soundness grounds before
implementation. Signed counter increments may wrap, so the proposed invariant
does not prove the worker nonterminating in Deagle's bit-vector semantics.

## Candidate 2

The high-fan-in RF selector built successfully in one native `deagle_exe`.
After correcting an optional-expression initialization bug, the target still
ran out of memory under the same 4 GB limit as accepted V291.

| Metric | V291 baseline | V293 selector | Change |
| --- | ---: | ---: | ---: |
| CPU time | 27.44 s | 28.39 s | +3.46% |
| Wall time | 27.44 s | 28.40 s | +3.50% |
| Peak RSS | 3,817,052 KiB | 3,841,352 KiB | +0.64% |
| SSA steps | 1,054,851 | 1,054,851 | 0 |
| Result | OOM | OOM | no gain |

The target-feasibility gate failed. No correctness, coverage, or performance
claim is made beyond this paired target run.

## Repository State

- Base: `a2d5303ae1d02e2a5f1a4289bb74cd7205345cd5`.
- Production source diff: empty.
- Wrapper diff: empty.
- Candidate source publication: prohibited.
