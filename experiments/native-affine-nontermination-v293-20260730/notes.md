# V293 Notes

## Base

- Remote base:
  `a2d5303ae1d02e2a5f1a4289bb74cd7205345cd5`.
- V292 contains documentation only; production semantics equal accepted V291.

## Affine Nontermination Soundness

The target increments two signed counters without a proven finite upper
bound. Bit-vector wraparound can invalidate the apparent nonnegative
invariant, so the candidate was rejected before source implementation.

## High-Fan-In RF Selector

The second candidate replaced the fresh Boolean for each read/write RF pair
with a generic unsigned selector for reads having at least 64 candidate
writes. No benchmark name, path, source line, expected label, or wrapper logic
was used.

Target:
`pthread-complex/elimination_backoff_stack.i`

Artifacts:

- `/home/lapulatos/deagle-experiments/v293-rf-selector-elimination-r1/baseline`
- `/home/lapulatos/deagle-experiments/v293-rf-selector-elimination-r1/candidate`
- `/home/lapulatos/deagle-experiments/v293-rf-selector-elimination-r1/fixed`

The first candidate run stopped on an invariant check because default
construction of an optional `exprt` produced an empty expression rather than
the explicit `nil_exprt()` sentinel. That defect was fixed and diagnostic
instrumentation was removed before the final comparison.

The corrected candidate created selectors for 7,680 reads covering 854,100
RF choices. Both baseline and candidate retained 1,054,851 SSA steps.

| Run | Outcome | CPU s | Wall s | Peak RSS KiB |
| --- | --- | ---: | ---: | ---: |
| V291 baseline | OOM | 27.44 | 27.44 | 3,817,052 |
| V293 corrected | OOM | 28.39 | 28.40 | 3,841,352 |

The generic bit-vector backend expands every selector equality and repeats it
through RF, FR, and cutting constraints. The selector therefore did not
reduce the propositional working set and slightly increased resource use.

## Publication Boundary

- Production source diff: empty.
- Wrapper diff: empty.
- Target coverage gain: zero.
- Prior90 and Exact725 were not run because target feasibility failed.
- Candidate source is not committed.
