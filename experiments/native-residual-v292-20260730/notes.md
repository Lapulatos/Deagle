# V292 Notes

## Starting Point

- Base: accepted remote V291 at
  `a838944c8efcca05f27c7c5c25d5b95d844e52c5`.
- Accepted adjudicated frontier: 705.
- V291 changed only `libvsync/rec_ticketlock.yml` against its paired V290
  baseline.
- Remaining natural controls from V291:
  `rec_mcslock`, `mcslock`, `bounded_mpmc_check_full`, `hclhlock`, `hmcslock`,
  `rwlock`, `semaphore`, and `ttaslock`.

## Evidence Log

### Attempt 1: type-general unreserved single pure-read loop

- Generalized the existing one-model/one-loop pointer exception to a scalar
  pure-read loop while retaining the global exactly-one-unreserved-loop gate.
- Artifact:
  `/home/lapulatos/deagle-experiments/v292-unreserved-single-read-r1`.
- `bounded_mpmc_check_full`, `hclhlock`, `semaphore`, and `ttaslock` passed
  native admission but did not finish within 45 seconds.
- Accepted `ticketlock` and `cnalock` remained successful.
- Multi-loop `rec_mcslock` and `mcslock` remained inconclusive at the global
  gate, so the historical broad-collapse failure mode was not reopened.
- Decision: reject for zero coverage gain. The production source was restored
  exactly to V291 before selecting the next attempt.

### Attempt 2: bounded shared-progress loops

- Phase artifact:
  `/home/lapulatos/deagle-experiments/v292-timeout-phase-r1`.
- `safestack_relacy` and `workstealqueue_mutex-2` spend the full budget in
  symbolic loop unwinding rather than SAT solving. At 35 seconds their main
  loops had reached approximately 242 and 2819 iterations.
- Explicit-bound feasibility artifact:
  `/home/lapulatos/deagle-experiments/v292-safestack-bound-feasibility-r1`.
- Bound 2 correctly fails an unwinding assertion. Bound 3 reaches SC
  construction but exhausts the default 8-bit addressed-object namespace.
- Object-width feasibility artifact:
  `/home/lapulatos/deagle-experiments/v292-safestack-bound-objectbits-r1`.
- Bounds of 3 with 9, 10, and 11 object bits all fail to finish within
  90 seconds.
- Decision: do not implement the native completeness admission. Even after
  supplying its anticipated conclusion, the target remains outside the
  release time limit, so it cannot add coverage.
