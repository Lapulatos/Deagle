# Results: V291 Native Guided Short-Schedule Search

## Target Diagnostic

- Artifact:
  `/home/lapulatos/deagle-experiments/v291-rec-ticketlock-prefix-r15`
- Unified binary SHA-256:
  `f251a2748acb7c96dee3b1cbc0206aebfb56bb3fd72d2050b06280e6e1c8408f`
- Native admission:
  - existing scalar await loop: accepted;
  - outer retry loop: accepted with `stuttering_retry=1`,
    `stutter_reason=none`.
- Native collapse: `applied=1`, two loops in two functions.
- Result: `VERIFICATION SUCCESSFUL`, exit code 0.
- CPU: 0.27 s.
- Wall: 0.29 s.
- Peak RSS: 38,788 KiB.
- Witness: 3,457 bytes.

The target result is accepted only together with the gates below.

## Natural Controls

Artifact:
`/home/lapulatos/deagle-experiments/v291-libvsync-controls-r1`

- Preserved successful: `ticketlock`, `cnalock`.
- Preserved inconclusive: `rec_mcslock`, `mcslock`,
  `bounded_mpmc_check_full`, `hclhlock`, `hmcslock`, `rwlock`,
  `semaphore`, and `ttaslock`.
- No previously inconclusive control was newly admitted.

## Structural Mutations

Artifact:
`/home/lapulatos/deagle-experiments/v291-prefix-mutations-r1`

- Prefix selects a reserved identifier: outer retry rejected with
  `inline_assert`; result remains inconclusive.
- Failure retry writes shared state: outer retry rejected with
  `inline_failure_shared_write`; result remains inconclusive.
- Bypass branch reaches the error location: admission may ignore that
  non-loop branch, but the final native Deagle solve reports
  `VERIFICATION FAILED` (exit code 10) and emits a violation witness.

These checks show that reverse reachability only guides loop admission; it
does not remove bypass properties from the final model.

## Official Wrapper Smoke

Artifact:
`/home/lapulatos/deagle-experiments/v291-wrapper-smoke-r1`

- Wrapper source is unchanged from V290.
- The wrapper adds only native arguments and calls the same unified
  `deagle_exe`.
- Result: `SUCCESSFUL`, exit code 0.
- CPU: 5.76 s.
- Wall: 5.77 s.
- Peak RSS: 80,052 KiB.
- Witness: 3,457 bytes.

## Correctness Witness Gate

- SHA-256:
  `3563906d145cda0339d9e5eea1c1cc014108b243312db41ab333fe303d28a0f0`.
- WitnessLint 2.1.3-dev commit
  `5297b5889b936f5eff5a1f2b594230df9a28d1c5`: exit 0.
- `xmllint --noout`: exit 0.

## Prior90

Valid artifact:
`/home/lapulatos/deagle-experiments/v291-prior90-r3`

- Correct: 90/90.
- Incorrect: 0.
- Unknown: 0.

The two earlier runs that lost all portfolio options through the stock
BenchExec tool-info module are invalid and excluded.

## Exact725 Paired Release Gate

V291 artifact:
`/home/lapulatos/deagle-experiments/v291-exact725-r1`

Paired V290 artifact:
`/home/lapulatos/deagle-experiments/v290-paired-exact725-r1`

Both runs use the same wrapper, task set, property, option list, 8 workers,
60-second CPU limit, 4 GB memory limit, and experiment-local option-forwarding
tool-info module.

| Metric | V290 paired | V291 | Change |
| --- | ---: | ---: | ---: |
| Official correct | 692 | 693 | +1 |
| Incorrect | 3 | 3 | 0 |
| Unknown | 30 | 29 | -1 |
| CPU | 1,371.992259 s | 1,383.883154 s | +0.867% |
| Summed wall | 1,410.289371 s | 1,421.667930 s | +0.807% |
| Summed memory | 29,277,474,816 B | 28,949,061,632 B | -1.122% |

The two XML files contain the same 725 task names. The only status/category
change is `libvsync/rec_ticketlock.yml`, from `unknown/unknown` to
`true/correct`. V290-correct losses are zero and new genuine wrong results
are zero.

The historical V290 dashboard was run with 48 workers and is retained as
historical evidence, not used for the N8 performance delta.

## Release Decision

V291 passes target, natural-control, mutation, wrapper-boundary, Prior90,
Exact725, no-loss, no-new-wrong, resource, build, and witness-format gates.
It is eligible for an accepted native commit after final diff review.
