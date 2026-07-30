# V299 Results

## Target

- Native transform marker: `NATIVE_SYMMETRIC_ARRAY_SCAN applied=1`.
- Actual byte-identical wrapper result: `true`.
- CPU: 0.17 s.
- Wall: 0.23 s.
- Peak memory: 13.504 MB.
- Correctness witness: 3,450 bytes, WitnessLint 2.1.3-dev exit 0.
- Evidence:
  `/data3/sujie/experiments/v299-symmetric-scan-wrapper-target-r3`.

## Mutation Gate

All 12 non-equivalent structural mutations reject the native transform.
Evidence:
`/data3/sujie/experiments/v299-symmetric-scan-mutations-r3/results/summary.tsv`.

## Prior90 Paired Gate

The current server benchmark tree differs from the accepted archival
environment, so only same-machine paired deltas are used for regression
claims.

| Metric | V298 control | V299 final | Delta |
| --- | ---: | ---: | ---: |
| Task statuses changed | — | 0 / 90 | 0 |
| CPU sum | 477.777 s | 478.895 s | +0.23% |
| Wall sum | 479.983 s | 481.248 s | +0.26% |
| Summed peak memory | 38.544 GB | 38.592 GB | +0.12% |

## Exact725 Paired Gate

| Metric | V298 control | V299 final | Delta |
| --- | ---: | ---: | ---: |
| Official correct in current tree | 225 | 226 | +1 |
| Task statuses changed | — | 1 / 725 | target only |
| Old-correct losses | — | 0 | pass |
| New wrong results | — | 0 | pass |
| CPU sum | 1397.609 s | 1404.257 s | +0.48% |
| Wall sum | 1419.671 s | 1426.350 s | +0.47% |
| Summed peak memory | 100.921 GB | 101.155 GB | +0.23% |

The single change is `array-eq-symm.wvr.yml`, from wrong
`false(unreach-call)` to correct `true`. The other 724 statuses are identical.
The current tree's absolute count is not substituted for the accepted V298
archival total because the former benchmark tree is unavailable.

## Reproducible Build

- Evaluated binary:
  `b7d0ee363be9b9c1cecf30016ad53c09dd85b7c8c8952c9a56d34a6a73e33afd`.
- Clean build 1:
  `ea2168ae9163f05b10b745a7e0c132d5e9b8a21a99fbbfed73991d01987fa139`.
- Clean build 2:
  `ea2168ae9163f05b10b745a7e0c132d5e9b8a21a99fbbfed73991d01987fa139`.
- Clean-build byte comparison: exit 0.
