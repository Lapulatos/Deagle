# V300 Results

## Final Candidate

- Candidate binary SHA-256:
  `549ce2ac77fe8d726d40fc7efb3b64027d017df8b16aa673e5a18d1ecc06a03f`.
- Wrapper hashes are unchanged from V299:
  `adbec275...` (`deagle`) and `da7af28e...` (`deagle.py`).

## Target

With the byte-identical wrapper, the three comparator scan-law tasks complete
as correct true in `0.25 s`, `0.23 s`, and `0.21 s`. Deagle emits native
correctness witnesses for all three.

## Negative Gate

- All 14 structural mutations reject both native comparator rules.
- The first candidate was rejected because Prior90 changed `fibonacci.wvr` and
  `test-easy1.wvr` from false to true.
- After restricting unresolved `abort` and assume-wrapper admission to the
  fully audited comparator-scan path, both controls are false again.

## Prior90 Paired Gate

| Metric | V299 control | V300 final | Delta |
| --- | ---: | ---: | ---: |
| Correct | 57 | 60 | +3 |
| Wrong | 13 | 13 | 0 |
| Task statuses changed | — | 3 / 90 | targets only |
| Old-correct losses | — | 0 | pass |
| New wrong results | — | 0 | pass |
| CPU sum | 475.514 s | 290.153 s | -38.98% |
| Wall sum | 477.286 s | 291.674 s | -38.89% |
| Summed peak memory | 38.572 GB | 37.636 GB | -2.43% |

The only changes are the three target tasks, each from timeout to correct true.

## Exact725 Paired Gate

| Metric | V299 | V300 final | Delta |
| --- | ---: | ---: | ---: |
| Correct in current tree | 226 | 229 | +3 |
| Wrong | 374 | 374 | 0 |
| Task statuses changed | — | 3 / 725 | targets only |
| Old-correct losses | — | 0 | pass |
| New wrong results | — | 0 | pass |
| CPU sum | 1404.257 s | 1184.184 s | -15.67% |
| Wall sum | 1426.350 s | 1203.763 s | -15.61% |
| Summed peak memory | 101.155 GB | 100.949 GB | -0.20% |

The only changes are the three target tasks, each from timeout to correct true.
Under the accepted adjudicated lineage, coverage rises from 714 to 717.

## Witness Gate

| Rule | Wrapper wall | Witness bytes | WitnessLint |
| --- | ---: | ---: | ---: |
| Equality substitution | 0.21 s | 3,474 | exit 0 |
| Antisymmetry | 0.21 s | 3,472 | exit 0 |
| Strict transitivity | 0.23 s | 3,474 | exit 0 |

WitnessLint is a format gate. Its parser does not fully parse these Weaver C
inputs, so no independent semantic-validation claim is made.

## Reproducible Build

Two independent object-free builds from the same source tree produced
byte-identical executables:

- Build A SHA-256:
  `8b96d184c37d85105ad30619b412ea21704468c96f7f40ded0c4190d236f90fe`.
- Build B SHA-256:
  `8b96d184c37d85105ad30619b412ea21704468c96f7f40ded0c4190d236f90fe`.

The clean-build hash differs from the incrementally evaluated binary because
the latter predates a complete object-free rebuild. The A/B equality proves
that the committed source rebuilds deterministically; the paired target,
Prior90, Exact725, mutation, and witness gates above remain tied to the
explicitly recorded evaluated candidate hash.
