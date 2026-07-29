# V297 Results

## Native Target and Semantic Gates

Evaluated binary:

`/home/lapulatos/deagle-v297-phase-boundary-r1-20260730/src/cbmc/deagle_exe`

SHA-256:

`ea13e643d32aa9a288fb056ed7d871e58dbbdc4f7dd81b36b3c6dcbc8640af41`

Target artifact:

`/home/lapulatos/deagle-experiments/v297-phase-boundary-target-final-r4`

| Task | Workers | CPU | Wall | Peak RSS | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| `parallel-misc-3` | 2 | 0.04 s | 0.05 s | 18,048 KiB | true |
| `parallel-misc-3-extended` | 3 | 0.03 s | 0.05 s | 18,176 KiB | true |

Fourteen premise-breaking mutations reject the transform. The property-flipped
control remains admitted and the ordinary backend reports
`VERIFICATION FAILED`. Six natural controls reach the new transform and reject;
two others are handled first by their already accepted native transforms.

## Prior90

Artifact:

`/home/lapulatos/deagle-experiments/v297-phase-boundary-prior90-final-r3`

Final result:

`results/prior90.server.2026-07-30_06-08-05.results.v297-native-phase-boundary-release-prior90.prior90.xml.bz2`

- correct: 90;
- incorrect: 0;
- unknown: 0.

## Paired Exact725

V296 control:

`/home/lapulatos/deagle-experiments/v296-paired-candidate-exact725-r1`

V297 candidate:

`/home/lapulatos/deagle-experiments/v297-phase-boundary-exact725-final-r3`

Both use the same 725 tasks, eight parallel runs, one core and 4 GB per task,
and a 60-second task limit.

| Metric | V296 | V297 | Change |
| --- | ---: | ---: | ---: |
| Official correct | 698 | 700 | +2 |
| Adjudicated correct | 710 | 712 | +2 |
| Raw wrong | 3 | 3 | 0 |
| Unfinished | 24 | 22 | -2 |
| Aggregate CPU | 1,093.065036 s | 968.657205 s | -11.382% |
| Aggregate wall | 1,134.919317 s | 1,014.959859 s | -10.570% |
| Summed task memory | 27,417,141,248 B | 26,867,920,896 B | -2.003% |
| Peak task memory | 3,999,997,952 B | 3,999,997,952 B | 0 |

The only paired status changes are `parallel-misc-3` and
`parallel-misc-3-extended`, both from timeout to correct true. There are zero
V296-correct losses and zero new wrong results.

The checked-in XML files and `exact-comparison.json` preserve the complete
comparison evidence. The two earlier candidate XML files are retained with
`pre-final-r1-` and `pre-final-r2-` prefixes; release claims use only the
`release-exact725` XML.

## Wrapper, Witness, and Reproducibility

The wrapper files are byte-identical to V296:

- `deagle`:
  `adbec275658ee2a7a8bad6ac793b4aa52a029f868ef75ad2a3f40d902ed191ad`;
- `deagle.py`:
  `da7af28e973215a744437038633e23161047ba8ccfa66830fa28e3f759daa609`.

The build-tree executable and the evaluated package are byte-identical. A
second independent incremental build also produces the same executable
SHA-256.

Deagle generated correctness witnesses of 3,460 and 3,478 bytes. WitnessLint
2.1.3-dev exits 0 for both as a format gate. Its source parser reports
`sucessfully_parsed: False` and Type-Match Unknown, so no stronger semantic
validator claim is made.

## Version Time

- start: 2026-07-30 05:38:24 +08:00;
- witness gate: 2026-07-30 06:11:29 +08:00;
- elapsed: 33.08 minutes.

This interval starts after V296's final witness gate and preserves strictly
increasing version chronology.
