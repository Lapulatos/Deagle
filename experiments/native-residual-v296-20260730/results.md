# V296 Results

## Target and Semantic Gates

Evaluated binary:

`/home/lapulatos/deagle-v296-bounded-alternating-r1-20260730/src/cbmc/deagle_exe`

SHA-256:

`2ed1e3c11cf12e0ba97872011fd8fe9c57106d1c86d8d403ffbffc219e98cef3`

Target artifact:

`/home/lapulatos/deagle-experiments/v296-bounded-alternating-target-r3`

The previously timing-out target completes as correct true:

- wall: 0.14 s;
- CPU: 0.08 s;
- peak RSS: 18,176 KiB;
- native marker:
  `NATIVE_BOUNDED_ALTERNATING_CANCELLATION applied=1 workers=2`;
- backend result: `VERIFICATION SUCCESSFUL`.

The property-flipped control is also admitted and produces
`VERIFICATION FAILED`. Nine premise-breaking controls are rejected, and seven
natural sibling tasks remain rejected by the transform.

## Prior90

Artifact:

`/home/lapulatos/deagle-experiments/v296-bounded-alternating-prior90-r1`

BenchExec 3.25 result:

- correct: 90;
- incorrect: 0;
- unknown: 0.

## Paired Exact725

V295 control:

`/home/lapulatos/deagle-experiments/v295-paired-candidate-exact725-r1`

V296 candidate:

`/home/lapulatos/deagle-experiments/v296-paired-candidate-exact725-r1`

Both use 725 tasks, eight workers, one core and 4 GB per task, and a 60-second
task limit.

| Metric | V295 | V296 | Change |
| --- | ---: | ---: | ---: |
| Official correct | 697 | 698 | +1 |
| Adjudicated correct | 709 | 710 | +1 |
| Unfinished | 25 | 24 | -1 |
| Aggregate CPU | 1,146.603572 s | 1,093.065036 s | -4.669% |
| Aggregate wall | 1,187.298755 s | 1,134.919317 s | -4.412% |
| Summed task memory | 27,623,301,120 B | 27,417,141,248 B | -0.746% |

The only paired status change is `parallel-misc-2` from timeout to correct
true. There are zero V295-correct losses and zero new wrong results.

## Wrapper, Build, and Witness

The wrapper hashes remain byte-identical:

- `deagle`:
  `adbec275658ee2a7a8bad6ac793b4aa52a029f868ef75ad2a3f40d902ed191ad`;
- `deagle.py`:
  `da7af28e973215a744437038633e23161047ba8ccfa66830fa28e3f759daa609`.

The evaluated package and build-tree executable hashes are identical. Native
Deagle generated the 3,460-byte correctness witness. WitnessLint 2.1.3-dev
exits 0 as a format gate; its source parser reports Type-Match Unknown, so no
stronger semantic-validator claim is made.
