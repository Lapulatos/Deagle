# V295 Results

## Native Target Gate

The evaluated binary is:

`/home/lapulatos/deagle-v295-local-clamp-r1-20260730/src/cbmc/deagle_exe`

with SHA-256:

`1cff154b13235a25428adfb792d3608cb6cc7616989d917038d53f3249eb2674`.

The target artifact is:

`/home/lapulatos/deagle-experiments/v295-local-clamp-target-r1`.

The previously timing-out target completes as correct true:

- wall: 0.06 s;
- CPU: 0.05 s;
- peak RSS: 18,432 KiB;
- native marker:
  `NATIVE_LOCAL_LOOP_ACCEL applied=1 loops=2 functions=2`;
- backend result: `VERIFICATION SUCCESSFUL`.

## Mutation and Natural-Control Gates

Six generated semantic controls exercise the admission boundary:

- arbitrary initial value below the bound: accepted, correct true;
- arbitrary initial value above the bound: accepted, correct true;
- property flip: accepted, `VERIFICATION FAILED`;
- step size changed to two: transform rejected;
- extra local semantic instruction: transform rejected;
- shared write in the loop: transform rejected.

Each generated case finishes in 0.04-0.06 s. The eight other residual Weaver
timeouts all report:

`NATIVE_LOCAL_LOOP_ACCEL applied=0 loops=0 functions=0`

under a five-second natural-control run. Thus V295 does not accidentally admit
the array, recurrence, or indirect-index families.

## Prior90

Artifact:

`/home/lapulatos/deagle-experiments/v295-local-clamp-prior90-r1`

BenchExec 3.25 ran 90 tasks with eight workers, one core and 4 GB per task, and
a 60-second task limit. Result:

- correct: 90;
- incorrect: 0;
- unknown: 0.

## Paired Exact725

V294 control:

`/home/lapulatos/deagle-experiments/v294-paired-candidate-exact725-r1`

V295 candidate:

`/home/lapulatos/deagle-experiments/v295-paired-candidate-exact725-r1`

Both use the same 725-task set, eight workers, one core and 4 GB per task, and a
60-second task limit.

| Metric | V294 | V295 | Change |
| --- | ---: | ---: | ---: |
| Official correct | 696 | 697 | +1 |
| Adjudicated correct | 708 | 709 | +1 |
| Unfinished | 26 | 25 | -1 |
| Aggregate CPU | 1,206.378018 s | 1,146.603572 s | -4.955% |
| Aggregate wall | 1,247.400825 s | 1,187.298755 s | -4.818% |
| Summed task memory | 28,088,336,384 B | 27,623,301,120 B | -1.656% |

The only paired status change is `test-easy11` from timeout to correct true.
There are zero V294-correct losses and zero new wrong results.

## Wrapper and Witness Boundary

The packaged wrapper hashes are unchanged from V294:

- `deagle`:
  `adbec275658ee2a7a8bad6ac793b4aa52a029f868ef75ad2a3f40d902ed191ad`;
- `deagle.py`:
  `da7af28e973215a744437038633e23161047ba8ccfa66830fa28e3f759daa609`.

The evaluated package and build-tree `deagle_exe` hashes are identical.
Deagle generated the 3,452-byte correctness witness. WitnessLint 2.1.3-dev
exits 0 as a GraphML format gate; its program parser reports Type-Match
Unknown, so no stronger semantic-validator claim is made.
