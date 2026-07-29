# Results: V294 Native Modular Loop Summary

## Decision Summary

V294 passes the native release gates. It changes exactly three Exact725 tasks
from timeout to correct true, loses no previously correct result, introduces no
new wrong result, and reduces paired aggregate resource use.

## Target Gate

Artifact:
`/home/lapulatos/deagle-experiments/v294-modular-loop-target-r4`.

| Target | Result | Wall time | Witness bytes |
| --- | --- | ---: | ---: |
| `mult-comm.wvr` | true | 0.06 s | 3,448 |
| `mult-dist.wvr` | true | 0.04 s | 3,448 |
| `mult-flipped-dist.wvr` | true | 0.04 s | 3,464 |
| `array-eq-symm.wvr` | timeout, transform rejected | 8.00 s | none |

The three accepted targets log native commuting sequentialization, exact
unsigned modular loop summarization, modular-ring normalization, and routing
of the resulting sequential formula to Deagle's ordinary SAT backend.

## Mutation Gate

Artifact:
`/home/lapulatos/deagle-experiments/v294-modular-loop-mutations-r2`.

Eight premise-breaking controls cover an extra write, an
induction-dependent delta, interfering workers, an internal branch, a signed
accumulator, a non-unit step, a volatile delta, and a flipped property. The
first seven reject at the commuting or transactional summary boundary. The
flipped property is transformed but Deagle still reports verification failure,
showing that the transform does not directly manufacture a true verdict.

## Prior90

Valid artifact:
`/home/lapulatos/deagle-experiments/v294-modular-loop-prior90-r2`.

- Correct: 90/90.
- Incorrect: 0.
- Unknown: 0.
- The benchmark uses `benchexec.tools.deagle_benchexec`.

The earlier `v294-modular-loop-prior90-r1` launch used the wrong generic tool
module, ignored the intended option portfolio, and was stopped. It is retained
only as an invalid diagnostic artifact.

## Paired Exact725

Both runs used the same restarted server, 8 workers, 1 core and 4 GB per task,
and a 60-second limit.

- Control:
  `/home/lapulatos/deagle-experiments/v294-paired-v291-exact725-r1`.
- Candidate:
  `/home/lapulatos/deagle-experiments/v294-paired-candidate-exact725-r1`.

| Metric | V291 control | V294 candidate | Change |
| --- | ---: | ---: | ---: |
| Official correct | 693 | 696 | +3 |
| Adjudicated correct | 705 | 708 | +3 |
| Incorrect under official labels | 3 | 3 | 0 |
| Unknown | 29 | 26 | -3 |
| Aggregate CPU | 1,390.094 s | 1,206.378 s | -13.216% |
| Aggregate wall | 1,429.296 s | 1,247.401 s | -12.726% |
| Summed per-task peak memory | 28,998,311,936 B | 28,088,336,384 B | -3.138% |

The only three status changes are:

- `weaver/mult-comm.wvr.yml`: timeout to true.
- `weaver/mult-dist.wvr.yml`: timeout to true.
- `weaver/mult-flipped-dist.wvr.yml`: timeout to true.

There are zero old-correct losses and zero new wrong results.

## Wrapper, Binary, and Source Gates

- `svcomp_stuff/deagle` SHA-256 remains
  `adbec275658ee2a7a8bad6ac793b4aa52a029f868ef75ad2a3f40d902ed191ad`.
- `svcomp_stuff/deagle.py` SHA-256 remains
  `da7af28e973215a744437038633e23161047ba8ccfa66830fa28e3f759daa609`.
- The candidate `deagle_exe` SHA-256 is
  `3fd753deed24aa83488cc53227ee1069f0fe9ce06af5ae0c41de323385c09e74`.
- The build-tree and evaluated binary hashes are identical.
- Production-source search finds no target name, benchmark path, expected
  label, version string, or source-line special case.
- `git diff --check` passes.

## Witness Gate

The three native correctness witnesses are preserved in `witnesses/`.
Each passes XML parsing and official WitnessLint 2.1.3-dev's
program-independent GraphML format check with exit 0. Their SHA-256 values are:

- `mult-comm`: `d78593293e4369f7dd82da9e17da03a6d159e6315535bafd97a1904e9a2187cc`.
- `mult-dist`: `7c4ae52e11cc75c11322010ba97f472af80e3d28c5935000c2c1fbd2adad51d2`.
- `mult-flipped-dist`: `b3650412fcf800139e3cf29f8ded3c461455ab3190d8b011bdc39c060ea6e75c`.

This is a format gate. The witnesses encode the native proof result but were
not independently re-proved by a separate semantic witness validator.
