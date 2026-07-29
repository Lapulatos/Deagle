# V297 Notes

## Base

- Accepted V296:
  `76252282d2949d092376e7d20f9e723bbac7627e`.
- V296 Exact725 has 698 official / 710 adjudicated correct and 24 unfinished
  tasks.

## Candidate Principle

The next residual family performs equal opposite atomic updates under a private
phase, exactly as in V296, but has no finite numeric bound. Instead, a private
loop flag may be cleared nondeterministically only after the phase has returned
to its initial boundary.

For partial-correctness reachability, every terminating execution therefore
contains a whole number of identity transition pairs. Nonterminating
executions never pass the joins and cannot reach the post-join property. A
sound native summary may replace only the terminating transition word, provided
Deagle derives private ownership, initial phase/flag values, phase-boundary
exit control, opposite atomic updates, full joins, and absence of external
observation.

## Normalized GOTO Evidence

The V296 binary's `--show-goto-functions` output is stored remotely at:

`/home/lapulatos/deagle-experiments/v297-phase-boundary-goto-r1`

Each worker has 11 semantic instructions: loop-flag exit, phase branch,
equal-opposite atomic updates, phase negation, a second phase guard,
nondeterministic Boolean materialization, conditional loop-flag clearing, and
one unconditional backedge. The clearing assignment is reachable only when
the phase has returned to its initial true boundary.

## Native Implementation

The candidate adds `phase_boundary_cancellation_transform` to the native JCES
portfolio. Admission derives:

- two or more fully joined workers and a valid main lifecycle;
- one distinct private Boolean phase and loop flag per worker;
- straight-line dominating initialization of every phase and flag to one;
- one shared atomic signed scalar, with no explicit pre-spawn assignment;
- exactly one zero assignment to that scalar in `__CPROVER_initialize`;
- equal-opposite constant updates and exact phase-boundary exit control;
- no foreign or cross-worker access to private state;
- no post-spawn private observation or shared-object write;
- a summed outstanding positive weight within the signed scalar range.

The last obligation covers transient states in which every worker has executed
its positive half-step but not its cancelling half-step.

## Target and Semantic Gates

Evaluated binary:

`/home/lapulatos/deagle-v297-phase-boundary-r1-20260730/src/cbmc/deagle_exe`

Target artifact:

`/home/lapulatos/deagle-experiments/v297-phase-boundary-target-final-r4`

- `parallel-misc-3`: applied with two workers; successful in 0.05 s wall,
  0.04 s user CPU, 18,048 KiB peak RSS.
- `parallel-misc-3-extended`: applied with three workers; successful in
  0.05 s wall, 0.03 s user CPU, 18,176 KiB peak RSS.
- Both emit native correctness witnesses of 3,460 and 3,478 bytes.

Mutation artifact:

`/home/lapulatos/deagle-experiments/v297-phase-boundary-mutations-final-r3`

The transform rejects wrong exit phase, asymmetric updates, zero phase or flag
initialization, shared private state, a non-atomic object, an extra shared
step, early termination, an explicit object prefix value, and transient
overflow. A property-flipped control remains admitted and the ordinary backend
reports `VERIFICATION FAILED`.

Natural controls:

`/home/lapulatos/deagle-experiments/v297-phase-boundary-natural-controls-r2`

Six controls reach this transform and report `applied=0`. `parallel-misc-1`
and `parallel-misc-2` are handled first by their already accepted native
transforms, so the new transform cannot affect them in the production chain.

## Prior90

Artifact:

`/home/lapulatos/deagle-experiments/v297-phase-boundary-prior90-final-r3`

The completed result is:

`results/prior90.server.2026-07-30_06-08-05.results.v297-native-phase-boundary-release-prior90.prior90.xml.bz2`

BenchExec reports 90/90 correct: 80 true, 10 false, zero incorrect, and zero
unknown. Two earlier launch attempts stopped before any task ran because the
tool directory and then the delegated cgroup scope were missing; their logs
remain in the artifact directory and are not treated as results.

## Exact725 and Release Gates

The paired comparison is preserved in `exact-comparison.json`. V297 reaches
700 official / 712 adjudicated correct and 22 unfinished tasks. The only
status changes from V296 are the two intended targets, both timeout to correct
true. There are zero old-correct losses and zero new wrong results.

Aggregate CPU, wall, and summed memory change by -11.382%, -10.570%, and
-2.003%. Peak per-task memory is unchanged at 3,999,997,952 bytes.

The wrapper hashes remain byte-identical to V296. The evaluated package,
primary build, and second build all share executable SHA-256
`ea13e643d32aa9a288fb056ed7d871e58dbbdc4f7dd81b36b3c6dcbc8640af41`.

Both native correctness witnesses pass WitnessLint 2.1.3-dev with exit 0 as a
format gate. The linter reports that it could not parse the source and labels
the type match Unknown, so this is not presented as semantic witness
validation.
