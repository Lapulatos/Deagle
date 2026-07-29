# Conclusion: V285 Native Residual Portfolio

## Decision

Accept the native ticket retry-stuttering extension. The categorized native
source commit `7a366e465585691b98aa53b277c1980209d86d5e` is pushed to
`origin/deagle-dev`.

The implementation changes one native C++ analysis and does not add wrapper
verdict logic. Deagle derives caller-path reservation dominance and, for a
non-read-only marked loop, transitively inlines its callees and checks every
path. A retrying path must perform no shared write, must not observe a
loop-carried local before it is overwritten, and must coexist with an exit
path. Weak compare-exchange is rejected.

## Correctness

The final exact725 artifact is:

`/data3/sujie/experiments/v285-ticket-native-final-exact725-r1`

- official correct: 700;
- adjudicated correct: 701;
- incorrect: one unchanged task-82 label dispute;
- unknown/error: 24;
- V284-correct losses: zero;
- new wrong results: zero;
- only V284 status change: `libvsync/ticketlock.yml`, unknown to correct true.

The final prior90 artifact is:

`/data3/sujie/experiments/v285-ticket-native-final-prior90-r1`

It passes 90/90 with 80 correct true, 10 correct false, zero unknown, and zero
incorrect.

## Resource Gate

Against the contemporaneous V284 control
`/data3/sujie/experiments/v285-ticket-native-v284-control-r2`:

- CPU: `864.813168672 s -> 861.356850191 s` (`-0.400%`);
- summed wall: `914.349700423 s -> 906.056512353 s` (`-0.907%`);
- summed memory: `25,404,715,008 B -> 25,645,174,784 B` (`+0.947%`);
- 48-way batch wall: `82.568952 s -> 83.543340 s` (`+1.180%`).

The small wall/memory differences are within run variance and there is no
performance cliff.

## Witness and Build

- ticketlock correctness witness: 3,269 bytes;
- arraylock correctness witness: 3,267 bytes;
- WitnessLint 2.1.3-dev: exit 0 for both;
- final build was produced after `make clean`;
- built and deployed binary SHA-256:
  `a01ca0735912b4a4223455af7c7c9a30c7ec2f1c54d81a9232d86c8cdb75b5da`;
- `git diff --check`: pass.

## Negative Gates

- Eight premise-breaking mutations return inconclusive.
- Removing the inner reservation and removing the inner wait produce native
  failure results rather than an unsound success.
- The success-stride mutation remains correct under partial-correctness
  semantics and is retained as a positive robustness control.
- Ten historical libvsync residual controls remain inconclusive.
- `rec_mcslock`, the mandatory V278 regression sentinel, is inconclusive.
- `arraylock` remains correct.
