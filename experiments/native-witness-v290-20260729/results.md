# Results: V290 Original-GOTO Guided Replay

## Implementation

- One unified native `deagle_exe` performs candidate analysis, original-model
  replay, verdict, and GraphML generation.
- The transformed candidate contributes only two source-level nondeterministic
  choices and the expected source assertion location.
- Deagle processes and solves a saved untransformed GOTO model independently.
- Replay fails closed on a missing guide, unmatched choice, safe/unknown
  original solve, or property-location mismatch.
- The Python wrapper remains unchanged and supplies only arguments and mounts.
- Production code contains no benchmark name, task number, YAML label,
  expected-result label, or target source-line condition.

## Target Results

Final smoke artifact:
`/data3/sujie/experiments/v290-original-goto-replay-final-smoke-r1`

| Task | Result | Choices | Original trace steps | Witness bytes |
| --- | --- | ---: | ---: | ---: |
| 91 arrayloop2 | `false(unreach-call)` | 2/2 | 17,814 | 980,803 |
| 93 evilcollapse | `false(unreach-call)` | 2/2 | 17,868 | 992,981 |

Both results terminate with exit code 10 and `VERIFICATION FAILED`. The
reported failing source function and line match between the transformed guide
and the original-model replay.

Final target resource artifact:
`/data3/sujie/experiments/v290-original-goto-replay-cost-r2`

| Task | CPU s | Wall s | Peak memory bytes |
| --- | ---: | ---: | ---: |
| 91 arrayloop2 | 14.3892 | 14.5255 | 415,399,936 |
| 93 evilcollapse | 14.3952 | 14.6889 | 416,382,976 |

Scoping and destroying the candidate verifier before original replay reduced
target peak memory by about 19% relative to the first working replay.

## Witness Checks

- Final local copies:
  `/Users/sujie/Downloads/deagle-v290-witnesses-20260730/`
- Both GraphML files pass `xmllint --noout`.
- UGemCutter reports no bad edge but matches only 7 of 3,968 edges and returns
  `TRUE`.
- The same Ultimate backend also returns `TRUE` on the original program without
  a witness, so it cannot establish or refute this execution for this program.
- The semantic release gate is Deagle's separate second SAT solve over the
  untransformed original GOTO model. A reduced-model verdict alone is never
  published.

## Mutation Gate

Artifact:
`/data3/sujie/experiments/v290-original-goto-replay-mutations-r1`

- Nonzero outer initialization: safe.
- Fixed worker selector: safe.
- Escaped outer address: safe.
- Extra outer write: safe.
- Outer bound two: safe.
- Inner bound two: structural admission rejected; ordinary fallback was
  manually stopped after running long and produced no incorrect verdict.

## Regression Gates

Final Prior90 artifact:
`/data3/sujie/experiments/v290-original-goto-replay-prior90-r2`

- 90 correct, 0 incorrect, 0 unknown.

Final Exact725 artifact:
`/data3/sujie/experiments/v290-original-goto-replay-exact725-r2`

- 701 official correct, 3 label-relative incorrect, 21 unknown.
- 704 adjudicated correct after the established task82/task91 adjudications
  and the task93 original-model execution.
- The only V288-to-V290 raw status change is task93:
  `ERROR -> false(unreach-call)`.
- V288-correct losses: 0.
- New genuine wrong results: 0.

| Metric | V288 | V290 | Change |
| --- | ---: | ---: | ---: |
| CPU time | 865.0479 s | 894.0098 s | +3.35% |
| Wall time | 908.8000 s | 938.8530 s | +3.31% |
| Summed peak memory | 25.7152 GB | 26.4938 GB | +3.03% |

These totals come from the BenchExec XML for all 725 runs. The plain-text
footer excludes timeout resource limits and is not used for cost comparison.
