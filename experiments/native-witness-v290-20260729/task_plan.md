# Task Plan: V290 Original-Program Violation-Trace Repair

## Goal

Repair the native task91/task93 violation path so Deagle emits a witness
for an execution of the original program, without wrapper verdict logic,
old-correct losses, or material resource regression.

## Acceptance Gates

- Preserve all 10 outer and 30 inner initialization iterations.
- Reach the worker violation after a real `pthread_create` and before relying on an
  artificial exit from the 10,000-create loop.
- Deagle owns analysis, verdict, and witness generation.
- The GraphML is structurally valid and independently path-checked where tool
  support exists; a parser-only WitnessLint result is insufficient.
- Premise-breaking mutations remain non-violations.
- Prior90 remains 90/90.
- Exact725 has zero V288-correct losses and no new genuine wrong result.
- No material CPU, wall-time, or memory regression.

## Phases

- [x] Seal V289 as failed and create an isolated V290 worktree from V288.
- [x] Trace native model transformation and witness projection.
- [x] Implement the smallest generic original-path-preserving repair.
- [x] Run task91/task93 and mutation gates.
- [x] Replay the reduced candidate inside Deagle over the original GOTO model.
- [x] Run Prior90 and Exact725 after the original-model replay passes.
- [x] Complete the source-boundary and diff audit.
- [x] Commit the accepted native implementation and verification record.

## Status

The unified native child now treats the transformed execution only as a
guide. It extracts two source nondeterministic choices, destroys the candidate
solver, processes a saved untransformed GOTO model, constrains those choices,
and asks Deagle to solve the original model independently. Both task91 and
task93 reach the same source assertion through original instructions, and the
final GraphML is exported from that second solver trace. All five terminating
premise-breaking mutations fail closed; the sixth structure-breaking mutation
entered the ordinary fallback and was stopped without producing a verdict.

The final gates are 90/90 Prior90 and 701 official / 704 adjudicated Exact725.
Against V288, the only raw status change is task93 from `ERROR` to
`false(unreach-call)`; there are zero old-correct losses. Aggregate cost changes
from 865.05 to 894.01 CPU seconds (+3.35%), 908.80 to 938.85 wall seconds
(+3.31%), and 25.715 to 26.494 GB summed peak memory (+3.03%). V290 is
accepted. The source-boundary scan found no benchmark identifiers, expected
labels, or target line conditions; the wrapper is unchanged and
`git diff --check` passes.

## Errors Encountered

- Full original-program re-solving exceeded the acceptable per-task budget, so
  it is not a release candidate.
- Keeping the first SSA assignment at a repeated source location exposed
  library temporaries instead of source variables. Keeping the final visible
  state repaired this mapping defect.
- UGemCutter still rejected the repaired 24,860-line witness on 2026-07-30,
  proving that format and visible assignments alone are insufficient.
- Directly launching Deagle as container PID 1 makes portfolio children exit
  through the parent-death guard. Official runs must retain the shell parent;
  all PID-1 diagnostics were discarded.
- Two wrapper-level exploratory launches continued after the client yielded
  and entered ordinary large-unwind analysis. Their two exact containers were
  stopped before further measurement; no unrelated container was touched.
- Restoring source-level branch polarity removed the missing branch annotation
  and increased UGem matching to 17/3982, but UGem still returned TRUE. This is
  not sufficient independent semantic validation.
- The first final Prior90 relaunch passed `bash` through the image's default
  shell entry point and exited before running Deagle. The retained log reports
  `/bin/sh: 0: cannot open bash`; the corrected launch used
  `--entrypoint /bin/bash` and completed 90/90.
- BenchExec's plain-text Exact725 footer reports only 568.28 CPU seconds
  because it omits timeout resource limits from that display. The authoritative
  XML totals all 725 runs and reports 894.01 CPU seconds, 938.85 wall seconds,
  and 26,493,808,640 bytes.
