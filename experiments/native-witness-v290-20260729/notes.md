# Notes: V290 Original-Program Violation-Trace Repair

## Confirmed Historical Projection Defect

- The historical V288/V289 transform replaced the outer initialization bound
  10 with 2. V290 removes that rewrite.
- The historical GraphML exited initialization at `i = 2`, which is impossible
  in the original source. V290 now preserves all 10-by-30 iterations.
- V290 retains the first real worker creation and lifts the execution to the
  legal source schedule in which main pauses immediately after that creation.

## Required Semantic Shape

- Complete all original initialization iterations.
- Execute the first original `pthread_create`.
- Schedule that worker before main performs the next create-loop iteration.
- Select an original-program-allowed worker path that reaches the violated
  assertion.

## Guided Path-Lift Prototype

- Deagle retains the original 10-by-30 initialization.
- The lifted prefix ends main-thread execution after the first real
  `pthread_create`, then keeps only the selected worker through the violated
  assertion.
- The mechanism is enabled only after strict structural admission. It contains
  no task path, YAML label, benchmark name, or source-line condition.
- A full original-program solve took too long and was rejected as the default
  witness strategy. The guided solve completed in about 6.38 seconds.

## 2026-07-30 Validation

- Generated witness:
  `/data3/sujie/experiments/v290-guided-prefix-native-r7/witness.graphml`
- Size: 24,860 lines, 1,027,781 bytes.
- SHA-256:
  `c7d46a9a25e421c61e0f31769f20f34c297e2888c3fc43e432a14b753ee35699`
- Confirmed visible constraints: `j = 1` at source line 1037 and `cond = 0`
  at source line 1046.
- Confirmed thread metadata: one transition into thread 1 carries
  `createThread`, and its first edge carries `enterFunction`.
- Independent path-check output:
  `/data3/sujie/experiments/v290-guided-prefix-validation-r3/`
- UGemCutter exited normally but returned `TRUE`; therefore this witness is not
  accepted and V290 remains unpublished.

## Generic Prefix-Feasibility Gate

- Require a real original `pthread_create` before the failing worker.
- Require the original nondeterministic worker selector to evaluate to one.
- Require exactly the first original worker-domain iteration.
- Drop main-thread steps after the first creation and interpret them as a
  legal scheduler pause, not as an original loop exit.
- Fail closed if any of these obligations is absent.

## Literature-Guided Path-Lifting Design

The repair should not edit the transformed GraphML after the fact. It should
construct a concrete path program over original GOTO instructions and let the
existing `build_goto_trace` and GraphML exporter consume the resulting solver
model.

### Transformation provenance

Each reduced-model rule records:

- original instruction identities for every retained instruction;
- a path-expansion recipe for each synthetic or folded transition;
- the relation between transformed and original symbols;
- original thread-creation and shared-event identities;
- the rule premises that justify trace inclusion.

### Guided concretization

After the reduced model reaches a violated assertion:

1. Extract the selected worker, nondeterministic choices, loop parameters, and
   event order from the reduced solver model.
2. Expand every synthetic transition through its recorded recipe.
3. Build a path program from original GOTO instructions only.
4. Solve the path-feasibility formula
   `Init_original AND Path_original AND Schedule_guide AND violation`.
5. Export GraphML from that concrete original-model solver result.
6. Fail closed if the formula is unsatisfiable, unknown, times out, or any
   transformed step lacks provenance.

The schedule and branch guide are constraints, not verdicts. Deagle performs
the concrete replay and witness generation.

### Task91 instantiation without task-specific code

- The complete initialization is retained verbatim.
- The reduced single-create step maps to the first original
  `pthread_create`.
- Scheduling the selected worker immediately afterward is a legal original
  prefix; later creates and joins are outside the prefix and need not execute.
- Worker-domain restriction maps to an original nondeterministic choice.
- Only values in the backward data/control cone of the violated assertion are
  fixed; heap values are recomputed by the original-model replay.

## 2026-07-30 Native Prefix Results

- Final pre-cleanup task91 run:
  `/data3/sujie/experiments/v290-prefix-proof-container-r4/task91`
- Task91 result: native violation path accepted; lifted prefix has 17,794
  trace steps.
- Final pre-cleanup task93 run:
  `/data3/sujie/experiments/v290-prefix-proof-container-r4/task93`
- Task93 result: native violation path accepted in 6.51 seconds with
  28,176 KiB host-accounted peak RSS; lifted prefix has 17,820 trace steps.
- The generic read-only-prefix analysis admitted four transitive calls for
  task93. It uses no task name, YAML label, source line, or expected result.
- Both runs used one `deagle_exe` inside `deagle-rvf-p1:sujie`; the wrapper
  supplied only arguments and mounts.

## 2026-07-30 Source-Level GraphML Repair

- Actual-parameter assignments are no longer exported as source-variable
  assumptions. This removes call-plumbing state from the witness without
  relying on variable names or source lines.
- Conditional GOTO steps now recover source-level branch polarity by peeling
  logical negations from the lowered guard.
- Conditional GOTO steps are retained even when adjacent lowered instructions
  share the same source location; the final line-1046 branch is now exported
  as `condition-false`.
- Test artifact:
  `/data3/sujie/experiments/v290-branch-control-r1/task91/witness.graphml`
- Independent-check artifact:
  `/data3/sujie/experiments/v290-branch-control-validation-r1/task91/`
- UGem matched 17 of 3,982 witness edges, reported zero bad edges, then
  returned `TRUE`. The previous repaired witness matched 13 edges. This is an
  observable improvement, but it does not pass the release gate.
- The same Ultimate backend also returned `TRUE` when run on the completed
  original program without any witness:
  `/data3/sujie/experiments/task91-manual-witness-20260730/runs/uautomizer-completed-v1/`.
  Therefore its final `TRUE` cannot distinguish a bad witness from an
  underlying verifier limitation on this concurrent heap program.
- Further validator-specific GraphML tuning is not an acceptable release path.
  The next implementation step is guided feasibility replay over original GOTO
  instructions inside the unified Deagle binary.
- V290 remains local and unpublished. Prior90 and Exact725 have not been run
  for this candidate because independent path acceptance is still missing.

## 2026-07-30 Original-GOTO Guided Replay

- The transformed run is now only a guide. It supplies the final source-level
  values of the two relevant nondeterministic assignments.
- The candidate verifier is destroyed before replay to avoid retaining two
  solver states simultaneously.
- Deagle then processes the saved untransformed GOTO model, inserts assumptions
  for the two matched source assignments, and performs a second SAT solve.
- The replay must fail at the same source function and line as the candidate.
  Otherwise the child returns safe and the portfolio continues.
- Final GraphML is generated directly from the original replay trace with
  prefix lifting disabled.
- Final task smoke:
  `/data3/sujie/experiments/v290-original-goto-replay-final-smoke-r1`.
- Final target resource run:
  `/data3/sujie/experiments/v290-original-goto-replay-cost-r2`.
- Final Prior90:
  `/data3/sujie/experiments/v290-original-goto-replay-prior90-r2`, 90/90.
- Final Exact725:
  `/data3/sujie/experiments/v290-original-goto-replay-exact725-r2`.
- Exact725 changes only task93 from `ERROR` to `false(unreach-call)` and loses
  no V288-correct task.
- XML resource totals are CPU 894.009791330 seconds, wall
  938.853009189 seconds, and 26,493,808,640 bytes summed peak memory.
