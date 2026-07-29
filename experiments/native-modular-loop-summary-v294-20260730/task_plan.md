# V294 Native Modular Loop Summary Plan

## Objective

Increase Exact725 coverage beyond accepted V291 without wrapper analysis,
without losing a previously correct task, and without a material resource
regression.

## Candidate

After the existing native commuting-sequentialization proof has eliminated
the pthread lifecycle, summarize a simple unsigned counting loop of the form

`for (i = 0; i < bound; ++i) accumulator += delta`

as the exact modular assignment

`accumulator += exact_count(bound) * delta`.

## Gates

- [done] Implement fail-closed GOTO recognition and transformation.
- [done] Run the three Weaver multiplication targets.
- [done] Run premise-breaking mutations and natural loop controls.
- [done] Verify one unified `deagle_exe` and unchanged wrapper.
- [done] Run Prior90 and paired V291/V294 Exact725.
- [done] Validate native correctness witnesses.
- [done] Commit and push immediately only if every release gate passes.

## Current Checkpoint

- Target artifact:
  `/home/lapulatos/deagle-experiments/v294-modular-loop-target-r4`.
- All three multiplication targets finish with native Deagle verification
  success in 0.04--0.06 seconds.
- Eight premise-breaking mutations either reject the transform or preserve the
  deliberately flipped failure result.
- The first Prior90 launch used the wrong generic BenchExec module and is
  invalid evidence. It was stopped and left as an explicit diagnostic
  artifact. The release run must use `benchexec.tools.deagle_benchexec`, as in
  the accepted V291 Prior90 configuration.

## Release Boundary

- Apply only after native commuting sequentialization succeeds.
- Accept only unsigned accumulators and exact zero-based counting loops.
- Reject calls, memory dereferences, volatile operands, extra writes, branch
  entries, non-unit induction updates, and any unstable bound or delta.
- Use no benchmark name, path, source line, expected verdict, or wrapper
  property inspection.
