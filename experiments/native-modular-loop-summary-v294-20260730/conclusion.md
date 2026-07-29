# Conclusion: V294 Native Modular Loop Summary

## Decision

Accept V294.

After native commuting sequentialization has removed the concurrent lifecycle,
Deagle recognizes a fail-closed class of zero-based unsigned accumulation
loops, replaces each accepted loop with its exact modular closed form, and
normalizes bounded unsigned addition/multiplication expressions in the
bit-vector ring. The wrapper remains byte-identical and does not analyze the
program, prove the property, or choose a verdict.

## Coverage and Cost

Under the paired N8 Exact725 protocol, V294 reaches 696 official / 708
adjudicated correct. It adds only `mult-comm`, `mult-dist`, and
`mult-flipped-dist`, with zero V291-correct losses and zero new wrong results.

Relative to the contemporaneous V291 control, aggregate CPU falls 13.216%,
aggregate wall falls 12.726%, and summed per-task peak memory falls 3.138%.
Prior90 remains 90/90.

## Soundness Boundary

- The transform runs only after native commuting sequentialization succeeds.
- Every backward loop in every selected direct worker call must satisfy the
  exact transactional preflight; otherwise no loop is changed.
- Accepted loops require one zero-initialized unsigned induction variable, one
  unit increment, one unsigned static accumulator update, no internal branch,
  no pointer effect, no volatile operand, no extra write, and stable scalar
  bound and delta expressions.
- The closed form uses the original bit-vector widths, so unsigned overflow is
  preserved modulo the accumulator width.
- No benchmark identifier, path, expected label, source line, or wrapper
  verdict certificate is used.

## Witness and Build

All three native GraphML correctness witnesses pass XML parsing and official
WitnessLint's format check. The rebuilt source-tree binary is byte-identical to
the evaluated candidate binary.

## Timing

- Start: `2026-07-29T20:18:29Z`
  (`2026-07-30 04:18:29 +0800`).
- End: `2026-07-29T20:50:47Z`
  (`2026-07-30 04:50:47 +0800`).
- Duration: 32.30 minutes.

The interval begins after V293 ended at `2026-07-29T20:10:12Z`.
