# V294 Notes

## Base

- Remote base:
  `dc112ff7493bcb3d700bf43bc669abebaf2dacd5`.
- V293 contains documentation only; production semantics equal accepted V291.

## Residual Selection

The V291 Exact725 result has 29 unfinished tasks. V292 already tested the six
LDV front-end residuals, eight fast libvsync unknowns, and SafeStack. V293
tested elimination-backoff RF encoding. V294 therefore targets the remaining
Weaver timeout family.

The existing native commuting-sequentialization transform admits
`mult-comm`, `mult-dist`, `mult-flipped-dist`, and `array-eq-symm`, but all
still time out because their unbounded worker loops remain in the sequential
model. The first V294 candidate targets the three scalar multiplication
identities with an exact modular loop summary.

## Target and Mutation Evidence

- Candidate build:
  `/home/lapulatos/deagle-v294-modular-loop-r1-20260730`.
- Target artifact:
  `/home/lapulatos/deagle-experiments/v294-modular-loop-target-r4`.
- `mult-comm`, `mult-dist`, and `mult-flipped-dist` complete with native
  verification success and write GraphML witnesses.
- `array-eq-symm` does not satisfy the scalar-loop premises and therefore
  remains unchanged.
- Mutation artifact:
  `/home/lapulatos/deagle-experiments/v294-modular-loop-mutations-r2`.
- Eight controls cover an extra write, induction-dependent delta, worker
  interference, an internal branch, signed accumulation, a non-unit step,
  volatile input, and a flipped property. The first seven fail closed at the
  relevant admission boundary; the flipped property is still reported as a
  verification failure.

## Invalid Prior90 Launch

`v294-modular-loop-prior90-r1` used the generic
`benchexec.tools.deagle` module, which ignored the experiment option portfolio.
It is not correctness or performance evidence. The run was stopped after the
configuration error became visible, and its systemd scope was terminated.
The clean release run must copy the accepted V291 r3 configuration using
`benchexec.tools.deagle_benchexec`.
