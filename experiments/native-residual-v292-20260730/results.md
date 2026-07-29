# Results: V292 Native Residual Feasibility

## Attempt 1: unreserved single pure-read loop

Artifact:
`/home/lapulatos/deagle-experiments/v292-unreserved-single-read-r1`

- Four one-loop scalar libvsync tasks passed native admission.
- All four remained incomplete after 45 seconds.
- Accepted `ticketlock` and `cnalock` remained successful.
- Multi-loop `rec_mcslock` and `mcslock` remained inconclusive at the global
  fail-closed gate.
- Coverage gain: zero.

The diagnostic source edit was restored exactly to V291.

## Attempt 2: bounded shared progress

Artifacts:

- `/home/lapulatos/deagle-experiments/v292-timeout-phase-r1`
- `/home/lapulatos/deagle-experiments/v292-safestack-bound-feasibility-r1`
- `/home/lapulatos/deagle-experiments/v292-safestack-bound-objectbits-r1`
- `/home/lapulatos/deagle-experiments/v292-weaver-phase-r1`

The residual pthread-complex and Weaver tasks spend the release budget in
symbolic loop unwinding. For `safestack_relacy`, bound 2 correctly violates
the unwinding assertion. Bound 3 reaches SC construction, but increasing the
addressed-object width from 8 to 9, 10, or 11 bits still does not finish
within 90 seconds.

Coverage gain: zero.

## Front-End Residual Boundary

Six LDV tasks contain nonempty x86 instructions, including atomic bit
operations, exchanges, port I/O, traps, and indirect paravirtual calls.
Treating those instructions as empty barriers is not a sound native lowering.
No source change was attempted in V292.

## Repository State

- Base: `a838944c8efcca05f27c7c5c25d5b95d844e52c5`.
- Production source diff: empty.
- Wrapper diff: empty.
- `git diff --check`: pass.
- Stale server Deagle/BenchExec processes: zero.
