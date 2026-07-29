# Task Plan: V285 Native Residual Portfolio

## Goal

Find and implement the next general Deagle-native residual mechanism after
V284, without wrapper verdict logic, without losing any V284-correct result,
and without materially regressing full-suite resources.

## Acceptance Gates

- The wrapper may select only a normal Deagle argument; it may not prove or
  synthesize the verdict.
- Deagle derives every semantic premise from the GOTO model.
- Every newly covered target returns the correct verdict and emits a
  WitnessLint-valid native witness.
- All semantic premise mutations and natural negative controls reject or
  remain inconclusive.
- Prior90 remains 90/90.
- Exact725 has zero V284-correct losses and zero new wrong results.
- Commit and push only if full-suite coverage/resources pass.

## Phases

- [x] Inspect cnalock and rejected sibling GOTO models.
- [x] State the initial native invariant and fail-closed admission boundary.
- [x] Implement the first candidate in an isolated branch based on
  `origin/deagle-dev`.
- [x] Run positive, negative-mutation, and witness gates.
- [x] Run prior90 and exact725 gates.
- [x] Commit and push only after acceptance.

## Status

V285 starts from accepted unified V284 SHA
`a379e0a17138c491be9cd4e26145373fadf2f9ef`. The accepted candidate extends
the native pure-spin analysis with two fail-closed mechanisms: caller-path
reservation dominance for delegated read-only waits, and an inlined
path-sensitive proof that every retrying iteration is shared-state
stuttering. The final clean binary SHA-256 is
`a01ca0735912b4a4223455af7c7c9a30c7ec2f1c54d81a9232d86c8cdb75b5da`.

The final target, mutation, natural-control, witness, prior90, and exact725
gates pass. Exact725 reaches 700 official / 701 adjudicated correct and
changes only `libvsync/ticketlock.yml` from unknown to correct true. The
accepted native source was committed as
`7a366e465585691b98aa53b277c1980209d86d5e` and pushed to
`origin/deagle-dev`. The dashboard records the strictly post-V284 acceptance
window `2026-07-29 14:44:08–17:47:33 +0800`.
