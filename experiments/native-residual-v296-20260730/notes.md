# V296 Notes

## Base

- Accepted V295:
  `bc88186d63318a2c10a506f825871d53791d5ca8`.
- V295 Exact725 has 697 official / 709 adjudicated correct and 25 unfinished
  tasks.
- The wrapper remains fixed at the V291-compatible byte-identical routing
  boundary.

## Initial Candidate Direction

The bounded alternating recurrence family is the first V296 candidate to
audit. Its workers update one atomic scalar by opposite deltas, toggle a
private phase after every step, and execute an even number of steps. If those
premises are derived from the GOTO model, each worker's transition word
cancels pairwise regardless of its initial phase.

Before implementation, the audit will compare this structure against the
existing alternating-phase native analysis and determine why it rejects the
remaining bounded case. No direct verdict or benchmark-specific admission
will be added.

## First Native Audit

The accepted V295 binary reports:

`NATIVE_ALTERNATING_PHASE_AUDIT applicable=0
reason=phase_worker_instruction_count_8`

It then reports no local-loop, commuting-sequentialization, or JCES transform
and enters bounded model checking. The existing alternating-phase analysis is
for a producer/consumer triangular recurrence, not this cancellation family.

The normalized worker GOTO word has exactly:

1. an unsigned bound guard;
2. a private Boolean phase branch;
3. `shared := shared + weight` or `shared := shared - weight`;
4. private phase negation;
5. private induction increment;
6. one unconditional backedge.

For the bounded residual, the bound is an unsigned constant factor of an
immutable shared scalar. The required proof obligations are therefore:

- the factor is even under bit-vector multiplication;
- the induction is zero at spawn and is owned by exactly one worker;
- the phase is private to that same worker;
- both branch updates target one atomic scalar with equal opposite magnitude;
- the worker performs no other shared access;
- all workers complete and are joined before the sole property suffix;
- the shared scalar's pre-spawn value is fixed by an assumption.

If every obligation is derived, each adjacent transition pair is the identity
on the atomic scalar for either initial phase. The implementation should
summarize the loop state and continue through Deagle's ordinary backend,
rather than return a direct verdict.

## Implemented Admission

The final implementation derives all of the obligations above from the GOTO
model and additionally requires:

- a straight-line, dominating pre-spawn equality that initializes every
  private induction variable to zero;
- an unsigned loop bound that is either an even constant or an even constant
  factor times one stable shared integer symbol;
- no bound dependence on the induction, phase, or updated object;
- no late bound/object writes;
- no cross-worker or post-spawn observation of private state;
- no foreign function access except CBMC's pre-main static initializer.

The first build correctly rejected the candidate because the exclusivity scan
included `__CPROVER_initialize`. The final implementation excludes only this
standard pre-main initializer; all ordinary foreign functions remain covered.

## Gates

- Native target: correct true in 0.14 s, with
  `NATIVE_BOUNDED_ALTERNATING_CANCELLATION applied=1 workers=2`.
- Ten semantic gates cover odd factors, asymmetric weights, nonzero
  induction, shared phase, non-atomic state, an extra shared step,
  conditional initialization, a self-dependent bound, a late bound write,
  and a property flip.
- The property flip remains admitted and Deagle reports
  `VERIFICATION FAILED`; every premise-breaking mutation is rejected.
- Seven other residual Weaver tasks are natural controls and all report
  `applied=0`.
- Prior90 remains 90/90.
- Paired Exact725 changes only the target timeout to correct true.
