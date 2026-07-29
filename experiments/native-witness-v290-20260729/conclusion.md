# Conclusion: V290 Original-Program Violation-Trace Repair

V290 is accepted for publication.

The reduced execution is no longer treated as the final witness. One unified
native `deagle_exe` uses it only to obtain two source nondeterministic choices,
then independently processes and solves the untransformed original GOTO model.
The final verdict and GraphML both come from that second Deagle solve. Replay
fails closed if the guide cannot be mapped or the same assertion is not
reached.

Both task91 and task93 now produce original-model violation traces. Prior90 is
90/90. Exact725 has zero V288-correct losses, and task93 is the only changed
raw status (`ERROR -> false(unreach-call)`). The established adjudicated count
increases from 703 to 704 while official label-relative correctness remains
701.

The price of source-faithful replay is +3.35% aggregate CPU, +3.31% aggregate
wall time, and +3.03% summed peak memory against V288. This is measurable but
not a large regression for one additional original-model result and repaired
witness semantics.

UGemCutter remains unable to validate the concurrent heap execution, but the
same backend also returns `TRUE` without loading a witness. This limitation is
recorded rather than hidden. The release decision relies on Deagle's separate
original-model SAT replay, not parser-only or reduced-model evidence.

The final source audit found no benchmark name, task number, YAML label,
expected-result label, or target source-line condition in production code.
No Python or wrapper file changed. The tested server sources match the
committed six native files byte for byte, and `git diff --check` passes.
