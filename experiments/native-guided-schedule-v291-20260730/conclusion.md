# Conclusion: V291 Native Prefix-Aware Retry Admission

V291 is accepted for publication.

The native pure-spin checker now retains function-prefix equality facts and
prunes prefix CFG branches that cannot reach the marked retry loop. This lets
Deagle prove `libvsync/rec_ticketlock.yml` with one unified `deagle_exe`.
The wrapper is unchanged and performs no source analysis, proof, verdict, or
witness generation.

The final native correctness witness is 3,457 bytes and passes WitnessLint
2.1.3-dev plus `xmllint`. Prior90 remains 90/90.

Under a contemporaneous 8-worker Exact725 comparison, V291 changes exactly
one task from `unknown` to `true(correct)`, with zero old-correct losses and
zero new wrong results. Relative to the same-configuration V290 control, CPU
changes `+0.867%`, summed wall `+0.807%`, and summed memory `-1.122%`.

The historical V290 dashboard used 48 workers. Its totals remain historical
evidence and are not mixed with the N8 release comparison.
