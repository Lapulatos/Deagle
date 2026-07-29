# Conclusion: V287 Pointer-Exception Scope

Accepted. Native V287 preserves V285 `ticketlock` and adds only
`libvsync/cnalock.yml`, reaching 701 official / 702 adjudicated correct with
zero old-correct losses and zero new wrong results. Prior90 is 90/90 and the
3,223-byte correctness witness passes WitnessLint. CPU and summed wall rise
0.601% and 0.532%, while summed memory falls 0.077%.

The wrapper remains byte-identical to V285 and performs bounded routing and
argument selection only. Admission, proof, verdict, and witness generation
remain inside one native `deagle_exe`.
