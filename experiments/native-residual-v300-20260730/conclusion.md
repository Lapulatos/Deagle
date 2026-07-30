# Conclusion: V300 Comparator Scan Laws

V300 is accepted for publication. A generic native structural proof covers
three comparator scan laws in one unified `deagle_exe`; the wrapper is
byte-identical to V299 and performs no proof or verdict work.

Paired Exact725 changes only the three intended timeouts to correct true,
raising accepted adjudicated coverage from 714 to 717 with zero old-correct
losses and zero new wrong results. CPU, wall time, and summed task memory
improve by 15.67%, 15.61%, and 0.20% against the same-machine V299 control.
Prior90 changes only those three targets, all 14 structural mutations reject,
all three native correctness witnesses pass WitnessLint's format gate, and two
independent object-free builds produce the same executable SHA-256.

The initial broader candidate is rejected and not published: it incorrectly
changed two negative controls from false to true. The accepted implementation
scopes the necessary standard-abort and verified-assume handling to the fully
audited comparator-scan path.
