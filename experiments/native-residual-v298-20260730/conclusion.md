# V298 Conclusion

V298 is accepted. A generic native joined-terminal-overwrite transform replaces
fully joined nondeterministic unsigned loop effects only when every finite
worker execution ends in a proved constant overwrite and every nonterminating
execution remains before the joins. One `deagle_exe` performs admission,
transformation, backend verification, verdict, and witness generation; the
wrapper is byte-identical to V297.

Exact725 reaches 701 official / 713 adjudicated correct by changing only
`spaghetti.wvr.yml` from timeout to correct true. There are zero old-correct
losses and zero new wrong results. CPU, summed wall, and summed memory improve
by 6.920%, 7.248%, and 0.476%, while peak memory is unchanged. Prior90 remains
90/90. The correctness witness passes WitnessLint's format gate, and an
independent build reproduces the evaluated executable byte-for-byte.
