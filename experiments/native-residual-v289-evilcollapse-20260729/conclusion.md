# Conclusion: V289 Shortened-Trace Projection Attempt

V289 is a completed failed candidate.

The native admission relaxation preserves Prior90 at 90/90 and changes only
task93 from `ERROR` to `false(unreach-call)` in Exact725. Against the
contemporaneous V288 control, CPU and wall rise 0.624% and 0.616%, while summed
memory falls 0.931%.

The candidate fails the mandatory semantic gate. Its GraphML still exits the
outer initialization loop after two iterations, which is impossible under the
original bound of ten. The apparent result is not counted as coverage. The
four-line native source change was neither committed nor pushed.

V290 therefore starts from accepted V288 and replaces projected-trace evidence
with an independent native replay over the untransformed original GOTO model.
