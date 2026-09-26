# Build benchmark baselines

`run.py` measures the fixed build-target suite in fresh calyx processes. It
records every wall time, the best and median wall time, peak resident memory,
the complete `calyx --version --verbose` output, and a hash of each workload.
OpenBLAS is held to one thread.

Run a release build with:

```text
build/benchmarks/run.py --binary target/release/calyx --output calyx-benchmark.json
```

The five workloads cover large-integer multiplication, dense product and
rank over GF(10007), packed extension-field polynomial multiplication, and an
F4 Gröbner basis over a prime field. A complete run is bounded to ten fresh
processes per workload and ten minutes per process; the defaults are three
and five minutes.

Committed Linux baselines are measured in the benchmark lab. Results from an
Apple development machine are deliberately not committed because shared-machine
load makes them unsuitable as release baselines.
