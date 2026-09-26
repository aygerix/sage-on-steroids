# Linux x86-64 build baselines

Recorded 2026-09-26 in the isolated Linux benchmark lab on AMD Zen 5. The
sandbox identifies the virtual CPU model as `unknown`; FLINT configures it as
`zen5-pc-linux-gnu`. OpenBLAS used one thread. Each result is the best wall
time of three fresh processes and the largest peak RSS of those runs. The
release binaries used thin LTO.

| Workload | General time | General RSS | AVX2 time | AVX2 RSS | AVX-512 time | AVX-512 RSS |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 2,000,000-digit integer product | 0.055 s | 90.5 MiB | 0.054 s | 98.8 MiB | 0.055 s | 97.6 MiB |
| 3000 x 3000 product over GF(10007) | 0.707 s | 640.3 MiB | 0.708 s | 641.4 MiB | 0.709 s | 639.5 MiB |
| Rank of a 3000 x 3000 matrix over GF(10007) | 0.812 s | 303.5 MiB | 0.676 s | 304.8 MiB | 0.679 s | 303.3 MiB |
| Degree-100,000 packed polynomial product over GF(251^10) | 0.656 s | 217.2 MiB | 0.416 s | 245.5 MiB | 0.415 s | 245.2 MiB |
| Cyclic-8 F4 basis over GF(32003) | 0.932 s | 181.8 MiB | 0.928 s | 181.6 MiB | 0.918 s | 181.4 MiB |

AVX-512 was 0.34% slower than AVX2 by the geometric mean of the median wall
times. It was slower on the integer product, matrix rank and packed polynomial
product, indistinguishable on matrix product, and 1.1% faster on F4 even
though that workload dispatches the same calyx AVX2 kernel in both binaries.
The AVX-512 FLINT tier is therefore not retained. AVX2 is retained: it cut the
rank baseline by 17% and the packed polynomial product by 37%.

## General build details

```text
calyx 0.1.0
Build target: x86_64-unknown-linux-gnu
FLINT: 3.6.0
FLINT CFLAGS: -g -O3 -march=x86-64
BLAS: OpenBLAS
CPU dispatch: AVX2, PCLMULQDQ
Cunningham tables: /root/lanes/lane-build/data/cunningham/cunningham-small.bin (bases 2 to 99)
```

## AVX2 build details

```text
calyx 0.1.0
Build target: x86_64-unknown-linux-gnu
FLINT: 3.6.0
FLINT CFLAGS: -mfma -mavx2 -g -O3 -march=x86-64-v3
BLAS: OpenBLAS
CPU dispatch: AVX2, PCLMULQDQ
Cunningham tables: /root/lanes/lane-build/data/cunningham/cunningham-small.bin (bases 2 to 99)
```

## Rejected AVX-512 build details

```text
calyx 0.1.0
Build target: x86_64-unknown-linux-gnu
FLINT: 3.6.0
FLINT CFLAGS: -mavx512f -mfma -mavx2 -g -O3 -march=x86-64-v4
BLAS: OpenBLAS
CPU dispatch: AVX2, PCLMULQDQ
Cunningham tables: /root/lanes/lane-build/data/cunningham/cunningham-small.bin (bases 2 to 99)
```
