# Tables of factors of b^n - 1 and b^n + 1

`Cunningham` and `Factorization` look up the known prime factors of
b^n - 1 and b^n + 1 in these tables.

- `cunningham-small.bin`, in the repository: the bases from 2 to 99
  (965,433 primes, 6,646,179 bytes).
- `cunningham.bin`, not in the repository: all the bases from 2 to 9999
  (19,780,262 primes, 124,003,527 bytes). calyx's releases offer it as a
  separate download.

calyx uses the first file it finds. It looks for `cunningham.bin`, and then
for `cunningham-small.bin`, in the directory named by `CALYX_DATA`, in
`share/calyx` next to the directory of the calyx binary, and here. Without
the files, or for bases a file doesn't cover, calyx finds the factors by
computation alone. The results are the same, but large exponents can take
much longer.

## Sources

The tables come from `factors.gz` (the edition of 3 September 2026), Crombie's
collection of the known factors of b^n - 1 and b^n + 1 for b and n below
10000. It continues R. P. Brent's tables of factors of a^n ± 1, and
includes the Cunningham project's tables for the bases 2, 3, 5, 6, 7, 10, 11
and 12. Those tables (`pmain126.txt`, `appa126.txt` and `appc126.txt`) were
used to check the collection.

Like the collection, the tables hold the primes above 10^9, and leave out the
largest prime of each number, or of each of its Aurifeuillian factors. calyx
finds the primes left out by division, by a search of the primes below
10^9 that can divide the number, and by the Aurifeuillian factorization.

## Regenerating the files

The builder reads the lines of `factors.gz` ("b n- p" or "b n+ p" for a
prime p dividing b^n - 1 or b^n + 1), checks each prime, and writes a file
for a range of bases:

```sh
gzip -dc factors.gz | cargo run --release --example cunningham_build -- --bases 2-99 --check data/cunningham/cunningham-small.bin
gzip -dc factors.gz | cargo run --release --example cunningham_build -- --bases 2-9999 --check data/cunningham/cunningham.bin
```

The layout of the files is described at the top of
`crates/calyx-runtime/src/intrinsics/factoring/cunningham.rs`.
