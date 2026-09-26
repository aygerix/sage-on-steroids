# Compatibility tests

Each `NAME.m` here is a script written for calyx's test suite, and
`NAME.out` is what **real Magma** (V2.29-10, via the public Magma
calculator) printed when running it. The test `tests/compat.rs` runs each
script through calyx and requires the same output, ignoring trailing
whitespace (the calculator strips it from every line).

Only behaviour where calyx is meant to match Magma exactly belongs here.
Scripts that exercise calyx extensions, file I/O, packages, or output that
depends on Magma's internal hash order (the iteration and printing order
of some sets) live in `../scripts/` instead, with outputs blessed from
calyx.

To add or refresh a test, run the script through Magma 2.29 and save what
it prints as `NAME.out`.

The expected outputs are observations of Magma's behaviour on these
scripts; no Magma code or documentation is included.
