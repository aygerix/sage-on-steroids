# Pending compatibility tests

Scripts here are waiting for their expected output from Magma 2.29 (the
public calculator). The compatibility test only reads the directory above,
so these are not run yet.

To promote one, save its output from Magma 2.29 as `NAME.out` in the
directory above, and move the script up:

```sh
git mv crates/calyx-cli/tests/compat/pending/NAME.m crates/calyx-cli/tests/compat/
```
