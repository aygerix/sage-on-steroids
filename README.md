# calyx

A free, open-source computer algebra system that runs programs written in
the **Magma language**. calyx is a command-line application written in Rust,
with [FLINT](https://flintlib.org/) as its arithmetic engine.

calyx is an independent, clean-room implementation: it aims to run existing
Magma scripts unchanged (same syntax, intrinsic names and printed output),
but none of its code or documentation is taken from Magma.

```
$ calyx

 ✿ calyx 0.1.0 · free computer algebra · Magma language
   Seed = 2714893215 · ?Name help · Tab complete · Ctrl-D quit

> Factorization(2^64 + 1);
[ <274177, 1>, <67280421310721, 1> ]
> S := { x^2 mod 7 : x in [1..20] };
> S;
{ 0, 1, 2, 4 }
> f := map< Integers() -> Rationals() | x :-> x/2 >;
> [ f(n) : n in [1..5] ];
[ 1/2, 1, 3/2, 2, 5/2 ]
```

## Status

Development follows the order of the Magma handbook. Currently implemented:

- **Part I, The Magma Language**: statements, expressions, functions and
  procedures, reference arguments, packages and user intrinsics, user-defined
  types and attributes, error handling, `eval`, printing and `printf`, files,
  verbose flags, and the environment intrinsics.
- **Part II, Sets, Sequences, and Mappings**: enumerated, indexed and
  multi-sets, sequences, tuples and Cartesian products, lists, associative
  arrays, coproducts, records, and maps.
- **Part III, Basic Rings** (in progress): residue class rings, finite
  fields, polynomial rings and the complex field, the generic ring
  functions of the chapter "Introduction to Rings" (ring properties,
  element predicates, ideals of the integers), and the chapter "Ring of
  Integers" (arithmetic, primality, factorization and its methods,
  factorization sequences, arithmetic and combinatorial functions,
  modular arithmetic). The other chapters follow (see the roadmap).

See [docs/ROADMAP.md](docs/ROADMAP.md) for a chapter-by-chapter summary,
and the [issues](https://github.com/aygerix/calyx-math/issues) for open
work and known differences from Magma.

## Building

calyx needs Rust 1.85 or newer and FLINT 3.6 with its dependencies (GMP and
MPFR). By default it links against the system FLINT found by `pkg-config`.

On macOS:

```sh
brew install flint pkg-config
cargo build --release
```

On Debian/Ubuntu, install `libflint-dev` (3.6 or newer) and `pkg-config`.

To build FLINT from source instead of using the system library (slower, and
needs a C toolchain and autotools):

```sh
cargo build --release --no-default-features -p calyx-flint
```

## Running

```sh
calyx                 # interactive session
calyx script.m        # run a file, then continue interactively
calyx -b < script.m   # run statements from standard input
calyx -h              # all options
```

Type `?Name` at the prompt to see the signatures of an intrinsic.

In an interactive session the input is syntax-highlighted as you type, Tab
completes the names of intrinsics, keywords and variables (and file names
inside strings), and pressing Enter on an unfinished statement continues it
on a new, automatically indented line, so a whole function can be edited and
recalled from history as one entry. Errors and help are shown in colour.
Values are always printed exactly as Magma prints them, and colour is only
used on a terminal: pass `--no-color` or set `NO_COLOR` to turn it off.

The environment settings use calyx-specific names so installing both systems
does not make either one read the other's startup files or search paths:

| calyx variable | Corresponding Magma variable | Purpose |
| --- | --- | --- |
| `CALYX_STARTUP_FILE` | `MAGMA_STARTUP_FILE` | Default startup file |
| `CALYX_PATH` | `MAGMA_PATH` | Colon-separated file search path |
| `CALYX_LIBRARY_ROOT` | `MAGMA_LIBRARY_ROOT` | Root containing library directories |
| `CALYX_LIBRARIES` | `MAGMA_LIBRARIES` | Colon-separated directories below the library root |
| `CALYX_SYSTEM_SPEC` | `MAGMA_SYSTEM_SPEC` | System package specification file |
| `CALYX_USER_SPEC` | `MAGMA_USER_SPEC` | User package specification file |
| `CALYX_TEMP_DIR` | `MAGMA_TEMP_DIR` | Temporary-file directory |

`CALYX_MEMORY_LIMIT` and `CALYX_HELP_DIR` are not implemented. calyx never
reads the corresponding `MAGMA_*` variables.

## Layout

| Crate | Purpose |
| --- | --- |
| `crates/calyx-flint` | Safe Rust wrappers around FLINT (integers, rationals, reals). The only crate that uses FFI. |
| `crates/calyx-syntax` | Lexer, parser and syntax tree for the Magma language. |
| `crates/calyx-runtime` | The interpreter: values, types, scoping, evaluation, printing and the built-in intrinsics. |
| `crates/calyx-cli` | The `calyx` binary and the golden tests. |

Inside the runtime, source is parsed, then compiled (`compile.rs`) to an IR
in which every identifier is resolved according to Magma's scoping rules
(function locals, values captured when a function is created, and dynamic
top-level globals). The interpreter (`interp/`) executes that IR. Built-in
functions are registered with Magma-style type signatures in `intrinsics/`
and dispatched to the most specific matching signature, exactly like user
intrinsics defined in packages.

## Testing

```sh
cargo test
```

There are two script suites in `crates/calyx-cli/tests`:

- `compat/`: each `NAME.m` has as its expected output `NAME.out` what real
  Magma printed for it (see `compat/README.md`). calyx must match it.
- `scripts/`: golden tests for behaviour Magma's calculator cannot check
  (files, packages) or where calyx deliberately differs. After an intended
  change in output, regenerate their expected files with
  `CALYX_BLESS=1 cargo test -p calyx-cli --test golden`, then review the
  diff.

## License

calyx is licensed under the GNU General Public License, version 3 or later.
See [LICENSE](LICENSE).
