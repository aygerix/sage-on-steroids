# Building from source

calyx builds with Rust 1.98.1, pinned in `rust-toolchain.toml` and installed
automatically by rustup. It also needs a C toolchain, `make`,
`pkg-config`, GMP, MPFR and FLINT 3.6. Linux builds use OpenBLAS. Apple silicon
builds use the Accelerate framework included with macOS.

## Building FLINT

The scripts in `build/flint/` are the reference FLINT configurations used by
CI and release packaging. Give a script an installation prefix and an
unpacked FLINT source tree:

```sh
build/flint/linux-x86-64-avx2.sh "$HOME/.local/flint" /path/to/flint-3.6.0
```

| Target | Script | CFLAGS | FLINT options | BLAS |
| --- | --- | --- | --- | --- |
| Apple silicon | `apple-arm64.sh` | `-O3` | ARM fast FFT | Accelerate |
| Linux x86-64 AVX2 | `linux-x86-64-avx2.sh` | `-O3 -march=x86-64-v3` | AVX2 | OpenBLAS |
| Linux ARM64 | `linux-arm64.sh` | `-O3` | ARM fast FFT | OpenBLAS |
| General Linux x86-64 | `linux-x86-64.sh` | `-O3 -march=x86-64` | portable x86-64 | OpenBLAS |

FLINT treats a user-supplied `CFLAGS` as the complete flag set rather than
adding it to its defaults. An inherited value can therefore remove all
optimization. The scripts always replace `CFLAGS`, include `-O3`, and stop if
FLINT's generated Makefile does not contain the required flags.

The Linux configurations require the OpenBLAS headers and library. Keep it to
one thread when testing or benchmarking:

```sh
export OPENBLAS_NUM_THREADS=1
```

The Apple script finds GMP and MPFR under `/opt/homebrew` by default. Set
`FLINT_DEPS_PREFIX` if both are installed under another prefix. It uses
Accelerate for BLAS and does not require OpenBLAS.

## Building calyx

Point `pkg-config` and the dynamic loader at the FLINT installation, then
build the release binary:

```sh
export PKG_CONFIG_PATH="$HOME/.local/flint/lib/pkgconfig"
export LD_LIBRARY_PATH="$HOME/.local/flint/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
cargo build --release
```

On macOS, use `DYLD_LIBRARY_PATH` instead of `LD_LIBRARY_PATH`. The target
scripts record their CFLAGS and BLAS backend in FLINT's pkg-config metadata;
`calyx --version --verbose` shows those values, the linked FLINT version, the
Rust build target, and the CPU acceleration selected at run time. A system
FLINT that lacks this metadata is reported as `not recorded` rather than
guessed.

## Data files

Optional data belongs in `share/calyx` next to the installation. Every package
ships the Cunningham subset for bases 2 through 99 there. The 124 MB full
`cunningham.bin` is a separate optional release asset and is never stored in
the source repository. Install it as `share/calyx/cunningham.bin`, or put it
in another directory selected with `CALYX_DATA`.

The committed subset lives under `data/cunningham/` in a source checkout.

At run time calyx checks the full file under the directory named by
`CALYX_DATA`, then `../share/calyx` relative to the executable, then the
source-tree data path recorded when a developer build was compiled. If the
full table is absent, it repeats that search for the packaged subset. Missing
optional data is reported by `calyx --version --verbose`; it does not prevent
calyx from starting.

## Release archives

The release workflow runs only for a version tag or when started by hand. It
prepares one archive each for Apple ARM64, Linux ARM64 and Linux x86-64. The
x86-64 archive includes both the general and AVX2 FLINT builds. On an AVX2
machine, the GNU C dynamic loader selects the optimized library from
`lib/glibc-hwcaps/x86-64-v3`; older machines use the general library in
`lib`. `calyx --version --verbose` reports the CFLAGS of the library selected
at run time. The measured AVX-512 build was not faster overall, so it is not
packaged. The workflow uploads the archives as workflow artifacts; it does
not create a release or publish a container image.

An archive contains `bin/calyx`, the project `LICENSE`, bundled non-system
libraries under `lib`, and packaged data under `share/calyx`. Linux archives
leave only the GNU C library and its standard runtime libraries to the host.
The Apple archive leaves macOS frameworks and system libraries to the host.
All other libraries, including FLINT, GMP, MPFR and Linux's OpenBLAS, are
bundled so the archive does not require build dependencies on the target
system.

Before publishing a release, download its workflow artifacts and attach the
three archives by hand. Build the full Cunningham table separately and attach
`cunningham.bin` as an optional release asset; CI deliberately does not build
or upload the 124 MB file. Users can place it in an extracted archive's
`share/calyx` directory or select its containing directory with `CALYX_DATA`.

The top-level `Dockerfile` builds the general Linux x86-64 configuration. It
uses `build/flint/linux-x86-64.sh`, bundles the same runtime libraries as the
general archive, and leaves only the finished installation in a small runtime
image. The release workflow builds and runs this image but never pushes it.
