#!/usr/bin/env bash

set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "usage: $0 PACKAGE_ROOT" >&2
    exit 2
fi

package_root=$1
files_checked=0
while IFS= read -r -d '' file; do
    files_checked=$((files_checked + 1))
    if (( files_checked > 256 )); then
        echo "dependency check exceeded 256 files" >&2
        exit 1
    fi
    dependencies=$(ldd "$file")
    printf '%s\n' "$dependencies"
    if grep -q 'not found' <<<"$dependencies"; then
        echo "missing shared library for $file" >&2
        exit 1
    fi
done < <(find "$package_root/bin" "$package_root/lib" -type f -print0)

verbose=$(OPENBLAS_NUM_THREADS=1 "$package_root/bin/calyx" --version --verbose)
printf '%s\n' "$verbose"
result=$(printf '1 + 1;\n' | OPENBLAS_NUM_THREADS=1 "$package_root/bin/calyx" -b)
[[ "$result" == "2" ]]

avx2_flint=$(find "$package_root/lib/glibc-hwcaps/x86-64-v3" -maxdepth 1 -type f -name 'libflint.so.*' -print -quit 2>/dev/null || true)
if [[ -n "$avx2_flint" ]]; then
    default_trace=$(LD_DEBUG=libs OPENBLAS_NUM_THREADS=1 "$package_root/bin/calyx" --version 2>&1 >/dev/null)
    grep -Eq 'calling init: .*/glibc-hwcaps/x86-64-v3/libflint\.so' <<<"$default_trace"
    grep -Fq 'FLINT CFLAGS: -O3 -march=x86-64-v3' <<<"$verbose"

    loader=$(ldd "$package_root/bin/calyx" | sed -n 's|^[[:space:]]*\(/[^ ]*/ld-linux[^ ]*\).*|\1|p' | head -n 1)
    if [[ -z "$loader" ]]; then
        echo "GNU C dynamic loader not found" >&2
        exit 1
    fi
    general_verbose=$(OPENBLAS_NUM_THREADS=1 "$loader" --glibc-hwcaps-mask x86-64-v2 --library-path "$package_root/lib" "$package_root/bin/calyx" --version --verbose)
    printf '%s\n' "$general_verbose"
    general_trace=$(LD_DEBUG=libs OPENBLAS_NUM_THREADS=1 "$loader" --glibc-hwcaps-mask x86-64-v2 --library-path "$package_root/lib" \
        "$package_root/bin/calyx" --version 2>&1 >/dev/null)
    grep -Eq 'calling init: .*/lib/libflint\.so' <<<"$general_trace"
    grep -Fq 'FLINT CFLAGS: -O3 -march=x86-64' <<<"$general_verbose"
    ! grep -Fq 'FLINT CFLAGS: -O3 -march=x86-64-v3' <<<"$general_verbose"
fi
