#!/usr/bin/env bash

set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "usage: $0 PACKAGE_ROOT" >&2
    exit 2
fi

package_root=$1
for file in "$package_root/bin/calyx" "$package_root"/lib/*; do
    [[ -e "$file" ]] || continue
    dependencies=$(ldd "$file")
    printf '%s\n' "$dependencies"
    if grep -q 'not found' <<<"$dependencies"; then
        echo "missing shared library for $file" >&2
        exit 1
    fi
done

OPENBLAS_NUM_THREADS=1 "$package_root/bin/calyx" --version --verbose
result=$(printf '1 + 1;\n' | OPENBLAS_NUM_THREADS=1 "$package_root/bin/calyx" -b)
[[ "$result" == "2" ]]
