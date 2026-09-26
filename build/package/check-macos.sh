#!/usr/bin/env bash

set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "usage: $0 PACKAGE_ROOT" >&2
    exit 2
fi

package_root=$1
for file in "$package_root/bin/calyx" "$package_root"/lib/*; do
    [[ -e "$file" ]] || continue
    while read -r dependency; do
        case "$dependency" in
            /System/Library/*|/usr/lib/*)
                ;;
            @rpath/*)
                name=${dependency#@rpath/}
                if [[ ! -e "$package_root/lib/$name" ]]; then
                    echo "missing bundled library $dependency for $file" >&2
                    exit 1
                fi
                ;;
            *)
                echo "non-system dependency $dependency for $file" >&2
                exit 1
                ;;
        esac
    done < <(otool -L "$file" | tail -n +2 | awk '{ print $1 }')
done

OPENBLAS_NUM_THREADS=1 "$package_root/bin/calyx" --version --verbose
result=$(printf '1 + 1;\n' | OPENBLAS_NUM_THREADS=1 "$package_root/bin/calyx" -b)
[[ "$result" == "2" ]]
