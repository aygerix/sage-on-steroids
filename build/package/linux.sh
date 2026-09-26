#!/usr/bin/env bash

set -euo pipefail

if [[ $# -ne 2 ]]; then
    echo "usage: $0 BINARY PACKAGE_ROOT" >&2
    exit 2
fi

script_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(cd "$script_dir/../.." && pwd)
binary=$1
package_root=$2

if [[ ! -x "$binary" ]]; then
    echo "not an executable: $binary" >&2
    exit 1
fi
if [[ -e "$package_root" ]]; then
    echo "package destination already exists: $package_root" >&2
    exit 1
fi
if ! command -v patchelf >/dev/null; then
    echo "patchelf is required to package Linux binaries" >&2
    exit 1
fi

source "$script_dir/common.sh"
package_common_files "$repo_root" "$package_root"
cp "$binary" "$package_root/bin/calyx"

is_system_library() {
    case "$1" in
        linux-vdso.so.*|ld-linux*.so*|libc.so.*|libdl.so.*|libm.so.*|libpthread.so.*|libresolv.so.*|librt.so.*|libutil.so.*)
            return 0
            ;;
        *)
            return 1
            ;;
    esac
}

queue=("$package_root/bin/calyx")
next=0
while (( next < ${#queue[@]} )); do
    if (( next >= 256 )); then
        echo "dependency walk exceeded 256 files" >&2
        exit 1
    fi
    file=${queue[$next]}
    next=$((next + 1))

    while read -r name arrow path rest; do
        [[ "$arrow" == "=>" ]] || continue
        if [[ "$path" == "not" ]]; then
            echo "missing dependency $name for $file" >&2
            exit 1
        fi
        is_system_library "$name" && continue
        [[ -e "$package_root/lib/$name" ]] && continue
        cp -L "$path" "$package_root/lib/$name"
        queue+=("$package_root/lib/$name")
    done < <(ldd "$file")
done

patchelf --set-rpath '$ORIGIN/../lib' "$package_root/bin/calyx"
for library in "$package_root"/lib/*; do
    [[ -e "$library" ]] || continue
    patchelf --set-rpath '$ORIGIN' "$library"
done
