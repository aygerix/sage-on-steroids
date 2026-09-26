#!/usr/bin/env bash

set -euo pipefail

if [[ $# -lt 2 || $# -gt 3 ]]; then
    echo "usage: $0 BINARY PACKAGE_ROOT [AVX2_LIBRARY_DIR]" >&2
    exit 2
fi

script_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(cd "$script_dir/../.." && pwd)
binary=$1
package_root=$2
avx2_library_dir=${3:-}

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

queue=("$package_root/bin/calyx")
if [[ -n "$avx2_library_dir" ]]; then
    avx2_flint=$avx2_library_dir/libflint.so
    if [[ ! -e "$avx2_flint" ]]; then
        echo "AVX2 FLINT library not found: $avx2_flint" >&2
        exit 1
    fi
    avx2_soname=$(patchelf --print-soname "$avx2_flint")
    if [[ -z "$avx2_soname" ]]; then
        echo "AVX2 FLINT library has no soname: $avx2_flint" >&2
        exit 1
    fi
    avx2_destination=$package_root/lib/glibc-hwcaps/x86-64-v3/$avx2_soname
    mkdir -p "$(dirname "$avx2_destination")"
    cp -L "$avx2_flint" "$avx2_destination"
    queue+=("$avx2_destination")
fi

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
while IFS= read -r -d '' library; do
    case "$library" in
        */glibc-hwcaps/x86-64-v3/*) patchelf --set-rpath '$ORIGIN/../..' "$library" ;;
        *) patchelf --set-rpath '$ORIGIN' "$library" ;;
    esac
done < <(find "$package_root/lib" -type f -print0)
