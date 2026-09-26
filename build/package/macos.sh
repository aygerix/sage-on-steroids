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

source "$script_dir/common.sh"
package_common_files "$repo_root" "$package_root"
cp "$binary" "$package_root/bin/calyx"

is_system_library() {
    case "$1" in
        /System/Library/*|/usr/lib/*)
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

    while read -r dependency; do
        is_system_library "$dependency" && continue
        case "$dependency" in
            @rpath/*|@loader_path/*|@executable_path/*)
                echo "cannot locate unresolved dependency $dependency for $file" >&2
                exit 1
                ;;
        esac
        name=$(basename "$dependency")
        [[ -e "$package_root/lib/$name" ]] && continue
        cp -L "$dependency" "$package_root/lib/$name"
        queue+=("$package_root/lib/$name")
    done < <(otool -L "$file" | tail -n +2 | awk '{ print $1 }')
done

for file in "$package_root/bin/calyx" "$package_root"/lib/*; do
    [[ -e "$file" ]] || continue
    while read -r dependency; do
        is_system_library "$dependency" && continue
        case "$dependency" in
            @rpath/*|@loader_path/*|@executable_path/*)
                continue
                ;;
        esac
        install_name_tool -change "$dependency" "@rpath/$(basename "$dependency")" "$file"
    done < <(otool -L "$file" | tail -n +2 | awk '{ print $1 }')
done

for library in "$package_root"/lib/*; do
    [[ -e "$library" ]] || continue
    install_name_tool -id "@rpath/$(basename "$library")" "$library"
done
install_name_tool -add_rpath '@executable_path/../lib' "$package_root/bin/calyx"

# Replacing install names invalidates any existing signatures. Ad-hoc signatures
# let the relocated files run without requiring a distribution certificate.
for library in "$package_root"/lib/*; do
    [[ -e "$library" ]] || continue
    codesign --force --sign - --timestamp=none "$library"
done
codesign --force --sign - --timestamp=none "$package_root/bin/calyx"
