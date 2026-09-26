#!/usr/bin/env bash

set -euo pipefail

package_common_files() {
    local repo_root=$1
    local package_root=$2

    mkdir -p "$package_root/bin" "$package_root/lib" "$package_root/share/calyx"
    cp "$repo_root/LICENSE" "$package_root/LICENSE"

    if [[ -d "$repo_root/data/cunningham" ]]; then
        cp -R "$repo_root/data/cunningham/." "$package_root/share/calyx/"
    fi
}
