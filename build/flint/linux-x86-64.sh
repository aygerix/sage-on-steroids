#!/bin/sh

set -eu

[ "$#" -ge 1 ] && [ "$#" -le 2 ] || { echo "usage: $0 PREFIX [SOURCE]" >&2; exit 2; }

script_dir=$(CDPATH= cd "$(dirname "$0")" && pwd)
. "$script_dir/common.sh"

build_flint "$1" "${2:-}" "-O3 -march=x86-64" --with-blas
