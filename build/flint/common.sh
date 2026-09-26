#!/bin/sh

set -eu

flint_usage() {
    echo "usage: $0 PREFIX [SOURCE]" >&2
    echo "       SOURCE may be omitted when FLINT_TARBALL_URL is set" >&2
    exit 2
}

build_flint() {
    [ "$#" -ge 3 ] || flint_usage
    prefix=$1
    source=$2
    flint_cflags=$3
    shift 3

    [ -n "$prefix" ] || flint_usage
    case "$prefix" in
        /*) ;;
        *) prefix=$(pwd)/$prefix ;;
    esac

    flint_tmp=
    if [ -z "$source" ]; then
        [ -n "${FLINT_TARBALL_URL:-}" ] || flint_usage
        flint_version=${FLINT_VERSION:-3.6.0}
        flint_tmp=$(mktemp -d "${TMPDIR:-/tmp}/calyx-flint.XXXXXX")
        trap 'rm -rf "$flint_tmp"' EXIT HUP INT TERM
        curl -fsSL "$FLINT_TARBALL_URL" -o "$flint_tmp/flint.tar.gz"
        tar xzf "$flint_tmp/flint.tar.gz" -C "$flint_tmp"
        source=$flint_tmp/flint-$flint_version
    fi

    [ -x "$source/configure" ] || { echo "FLINT source tree not found: $source" >&2; exit 2; }
    source=$(CDPATH= cd "$source" && pwd)

    flint_jobs=${FLINT_JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)}
    case "$flint_jobs" in
        ''|*[!0-9]*|0) echo "FLINT_JOBS must be a positive integer" >&2; exit 2 ;;
    esac

    cd "$source"
    ./configure --prefix="$prefix" --disable-static "$@" CFLAGS="$flint_cflags"

    effective_cflags=$(sed -n 's/^_CFLAGS:=//p' Makefile)
    case " $effective_cflags " in
        *" $flint_cflags "*) ;;
        *) echo "FLINT configure lost required CFLAGS: $flint_cflags" >&2; exit 1 ;;
    esac
    echo "FLINT CFLAGS: $effective_cflags"

    make -j"$flint_jobs"
    make DESTDIR="${DESTDIR:-}" install
}
