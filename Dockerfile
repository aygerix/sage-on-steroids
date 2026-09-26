FROM debian:bookworm AS flint

ARG FLINT_VERSION=3.6.0

RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential ca-certificates curl libgmp-dev libmpfr-dev libopenblas-dev m4 pkg-config \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /src
COPY build/flint/ build/flint/
RUN FLINT_JOBS=4 \
    FLINT_TARBALL_URL="https://github.com/flintlib/flint/releases/download/v${FLINT_VERSION}/flint-${FLINT_VERSION}.tar.gz" \
    build/flint/linux-x86-64.sh /opt/flint

FROM rust:bookworm AS builder

ENV CARGO_BUILD_JOBS=4 \
    OPENBLAS_NUM_THREADS=1
RUN apt-get update && apt-get install -y --no-install-recommends \
        libgmp-dev libmpfr-dev libopenblas-dev patchelf pkg-config \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /src
COPY rust-toolchain.toml ./
RUN rustup show active-toolchain
COPY --from=flint /opt/flint /opt/flint
ENV PKG_CONFIG_PATH=/opt/flint/lib/pkgconfig \
    LD_LIBRARY_PATH=/opt/flint/lib
COPY . .
RUN cargo build --release \
    && build/package/linux.sh target/release/calyx /package

FROM debian:bookworm-slim

ENV OPENBLAS_NUM_THREADS=1
COPY --from=builder /package/ /usr/local/
ENTRYPOINT ["/usr/local/bin/calyx"]
