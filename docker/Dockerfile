# =============================================================================
# Multi-stage Dockerfile for all pyana service binaries.
#
# Build:  docker build --target <stage> -t pyana-<service> ..
# Stages: node, gallery, discharge-gateway
#
# Multi-arch:
#   docker buildx build --platform linux/amd64,linux/arm64 --target node -t pyana-node .
# =============================================================================

# ---------------------------------------------------------------------------
# Stage 0: builder — compile all workspace binaries in one pass
# ---------------------------------------------------------------------------
FROM rust:latest AS builder

# Install the exact nightly toolchain the workspace requires.
RUN rustup toolchain install nightly-2026-01-01 && rustup default nightly-2026-01-01

# System deps needed for C dependencies (openssl headers for ring, etc.)
RUN apt-get update && apt-get install -y --no-install-recommends \
    pkg-config libssl-dev cmake \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /build
COPY . .

# Build all deployable service binaries.
RUN cargo build --release \
    -p pyana-node \
    -p pyana-gallery \
    -p discharge-gateway

# ---------------------------------------------------------------------------
# Stage 1: node — pyana federation node
# ---------------------------------------------------------------------------
FROM debian:bookworm-slim AS node

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /build/target/release/pyana-node /usr/local/bin/

EXPOSE 8420 9420
ENTRYPOINT ["pyana-node"]

# ---------------------------------------------------------------------------
# Stage 2: gallery — federated art gallery backend
# ---------------------------------------------------------------------------
FROM debian:bookworm-slim AS gallery

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /build/target/release/pyana-gallery /usr/local/bin/
COPY apps/gallery/frontend /srv/gallery/frontend

EXPOSE 3040
ENTRYPOINT ["pyana-gallery"]

# ---------------------------------------------------------------------------
# Stage 3: discharge-gateway — third-party macaroon caveat discharge service
# ---------------------------------------------------------------------------
FROM debian:bookworm-slim AS discharge-gateway

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /build/target/release/discharge-gateway /usr/local/bin/

EXPOSE 8080
ENTRYPOINT ["discharge-gateway"]

# ---------------------------------------------------------------------------
# Default target: node (backwards-compatible with existing usage)
# ---------------------------------------------------------------------------
FROM node
