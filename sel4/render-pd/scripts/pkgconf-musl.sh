#!/usr/bin/env bash
export PKG_CONFIG_LIBDIR="/opt/homebrew/opt/aarch64-unknown-linux-musl/toolchain/aarch64-unknown-linux-musl/lib/pkgconfig"
export PKG_CONFIG_SYSROOT_DIR="/opt/homebrew/opt/aarch64-unknown-linux-musl/toolchain/aarch64-unknown-linux-musl"
exec /opt/homebrew/bin/pkg-config "$@"
