# Starbridge v2 — the native dregg master interface.
#
# Always run FROM INSIDE this directory (`cd starbridge-v2 && make …`): the
# toolchain pin (`rust-toolchain.toml`, the rolling nightly gpui needs) is
# directory-scoped, and the standalone workspace must NOT be reached via
# `--manifest-path` from the repo root (see Cargo.toml + docs/STARBRIDGE-V2.md).
#
# The embedded VERIFIED executor (real conservation proofs / ocap checks / caveat
# crypto) is *pathologically slow in debug* — so the cockpit and the test suite
# default to `--release`. A debug cockpit grinds; a release cockpit is snappy.

.DEFAULT_GOAL := run-cockpit

# Open the native cockpit window (release). The window opens INSTANTLY on the
# at-rest image and seeds the demo turns in live, after first paint (see
# landing.rs / run_window). Release keeps the executor turns you then drive fast.
.PHONY: run-cockpit
run-cockpit:
	cargo run --release

# Same window, debug profile — for fast *rebuilds* while iterating on UI code.
# Expect the embedded-executor turns to be slow; the window itself still opens
# instantly (the seeding just trickles in more slowly).
.PHONY: run-cockpit-debug
run-cockpit-debug:
	cargo run

# The CI / pug-handoff self-check: the four-surface killer demo through the real
# embedded executor, no window. Exits non-zero iff the headline contract breaks.
.PHONY: headless
headless:
	cargo run --release -- --headless

# Build only (release) — link the verified archive + gpui without opening a window.
.PHONY: build
build:
	cargo build --release

# The library test suite (release — the embedded executor is unbearably slow in
# debug; release runs it in seconds).
.PHONY: test
test:
	cargo test --release --no-default-features --features embedded-executor --lib

# The Lean-free, gpui-free thin path (the eventual seL4 protection-domain client).
.PHONY: build-sel4-thin
build-sel4-thin:
	cargo build --no-default-features --features sel4-thin
