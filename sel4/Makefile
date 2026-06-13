# sel4/Makefile — build path for the dregg seL4 image (Microkit assembly).
#
# STATUS (2026-06-13): the seL4 Microkit SDK + rust-sel4 toolchain are NOT
# present in the dregg authoring environment, so `make image` cannot run here.
# This Makefile is the DOCUMENTED, reviewable recipe. The one target that DOES
# run on a normal host — and that we verified — is `make verify-isolation`: it
# proves the verifier core links Lean-free (no libuv / no GMP / no Lean symbols),
# which is the precondition for the whole weekend win.
#
# To actually build the image you need, on a Linux box:
#   1. the seL4 Microkit SDK:   https://github.com/seL4/microkit   (provides
#      `microkit` the tool + board support packages).
#   2. the rust-sel4 toolchain: https://github.com/seL4/rust-sel4  (provides the
#      aarch64-sel4-microkit target spec + the `sel4-microkit` crate).
#   3. a nightly Rust with `build-std` (the seL4 target is `no_std`/tier-3).

# ── Configuration ───────────────────────────────────────────────────────────
MICROKIT_SDK ?= $(HOME)/microkit-sdk
BOARD        ?= qemu_virt_aarch64
CONFIG       ?= debug
SEL4_TARGET  ?= aarch64-sel4-microkit
BUILD        ?= build

VERIFIER_PD_ELF := $(BUILD)/dregg-verifier-pd.elf
IMAGE           := $(BUILD)/dregg.img
SYSTEM          := dregg.system

.PHONY: all image verifier-pd verify-isolation clean help

help:
	@echo "dregg seL4 scaffold targets:"
	@echo "  make verify-isolation  — HOST: prove the verifier core is Lean-free (RUNS HERE)"
	@echo "  make verifier-pd       — cross-build the verifier PD ELF (needs rust-sel4 toolchain)"
	@echo "  make image             — link the Microkit image from dregg.system (needs Microkit SDK)"
	@echo "  make run               — boot the image in QEMU (needs qemu-system-aarch64)"

# ── The HOST proof (runs in any dregg dev env) ──────────────────────────────
# Builds the verifier with `no-lean-link` and asserts the resulting binary has
# NO Lean/libuv/GMP linkage. This is the empirical isolation verdict.
verify-isolation:
	cargo build -p dregg-verifier --features no-lean-link
	@echo "--- linked dynamic libs (expect system libs only, NO libuv/libleanshared) ---"
	@otool -L ../target/debug/dregg-verifier 2>/dev/null || ldd ../target/debug/dregg-verifier 2>/dev/null || true
	@echo "--- Lean/libuv symbols (expect NONE) ---"
	@! nm ../target/debug/dregg-verifier 2>/dev/null | grep -iE "uv_run|lean_initialize|leanrt|__gmp" \
		&& echo "PASS: no Lean runtime symbols" || (echo "FAIL: Lean symbols present" && exit 1)

# ── Cross-build the verifier PD (needs the seL4 toolchain) ───────────────────
verifier-pd:
	cd verifier-pd && \
	cargo build --release \
		--target $(SEL4_TARGET) \
		-Z build-std=core,alloc,compiler_builtins \
		-Z build-std-features=compiler-builtins-mem
	mkdir -p $(BUILD)
	cp verifier-pd/target/$(SEL4_TARGET)/release/dregg-verifier-pd $(VERIFIER_PD_ELF)

# ── Link the Microkit image (needs the Microkit SDK `microkit` tool) ────────
image: verifier-pd
	$(MICROKIT_SDK)/bin/microkit $(SYSTEM) \
		--search-path $(BUILD) \
		--board $(BOARD) \
		--config $(CONFIG) \
		-o $(IMAGE) \
		-r $(BUILD)/report.txt

# ── Boot in QEMU ────────────────────────────────────────────────────────────
run: image
	qemu-system-aarch64 -machine virt -cpu cortex-a53 -m 256 -nographic \
		-device loader,file=$(IMAGE),addr=0x70000000,cpu-num=0 \
		-serial mon:stdio

clean:
	rm -rf $(BUILD) verifier-pd/target
