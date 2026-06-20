# sel4/gpu-driver-vm/Makefile — M-a of the GPU driver-VM path:
# boot a minimal Linux GUEST under the seL4 Microkit VMM on qemu_virt_aarch64.
#
# This is the FIRST rung toward real-GPU acceleration for the deos cockpit
# (docs/desktop-os-research/SEL4-GPU-DRIVER-VM.md). It is a DISJOINT workstream:
# it does NOT touch sel4/Makefile, sel4/dregg-pd/, sel4/render-pd/, or any shared
# .system file. Everything it produces lives under this directory + $(LIBVMM_DIR).
#
# The VMM itself is the external au-ts/libvmm project (the Microkit SDK ships the
# hypervisor-capable kernel + the vCPU primitives, but NO VMM). libvmm targets the
# SAME Microkit SDK 2.2.0 we already have installed, and its qemu target uses the
# SAME QEMU line dregg already boots — so M-a is fetch-and-build, no kernel compile
# (libvmm fetches the guest Linux + initrd by hash from trustworthy.systems).
#
# Usage:
#   make -C sel4/gpu-driver-vm fetch-libvmm   # clone libvmm at the pinned rev
#   make -C sel4/gpu-driver-vm run            # build + boot the Linux guest in QEMU
#   make -C sel4/gpu-driver-vm doctor         # check the host has what it needs

# ── Configuration ───────────────────────────────────────────────────────────
MICROKIT_SDK ?= $(HOME)/sel4-sdk/microkit-sdk-2.2.0
BOARD        ?= qemu_virt_aarch64
MICROKIT     := $(MICROKIT_SDK)/bin/microkit

# libvmm: the Microkit VMM. Vendored under this dir so the dregg-pd workspace is
# untouched. Pin a commit when we adopt it for real (libvmm is main-only / in-dev).
LIBVMM_REPO ?= https://github.com/au-ts/libvmm
LIBVMM_REV  ?= main
LIBVMM_DIR  ?= $(CURDIR)/libvmm

# libvmm's simple example builds a Linux-guest image for $(BOARD). Its build dir.
EXAMPLE_DIR := $(LIBVMM_DIR)/examples/simple
EXAMPLE_BUILD ?= $(CURDIR)/build

# libvmm's toolchain is the full LLVM suite (clang/ld.lld/llvm-ar/llvm-ranlib/
# llvm-objcopy). Homebrew keeps `llvm` keg-only, so its bin is NOT on the default
# PATH (bare `llvm-ar` is missing even though clang/ld.lld resolve from elsewhere).
# Prepend it so the whole suite resolves. Override LLVM_BIN if yours lives elsewhere.
LLVM_BIN ?= $(shell brew --prefix llvm 2>/dev/null)/bin
export PATH := $(LLVM_BIN):$(PATH)

.PHONY: all run fetch-libvmm build doctor clean help

help:
	@echo "M-a: boot a Linux guest under the seL4 Microkit VMM (qemu_virt_aarch64)"
	@echo "  make doctor        — verify host toolchain + SDK (hypervisor kernel, clang, dtc, qemu)"
	@echo "  make fetch-libvmm  — clone au-ts/libvmm ($(LIBVMM_REV)) into ./libvmm"
	@echo "  make build         — build the libvmm 'simple' Linux-guest image against our SDK"
	@echo "  make run           — build + boot the guest in QEMU (serial in/out)"
	@echo "  make clean         — remove ./build (keeps ./libvmm)"

all: build

# ── doctor: prove the host has the pieces M-a needs ─────────────────────────
doctor:
	@echo "== Microkit SDK =="
	@test -x "$(MICROKIT)" && echo "  microkit tool: $(MICROKIT)" || \
		(echo "  MISSING microkit tool at $(MICROKIT) — run ../setup.sh" && exit 1)
	@echo "== hypervisor-capable kernel (required to host a VMM) =="
	@grep -q "CONFIG_ARM_HYPERVISOR_SUPPORT  1" \
		"$(MICROKIT_SDK)/board/$(BOARD)/debug/include/kernel/gen_config.h" \
		&& echo "  CONFIG_ARM_HYPERVISOR_SUPPORT = 1  (OK)" \
		|| (echo "  kernel lacks ARM_HYPERVISOR_SUPPORT — wrong SDK/board" && exit 1)
	@echo "== host build tools =="
	@command -v clang   >/dev/null && echo "  clang   OK" || echo "  clang   MISSING (brew install llvm)"
	@command -v ld.lld  >/dev/null && echo "  ld.lld  OK" || echo "  ld.lld  MISSING (brew install lld)"
	@command -v llvm-ar >/dev/null && echo "  llvm-ar OK ($$(command -v llvm-ar))" \
		|| echo "  llvm-ar MISSING — set LLVM_BIN (brew --prefix llvm: $(LLVM_BIN))"
	@command -v dtc     >/dev/null && echo "  dtc     OK" || echo "  dtc     MISSING (brew install dtc)"
	@command -v qemu-system-aarch64 >/dev/null && echo "  qemu-system-aarch64 OK" \
		|| echo "  qemu-system-aarch64 MISSING (brew install qemu)"
	@command -v make    >/dev/null && echo "  make    OK"

# ── fetch-libvmm: vendor the VMM (the one missing piece) ────────────────────
fetch-libvmm:
	@if [ -d "$(LIBVMM_DIR)/.git" ]; then \
		echo "libvmm already at $(LIBVMM_DIR); checking out $(LIBVMM_REV)"; \
		git -C "$(LIBVMM_DIR)" fetch --quiet && git -C "$(LIBVMM_DIR)" checkout --quiet "$(LIBVMM_REV)"; \
	else \
		echo "cloning $(LIBVMM_REPO) @ $(LIBVMM_REV) into $(LIBVMM_DIR)"; \
		git clone --recurse-submodules "$(LIBVMM_REPO)" "$(LIBVMM_DIR)"; \
		git -C "$(LIBVMM_DIR)" checkout "$(LIBVMM_REV)"; \
		git -C "$(LIBVMM_DIR)" submodule update --init --recursive; \
	fi

# ── build: link the Linux-guest Microkit image via libvmm's example ─────────
# libvmm's example/simple fetches the guest Linux kernel + initrd by hash from
# trustworthy.systems on first build (needs network), builds the DTB, compiles
# the VMM PD, and links the Microkit image. Toolchain is clang/ld.lld/dtc — all
# present per `make doctor`.
build:
	@test -d "$(EXAMPLE_DIR)" || (echo "libvmm not fetched — run 'make fetch-libvmm' first" && exit 1)
	$(MAKE) -C "$(EXAMPLE_DIR)" MICROKIT_BOARD=$(BOARD) MICROKIT_SDK=$(MICROKIT_SDK) \
		BUILD_DIR=$(EXAMPLE_BUILD)

# ── run: build + boot the guest. The QEMU line MATCHES dregg's QEMU_AARCH64 ──
# (libvmm's own 'qemu' target uses the identical machine/cpu/mem; we invoke it so
# the loader addr + image name stay in sync with whatever libvmm emits).
run:
	@test -d "$(EXAMPLE_DIR)" || (echo "libvmm not fetched — run 'make fetch-libvmm' first" && exit 1)
	$(MAKE) -C "$(EXAMPLE_DIR)" MICROKIT_BOARD=$(BOARD) MICROKIT_SDK=$(MICROKIT_SDK) \
		BUILD_DIR=$(EXAMPLE_BUILD) qemu

clean:
	rm -rf "$(EXAMPLE_BUILD)"
