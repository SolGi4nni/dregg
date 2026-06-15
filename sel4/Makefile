# sel4/Makefile — build + boot the dregg Robigalia v0 seL4 image.
#
# This BOOTS on a native-macOS toolchain (Microkit SDK 2.2.0 + rust-sel4 +
# qemu-system-aarch64/riscv64). Run `./setup.sh` once to install deps + the SDK,
# then `make run` (aarch64) or `make run-riscv` (riscv64).
#
# Boot ladder (docs/SEL4-EMBEDDING.md §5), each an actual QEMU boot:
#   make run-m0   — M0: a Rust PD prints "dregg robigalia v0" on seL4.
#   make run-m1   — M1: the verifier PD (proof-in -> verdict-out contract).
#   make run-m2   — M2: the rbg DirectoryCell PD (the Robigalia heart).
#   make run-riscv— M5: M0 retargeted to qemu_virt_riscv64.
#   make run      — alias for run-m2 (the richest single-PD demo).

# ── Configuration ───────────────────────────────────────────────────────────
MICROKIT_SDK ?= $(HOME)/sel4-sdk/microkit-sdk-2.2.0
BOARD        ?= qemu_virt_aarch64
CONFIG       ?= debug
PD_DIR       := dregg-pd
BUILD        ?= build
MICROKIT     := $(MICROKIT_SDK)/bin/microkit

# The libsel4 headers rust-sel4's build.rs locates via $SEL4_INCLUDE_DIRS.
export SEL4_INCLUDE_DIRS := $(MICROKIT_SDK)/board/$(BOARD)/$(CONFIG)/include

# The aarch64 / riscv64 seL4 Microkit target specs (vendored in dregg-pd/targets).
AARCH64_TARGET := targets/aarch64-sel4-microkit.json
RISCV_TARGET   := targets/riscv64imac-sel4-microkit.json

CARGO_FLAGS := --release -Z json-target-spec

# QEMU: the qemu_virt_aarch64 Microkit kernel is built as a hypervisor, so the
# vCPU must have EL2 — `virtualization=on`.
QEMU_AARCH64 := qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 \
                -m 2G -nographic
QEMU_RISCV   := qemu-system-riscv64 -machine virt -m 2G -nographic

# The GRAPHICAL boot reuses the same EL2 `virt` machine but DROPS -nographic and
# adds a display device. We keep the kernel/vCPU flags but build the QEMU line
# explicitly (so the serial stays on stdio for boot diagnostics alongside the
# window). `-device ramfb` is the simplest display on `virt`: a RAM framebuffer
# the compositor-fb PD configures over fw_cfg + scans out.
QEMU_AARCH64_GRAPHICAL := qemu-system-aarch64 -machine virt,virtualization=on \
                -cpu cortex-a53 -m 2G -device ramfb
# macOS display backend. On Linux swap `cocoa,show-cursor=on` for `gtk` (or
# `sdl`); everything else is identical.
QEMU_DISPLAY ?= cocoa,show-cursor=on

.PHONY: all run run-m0 run-m1 run-m2 run-stark run-net run-assembly run-riscv \
        build-aarch64 build-assembly build-riscv build-graphical run-graphical \
        run-graphical-headless verify-isolation clean help

help:
	@echo "dregg Robigalia v0 seL4 image:"
	@echo "  ./setup.sh        — install deps + Microkit SDK (run once)"
	@echo "  make run          — boot the rbg DirectoryCell PD (M2) in QEMU"
	@echo "  make run-m0       — boot the 'dregg robigalia v0' banner PD (M0)"
	@echo "  make run-m1       — boot the verifier PD (M1)"
	@echo "  make run-m2       — boot the rbg DirectoryCell PD (M2)"
	@echo "  make run-stark    — boot the verifier-stark PD: real STARK on-device"
	@echo "  make run-net      — boot the net-driver PD: probe a REAL virtio-net (M3 edge)"
	@echo "  make run-assembly — boot the 5-PD FIRMAMENT (verifier+executor+persist+net+app)"
	@echo "  make run-graphical— boot the compositor-fb PD: REAL ramfb pixels in a QEMU window"
	@echo "  make run-graphical-headless — same image, -display none, serial-proves ramfb config"
	@echo "  make run-riscv    — boot M0 on qemu_virt_riscv64 (M5)"

all: build-aarch64

# ── Cross-build the PD ELFs (aarch64) ───────────────────────────────────────
build-aarch64:
	cd $(PD_DIR) && cargo build $(CARGO_FLAGS)

build-riscv:
	cd $(PD_DIR) && SEL4_INCLUDE_DIRS=$(MICROKIT_SDK)/board/qemu_virt_riscv64/$(CONFIG)/include \
		cargo build $(CARGO_FLAGS) --target $(RISCV_TARGET) -p dregg-m0-hello

# M5 full: build the verifier-stark heart organ + the rbg DirectoryCell heart
# for riscv64 (the same no_std PDs that boot M-STARK/M2 on aarch64; they are
# arch-agnostic — sel4-microkit + blake3/serde only). Its own target dir
# (target-riscv) so it never collides with the aarch64 `target/`.
build-riscv-full:
	cd $(PD_DIR) && SEL4_INCLUDE_DIRS=$(MICROKIT_SDK)/board/qemu_virt_riscv64/$(CONFIG)/include \
		CARGO_TARGET_DIR=target-riscv \
		cargo build $(CARGO_FLAGS) --target $(RISCV_TARGET) \
			-p dregg-verifier-stark-pd -p dregg-rbg-dir

# ── Link an image for one PD and boot it (aarch64) ──────────────────────────
# $1 = PD elf basename (no ext), $2 = system file, $3 = pd-xml-name
define LINK_AND_RUN_AARCH64
	mkdir -p $(BUILD)
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/$(1).elf $(BUILD)/
	printf '<?xml version="1.0" encoding="UTF-8"?>\n<system>\n  <protection_domain name="$(3)" priority="100" stack_size="0x10000">\n    <program_image path="$(1).elf" />\n  </protection_domain>\n</system>\n' > $(BUILD)/$(1).system
	$(MICROKIT) $(BUILD)/$(1).system --search-path $(BUILD) --board $(BOARD) --config $(CONFIG) -o $(BUILD)/$(1).img -r $(BUILD)/$(1).report.txt
	$(QEMU_AARCH64) -device loader,file=$(BUILD)/$(1).img,addr=0x70000000,cpu-num=0 -serial mon:stdio
endef

run: run-m2

run-m0: build-aarch64
	$(call LINK_AND_RUN_AARCH64,dregg-m0-hello,m0,dregg_m0)

run-m1: build-aarch64
	$(call LINK_AND_RUN_AARCH64,dregg-verifier-pd,m1,dregg_verifier)

run-m2: build-aarch64
	$(call LINK_AND_RUN_AARCH64,dregg-rbg-dir,m2,dregg_rbg_dir)

# M1+ : the verified-compute heart organ — a REAL plonky3-style STARK
# (BabyBear+BLAKE3+FRI) proved + verified on-device, with the anti-ghost tooth.
run-stark: build-aarch64
	$(call LINK_AND_RUN_AARCH64,dregg-verifier-stark-pd,mstark,dregg_verifier_stark)

# M3: the firmament's network EDGE — the virtio-net driver PD probing a REAL
# QEMU virtio-net-device on the mmio bus. The driver maps mmio slot 31 (base
# 0xa000000 + 31*0x200 = 0xa003e00; region phys_addr 0xa003000 + OFFSET 0xe00),
# reads the VirtIOHeader, confirms DeviceType::Network, and brings the device UP
# (prints its MAC). The QEMU flags below are what make the slot non-empty — the
# wall this clears was InvalidDeviceType(0) (an empty mmio slot).
run-net: build-aarch64
	mkdir -p $(BUILD)
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-net-driver-pd.elf $(BUILD)/
	$(MICROKIT) net-driver-only.system --search-path $(BUILD) --board $(BOARD) --config $(CONFIG) -o $(BUILD)/net-driver.img -r $(BUILD)/net-driver.report.txt
	$(QEMU_AARCH64) \
		-global virtio-mmio.force-legacy=false \
		-netdev user,id=net0 \
		-device virtio-net-device,netdev=net0,bus=virtio-mmio-bus.31 \
		-device loader,file=$(BUILD)/net-driver.img,addr=0x70000000,cpu-num=0 \
		-serial mon:stdio

# ── THE 5-PD FIRMAMENT ASSEMBLY (dregg.system) ──────────────────────────────
# Wire the real PDs into ONE booting multi-PD seL4 image (docs/FIRMAMENT.md §2):
#   verifier — dregg-verifier-stark-pd : a REAL BabyBear+BLAKE3+FRI STARK
#              proved+verified on-device (the bankable verified-compute HEART
#              ORGAN; anti-ghost teeth fire). Self-contains its proof — no Lean.
#   executor — dregg-executor-stub-pd  : the HEART SEAT. Holds the executor's
#              exact cap partition (turn_in R, commit_out RW; NO device/NIC cap)
#              until the verified Lean execFullForestG cross-compiles (THE
#              blocker, docs/SEL4-EMBEDDING.md §2). Writes the commit_out sentinel.
#   persist  — dregg-persist-stub-pd   : the durable-store seat. Maps commit_out
#              (R) ONLY and reads the executor's sentinel back — the cross-PD
#              channel proven live. The storage-device cap lands HERE (§3).
#   net      — dregg-net-driver-pd     : the EDGE. SOLE holder of the NIC cap +
#              virtio-mmio + DMA paddr + IRQ 79; probes a REAL virtio-net device
#              and brings the NIC UP (the n>1 end of the cap gradation, §3).
#   app      — dregg-rbg-dir           : a houyhnhnm app-PD (rbg DirectoryCell:
#              CAS + ACL + factory slot-caveat). Holds ONLY its own caps.
# The cap partition IS the trust boundary ("capabilities all the way down").
# QEMU carries the same -device virtio-net-device the net edge probes (slot 31).
build-assembly: build-aarch64
	cd $(PD_DIR) && cargo build $(CARGO_FLAGS) \
		-p dregg-verifier-stark-pd -p dregg-executor-stub-pd \
		-p dregg-persist-stub-pd -p dregg-net-driver-pd -p dregg-rbg-dir
	mkdir -p $(BUILD)
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-verifier-stark-pd.elf $(BUILD)/
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-executor-stub-pd.elf  $(BUILD)/
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-persist-stub-pd.elf   $(BUILD)/
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-net-driver-pd.elf     $(BUILD)/
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-rbg-dir.elf           $(BUILD)/
	$(MICROKIT) dregg.system --search-path $(BUILD) --board $(BOARD) --config $(CONFIG) -o $(BUILD)/dregg.img -r $(BUILD)/dregg.report.txt

run-assembly: build-assembly
	$(QEMU_AARCH64) \
		-global virtio-mmio.force-legacy=false \
		-netdev user,id=net0 \
		-device virtio-net-device,netdev=net0,bus=virtio-mmio-bus.31 \
		-device loader,file=$(BUILD)/dregg.img,addr=0x70000000,cpu-num=0 \
		-serial mon:stdio

# ── THE GRAPHICAL BOOT (dregg-graphical.system) ─────────────────────────────
# The compositor-fb PD drives a REAL framebuffer visible in a QEMU window: it is
# the SOLE holder of the fw_cfg engine MMIO cap (phys 0x9020000) + a 2 MiB DMA
# framebuffer region (its guest-PHYSICAL base handed to ramfb via region_paddr),
# configures QEMU's `ramfb` display over fw_cfg, and writes a deos splash (test
# pattern + banner) into the framebuffer (docs/desktop-os-research/
# GRAPHICAL-SEL4-BOOT.md). The bytes->glass path on seL4, end to end.
build-graphical:
	cd $(PD_DIR) && cargo build $(CARGO_FLAGS) -p dregg-compositor-fb-pd
	mkdir -p $(BUILD)
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-compositor-fb-pd.elf $(BUILD)/
	$(MICROKIT) dregg-graphical.system --search-path $(BUILD) --board $(BOARD) --config $(CONFIG) -o $(BUILD)/dregg-graphical.img -r $(BUILD)/dregg-graphical.report.txt

# THE VISIBLE WINDOW — run this for ember: a real QEMU window scanning out the
# PD's pixels. Serial stays on stdio so the boot diagnostics print alongside.
run-graphical: build-graphical
	$(QEMU_AARCH64_GRAPHICAL) \
		-display $(QEMU_DISPLAY) \
		-device loader,file=$(BUILD)/dregg-graphical.img,addr=0x70000000,cpu-num=0 \
		-serial mon:stdio

# Window-less proof (CI / background): the SAME image with -display none. The PD
# still configures ramfb + draws; its serial output proves resolution, fb phys
# addr, the etc/ramfb selector, and bytes written — verifiable with no window.
run-graphical-headless: build-graphical
	$(QEMU_AARCH64_GRAPHICAL) \
		-display none \
		-device loader,file=$(BUILD)/dregg-graphical.img,addr=0x70000000,cpu-num=0 \
		-serial mon:stdio

# ── M5: M0 on riscv64 ───────────────────────────────────────────────────────
run-riscv: build-riscv
	mkdir -p $(BUILD)
	cp $(PD_DIR)/target/riscv64imac-sel4-microkit/release/dregg-m0-hello.elf $(BUILD)/
	printf '<?xml version="1.0" encoding="UTF-8"?>\n<system>\n  <protection_domain name="dregg_m0" priority="100" stack_size="0x10000">\n    <program_image path="dregg-m0-hello.elf" />\n  </protection_domain>\n</system>\n' > $(BUILD)/m0-riscv.system
	$(MICROKIT) $(BUILD)/m0-riscv.system --search-path $(BUILD) --board qemu_virt_riscv64 --config $(CONFIG) -o $(BUILD)/m0-riscv.img -r $(BUILD)/m0-riscv.report.txt
	$(QEMU_RISCV) -kernel $(BUILD)/m0-riscv.img -serial mon:stdio

# ── The HOST proof: the verify core links Lean-free (runs anywhere) ──────────
verify-isolation:
	cargo build -p dregg-verifier --features no-lean-link
	@echo "--- linked dynamic libs (expect system libs only) ---"
	@otool -L ../target/debug/dregg-verifier 2>/dev/null || true
	@! nm ../target/debug/dregg-verifier 2>/dev/null | grep -iE "uv_run|lean_initialize|leanrt|__gmp" \
		&& echo "PASS: no Lean runtime symbols" || (echo "FAIL: Lean symbols present" && exit 1)

clean:
	rm -rf $(BUILD) $(PD_DIR)/target
