/* loader.ld — linker script for the rust-sel4 sel4-kernel-loader on
 * qemu-arm-virt aarch64, for a STANDALONE cargo build (the nix build supplies an
 * equivalent layout via its layered sysroot; a plain `cargo build` has none, so
 * --gc-sections drops .text.startup and the loader ELF comes out as a 7 KB
 * data-only stub with entry 0x0 — the boot wall characterized in WALL-roottask.md).
 *
 * It (1) sets ENTRY(_start) so the asm entry is a GC root and the ELF entry is
 * correct, (2) KEEPs .text.startup (head.S `_start`) + the exception vectors,
 * (3) lays out text/rodata/data/bss at the loader image-base, and (4) defines
 * the BSS bounds head.S clears (__bss_start/_end). The image-base itself is set
 * by the loader build.rs via --image-base (kernel phys end + headroom); this
 * script uses that base implicitly by not hard-coding addresses (the
 * --image-base link-arg positions the first section).
 *
 * Symbols left to Rust/asm (do NOT define here): _start, secondary_entry,
 * arch_main, arm_vector_table, __primary_stack_bottom, loader_level_0_table,
 * kernel_boot_level_0_table (all #[no_mangle] / .global in the crate).
 */

ENTRY(_start)

SECTIONS
{
    /* The first output section starts at the --image-base the build.rs passes.
     * .text.startup (head.S `_start`) MUST be first so execution begins at the
     * image base. */
    .text : {
        KEEP(*(.text.startup))
        *(.text .text.*)
    }

    .rodata : {
        *(.rodata .rodata.*)
        *(.got .got.*)
        *(.gcc_except_table .gcc_except_table.*)
    }

    /* The exception vector table needs 2 KiB (0x800) alignment per the AArch64
     * VBAR_EL2 requirement (arm_vector_table is .align 11 in the asm). */
    . = ALIGN(2048);
    .vectors : {
        KEEP(*(.vectors .vectors.*))
        KEEP(*(.text.vectors))
    }

    .data : {
        *(.data .data.*)
    }

    .bss : {
        __bss_start = .;
        *(.bss .bss.*)
        *(COMMON)
        . = ALIGN(16);
        __bss_end = .;
    }
    . = ALIGN(4096);
    _end = .;

    /DISCARD/ : {
        *(.note .note.*)
        *(.comment .comment.*)
        *(.eh_frame .eh_frame.*)
        *(.eh_frame_hdr)
        *(.interp)
        *(.dynamic)
        *(.dynsym .dynstr .hash .gnu.hash)
    }
}
