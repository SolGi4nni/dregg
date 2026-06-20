// build.rs — link the lavapipe ICD (its Mesa component archives + the static
// LLVM 20.1.8 archive group) + the C render driver + the C++ runtime + libdrm
// into the render-PD root task.
//
// THE LINK REALITY (measured — see WIRING.md "The static link"):
// `scripts/build-mesa-lavapipe-elf.sh` produces `out/mesa-elf/libvulkan_lvp.so`,
// a self-contained software-Vulkan ICD (Mesa+lavapipe+llvmpipe objects + static
// LLVM linked in; clean DT_NEEDED, NO libLLVM). But the render-PD target
// (`aarch64-sel4-roottask-musl`) is FULLY STATIC (`crt-static-default`, no
// dynamic loader in-PD) — it cannot load a `.so`. So the PD links the SAME inputs
// the `.so` was built from, as static archives, under a `--start-group`, exactly
// as executor-rootserver links the Lean closure:
//   * the Mesa component archives (liblavapipe_st.a, libgallium.a, libllvmpipe.a,
//     libvulkan_util.a, libnir.a, libvtn.a, libcompiler.a, libmesa_util*.a,
//     libloader.a, libz.a, libblake3.a, ...) pulled --whole-archive (the ICD
//     entry points + the gallium/llvmpipe driver register via constructors);
//   * the static LLVM 20.1.8 archive set (the JIT — Orc/MCJIT/ExecutionEngine/
//     RuntimeDyld + AArch64 codegen), --start-group (mutually recursive);
//   * libdrm (the headless-link satisfier — never called at runtime offscreen);
//   * the aarch64-linux-musl GCC libstdc++/libsupc++/libgcc group;
//   * the seL4 musl libc.a (via -lc from the target link args).
//
// These archive trees are BUILD OUTPUTS of the gate scripts. The durable banked
// artifact today is the `.so`; the component `.a`s live in the gate build trees
// (`$MESA_CROSS_BUILD`, `$LLVM_CROSS_BUILD`, default /tmp/...). When present, this
// build emits the full link line. When absent, it still type-checks the Rust PD +
// the W→X syscall handler (the link is what needs the archives) and prints a clear
// note — so the PD shell + the one new OS demand are reviewable before the (heavy)
// archive provisioning.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let out = crate_dir.join("out");
    let musl_sel4 = out.join("musl-sel4"); // seL4/musllibc: include + lib/libc.a

    // The gate build trees (overridable; defaults match the gate scripts).
    let mesa_build = PathBuf::from(
        env::var("MESA_CROSS_BUILD").unwrap_or_else(|_| "/tmp/mesa-cross-musl".into()),
    );
    let llvm_build = PathBuf::from(
        env::var("LLVM_CROSS_BUILD").unwrap_or_else(|_| "/tmp/llvm-cross-musl".into()),
    );
    let mesa_src = PathBuf::from(env::var("MESA_SRC").unwrap_or_else(|_| "/tmp/mesa-src".into()));

    println!("cargo:rerun-if-changed=scripts/driver-render.c");
    println!("cargo:rerun-if-changed=scripts/llvm-target-diag.c");
    println!("cargo:rerun-if-changed=scripts/musl-compat.c");
    println!("cargo:rerun-if-changed=build.rs");

    let cc = env::var("DREGG_SEL4_MUSL_CC")
        .unwrap_or_else(|_| "aarch64-linux-musl-gcc".to_string());

    // (1) Compile the C render driver against the seL4 musl + Mesa's Vulkan
    //     headers (Mesa ships them in its source tree — no Vulkan SDK needed).
    let vk_inc = mesa_src.join("include");
    let driver_o = out.join("driver-render.o");
    if musl_sel4.join("include").is_dir() && vk_inc.join("vulkan").is_dir() {
        let status = Command::new(&cc)
            .args(["-O2", "-ffreestanding", "-fno-stack-protector", "-c"])
            .arg("-isystem").arg(musl_sel4.join("include"))
            .arg("-I").arg(&vk_inc)
            .arg("scripts/driver-render.c")
            .arg("-o").arg(&driver_o)
            .status();
        match status {
            Ok(s) if s.success() => {
                println!("cargo:rustc-link-arg={}", driver_o.display());
            }
            other => {
                println!("cargo:warning=driver-render.c compile failed/absent ({other:?}); link will be incomplete");
            }
        }

        // The LLVM-target-registration diagnostic/lever (scripts/llvm-target-diag.c):
        // drives LLVMInitializeAArch64Target* explicitly + prints what the registry
        // resolves for the process triple, right before vkCreateDevice. No headers
        // needed (LLVM-C symbols forward-declared); compiled like the driver.
        let diag_o = out.join("llvm-target-diag.o");
        let status = Command::new(&cc)
            .args(["-O2", "-ffreestanding", "-fno-stack-protector", "-c"])
            .arg("-isystem").arg(musl_sel4.join("include"))
            .arg("scripts/llvm-target-diag.c")
            .arg("-o").arg(&diag_o)
            .status();
        match status {
            Ok(s) if s.success() => {
                println!("cargo:rustc-link-arg={}", diag_o.display());
            }
            other => {
                println!("cargo:warning=llvm-target-diag.c compile failed/absent ({other:?}); the JIT-target lever will be absent");
            }
        }
    } else {
        println!(
            "cargo:warning=seL4 musl headers ({}) or Mesa Vulkan headers ({}) not present — \
             run scripts/provision-sel4.sh + the gate scripts. Building the Rust PD shell + the \
             W->X syscall handler only (no lavapipe link).",
            musl_sel4.join("include").display(),
            vk_inc.display(),
        );
    }

    // (2) Link the lavapipe ICD's static component archives (--whole-archive: the
    //     ICD entry points + the gallium/llvmpipe driver self-register via ctors)
    //     + the static LLVM group + libdrm + the C++ runtime.
    let mesa_arcs = mesa_component_archives(&mesa_build);
    let llvm_arcs = llvm_archives(&llvm_build);
    let have_mesa = mesa_arcs.iter().all(|p| p.exists()) && !mesa_arcs.is_empty();
    let have_llvm = !llvm_arcs.is_empty();

    if have_mesa && have_llvm {
        // The lavapipe TARGET glue object (`lavapipe_target.c.o`): meson compiles
        // it directly INTO the `.so`, so it is in NO `.a`. It defines the sw
        // winsys screen factory (`sw_screen_create_vk`) the pipe-loader calls. Add
        // it as a direct object.
        let target_o = mesa_build
            .join("src/gallium/targets/lavapipe/libvulkan_lvp.so.p/lavapipe_target.c.o");
        if target_o.exists() {
            println!("cargo:rustc-link-arg={}", target_o.display());
        } else {
            println!("cargo:warning=lavapipe_target.c.o not found at {} — sw_screen_create_vk will be undefined", target_o.display());
        }

        // The musl-compat shim (scripts/musl-compat.c): provides the handful of
        // libc functions the lean seL4 musl fork lacks but Mesa/LLVM reference
        // (secure_getenv/qsort_r/c23_timespec_get/getrandom/memfd_create/
        // reallocarray) + stubs the pthread cancellation-point asm
        // (__syscall_cp_asm/__cp_*) the `aarch64_sel4` musl ARCH omits — safe
        // because LP_NUM_THREADS=0 means no threads/cancellation. Wrapped in
        // --whole-archive so `--gc-sections` (active on this target) cannot drop
        // the definitions before the later Mesa/LLVM archives reference them.
        let compat_o = compile_musl_compat(&cc, &out, &musl_sel4);

        // Mesa components: whole-archive so the Vulkan ICD symbols + the driver
        // descriptor constructors + the compat shim are all retained (reached by
        // name / ctor / late-archive reference, not by direct call).
        println!("cargo:rustc-link-arg=--whole-archive");
        if let Some(o) = &compat_o {
            println!("cargo:rustc-link-arg={}", o.display());
        }
        for a in &mesa_arcs {
            println!("cargo:rustc-link-arg={}", a.display());
        }
        println!("cargo:rustc-link-arg=--no-whole-archive");

        // Static LLVM 20.1.8: the JIT. Mutually recursive → one big group.
        println!("cargo:rustc-link-arg=--start-group");
        for a in &llvm_arcs {
            println!("cargo:rustc-link-arg={}", a.display());
        }
        println!("cargo:rustc-link-arg=--end-group");

        // libdrm (the headless link satisfier; never called offscreen). Prefer a
        // cross-built static libdrm.a if the gate provisioned one.
        if let Some(libdrm) = find_libdrm() {
            println!("cargo:rustc-link-arg={}", libdrm.display());
        } else {
            println!("cargo:warning=libdrm.a not found in the musl sysroot — run the gate's build-libdrm-elf.sh");
        }

        // The C++ runtime (libstdc++/libsupc++/libgcc) — Mesa + LLVM are hosted
        // C++. From the aarch64-linux-musl GCC; grouped (mutually recursive).
        for lib in cxx_runtime_archives() {
            let s = lib.to_string_lossy();
            if s.starts_with("--") {
                println!("cargo:rustc-link-arg={s}");
            } else if lib.exists() {
                println!("cargo:rustc-link-arg={s}");
            } else {
                println!("cargo:warning=C++ runtime archive missing: {s}");
            }
        }
        println!("cargo:rustc-link-search=native={}", musl_sel4.join("lib").display());
    } else {
        println!(
            "cargo:warning=lavapipe archive trees not present (mesa@{} present={}, llvm@{} present={}). \
             Run scripts/build-mesa-lavapipe-elf.sh (which builds them). The PD will not link the \
             render path yet; the Rust shell + the W->X syscall handler still type-check.",
            mesa_build.display(), have_mesa, llvm_build.display(), have_llvm,
        );
    }
}

/// Compile the musl-compat shim (the few libc symbols the lean seL4 musl fork
/// lacks + the cancellation-point asm stubs). Returns the object path on success.
fn compile_musl_compat(cc: &str, out: &Path, musl_sel4: &Path) -> Option<PathBuf> {
    let src = Path::new("scripts/musl-compat.c");
    if !src.exists() || !musl_sel4.join("include").is_dir() {
        return None;
    }
    let o = out.join("musl-compat.o");
    let status = Command::new(cc)
        .args(["-O2", "-ffreestanding", "-fno-stack-protector", "-c"])
        .arg("-isystem").arg(musl_sel4.join("include"))
        .arg(src)
        .arg("-o").arg(&o)
        .status();
    match status {
        Ok(s) if s.success() => Some(o),
        other => {
            println!("cargo:warning=musl-compat.c compile failed ({other:?})");
            None
        }
    }
}

/// The Mesa component archives the lavapipe `.so` is built from, in dependency
/// order (callers → callees), as produced by `scripts/build-mesa-lavapipe-elf.sh`
/// in `$MESA_CROSS_BUILD`. Pulled `--whole-archive` by the caller.
fn mesa_component_archives(b: &Path) -> Vec<PathBuf> {
    let rel = [
        "src/gallium/frontends/lavapipe/liblavapipe_st.a",
        "src/gallium/drivers/llvmpipe/libllvmpipe.a",
        "src/gallium/auxiliary/libgallium.a",
        "src/gallium/winsys/sw/wrapper/libwsw.a",
        "src/gallium/winsys/sw/null/libws_null.a",
        "src/gallium/auxiliary/pipe-loader/libpipe_loader_static.a",
        "src/vulkan/util/libvulkan_util.a",
        "src/compiler/spirv/libvtn.a",
        "src/compiler/nir/libnir.a",
        "src/compiler/libcompiler.a",
        "src/compiler/isaspec/libisaspec.a",
        "src/util/libmesa_util.a",
        "src/util/libmesa_util_sse41.a",
        // NOTE: `libmesa_util_c11.a` (Mesa's C11-threads shim: thrd_*/mtx_*/cnd_*/
        // call_once) is DELIBERATELY omitted — the seL4 musl libc already defines
        // those 14 symbols, so linking both is a duplicate-symbol collision. The
        // seL4 musl provides the C11 threads ABI, and with LP_NUM_THREADS=0
        // lavapipe never spawns a thread anyway, so the musl definitions suffice.
        "src/util/blake3/libblake3.a",
        "src/util/libxmlconfig.a",
        "src/loader/libloader.a",
        "subprojects/zlib-1.3.1/libz.a",
    ];
    rel.iter().map(|r| b.join(r)).collect()
}

/// The static LLVM 20.1.8 archive set in `$LLVM_CROSS_BUILD/lib` (the cross-built
/// JIT). All of them — they are mutually recursive, the caller wraps them in a
/// `--start-group`.
fn llvm_archives(b: &Path) -> Vec<PathBuf> {
    let libdir = b.join("lib");
    let mut v = Vec::new();
    if let Ok(rd) = std::fs::read_dir(&libdir) {
        for e in rd.flatten() {
            let p = e.path();
            if p.extension().map(|x| x == "a").unwrap_or(false)
                && p.file_name()
                    .and_then(|n| n.to_str())
                    .map(|n| n.starts_with("libLLVM"))
                    .unwrap_or(false)
            {
                v.push(p);
            }
        }
    }
    v.sort();
    v
}

/// A cross-built static libdrm.a, if the gate provisioned one into the musl
/// sysroot. (lavapipe never calls into it offscreen; it satisfies the link.)
fn find_libdrm() -> Option<PathBuf> {
    let sysroot = PathBuf::from(
        "/opt/homebrew/opt/aarch64-unknown-linux-musl/toolchain/aarch64-unknown-linux-musl",
    );
    for cand in ["lib/libdrm.a", "usr/lib/libdrm.a"] {
        let p = sysroot.join(cand);
        if p.exists() {
            return Some(p);
        }
    }
    None
}

/// The static C++ runtime + libgcc archives from the aarch64-linux-musl GCC,
/// wrapped in a group (libstdc++ <-> libgcc_eh <-> libsupc++ are mutually
/// recursive). Same set executor-rootserver uses.
fn cxx_runtime_archives() -> Vec<PathBuf> {
    let base = env::var("DREGG_MUSL_TOOLCHAIN").unwrap_or_else(|_| {
        "/opt/homebrew/Cellar/aarch64-unknown-linux-musl/15.2.0/toolchain".to_string()
    });
    let base = PathBuf::from(base);
    let stdcpp = base.join("aarch64-unknown-linux-musl/lib64");
    let gcc = base.join("lib/gcc/aarch64-unknown-linux-musl/15.2.0");
    let mut v = vec![PathBuf::from("--start-group")];
    v.push(stdcpp.join("libstdc++.a"));
    v.push(stdcpp.join("libsupc++.a"));
    v.push(gcc.join("libgcc.a"));
    v.push(gcc.join("libgcc_eh.a"));
    v.push(PathBuf::from("--end-group"));
    v
}
