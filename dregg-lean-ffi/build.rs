// build.rs — wire the Rust binary to the compiled Lean kernel + Lean runtime.
//
// We link against:
//   * libdregg_lean.a — a single static archive of the native objects emitted by the
//     Lean compiler for `Dregg2.Exec.FFI` and its ENTIRE transitive dependency
//     closure (Dregg2 modules + mathlib + batteries + aesop + Qq + … — ~8200 .o).
//     The archive lives next to this build.rs; it was produced by compiling each
//     module's `.c` (lake's `:c` facet) with `leanc -c` and archiving with `llvm-ar`.
//   * the Lean runtime + stdlib in the elan toolchain `lib/lean` dir — STATIC by default
//     (leancpp/Init/Std/Lean/leanrt + gmp/uv/c++), or SHARED (libleanshared + Lake_shared)
//     when `DREGG_LEAN_LINK=shared` (the cdylib link mode, see `shared_link_mode`).
//
// Toolchain paths are discovered from `lake env` (LEAN_SYSROOT) with a fallback to the
// pinned elan toolchain, so this stays robust to elan being on PATH.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Locate the project's `metatheory` Lean directory relative to this crate, so
/// `lake env` runs against the project's pinned toolchain regardless of the host
/// (no hardcoded absolute paths — works on macOS dev boxes and the Linux deploy
/// box alike). `CARGO_MANIFEST_DIR` is `.../dregg-lean-ffi`; the sibling is
/// `.../metatheory`. An explicit `DREGG_METATHEORY_DIR` override wins if set.
fn metatheory_dir() -> Option<PathBuf> {
    if let Ok(dir) = std::env::var("DREGG_METATHEORY_DIR") {
        let p = PathBuf::from(dir);
        if p.join("lean-toolchain").exists() {
            return Some(p);
        }
    }
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let candidate = crate_dir.parent().map(|p| p.join("metatheory"));
    candidate.filter(|p| p.join("lean-toolchain").exists())
}

fn lean_sysroot() -> Option<PathBuf> {
    // Prefer `lake env` (authoritative for the project's toolchain). `DREGG_LEAN_SYSROOT`
    // overrides for environments where `lake` is not on PATH at build time.
    if let Ok(s) = std::env::var("DREGG_LEAN_SYSROOT") {
        if !s.trim().is_empty() {
            return Some(PathBuf::from(s.trim()));
        }
    }
    if let Some(meta) = metatheory_dir() {
        if let Ok(out) = Command::new("lake")
            .args(["env", "printenv", "LEAN_SYSROOT"])
            .current_dir(&meta)
            .output()
        {
            let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
            if !s.is_empty() {
                return Some(PathBuf::from(s));
            }
        }
    }
    None
}

/// Flatten an IR-relative `.c` path into the splice object name the archive uses, matching the
/// shell script: `Dregg2/Exec/FFI.c` → `Dregg2_Exec_FFI.o` (path separators → `_`). Keeping the
/// exact same naming is what lets us REPLACE (not duplicate) the old Dregg2 members on re-splice.
fn splice_obj_name(ir_root: &Path, c: &Path) -> String {
    let rel = c.strip_prefix(ir_root).unwrap_or(c);
    let stem = rel.with_extension("");
    let mut name: String = stem
        .components()
        .map(|comp| comp.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join("_");
    name.push_str(".o");
    name
}

/// `true` iff `target` is missing or older than `src` (the "recompile this" predicate — mirrors the
/// script's `[ ! -f "$out" ] || [ "$c" -nt "$out" ]`). Treats unreadable mtimes as "stale" so we
/// fail toward recompiling rather than shipping a stale object.
fn newer_than(src: &Path, target: &Path) -> bool {
    let Ok(target_meta) = std::fs::metadata(target) else {
        return true;
    };
    let (Ok(src_m), Ok(tgt_m)) = (
        std::fs::metadata(src).and_then(|m| m.modified()),
        target_meta.modified(),
    ) else {
        return true;
    };
    src_m > tgt_m
}

/// Recursively collect every regular file under `dir` (used to emit `rerun-if-changed` for the
/// whole Lean `Dregg2` source tree, so a no-op cargo build truly skips the closure rebuild).
fn collect_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_files(&path, out);
        } else {
            out.push(path);
        }
    }
}

/// Produce / refresh `libdregg_lean.a` next to build.rs by (1) `lake build`-ing the FFI module's
/// `:c` facet, (2) `leanc -c`-compiling each freshly-emitted `Dregg2/**/*.c` whose `.c` is newer
/// than its cached `.o`, and (3) splicing ONLY those `Dregg2_*.o` back into the existing archive —
/// preserving the ~5600 expensive mathlib/batteries/aesop dependency objects untouched.
///
/// Incremental + cached: `lake` is itself incremental, the `leanc` step is guarded on
/// `.c`-newer-than-`.o`, and the (relatively expensive) `ar` extract/repack only runs when at least
/// one Dregg2 object actually changed or the archive lacks Dregg2 members. `rerun-if-changed` is
/// emitted by the caller for the source tree + toolchain marker, so a genuine no-op cargo build does
/// not even re-enter this function.
fn build_dregg2_archive(meta: &Path, sysroot: &Path, archive: &Path, out_dir: &Path) {
    // (1) Refresh the Lean `:c` facets. `lake build` is incremental; building the FFI module pulls
    // in (and emits `:c` for) its whole Dregg2 transitive closure.
    let inc = sysroot.join("include");
    let ir_root = meta.join(".lake/build/ir");
    let dregg2_ir = ir_root.join("Dregg2");

    // We build `Dregg2.Exec.FFI` (the executor exports) PLUS the verified-gate modules that live
    // OUTSIDE its import closure — `Dregg2.Distributed.{FinalityGate,StrandAdmission}` and
    // `Dregg2.Exec.DistributedExports` (the CapTP+coord decision gates). The splice compiles every
    // `Dregg2/**/*.c` present in the IR tree, so each of these must be `lake build`-t for its `.c` to
    // exist and be spliced in. Building them explicitly here (rather than relying on a prior full
    // `lake build` of the root) is what lets a FRESH lane (e.g. a persvati build dir with no warm
    // `.lake`) still emit and splice the gate exports. Each is incremental: an already-built module is
    // a no-op. A failure on one is non-fatal — we splice whatever `:c` facets exist.
    let lake_targets = [
        "Dregg2.Exec.FFI",
        "Dregg2.Distributed.FinalityGate",
        "Dregg2.Distributed.StrandAdmission",
        "Dregg2.Exec.DistributedExports",
    ];
    let lake_status = Command::new("lake")
        .arg("build")
        .args(lake_targets)
        .current_dir(meta)
        .status();
    match lake_status {
        Ok(s) if s.success() => {}
        Ok(s) => {
            println!(
                "cargo:warning=dregg-lean-ffi: `lake build` of the FFI + gate modules exited {s} — \
                 using whatever `:c` facets already exist; the spliced archive may be stale."
            );
        }
        Err(e) => {
            println!(
                "cargo:warning=dregg-lean-ffi: could not run `lake build` ({e}) — is elan/lake on \
                 PATH? Falling back to the existing archive (if any)."
            );
            return;
        }
    }

    // The `:c` facet must have landed for us to compile anything.
    if !dregg2_ir.exists() {
        println!(
            "cargo:warning=dregg-lean-ffi: no `:c` IR at {} after `lake build` — cannot compile the \
             Dregg2 native objects. Run `lake build Dregg2.Exec.FFI` in metatheory and re-check.",
            dregg2_ir.display()
        );
        return;
    }

    // Persistent object cache (so the `.c`-newer-than-`.o` guard survives across cargo builds).
    let obj_dir = out_dir.join("dregg2_closure_objs");
    if let Err(e) = std::fs::create_dir_all(&obj_dir) {
        println!(
            "cargo:warning=dregg-lean-ffi: cannot create {} ({e})",
            obj_dir.display()
        );
        return;
    }

    // (2) Compile each Dregg2 `.c` newer than its cached `.o`, in parallel up to the CPU count.
    let mut c_files = Vec::new();
    collect_files(&dregg2_ir, &mut c_files);
    c_files.retain(|p| p.extension().map(|e| e == "c").unwrap_or(false));
    c_files.sort();

    // The exact set of object names we expect from the CURRENT source. Used to (a) drive the
    // splice and (b) prune STALE cached objects whose `.c` was deleted/renamed — otherwise a
    // removed module's old `Dregg2_*.o` would keep getting spliced back in (dangling/duplicate
    // symbols). We treat such a prune as a change so the splice picks up the removal.
    let expected: std::collections::HashSet<String> = c_files
        .iter()
        .map(|c| splice_obj_name(&ir_root, c))
        .collect();
    let mut pruned = false;
    if let Ok(entries) = std::fs::read_dir(&obj_dir) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            if name.starts_with("Dregg2_") && name.ends_with(".o") && !expected.contains(&name) {
                let _ = std::fs::remove_file(entry.path());
                pruned = true;
            }
        }
    }

    let mut jobs: Vec<(PathBuf, PathBuf)> = Vec::new();
    for c in &c_files {
        let obj = obj_dir.join(splice_obj_name(&ir_root, c));
        if newer_than(c, &obj) {
            jobs.push((c.clone(), obj));
        }
    }

    let recompiled = !jobs.is_empty() || pruned;
    if !jobs.is_empty() {
        println!(
            "cargo:warning=dregg-lean-ffi: compiling {} changed Dregg2 C facet(s) via leanc …",
            jobs.len()
        );
        let ncpu = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .max(1);
        let failed = std::sync::atomic::AtomicBool::new(false);
        let jobs_ref = &jobs;
        let next = std::sync::atomic::AtomicUsize::new(0);
        std::thread::scope(|scope| {
            for _ in 0..ncpu {
                scope.spawn(|| loop {
                    let i = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    let Some((c, obj)) = jobs_ref.get(i) else {
                        break;
                    };
                    // `-fPIC` so the spliced objects are position-independent: the SAME archive
                    // then serves both link modes (static bins AND the `DREGG_LEAN_LINK=shared`
                    // cdylib link, e.g. the sdk-py pyo3 module). No-op on macOS (PIC is the
                    // default); on Linux it guards against a leanc default change (leanc
                    // currently compiles PIC there too — Lean plugins are dlopen'd).
                    let status = Command::new("lake")
                        .args(["env", "leanc", "-c", "-fPIC", "-I"])
                        .arg(&inc)
                        .arg(c)
                        .arg("-o")
                        .arg(obj)
                        .current_dir(meta)
                        .status();
                    let ok = matches!(status, Ok(s) if s.success());
                    if !ok {
                        // Drop a stale/partial object so the next build retries this `.c`.
                        let _ = std::fs::remove_file(obj);
                        failed.store(true, std::sync::atomic::Ordering::SeqCst);
                        println!(
                            "cargo:warning=dregg-lean-ffi: leanc failed on {}",
                            c.display()
                        );
                    }
                });
            }
        });
        if failed.load(std::sync::atomic::Ordering::SeqCst) {
            println!(
                "cargo:warning=dregg-lean-ffi: at least one Dregg2 C facet failed to compile — \
                 NOT re-splicing the archive (it keeps its previous, consistent contents)."
            );
            return;
        }
    }

    // (3) Splice. Only pay the extract/repack cost when something actually changed, or when the
    // archive is missing Dregg2 members entirely (e.g. a freshly-seeded dependency-only base).
    let needs_splice = recompiled || !archive_has_dregg2(archive);
    if !needs_splice {
        return;
    }

    if !archive.exists() {
        println!(
            "cargo:warning=dregg-lean-ffi: base archive {} is ABSENT — it must hold the ~5600 \
             precompiled mathlib/batteries/aesop dependency objects, which are EXPENSIVE to \
             regenerate. Run `./scripts/bootstrap.sh` from the repo root: it checks the toolchain \
             + mathlib pin, lake-builds the executor, seeds this archive once, and verifies the \
             link (afterwards plain `cargo build` keeps it fresh automatically). Building \
             marshal-only for now.",
            archive.display()
        );
        return;
    }

    if let Err(e) = splice_objects(archive, &obj_dir, out_dir) {
        println!(
            "cargo:warning=dregg-lean-ffi: archive splice failed ({e}) — the archive was left \
             unchanged; a previous-but-consistent build will be linked."
        );
        return;
    }

    // (4) Closure-completion. The freshly-built Dregg2 objects may import NEW dependency modules
    // (e.g. a `Mathlib.Order.Extension.Linear` that a concurrent edit just added) whose initializer
    // objects are NOT in the frozen base archive's dependency closure. Splicing in only the Dregg2
    // objects would then leave a dangling `_initialize_<dep>` undefined symbol and the FINAL Rust
    // link fails. So we close the archive: detect undefined `_initialize_*` symbols, compile the
    // matching `.c` from the Lean source/dependency IR trees, splice them in, and repeat until the
    // archive is self-contained (or no resolvable `.c` remains — which we surface loudly).
    complete_initializer_closure(meta, sysroot, archive, out_dir);

    // (5) Reachability GC. Closure-completion makes the archive self-LINKING, but the base still
    // carries every dependency object it was ever seeded with — including the mathlib CategoryTheory/
    // Tactic objects the import-trimmed FFI closure no longer references. Drop every member NOT
    // reachable, by symbol, from the `dregg_*` exports. This is the durable payoff of the import-graph
    // split: without it the next splice would re-bloat the archive back to its seeded size.
    //
    // ESCAPE HATCH (`DREGG_LEAN_FFI_NO_ARCHIVE_GC=1`): the GC's symbol-reachability BFS chases only
    // UNDEFINED-symbol edges, so if the closure-completion pass (step 4) seeded an archive whose
    // dependency members reference mathlib FUNCTION symbols that no kept member leaves UNDEFINED (e.g.
    // after a hand re-seed of the FULL dependency closure), the GC can drop the very mathlib members
    // those functions need — leaving `_lp_mathlib_*` unresolved at the final Rust link. When a FULL
    // archive was just restored out-of-band, set this to keep EVERY member (correct, larger) rather
    // than risk the destructive prune. Off by default (the GC stays the steady-state size payoff).
    if std::env::var("DREGG_LEAN_FFI_NO_ARCHIVE_GC").as_deref() == Ok("1") {
        println!(
            "cargo:warning=dregg-lean-ffi: DREGG_LEAN_FFI_NO_ARCHIVE_GC=1 — skipping archive \
             reachability GC, keeping every member (full self-linking archive)."
        );
    } else {
        gc_unreachable_members(archive, out_dir);
    }
}

/// Discover every `.lake/build/ir` directory that can supply a `.c` for the dependency closure:
/// the project's own IR, each git-package IR (`.lake/packages/*/.lake/build/ir`), and each
/// `type:path` dependency's IR (its `dir` is recorded in `lake-manifest.json`; we scan the manifest
/// text for `"dir": "..."` rather than pull a JSON crate into build-deps).
fn discover_ir_roots(meta: &Path) -> Vec<PathBuf> {
    let mut roots = Vec::new();
    let project_ir = meta.join(".lake/build/ir");
    if project_ir.is_dir() {
        roots.push(project_ir);
    }
    let pkgs = meta.join(".lake/packages");
    if let Ok(entries) = std::fs::read_dir(&pkgs) {
        for entry in entries.flatten() {
            let ir = entry.path().join(".lake/build/ir");
            if ir.is_dir() {
                roots.push(ir);
            }
        }
    }
    // `type:path` deps (e.g. a local mathlib checkout): pull their `dir` from the manifest.
    if let Ok(text) = std::fs::read_to_string(meta.join("lake-manifest.json")) {
        for raw in text.split("\"dir\":") {
            // The value is the first quoted string after the key.
            if let Some(start) = raw.find('"') {
                if let Some(end) = raw[start + 1..].find('"') {
                    let dir = &raw[start + 1..start + 1 + end];
                    let p = meta.join(dir).join(".lake/build/ir");
                    if p.is_dir() && !roots.iter().any(|r| r == &p) {
                        roots.push(p);
                    }
                }
            }
        }
    }
    roots
}

/// Lean's C-symbol mangling of a module path: each path component has its INTERNAL underscores
/// doubled (`_`→`__`), then the components are joined with a single `_`. So `A/B/CommMon_.c` →
/// `A_B_CommMon__` — which is exactly the `<flat>` that appears in `_initialize_<lib>_<flat>`. This
/// is what lets the resolver match modules whose name itself contains `_` (e.g. mathlib's `CommMon_`,
/// `Mon_`), which a naive `/`→`_` flatten would get wrong (one `_` instead of two).
fn lean_mangle_relpath(rel: &Path) -> String {
    rel.with_extension("")
        .components()
        .map(|comp| comp.as_os_str().to_string_lossy().replace('_', "__"))
        .collect::<Vec<_>>()
        .join("_")
}

/// Index every `.c` under the IR roots by its Lean-mangled module name (see `lean_mangle_relpath`,
/// e.g. `Mathlib/Order/Extension/Linear.c` → `Mathlib_Order_Extension_Linear`). An undefined
/// `_initialize_<lib>_<flat>` symbol then resolves by stripping the `_initialize_` prefix and
/// matching some suffix of the remainder against this index (the leading `<lib>` token is dropped).
fn build_cfile_index(roots: &[PathBuf]) -> std::collections::HashMap<String, PathBuf> {
    let mut index = std::collections::HashMap::new();
    for root in roots {
        let mut files = Vec::new();
        collect_files(root, &mut files);
        for c in files {
            if c.extension().map(|e| e == "c").unwrap_or(false) {
                if let Ok(rel) = c.strip_prefix(root) {
                    let flat = lean_mangle_relpath(rel);
                    // First writer wins; module names are unique across roots in practice.
                    index.entry(flat).or_insert(c);
                }
            }
        }
    }
    index
}

/// The Lean module initializers that are UNDEFINED in the archive AS A WHOLE: referenced (`U`) by
/// some member but DEFINED (`T`) by NO member. (`nm -u` is unreliable on archives — it lists symbols
/// undefined in individual members even when another member defines them — so we run full `nm` once
/// and compute the U-minus-T set ourselves.) These are the genuine dangling dependency edges the
/// final Rust link would fail on; closure-completion must supply each one's defining object.
fn undefined_initializers(archive: &Path) -> Vec<String> {
    let Ok(out) = Command::new("nm").arg(archive).output() else {
        return Vec::new();
    };
    let text = String::from_utf8_lossy(&out.stdout);
    let mut defined = std::collections::HashSet::new();
    let mut referenced = std::collections::HashSet::new();
    for line in text.lines() {
        // `nm` archive symbol lines come in two shapes:
        //   "                 U _sym"   (undefined: type letter, then symbol)
        //   "0000000000001234 T _sym"   (defined: address, type letter, symbol)
        // Other lines (blank, "archive.a:", "obj.o:") have no type+symbol and are skipped.
        let toks: Vec<&str> = line.split_whitespace().collect();
        let (ty, sym) = match toks.as_slice() {
            [ty, sym] if ty.len() == 1 => (*ty, *sym), // undefined / no-address
            [_addr, ty, sym] if ty.len() == 1 => (*ty, *sym), // defined / with-address
            _ => continue,
        };
        let name = sym.trim_start_matches('_');
        if let Some(rest) = name.strip_prefix("initialize_") {
            // The toolchain stdlib initializers (Init/Std/Lean/Lake) are supplied by the sysroot
            // static libs the FINAL Rust link pulls in (rustc-link-lib=static={Init,Std,Lean,Lake});
            // they have no `.c` in the project/dependency IR and are NOT ours to splice. Skip them so
            // closure-completion chases only genuinely-missing in-closure modules.
            let toolchain = ["Init", "Std", "Lean", "Lake"]
                .iter()
                .any(|lib| rest == *lib || rest.starts_with(&format!("{lib}_")));
            if toolchain {
                continue;
            }
            if ty == "U" {
                referenced.insert(name.to_string());
            } else {
                defined.insert(name.to_string());
            }
        }
    }
    let mut missing: Vec<String> = referenced.difference(&defined).cloned().collect();
    missing.sort();
    missing
}

/// Map a bare initializer symbol (`initialize_<lib>_<flat>`) to its source `.c` via the index. The
/// `<lib>` token is a single library name (no internal-underscore doubling); we strip `initialize_`,
/// then strip a KNOWN library token + `_`, leaving exactly the Lean-mangled `<flat>` index key. This
/// is unambiguous (vs suffix-guessing, which breaks on `__`-mangled names like `CommMon__`). We try
/// the known tokens longest-first so e.g. `LeanSearchClient` is preferred over a shorter prefix.
fn resolve_initializer_cfile<'a>(
    sym: &str,
    index: &'a std::collections::HashMap<String, PathBuf>,
) -> Option<(String, &'a PathBuf)> {
    let rest = sym.strip_prefix("initialize_")?;
    // Library tokens that prefix a module initializer (the project libs + every dependency package).
    // `Init`/`Std`/`Lean`/`Lake` are filtered out earlier (sysroot-provided), so they need not appear.
    let mut libs = [
        "Dregg2",
        "Metatheory",
        "mathlib",
        "aesop",
        "batteries",
        "importGraph",
        "LeanSearchClient",
        "plausible",
        "proofwidgets",
        "Qq",
        "Cli",
    ];
    libs.sort_by_key(|l| std::cmp::Reverse(l.len()));
    for lib in libs {
        if let Some(flat) = rest.strip_prefix(lib).and_then(|r| r.strip_prefix('_')) {
            if let Some(cfile) = index.get(flat) {
                return Some((flat.to_string(), cfile));
            }
        }
    }
    None
}

/// Iteratively add the dependency-closure objects the freshly-spliced Dregg2 objects need, until the
/// archive has no resolvable undefined `_initialize_*` edge left. Each pass compiles the missing
/// `.c` (cached by flattened name under OUT_DIR) and splices them in; new objects can introduce
/// further deps, hence the loop. Bounded to avoid runaway; unresolved symbols are surfaced loudly.
fn complete_initializer_closure(meta: &Path, sysroot: &Path, archive: &Path, out_dir: &Path) {
    let inc = sysroot.join("include");
    let dep_dir = out_dir.join("dregg2_closure_deps");
    if std::fs::create_dir_all(&dep_dir).is_err() {
        return;
    }
    let roots = discover_ir_roots(meta);
    let index = build_cfile_index(&roots);

    for pass in 0..16 {
        let undefined = undefined_initializers(archive);
        if undefined.is_empty() {
            return;
        }
        // Resolve as many as we can to source `.c`; compile those not already cached.
        let mut to_add: Vec<(String, PathBuf)> = Vec::new(); // (objname, objpath)
        let mut unresolved = Vec::new();
        for sym in &undefined {
            match resolve_initializer_cfile(sym, &index) {
                Some((flat, cfile)) => {
                    let obj = dep_dir.join(format!("{flat}.o"));
                    if newer_than(cfile, &obj) {
                        // `-fPIC` for the same shared-link-compatibility reason as the splice
                        // compile above (one archive, both link modes).
                        let status = Command::new("lake")
                            .args(["env", "leanc", "-c", "-fPIC", "-I"])
                            .arg(&inc)
                            .arg(cfile)
                            .arg("-o")
                            .arg(&obj)
                            .current_dir(meta)
                            .status();
                        if !matches!(status, Ok(s) if s.success()) {
                            let _ = std::fs::remove_file(&obj);
                            println!(
                                "cargo:warning=dregg-lean-ffi: closure leanc failed on {} (dep of \
                                 {sym})",
                                cfile.display()
                            );
                            continue;
                        }
                    }
                    to_add.push((format!("{flat}.o"), obj));
                }
                None => unresolved.push(sym.clone()),
            }
        }

        if to_add.is_empty() {
            if !unresolved.is_empty() {
                println!(
                    "cargo:warning=dregg-lean-ffi: {} undefined initializer(s) could not be \
                     resolved to a `.c` in the IR trees (e.g. {}); the archive may not self-link. \
                     Re-seed the closure (scripts/seed-dregg2-closure.sh) if the dependency set \
                     changed substantially.",
                    unresolved.len(),
                    unresolved.first().map(|s| s.as_str()).unwrap_or("?")
                );
            }
            return;
        }

        if let Err(e) = add_objects_to_archive(archive, &to_add, out_dir) {
            println!("cargo:warning=dregg-lean-ffi: closure splice failed on pass {pass} ({e}).");
            return;
        }
        println!(
            "cargo:warning=dregg-lean-ffi: closure pass {pass}: added {} dependency object(s).",
            to_add.len()
        );
    }
    println!(
        "cargo:warning=dregg-lean-ffi: closure completion hit the 16-pass bound — archive may \
         still have undefined initializers. Consider re-seeding the closure."
    );
}

/// **Archive reachability GC — the import-graph-trim payoff made durable.**
///
/// After the splice + closure-completion the archive self-links, but it still carries every
/// dependency object the BASE archive was ever seeded with — including the thousands of mathlib
/// `CategoryTheory`/`Tactic` objects that the (now import-trimmed) FFI closure no longer references.
/// Lean runs an `initialize_` per ARCHIVED module at boot, so those dead members are not just dead
/// weight — they inflate the linked binary and the wasm executor. `-Oz`/`--gc-sections` cannot strip
/// them (each module's initializer is reachable from its own object's ctor), so we garbage-collect at
/// the ARCHIVE level: keep only members reachable, by symbol, from the `dregg_*` FFI exports.
///
/// Reachability is exact and conservative: a member is kept iff it is the export-defining root, or it
/// defines a symbol that some kept member leaves undefined (`U`). Toolchain-supplied symbols (resolved
/// by the final Rust link against the sysroot `Init`/`Std`/`Lean`/`Lake` static libs) need no archive
/// member, so members that ONLY serve them drop out. If `nm` is unavailable or the computed reachable
/// set looks implausibly small (a parse failure), we SKIP the GC and keep the (correct, larger) archive
/// — never risk a broken link to save bytes.
fn gc_unreachable_members(archive: &Path, out_dir: &Path) {
    let Ok(out) = Command::new("nm").arg("-A").arg(archive).output() else {
        return;
    };
    let text = String::from_utf8_lossy(&out.stdout);
    use std::collections::{HashMap, HashSet};
    // member -> (defined syms, undefined syms);  symbol -> members defining it.
    let mut undef: HashMap<String, HashSet<String>> = HashMap::new();
    let mut sym_def_in: HashMap<String, HashSet<String>> = HashMap::new();
    let mut members: HashSet<String> = HashSet::new();
    let mut roots: HashSet<String> = HashSet::new();
    for line in text.lines() {
        // `nm -A` location-prefixed forms (see `members_defining_project_initializers`):
        //   macOS/llvm: `<archive>:<member.o>: <addr> T _sym`  /  `<archive>:<member.o>:    U _sym`
        //   GNU:        `<archive>[<member.o>]: <addr> T _sym`
        let Some((prefix, rest)) = line.split_once(": ") else {
            continue;
        };
        let prefix = prefix.trim_end_matches(']');
        let member = prefix.rsplit(['/', ':', '[']).next().unwrap_or(prefix);
        if !member.ends_with(".o") {
            continue;
        }
        let toks: Vec<&str> = rest.split_whitespace().collect();
        let (ty, sym) = match toks.as_slice() {
            [ty, sym] if ty.len() == 1 => (*ty, *sym),
            [_addr, ty, sym] if ty.len() == 1 => (*ty, *sym),
            _ => continue,
        };
        members.insert(member.to_string());
        if ty == "U" || ty == "u" {
            undef
                .entry(member.to_string())
                .or_default()
                .insert(sym.to_string());
        } else {
            sym_def_in
                .entry(sym.to_string())
                .or_default()
                .insert(member.to_string());
            // Root: any member defining a `_dregg_*` FFI export (the C-ABI entry points).
            if sym.trim_start_matches('_').starts_with("dregg_") {
                roots.insert(member.to_string());
            }
        }
    }
    if members.is_empty() || roots.is_empty() {
        // Parse failure or no exports found — do not risk a destructive GC.
        return;
    }
    // BFS: keep a member, then chase each of its undefined symbols to the member(s) defining them.
    let mut reach: HashSet<String> = HashSet::new();
    let mut queue: Vec<String> = roots.iter().cloned().collect();
    while let Some(member) = queue.pop() {
        if !reach.insert(member.clone()) {
            continue;
        }
        if let Some(us) = undef.get(&member) {
            for u in us {
                if let Some(defs) = sym_def_in.get(u) {
                    for dm in defs {
                        if !reach.contains(dm) {
                            queue.push(dm.clone());
                        }
                    }
                }
            }
        }
    }
    let unreachable = members.len().saturating_sub(reach.len());
    if unreachable == 0 {
        return; // already minimal.
    }
    // Sanity floor: the FFI closure genuinely needs hundreds of dependency members; if the reachable
    // set collapsed below a plausible floor the `nm` parse misfired — keep the larger, correct archive.
    if reach.len() < 200 {
        println!(
            "cargo:warning=dregg-lean-ffi: archive GC computed only {} reachable members (< floor) — \
             skipping the prune to avoid a destructive parse error.",
            reach.len()
        );
        return;
    }
    // Repack keeping only reachable members. Extract to scratch, delete the unreachable, `ar rcs`.
    let work = out_dir.join("dregg2_gc_work");
    if work.exists() {
        let _ = std::fs::remove_dir_all(&work);
    }
    if std::fs::create_dir_all(&work).is_err() {
        return;
    }
    if !matches!(Command::new("ar").arg("x").arg(archive).current_dir(&work).status(), Ok(s) if s.success())
    {
        return;
    }
    let mut kept: Vec<String> = Vec::new();
    if let Ok(entries) = std::fs::read_dir(&work) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            if !name.ends_with(".o") {
                continue;
            }
            if reach.contains(&name) {
                kept.push(name);
            } else {
                let _ = std::fs::remove_file(entry.path());
            }
        }
    }
    if kept.is_empty() {
        return;
    }
    kept.sort();
    let tmp = out_dir.join("libdregg_lean.a.gc");
    let _ = std::fs::remove_file(&tmp);
    if !matches!(
        Command::new("ar").arg("rcs").arg(&tmp).args(&kept).current_dir(&work).status(),
        Ok(s) if s.success()
    ) {
        return;
    }
    let _ = Command::new("ranlib").arg(&tmp).status();
    if std::fs::rename(&tmp, archive).is_err() {
        // Cross-device rename fallback: copy.
        if std::fs::copy(&tmp, archive).is_ok() {
            let _ = std::fs::remove_file(&tmp);
        } else {
            return;
        }
    }
    println!(
        "cargo:warning=dregg-lean-ffi: archive GC pruned {unreachable} unreachable dependency \
         object(s) (kept {} reachable from the `dregg_*` exports).",
        kept.len()
    );
}

/// Add (replace) the given objects into the archive, preserving everything else. Like `splice_objects`
/// but for an arbitrary object set (the dependency-closure additions), and incremental — it does NOT
/// re-extract the whole archive; it uses `ar r` to insert/replace members by name, then `ranlib`.
fn add_objects_to_archive(
    archive: &Path,
    objs: &[(String, PathBuf)],
    out_dir: &Path,
) -> std::io::Result<()> {
    // Stage the objects under their archive member names in a scratch dir, then `ar r` them in.
    let stage = out_dir.join("dregg2_closure_stage");
    if stage.exists() {
        std::fs::remove_dir_all(&stage)?;
    }
    std::fs::create_dir_all(&stage)?;
    let mut names = Vec::new();
    for (name, path) in objs {
        std::fs::copy(path, stage.join(name))?;
        names.push(name.clone());
    }
    // `ar r <archive> *.o` inserts or replaces the named members in place (preserving the other
    // ~6100 members). We pass the absolute archive path and run in the stage dir for clean names.
    let r = Command::new("ar")
        .arg("r")
        .arg(archive)
        .args(&names)
        .current_dir(&stage)
        .status()?;
    if !r.success() {
        return Err(std::io::Error::other(format!("`ar r` exited {r}")));
    }
    let _ = Command::new("ranlib").arg(archive).status();
    let _ = std::fs::remove_dir_all(&stage);
    Ok(())
}

/// Whether the archive already contains any `Dregg2_*.o` member (via `ar t`). Used to force a
/// splice when the base archive is dependency-closure-only.
fn archive_has_dregg2(archive: &Path) -> bool {
    let Ok(out) = Command::new("ar").arg("t").arg(archive).output() else {
        return false;
    };
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .any(|l| l.trim().starts_with("Dregg2_") && l.trim().ends_with(".o"))
}

/// The set of archive MEMBER names (e.g. `Await.o`, `Dregg2_Spec_Await.o`) that define a project
/// module initializer (`_initialize_Dregg2_*` / `_initialize_Metatheory_*`). Computed with `nm -A`,
/// which prefixes each symbol line with the member location. The prefix format differs by platform:
///   * macOS/llvm-nm: `<archive>:<member.o>: <addr> T <sym>`
///   * GNU/binutils:  `<archive>[<member.o>]: <addr> T <sym>`
/// We extract the member by taking the basename of the path segment ending in `.o`, so the splice can
/// purge stale project objects regardless of how they were named when the base archive was seeded.
fn members_defining_project_initializers(archive: &Path) -> std::collections::HashSet<String> {
    let mut members = std::collections::HashSet::new();
    let Ok(out) = Command::new("nm").arg("-A").arg(archive).output() else {
        return members;
    };
    let text = String::from_utf8_lossy(&out.stdout);
    for line in text.lines() {
        // Only DEFINING (`T`) lines for a project initializer; skip undefined (`U`) references.
        if !(line.contains("T _initialize_Dregg2_") || line.contains("T _initialize_Metatheory_")) {
            continue;
        }
        // The location prefix is everything up to the first `: ` (space-separated from the address).
        let Some(prefix) = line.split(": ").next() else {
            continue;
        };
        // Strip a trailing `]` (GNU bracket form), then take the basename and keep it iff it's a `.o`.
        let prefix = prefix.trim_end_matches(']');
        let member = prefix.rsplit(['/', ':', '[']).next().unwrap_or(prefix);
        if member.ends_with(".o") {
            members.insert(member.to_string());
        }
    }
    members
}

/// Splice the freshly-built `Dregg2_*.o` into `archive`, preserving every non-project dependency
/// object. Extract → purge stale project members (by defined symbol, see above) → drop in the fresh
/// `Dregg2_*.o` → `ar rcs` + `ranlib`. Works in a scratch dir under `OUT_DIR` (writable, local).
fn splice_objects(archive: &Path, obj_dir: &Path, out_dir: &Path) -> std::io::Result<()> {
    let work = out_dir.join("dregg2_splice_work");
    if work.exists() {
        std::fs::remove_dir_all(&work)?;
    }
    std::fs::create_dir_all(&work)?;

    // Extract the existing archive (all ~6100 members) into the scratch dir.
    let extract = Command::new("ar")
        .arg("x")
        .arg(archive)
        .current_dir(&work)
        .status()?;
    if !extract.success() {
        return Err(std::io::Error::other(format!("`ar x` exited {extract}")));
    }

    // Purge EVERY stale project-module object, by DEFINED SYMBOL not just filename. The base archive
    // was historically seeded with SHORT member names (`Await.o`, `Transfer.o`, …) while our splice
    // uses flattened names (`Dregg2_Spec_Await.o`); a filename-only purge would leave the short-named
    // stale copies behind as DUPLICATE definitions — and, when a concurrent edit renames/deletes a
    // module, those stale copies carry dangling references to the old name (the empirical cause of the
    // `_initialize_…burnAWitness` / `_initialize_Metatheory_Metatheory_Core` link failures). So we
    // drop every extracted member that defines a `_initialize_Dregg2_*` or `_initialize_Metatheory_*`
    // symbol, then re-add ONLY the freshly compiled objects.
    let stale_members = members_defining_project_initializers(archive);
    for entry in std::fs::read_dir(&work)?.flatten() {
        let fname = entry.file_name();
        let name = fname.to_string_lossy();
        let is_flattened_project = (name.starts_with("Dregg2_") || name.starts_with("Metatheory_"))
            && name.ends_with(".o");
        if is_flattened_project || stale_members.contains(name.as_ref()) {
            std::fs::remove_file(entry.path())?;
        }
    }
    let mut dregg2_count = 0usize;
    for entry in std::fs::read_dir(obj_dir)?.flatten() {
        let name = entry.file_name();
        let name_s = name.to_string_lossy();
        if name_s.starts_with("Dregg2_") && name_s.ends_with(".o") {
            std::fs::copy(entry.path(), work.join(&name))?;
            dregg2_count += 1;
        }
    }

    // Repack into a fresh archive next to build.rs, then atomically swap it into place. `ar rcs`
    // over the entire member set (Dregg2 + preserved dependency closure) followed by `ranlib`
    // rebuilds the symbol index. We pass the member list explicitly to keep ordering deterministic.
    let members: Vec<PathBuf> = std::fs::read_dir(&work)?
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().map(|e| e == "o").unwrap_or(false))
        .collect();
    if members.is_empty() {
        return Err(std::io::Error::other(
            "no .o members after extract — refusing to repack",
        ));
    }

    let tmp_archive = out_dir.join("libdregg_lean.a.new");
    let _ = std::fs::remove_file(&tmp_archive);
    // `ar rcs <out> *.o` — build with relative paths from `work` to keep member names clean.
    let rel_members: Vec<String> = members
        .iter()
        .map(|p| p.file_name().unwrap().to_string_lossy().into_owned())
        .collect();
    let rcs = Command::new("ar")
        .arg("rcs")
        .arg(&tmp_archive)
        .args(&rel_members)
        .current_dir(&work)
        .status()?;
    if !rcs.success() {
        return Err(std::io::Error::other(format!("`ar rcs` exited {rcs}")));
    }
    let ranlib = Command::new("ranlib").arg(&tmp_archive).status();
    // ranlib is advisory: `ar s`/`rcs` already wrote a symbol table on most toolchains. Only warn.
    if !matches!(ranlib, Ok(s) if s.success()) {
        println!(
            "cargo:warning=dregg-lean-ffi: ranlib on the new archive did not succeed (continuing)."
        );
    }

    std::fs::rename(&tmp_archive, archive)?;
    let _ = std::fs::remove_dir_all(&work);
    println!(
        "cargo:warning=dregg-lean-ffi: spliced {dregg2_count} Dregg2 objects into {} ({} total members).",
        archive.display(),
        rel_members.len()
    );
    Ok(())
}

/// Probe the archive for an exported symbol via `nm`, so the C shim only declares string
/// bridges whose underlying Lean `@[export]` actually exists in THIS archive. A stale
/// archive missing a later export (e.g. `dregg_exec_handler_turn`) would otherwise leave a
/// dangling reference that `-dead_strip` resolves by dropping the WHOLE shim object — taking
/// the forest-auth + init bridges with it. We fail-closed: absent ⇒ the bridge is compiled out.
fn archive_exports(archive: &std::path::Path, symbol: &str) -> bool {
    let Ok(out) = Command::new("nm").arg(archive).output() else {
        return false;
    };
    let text = String::from_utf8_lossy(&out.stdout);
    // A DEFINED symbol shows in the text section as `T <name>`. The C symbol name is mangled
    // with a leading underscore on Mach-O (macOS) but NOT on ELF (Linux), so accept both
    // ` T _<symbol>` and ` T <symbol>`.
    let mach_o = format!(" T _{symbol}");
    let elf = format!(" T {symbol}");
    text.lines()
        .any(|l| l.trim_end().ends_with(&mach_o) || l.trim_end().ends_with(&elf))
}

/// Whether the SHARED link mode is selected (`DREGG_LEAN_LINK=shared`).
///
/// An ENV VAR, deliberately NOT a cargo feature: features UNIFY across a workspace
/// dependency graph (a cdylib member asking for shared linkage would flip every native
/// crate in the same build), while an env var stays local to the invoking build. The one
/// consumer today is the standalone sdk-py workspace (a pyo3 cdylib), whose
/// `.cargo/config.toml` `[env]` sets it.
///
/// WHY a cdylib cannot use the static mode on ELF: rustc BUNDLES `static=`-linked native
/// libraries into the rlib, and `libleanrt.a`'s mimalloc objects (`static.c.o`:
/// `mi_heap_default` & co.) use local-exec TLS — `R_X86_64_TPOFF32` relocations that the
/// linker rejects under `-shared` (Convergence round 7). The Lean toolchain ships the
/// whole runtime+stdlib built FOR shared use as `libleanshared.{so,dylib}` in
/// `$LEAN_SYSROOT/lib/lean`; shared mode links that instead of the static
/// {leancpp,Init,Std,Lean,leanrt,Lake,gmp,uv} set. Our spliced `libdregg_lean.a` is still
/// linked statically in both modes — it holds ONLY Lean-compiled MODULE objects (Dregg2 +
/// the mathlib/batteries/… dependency closure; never runtime members), all compiled
/// `-fPIC`, so its symbols are disjoint from leanshared's.
fn shared_link_mode() -> bool {
    println!("cargo:rerun-if-env-changed=DREGG_LEAN_LINK");
    match std::env::var("DREGG_LEAN_LINK") {
        Ok(v) if v == "shared" => true,
        Ok(v) if v.is_empty() || v == "static" => false,
        Ok(v) => {
            println!(
                "cargo:warning=dregg-lean-ffi: unknown DREGG_LEAN_LINK={v:?} (expected \
                 `shared` or `static`) — defaulting to the static link."
            );
            false
        }
        Err(_) => false,
    }
}

fn main() {
    println!("cargo::rustc-check-cfg=cfg(lean_lib_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_handler_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_finalize_gate_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_strand_admit_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_distributed_exports_present)");

    // ── PLATFORM GATE (polarity inversion, docs/FEATURE-HYGIENE.md §Lean): the link is
    // UNCONDITIONAL on native; the ONE opt-out is the `no-lean-link` platform feature, set
    // only by builds whose target cannot link libdregg_lean.a (wasm32, the SP1 zkvm guest).
    // We also hard-skip on those targets regardless of the feature — a wasm32 build that
    // forgot to wire `no-lean-link` should degrade to the marshal-only stubs, never attempt
    // a native-archive link. No archive refresh, no shim, no link directives: the crate
    // builds marshal-only and `lean_available()` is false.
    let no_lean_link = std::env::var_os("CARGO_FEATURE_NO_LEAN_LINK").is_some();
    let gate_arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
    let gate_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    if no_lean_link || gate_arch == "wasm32" || gate_os == "zkvm" {
        return;
    }

    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").expect("OUT_DIR set by cargo"));
    let lean_archive = crate_dir.join("libdregg_lean.a");

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=src/lean_init.c");

    // Resolve the toolchain + metatheory location up front so we can both (a) refresh the archive
    // from the Lean source when it changed and (b) drive the link below. `lean_sysroot()` honours
    // `DREGG_LEAN_SYSROOT`; `metatheory_dir()` honours `DREGG_METATHEORY_DIR`.
    let sysroot_opt = lean_sysroot();
    let meta_opt = metatheory_dir();

    // ── PRODUCE / REFRESH the archive from the Lean source (the linchpin). We watch the whole
    // `metatheory/Dregg2` source tree + the toolchain marker; when any of those change, build.rs
    // reruns and `build_dregg2_archive` does the incremental `lake build` → `leanc -c` → `ar`
    // splice. A genuine no-op cargo build does NOT rerun build.rs (no watched file changed), so the
    // ~6000-object closure is never needlessly regenerated. We deliberately do NOT
    // `rerun-if-changed=libdregg_lean.a`: that file is our OWN output (we rewrite it here), and
    // watching it would force a perpetual rebuild loop.
    if let Some(meta) = &meta_opt {
        let mut watched = Vec::new();
        collect_files(&meta.join("Dregg2"), &mut watched);
        for f in &watched {
            println!("cargo:rerun-if-changed={}", f.display());
        }
        println!(
            "cargo:rerun-if-changed={}",
            meta.join("lean-toolchain").display()
        );

        match &sysroot_opt {
            Some(sysroot) => build_dregg2_archive(meta, sysroot, &lean_archive, &out_dir),
            None => println!(
                "cargo:warning=dregg-lean-ffi: cannot resolve the Lean sysroot (no \
                 DREGG_LEAN_SYSROOT and `lake env` failed in metatheory/) — skipping the archive \
                 refresh; the existing archive (if any) is used as-is. The two common causes: \
                 (1) elan/lake is not installed or not on PATH; (2) the mathlib LOCAL-PATH \
                 dependency pinned in metatheory/lakefile.toml is missing on this machine. \
                 `./scripts/bootstrap.sh` (repo root) checks both and teaches the exact fix."
            ),
        }
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: metatheory/ not found (set DREGG_METATHEORY_DIR) — \
             cannot refresh libdregg_lean.a from Lean source; using the existing archive if present."
        );
    }

    if !lean_archive.exists() {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a absent — building MARSHAL-ONLY: \
             lean_available() will be false and the node falls back to the UNVERIFIED Rust \
             executor. To link the verified Lean kernel, run `./scripts/bootstrap.sh` from the \
             repo root (one command: it checks elan + the mathlib pin, lake-builds the executor, \
             seeds this archive once, and verifies the link). Afterwards plain `cargo build` \
             keeps the archive fresh automatically."
        );
        return;
    }

    // Resolve the Lean sysroot BEFORE committing to the `lean_lib_present` cfg: linking the
    // archive requires the Lean runtime/stdlib from the toolchain. If we cannot find it, we must
    // NOT advertise `lean_lib_present` (that cfg drives `lean_available()` and the FFI link), or
    // the build would either fail to link or falsely claim the Lean kernel is available.
    let Some(sysroot) = sysroot_opt else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a present but could not resolve the Lean \
             sysroot (no DREGG_LEAN_SYSROOT and `lake env` failed) — building marshal-only. \
             Install elan + the project toolchain (`./scripts/bootstrap.sh` checks everything \
             and teaches the fix), or set DREGG_LEAN_SYSROOT to the toolchain root."
        );
        return;
    };
    let lean_lib = sysroot.join("lib").join("lean");
    let lean_include = sysroot.join("include");

    println!("cargo:rustc-cfg=lean_lib_present");

    // The handler-cutover export is a SECONDARY path; older archives predate it. Only wire its
    // string bridge when the archive actually exports it (otherwise the dangling ref breaks the
    // whole shim under -dead_strip). The forest-auth gate is the load-bearing path and is always
    // present.
    let handler_present = archive_exports(&lean_archive, "dregg_exec_handler_turn");
    if handler_present {
        println!("cargo:rustc-cfg=dregg_handler_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_exec_handler_turn` — \
             the handler-cutover bridge is compiled out (forest-auth gate unaffected). \
             Rebuild the archive to enable shadow_exec_handler_turn."
        );
    }

    // The verified FINALITY GATE export (`dregg_blocklace_finalize`) lives in
    // `Dregg2.Distributed.FinalityGate`, a module OUTSIDE the FFI module's import closure. The
    // archive splice compiles every `Dregg2/**/*.c` present in the IR tree, so once the module has
    // been `lake build`- t its object is spliced in and this symbol appears. Until then (e.g. a
    // stale archive) we compile the bridge out and the node falls back to the un-gated path.
    let finalize_gate_present = archive_exports(&lean_archive, "dregg_blocklace_finalize");
    if finalize_gate_present {
        println!("cargo:rustc-cfg=dregg_finalize_gate_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_blocklace_finalize` — \
             the verified finality-gate bridge is compiled out (executor gate unaffected). \
             Rebuild the archive (it splices Dregg2.Distributed.FinalityGate) to enable the gate."
        );
    }

    // The verified STRAND-ADMISSION GATE export (`dregg_strand_admit`) lives in
    // `Dregg2.Distributed.StrandAdmission`, also OUTSIDE the FFI module's import closure. Same
    // splice/probe discipline as the finality gate: once the module is `lake build`-t its object is
    // spliced in (the self-linking closure follows the C shim's `initialize_…_StrandAdmission` ref)
    // and this symbol appears; until then we compile the bridge out and the federation falls back to
    // the Rust admission gate.
    let strand_admit_present = archive_exports(&lean_archive, "dregg_strand_admit");
    if strand_admit_present {
        println!("cargo:rustc-cfg=dregg_strand_admit_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_strand_admit` — \
             the verified strand-admission bridge is compiled out (federation falls back to the \
             Rust gate). Rebuild the archive (it splices Dregg2.Distributed.StrandAdmission) to \
             enable the Lean-backed F-4 admission gate."
        );
    }

    // The verified CapTP+coord DISTRIBUTED-EXPORTS module (`dregg_captp_validate_handoff` and its five
    // siblings) lives in `Dregg2.Exec.DistributedExports`, also OUTSIDE the FFI module's import
    // closure. Same splice/probe discipline: once the module is `lake build`-t its object is spliced
    // in (the self-linking closure follows the C shim's `initialize_…_DistributedExports` ref) and the
    // symbols appear; until then we compile the six bridges out and the captp/coord runtime falls back
    // to its native Rust gates. We probe a single representative export — they are all defined in the
    // same module, so they are present/absent together.
    let distributed_exports_present =
        archive_exports(&lean_archive, "dregg_captp_validate_handoff");
    if distributed_exports_present {
        println!("cargo:rustc-cfg=dregg_distributed_exports_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_captp_validate_handoff` — \
             the verified CapTP+coord decision bridges are compiled out (captp/coord fall back to \
             native Rust gates). Rebuild the archive (it splices Dregg2.Exec.DistributedExports) to \
             enable the Lean-backed handoff / GC-drop / pipeline / 2PC / causal / shared-budget gates."
        );
    }

    // Compile the C init shim (it uses the `static inline` runtime helpers from
    // <lean/lean.h>, which have no linkable symbol and so must be used from C).
    //
    // We suppress cc's automatic `rustc-link-lib` directive (`cargo_metadata(false)`)
    // and emit our own `+whole-archive` directive below. Reason: the final link runs
    // under `-Wl,-dead_strip` with `-nodefaultlibs`, and on macOS ld64 the shim's
    // single object is otherwise dead-stripped before the linker has recorded the
    // binary's undefined references to `dregg_ffi_init` / `dregg_exec_full_forest_auth_str`
    // (an archive-member-ordering hazard). Forcing the whole archive in guarantees the
    // bridge symbols are present regardless of link order — the empirical fix for the
    // `marshal_roundtrip` / `full_turn_differential` link failures.
    let mut shim = cc::Build::new();
    shim.file("src/lean_init.c").include(&lean_include);
    if handler_present {
        shim.define("DREGG_HANDLER_TURN", None);
    }
    if finalize_gate_present {
        shim.define("DREGG_FINALIZE_GATE", None);
    }
    if strand_admit_present {
        shim.define("DREGG_STRAND_ADMIT", None);
    }
    if distributed_exports_present {
        shim.define("DREGG_DISTRIBUTED_EXPORTS", None);
    }
    // We drive the link with `rustc-link-lib` / `rustc-link-search` directives, NOT
    // `rustc-link-arg`. WHY: with the package's `links = "dregg_lean"` key, build-script
    // `rustc-link-lib` / `rustc-link-search` directives PROPAGATE to every DOWNSTREAM binary
    // (the `dregg-turn` lean-shadow tests, the node, …) — whereas `rustc-link-arg` is local
    // to this crate's own targets only. The cross-crate propagation is exactly what the
    // shadow harness needs to resolve `dregg_ffi_init` / `dregg_exec_full_forest_auth_str`.
    //
    // The shim is linked `+whole-archive` so its single bridge object survives the final
    // `-Wl,-dead_strip` regardless of archive-member ordering (the empirical fix for the
    // earlier `Undefined symbols` link failures). `+whole-archive` is a link-LIB modifier,
    // so it propagates too.
    shim.cargo_metadata(false);
    shim.compile("dregg_ffi_shim");
    let target_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let shim_archive = out_dir.join("libdregg_ffi_shim.a");

    // We drive the link with `rustc-link-lib` / `rustc-link-search` directives ONLY. With the
    // package's `links = "dregg_lean"` key these PROPAGATE to EVERY target that links this
    // crate's rlib — the `dregg-turn` lean-shadow tests + node (downstream) AND this crate's
    // own bins/tests (which `use dregg_lean_ffi` and so link the rlib). Emitting `rustc-link-arg`
    // in ADDITION would DOUBLE-link the shim for the FFI-crate-internal consumers (they'd see
    // the shim both via the propagated lib AND the arg) → "duplicate symbol" errors. So: one
    // mechanism. The standalone differential bins each carry `use dregg_lean_ffi as _;` to force
    // the rlib edge so they inherit these propagated directives.
    //
    // The shim is linked `+whole-archive` so its single bridge object survives the final
    // `-Wl,-dead_strip` regardless of archive-member ordering (the empirical link-failure fix).
    let _ = shim_archive;
    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=static:+whole-archive=dregg_ffi_shim");
    println!("cargo:rustc-link-search=native={}", crate_dir.display());
    println!("cargo:rustc-link-lib=static=dregg_lean");
    println!("cargo:rustc-link-search=native={}", lean_lib.display());
    println!(
        "cargo:rustc-link-search=native={}",
        sysroot.join("lib").display()
    );
    if shared_link_mode() {
        // ── SHARED runtime link (`DREGG_LEAN_LINK=shared`, see `shared_link_mode`) ──
        // The runtime+stdlib come from the toolchain's shared libraries instead of the
        // static archives (whose leanrt/mimalloc members are illegal in a `-shared` ELF
        // link). Link, in leanc's own order, every shared shell the sysroot ships:
        //   * Init_shared / leanshared_1 / leanshared_2 — the symbol-partition shells
        //     (real partitions on Windows; export-empty alongside the full libleanshared
        //     on macOS, where nm shows the whole runtime in libleanshared itself). We
        //     link whichever exist so the set is right on every platform.
        //   * leanshared — the runtime + Init/Std/Lean + leancpp + gmp + uv.
        //   * Lake_shared — Lake lives OUTSIDE leanshared, and the dependency closure
        //     references it (importGraph → `initialize_Lake_Util_Casing`), mirroring the
        //     `static=Lake` line of the static mode.
        // No c++/gmp/uv directives: leanshared bundles gmp+uv and carries its own libc++
        // dependency.
        for name in [
            "Init_shared",
            "leanshared_1",
            "leanshared_2",
            "leanshared",
            "Lake_shared",
        ] {
            let dylib = lean_lib.join(format!("lib{name}.dylib"));
            let so = lean_lib.join(format!("lib{name}.so"));
            if dylib.exists() || so.exists() {
                println!("cargo:rustc-link-lib=dylib={name}");
            }
        }
        // rpath so THIS crate's own bins/tests resolve libleanshared at run time.
        // `rustc-link-arg` does NOT propagate through the `links` key (unlike the
        // link-lib/link-search directives above), so downstream cdylibs — sdk-py — emit
        // their own rpath from their own build.rs.
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lean_lib.display());
        println!(
            "cargo:rustc-link-arg=-Wl,-rpath,{}",
            sysroot.join("lib").display()
        );
    } else {
        for name in [
            "leancpp", "Init", "Std", "Lean", "leanrt", "Lake", "gmp", "uv",
        ] {
            println!("cargo:rustc-link-lib=static={name}");
        }
        if target_os == "macos" {
            println!("cargo:rustc-link-lib=dylib=c++");
        } else {
            // Lean's Linux toolchain compiles its C++ (leancpp et al.) against the
            // BUNDLED LLVM libc++ (`std::__1::` ABI), shipped as static archives in
            // the sysroot's lib/ (already on the search path above). Linking the
            // GNU libstdc++ instead leaves `std::__1::cout` & friends undefined —
            // the first-ever Linux link of the full archive (Convergence round 6)
            // caught exactly that. Order matters: c++ before c++abi.
            println!("cargo:rustc-link-lib=static=c++");
            println!("cargo:rustc-link-lib=static=c++abi");
        }
    }
}
