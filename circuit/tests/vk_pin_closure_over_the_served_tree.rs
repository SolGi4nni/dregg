//! ⚑⚑ **THE `vkPin` CLOSURE — every pinned program is a program THIS TREE HAS.**
//!
//! ## The class this exists to kill
//!
//! A `proof_bind` leg's `vk_pin` is nine `Faithful9` lanes of the bound program's SEMANTIC
//! FINGERPRINT. The fingerprint is `blake3::derive_key` over the canonical descriptor encoding, so
//! it **cannot be computed in Lean** — the Lean AIR author has to obtain the nine digits from a
//! Rust tool (`cargo run -p dregg-circuit --example conj_fingerprint`) and **write them down**.
//!
//! A written-down derived value goes stale. Measured over one week in this tree, the same shape
//! landed ten times:
//!
//! ```text
//! ABSORB / CHAINLINK / MINA_HEAD_VK_LANES stale against a re-emitted descriptor   3
//! two copies of one fingerprint constant differing at HEAD                        1
//! a pin left naming a program no descriptor in this tree had                      1
//! ```
//!
//! The existing gates for this are **per-pin and hand-written**: `mina_accumulator_head_proves`
//! knows that `MINA_HEAD_VK_LANES` pins `dregg-mina-lightclient-verify-v1`,
//! `mina_transcript_carrier_binding` knows three more, and so on. Each such gate carries its own
//! copy of the target name AND its own copy of `key_lanes9`. **A gate that must be extended by hand
//! for each new pin is a gate that a new pin does not get.** Every pin added since those tests were
//! written is ungated by construction.
//!
//! ## What this gate does instead
//!
//! It needs **no map from pin to target**, so there is nothing in it to keep in sync:
//!
//! 1. fingerprint EVERY descriptor the tree serves, giving `lanes → name`;
//! 2. walk EVERY descriptor's `proof_bind` legs and collect every `vk_pin`;
//! 3. resolve each pin **by search** through the fingerprints of step 1.
//!
//! A pin that resolves names a program this tree emits. A pin that resolves to nothing is the
//! defect — a deployed bind attesting a program that does not exist here — and it is loud whether
//! or not anyone remembered to write a test for that particular pin.
//!
//! ⚑ This is a gate over the **emitted artifacts**, not over the Lean literals. That is deliberate
//! and it is the stronger question: the Lean literal is upstream of the bytes, and it is the bytes a
//! verifier consumes. A Lean literal that went stale shows up here as an emitted pin that resolves
//! to nothing — provided the descriptor was re-emitted. Gating the *literal* against the *bytes* is
//! `descriptor_pin_literals_are_not_transcriptions.rs`.
//!
//! ⚠ **What this gate does NOT say.** It says each pin names *some* descriptor here. It does not say
//! it names the *intended* one — a pin that resolves to the wrong descriptor is a semantic error
//! this cannot see, and the per-pin gates above are what pin intent. Those remain load-bearing.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2, parse_vm_descriptor2};
use dregg_circuit::descriptor_ir2_canonical::effect_vm_descriptor2_semantic_fingerprint;
use dregg_circuit::effect_vm::key_limbs9;

/// The nine base-`2^29` key lanes of a 32-byte fingerprint, as the `i64`s a `vk_pin` carries.
///
/// ⚑ This calls the library's [`key_limbs9`] rather than re-deriving the shift arithmetic. Five test
/// files and one example in this tree each carry their own `fn key_lanes9` copy; that is the same
/// transcription defect as the constants, one level up, and this file does not add a sixth.
fn pin_lanes(fingerprint: &[u8; 32]) -> Vec<i64> {
    key_limbs9(fingerprint)
        .iter()
        .map(|l| i64::from(l.as_u32()))
        .collect()
}

/// Every descriptor JSON the tree serves, as `(display path, contents)`.
///
/// ⚑ `DREGG_DESCRIPTOR_ROOT` retargets this at a materialised tree. In a shared working directory a
/// sibling lane's uncommitted re-emit makes this gate's verdict a fact about *that lane's tree*, and
/// such a verdict expires the moment the batch lands — this file's own history is a case of exactly
/// that (`mina_transcript_carrier_binding.rs` recorded a divergence as "a sibling's uncommitted
/// re-emit … not this file's to chase", and the reading outlived the tree it was measured on). To
/// ask the question of HEAD:
///
/// ```text
/// scripts/materialise-descriptors-at.sh HEAD /tmp/desc-HEAD
/// DREGG_DESCRIPTOR_ROOT=/tmp/desc-HEAD cargo test -p dregg-circuit \
///     --test vk_pin_closure_over_the_served_tree -- --nocapture
/// ```
fn served_descriptor_files() -> Vec<(String, String)> {
    let root = match std::env::var("DREGG_DESCRIPTOR_ROOT") {
        Ok(p) => PathBuf::from(p),
        Err(_) => PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("descriptors"),
    };
    let mut out = Vec::new();
    collect_json(&root, &root, &mut out);
    out.sort();
    out
}

/// ⚑ Recurses. A gate that reads only `descriptors/` and `descriptors/by-name/` would report a pin
/// as dangling merely because its target lives in `table-airs/` or `seams/` — "no descriptor in this
/// tree has it" has to mean the WHOLE tree, or the verdict is about the search, not the tree.
fn collect_json(dir: &Path, root: &Path, out: &mut Vec<(String, String)>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_json(&path, root, out);
            continue;
        }
        if !path.is_file() || path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        // PROVENANCE.json is the manifest, not a descriptor.
        if path.file_name().and_then(|n| n.to_str()) == Some("PROVENANCE.json") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        let display = path
            .strip_prefix(root)
            .unwrap_or(&path)
            .to_string_lossy()
            .into_owned();
        out.push((display, text));
    }
}

/// Everything the tree serves that parses as an `ir:2` descriptor, keyed by display path.
fn parsed_tree() -> BTreeMap<String, EffectVmDescriptor2> {
    let mut out = BTreeMap::new();
    for (display, text) in served_descriptor_files() {
        if let Ok(d) = parse_vm_descriptor2(&text) {
            out.insert(display, d);
        }
    }
    out
}

/// Every `vk_pin` in a descriptor, in constraint order.
fn vk_pins(d: &EffectVmDescriptor2) -> Vec<(usize, Vec<i64>)> {
    d.constraints
        .iter()
        .enumerate()
        .filter_map(|(i, c)| match c {
            VmConstraint2::ProofBind(spec) => spec.vk_pin.as_ref().map(|p| (i, p.clone())),
            _ => None,
        })
        .collect()
}

/// ⚑⚑ **THE GATE.** Every `vk_pin` served by this tree is the fingerprint of a descriptor served by
/// this tree.
///
/// A failure here reads: *a deployed recursion bind attests a program whose descriptor is not in
/// the tree.* That is either a stale Lean literal that a re-emit moved past, or a descriptor that
/// was re-emitted while the AIR pinning it was not — the two halves of the same flag day, landed
/// apart.
#[test]
fn every_served_vk_pin_names_a_served_descriptor() {
    let tree = parsed_tree();
    assert!(
        tree.len() > 100,
        "only {} descriptors parsed — the tree is not being read, and a gate that reads nothing \
         passes vacuously",
        tree.len()
    );

    // lanes → the descriptors whose fingerprint they are.
    let mut by_lanes: BTreeMap<Vec<i64>, Vec<String>> = BTreeMap::new();
    let mut unfingerprintable = Vec::new();
    for (path, d) in &tree {
        match effect_vm_descriptor2_semantic_fingerprint(d) {
            Ok(fp) => by_lanes
                .entry(pin_lanes(&fp))
                .or_default()
                .push(format!("{} ({path})", d.name)),
            Err(e) => unfingerprintable.push(format!("{path}: {e}")),
        }
    }

    let mut resolved = Vec::new();
    let mut dangling = Vec::new();
    for (path, d) in &tree {
        for (ci, pin) in vk_pins(d) {
            match by_lanes.get(&pin) {
                Some(targets) => {
                    resolved.push(format!("{} [{ci}] -> {}", d.name, targets.join(" | ")));
                }
                None => dangling.push(format!(
                    "  {path}\n    descriptor `{}` constraint {ci} pins {pin:?}\n    \
                     — no descriptor in this tree fingerprints to those lanes",
                    d.name
                )),
            }
        }
    }

    println!(
        "descriptors parsed: {}   fingerprinted: {}   vk_pins: {}",
        tree.len(),
        by_lanes.values().map(Vec::len).sum::<usize>(),
        resolved.len() + dangling.len()
    );
    for line in &resolved {
        println!("  RESOLVED  {line}");
    }
    if !unfingerprintable.is_empty() {
        println!(
            "not fingerprint-representable ({}):",
            unfingerprintable.len()
        );
        for line in &unfingerprintable {
            println!("  {line}");
        }
    }

    if !dangling.is_empty() {
        // The whole served fingerprint table, so the repair is mechanical rather than a hunt: the
        // author of a dangling pin needs to know what the tree DOES offer.
        println!("\nserved fingerprints ({}):", by_lanes.len());
        let mut table: Vec<_> = by_lanes.iter().collect();
        table.sort_by_key(|(_, names)| names.first().cloned().unwrap_or_default());
        for (lanes, names) in table {
            println!("  {:?}\n    {}", lanes, names.join(" | "));
        }
    }
    assert!(
        dangling.is_empty(),
        "⚑ {} of {} served vk_pin(s) name a program NO descriptor in this tree has — the pin and \
         the descriptor it pins landed on opposite sides of a flag day:\n{}\n\nThe served \
         fingerprint table is printed above. Recompute one directly with:\n  cargo run -p \
         dregg-circuit --release --example conj_fingerprint -- \
         circuit/descriptors/by-name/<name>.json",
        dangling.len(),
        dangling.len() + resolved.len(),
        dangling.join("\n")
    );

    assert!(
        !resolved.is_empty(),
        "no vk_pin found in any served descriptor — this gate has stopped asking its question. \
         Either the recursion binds lost their pins, or `vk_pins` no longer reads the emitted \
         shape."
    );
}

/// ⚑⚑ **A TRAILING NEWLINE CANNOT RE-KEY A DESCRIPTOR** — the semantic fingerprint is a function of
/// the PARSED descriptor, so it is invariant under any whitespace the JSON parser discards.
///
/// ## Why this needs to be a theorem and not a remark
///
/// `scripts/emit_descriptors.py` carries a hand-maintained 30-name frozenset,
/// `BY_NAME_NEWLINE_TERMINATED`, whose whole justification is a cost claim:
///
/// > *"it is purely cosmetic — JSON does not care — but the bytes are FP/VK-pinned, so NORMALIZING
/// > the convention would re-key those 5 descriptors for a whitespace change."*
///
/// **The premise is false.** `effect_vm_descriptor2_semantic_fingerprint` takes an
/// `&EffectVmDescriptor2` — a value that has already been through `parse_vm_descriptor2` — and
/// canonically re-encodes it. The raw file bytes are never hashed. A trailing `\n` therefore moves
/// the file's **sha256** (which `PROVENANCE.json` stamps) and moves **nothing else**: no `vk_pin`, no
/// VK, no federation key.
///
/// That distinction is the whole cost of normalising the convention — a re-stamp, not a re-key —
/// and while the frozenset stands, the repo has two emitters producing two byte streams for one
/// object (`MinaChainEmit.lean:48` appends `"\n"`, `EmitByName.lean:788` does not) with a
/// per-filename table reconciling them. Determinism cannot be a lookup table.
///
/// The census in that docstring is itself stale, which is the same defect one level up: it says
/// *"21 bare, 5 newline-terminated"*; the directory is 94 bare and 37 newline-terminated.
#[test]
fn a_trailing_newline_does_not_move_a_descriptors_fingerprint() {
    let tree = parsed_tree();
    assert!(!tree.is_empty(), "no descriptors read");

    let mut checked = 0usize;
    for (path, text) in served_descriptor_files() {
        let Ok(base) = parse_vm_descriptor2(&text) else {
            continue;
        };
        let Ok(base_fp) = effect_vm_descriptor2_semantic_fingerprint(&base) else {
            continue;
        };

        // Both directions: add a newline to a bare file, strip it from a terminated one.
        let flipped = match text.strip_suffix('\n') {
            Some(stripped) => stripped.to_string(),
            None => format!("{text}\n"),
        };
        let alt = parse_vm_descriptor2(&flipped)
            .unwrap_or_else(|e| panic!("{path} stopped parsing under a newline flip: {e}"));
        let alt_fp = effect_vm_descriptor2_semantic_fingerprint(&alt)
            .unwrap_or_else(|e| panic!("{path} stopped fingerprinting under a newline flip: {e}"));

        assert_eq!(
            base_fp, alt_fp,
            "{path}: flipping the trailing newline moved the semantic fingerprint — the \
             fingerprint would then be a function of file whitespace, and \
             `BY_NAME_NEWLINE_TERMINATED`'s cost claim would be right after all"
        );
        assert_eq!(
            base, alt,
            "{path}: the parsed descriptor differs under a newline flip"
        );
        checked += 1;
    }

    assert!(
        checked > 100,
        "only {checked} descriptors exercised — too few for this to be a statement about the tree"
    );
    println!("newline-invariant fingerprints verified over {checked} served descriptors");
}

/// ⚑ **THE FINGERPRINT IS INJECTIVE ON THE SERVED TREE** — no two distinct descriptors share the
/// nine lanes a pin would name them by.
///
/// Without this, "the pin resolves" above is not the statement it looks like: a pin could resolve to
/// a descriptor other than the intended one and every gate would stay green. This is the
/// precondition that makes resolution mean *identification*.
#[test]
fn distinct_descriptors_do_not_share_pin_lanes() {
    let tree = parsed_tree();
    let mut by_lanes: BTreeMap<Vec<i64>, Vec<String>> = BTreeMap::new();
    for (path, d) in &tree {
        if let Ok(fp) = effect_vm_descriptor2_semantic_fingerprint(d) {
            by_lanes.entry(pin_lanes(&fp)).or_default().push(format!(
                "{} ({path}) w={} pi={} cons={}",
                d.name,
                d.trace_width,
                d.public_input_count,
                d.constraints.len()
            ));
        }
    }

    let collisions: Vec<_> = by_lanes
        .iter()
        .filter(|(_, names)| names.len() > 1)
        .map(|(lanes, names)| format!("  {lanes:?}\n    {}", names.join("\n    ")))
        .collect();

    // ⚠ Two FILES holding byte-identical descriptors are one program under two paths, not a
    // collision — the fingerprint is over the semantic content, so that is correct behaviour. What
    // must not happen is two descriptors that DIFFER sharing lanes.
    let real: Vec<_> = collisions
        .iter()
        .filter(|c| {
            let distinct: std::collections::BTreeSet<&str> =
                c.lines().skip(1).map(|l| l.trim()).collect();
            distinct.len() > 1
        })
        .collect();

    assert!(
        real.is_empty(),
        "⚑ {} lane vector(s) name more than one DISTINCT descriptor — a `vk_pin` cannot identify \
         its program:\n{}",
        real.len(),
        real.iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n")
    );
}
