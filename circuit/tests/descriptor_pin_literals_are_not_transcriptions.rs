//! ⚑⚑ **THE LEAN PIN LITERAL AGAINST THE BYTES IT CLAIMS TO BE.**
//!
//! ## The claim this file was cited for before it existed
//!
//! `vk_pin_closure_over_the_served_tree.rs` says, of its own scope:
//!
//! > This is a gate over the **emitted artifacts**, not over the Lean literals. […] A Lean literal
//! > that went stale shows up here as an emitted pin that resolves to nothing — **provided the
//! > descriptor was re-emitted**. Gating the *literal* against the *bytes* is
//! > `descriptor_pin_literals_are_not_transcriptions.rs`.
//!
//! ⚠ **That file did not exist.** Measured 2026-08-11, the citation was its ONLY occurrence in the
//! tree: the literal side was gated by nothing while reading as gated, and the proviso in bold is
//! exactly the hole — a Lean literal edited without a re-emit, or a descriptor re-emitted without
//! the literal following, is invisible to a gate that only ever reads the emitted side. This file
//! is that gate.
//!
//! ## The three questions, and which one is whose
//!
//! A `vk_pin` is `canonical descriptor bytes → blake3 derive-key fingerprint → nine Faithful9
//! lanes`, written into a Lean AIR by hand. Three separate things can be true or false about it,
//! and conflating them is how the citation stayed comfortable:
//!
//! ```text
//!   (1) the Lean literal reached the BYTES        Lean `vkPin := some X` == some served pin
//!   (2) the emitted pin names a SERVED PROGRAM    served pin ∈ fingerprints(served tree)
//!   (3) a Lean DESCRIPTOR TERM fingerprints to    fingerprint(Lean term) == its own literal
//!       its own literal
//! ```
//!
//! **This file is (1), plus intent.** `vk_pin_closure_over_the_served_tree` is (2). Nothing is (3),
//! and this file cannot become (3) — see the last section, which says why in the plainest terms
//! available.
//!
//! The two are genuinely independent, and today they DISAGREE in a way that shows the split is not
//! bookkeeping: `MinaSeams.HEAD_VK_LANES` / `MinaAccumulatorAir.MINA_HEAD_VK_LANES` are both
//! `[385175014, …]`, that value IS the `vk_pin` the served `mina-accumulator-head-genesis.json`
//! carries — so (1) holds — while (2) is RED on it, because recomputing the fingerprint of
//! `dregg-mina-lightclient-verify::v1` gives `[107513588, …]`. Question (1) says *the Lean and the
//! bytes agree*; question (2) says *the bytes are right*. Only (2) went red, and only (2) should
//! have.
//!
//! ## What this gate asks, and how it avoids a hand-maintained map
//!
//! The closure gate's design lesson is that a gate needing a per-pin map is a gate a new pin never
//! gets. So the population here is defined by **use, not by a list**: every 9-lane `List ℤ` literal
//! that some Lean source REFERENCES from a `vkPin := some …` (an AIR's own `proofBind` leg) or a
//! `descLanes := …` (a seam end). A new pin written in the ordinary way joins by construction, and
//! a referenced identifier with no parsable literal is a REFUSAL, never a silently skipped row.
//!
//! Three teeth:
//!
//! 1. every such literal appears in the emitted bytes — as a `ProofBind.vk_pin` of a served
//!    DescriptorIR-v2 record, or as a served seam end's `lanes`;
//! 2. every seam end's literal is served under the descriptor NAME Lean pairs it with. ⚑ This is
//!    **intent**, the thing the closure gate says outright it cannot see ("it does not say it names
//!    the *intended* one"). Lean writes `descName := "N", descLanes := L`; the emitted seam writes
//!    `{descriptor: N, lanes: L}`; a pin that drifted onto the wrong program breaks the pairing even
//!    when both halves are individually well-formed;
//! 3. the three `FORGED_*_VK_LANES` falsifier literals name NO served pin. ⚑ This is the red arm and
//!    it cannot rot: those constants exist to be refused by the AIRs, so the day one of them
//!    coincides with a real served pin is the day the Lean falsifiers stop falsifying — the
//!    `a_falsifier_that_stopped_falsifying` shape, caught from the outside.
//!
//! ⚠ **WHAT THIS GATE CANNOT CHECK, SAID PLAINLY.** It compares a written-down number against
//! another written-down number that a Rust tool produced. It does NOT recompute the fingerprint
//! from a Lean descriptor term, and it cannot: `Dregg2.Crypto.Blake3Compute.blake3Derive` and
//! `Dregg2.Circuit.VkPinCompute.vkPinLanes` are pure Lean and differential-checked against the
//! deployed Rust on all served descriptors at both hops (`scripts/check-blake3-differential.sh`),
//! but their INPUT is canonical BYTES, and the canonical ENCODER
//! (`circuit/src/descriptor_ir2_canonical.rs::canonical_effect_vm_descriptor2_bytes` — 534 lines,
//! 13 mutually recursive writers over the IR-v2 AST) exists only in Rust. So `vkPinLanes` cannot be
//! handed a Lean `EffectVmDescriptor2` term, and **that is why the pin constants are still
//! constants.** Authoring that encoder in Lean and deleting the Rust one is question (3) and is a
//! lane of its own. Until it lands, a Lean AIR author's nine digits are checked for *agreeing with
//! the artifact* and for *being pointed at the program Lean names* — not for being that program's
//! fingerprint, which is the closure gate's question and is asked over there.
//!
//! Run: `cargo test -p dregg-circuit --test descriptor_pin_literals_are_not_transcriptions -- --nocapture`

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use dregg_circuit::descriptor_ir2::{VmConstraint2, parse_vm_descriptor2};

/// The `metatheory/` tree — the LITERAL side. `DREGG_METATHEORY_DIR` retargets it.
fn lean_root() -> PathBuf {
    match std::env::var("DREGG_METATHEORY_DIR") {
        Ok(p) => PathBuf::from(p),
        Err(_) => PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("the circuit crate has a workspace parent")
            .join("metatheory"),
    }
}

/// The descriptor tree — the BYTES side. `DREGG_DESCRIPTOR_ROOT` retargets it, exactly as in
/// `vk_pin_closure_over_the_served_tree`, so both gates can be asked of the same materialised HEAD.
fn descriptor_root() -> PathBuf {
    match std::env::var("DREGG_DESCRIPTOR_ROOT") {
        Ok(p) => PathBuf::from(p),
        Err(_) => PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("descriptors"),
    }
}

/// Every file under `dir` whose extension is `ext`, recursively, skipping `.lake` build output
/// (which holds copied sources — counting a literal twice from there would inflate the floors).
fn collect(dir: &Path, ext: &str, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().into_owned();
        if path.is_dir() {
            if name != ".lake" && name != "target" {
                collect(&path, ext, out);
            }
            continue;
        }
        if path.extension().and_then(|e| e.to_str()) == Some(ext) {
            out.push(path);
        }
    }
}

/// A Lean source with its `--` line comments blanked out.
///
/// ⚑ The stripping is load-bearing, not tidiness. Several of these literals carry a five-line
/// provenance comment between the `:=` and the array (`MINA_HEAD_VK_LANES` names the two re-emits
/// that moved it), and a comment quoting a bracketed value would otherwise be read AS the literal —
/// a parser that grabs the wrong nine numbers is a gate that compares the wrong thing and passes.
fn strip_line_comments(src: &str) -> String {
    src.lines()
        .map(|l| match l.find("--") {
            Some(i) => l[..i].to_string(),
            None => l.to_string(),
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// The text of a `def NAME … := <body>` block: everything up to the next line that starts in
/// column zero. Lean indents a definition's body, so this is the whole body and nothing else.
fn def_body<'a>(src: &'a str, after: usize) -> &'a str {
    let rest = &src[after..];
    let mut end = rest.len();
    let mut idx = 0usize;
    for line in rest.split_inclusive('\n') {
        // The first line is the tail of the `def …` line itself; never a terminator.
        if idx > 0 && !line.trim().is_empty() && !line.starts_with(' ') && !line.starts_with('\t') {
            end = idx;
            break;
        }
        idx += line.len();
    }
    &rest[..end]
}

/// The first `[a, b, …]` of decimal integers in `body`, if any.
fn first_int_list(body: &str) -> Option<Vec<i64>> {
    let open = body.find('[')?;
    let close = body[open..].find(']')? + open;
    let inner = &body[open + 1..close];
    let mut out = Vec::new();
    for tok in inner.split(',') {
        let t = tok.trim();
        if t.is_empty() {
            return None;
        }
        out.push(t.parse::<i64>().ok()?);
    }
    Some(out)
}

/// Every `def NAME : List ℤ := [nine ints]` in the Lean tree, as `name -> [(file, lanes)]`.
///
/// A name may legitimately appear more than once (`ABSORB_VK_LANES` is defined in both
/// `LightClientMinaLinkAir` and `MinaWrapClosingAir`), which is why the value is a list and why
/// [`same_named_pin_literals_are_one_value`] exists.
fn nine_lane_literals() -> BTreeMap<String, Vec<(String, Vec<i64>)>> {
    let root = lean_root();
    let mut files = Vec::new();
    collect(&root, "lean", &mut files);
    let mut out: BTreeMap<String, Vec<(String, Vec<i64>)>> = BTreeMap::new();
    for path in files {
        let Ok(raw) = std::fs::read_to_string(&path) else {
            continue;
        };
        let src = strip_line_comments(&raw);
        let display = path
            .strip_prefix(&root)
            .unwrap_or(&path)
            .to_string_lossy()
            .into_owned();
        let mut from = 0usize;
        while let Some(rel) = src[from..].find("def ") {
            let at = from + rel;
            from = at + 4;
            let line_end = src[at..].find('\n').map_or(src.len(), |i| at + i);
            let head = &src[at..line_end];
            let Some(colon) = head.find(':') else {
                continue;
            };
            // `List ℤ`, allowing any spacing the author used.
            if !head[colon..].replace(' ', "").starts_with(":Listℤ:=") {
                continue;
            }
            let name = head[4..colon].trim().to_string();
            if name.is_empty() || !name.chars().all(|c| c.is_alphanumeric() || c == '_') {
                continue;
            }
            let Some(assign) = head.find(":=") else {
                continue;
            };
            let body = def_body(&src, at + assign + 2);
            if let Some(lanes) = first_int_list(body) {
                if lanes.len() == 9 {
                    out.entry(name).or_default().push((display.clone(), lanes));
                }
            }
        }
    }
    out
}

/// The identifier on the right of every `vkPin := some X` and `descLanes := X` in the Lean tree,
/// with any module qualification dropped (`A.B.LINK_VK_LANES` -> `LINK_VK_LANES`).
///
/// ⚑ **THIS IS THE POPULATION, AND IT IS DEFINED BY USE.** Not a list of names this file knows —
/// that is precisely the shape the closure gate's header indicts ("a gate that must be extended by
/// hand for each new pin is a gate that a new pin does not get"). An AIR author who writes a new
/// `vkPin := some MY_NEW_LANES` is gated the moment the line lands, with no edit here. The cost of
/// that choice is that a referenced identifier this file cannot resolve to a literal must REFUSE
/// rather than be skipped, which is what the floors below enforce.
fn referenced_pin_idents() -> BTreeSet<String> {
    let root = lean_root();
    let mut files = Vec::new();
    collect(&root, "lean", &mut files);
    let mut out = BTreeSet::new();
    for path in files {
        let Ok(raw) = std::fs::read_to_string(&path) else {
            continue;
        };
        let src = strip_line_comments(&raw);
        for (field, opt_some) in [("vkPin", true), ("descLanes", false)] {
            let mut from = 0usize;
            while let Some(rel) = src[from..].find(field) {
                let at = from + rel + field.len();
                from = at;
                if let Some(base) = ident_after_assignment(&src[at..], opt_some) {
                    out.insert(base);
                }
            }
        }
    }
    out
}

/// After a field NAME, read `:= [some] IDENT` and return `IDENT`'s last dotted segment.
///
/// ⚑ **WHITESPACE-TOLERANT ON PURPOSE, AND THE FIRST DRAFT WAS NOT.** It matched the literal string
/// `"vkPin := some "` and therefore silently missed every `vkPin  := some …` — the ALIGNED spelling
/// `LightClientMinaLinkAir` uses at all four of its `proofBind` legs, which is where
/// `ABSORB_VK_LANES` and `FP_CHAINLINK_VK_LANES` live. The population went from eleven to nine and
/// the gate would have reported PASS over a quietly smaller corpus: a parser that drops rows is a
/// differential that stops differing, which is the exact defect this file gates one level up. It
/// was caught by the `resolved.len() >= 10` floor, which is the argument for having floors that
/// name a MEASURED number rather than asserting non-emptiness.
fn ident_after_assignment(rest: &str, allow_some: bool) -> Option<String> {
    let mut it = rest.char_indices().skip_while(|(_, c)| c.is_whitespace());
    let (i, _) = it.next()?;
    if !rest[i..].starts_with(":=") {
        return None;
    }
    let mut tail = rest[i + 2..].trim_start();
    if allow_some {
        // `vkPin := none` and `vkPin := m.vkPin` name no literal; `vkPin := some X` does.
        let after = tail.strip_prefix("some")?;
        if after.starts_with(|c: char| c.is_alphanumeric() || c == '_') {
            return None;
        }
        tail = after.trim_start();
    }
    let ident: String = tail
        .chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '.')
        .collect();
    let base = ident.rsplit('.').next()?;
    // `vkPin := some [45, 46, …]` (an inline literal in a DescriptorIR2 unit test) yields an empty
    // base; there is no named literal to gate.
    if base.is_empty() || !base.starts_with(|c: char| c.is_alphabetic()) {
        return None;
    }
    Some(base.to_string())
}

/// Every `descName := "N"` paired with the `descLanes := L` of the SAME seam end, as `(N, L)`.
///
/// The two fields sit in one record literal and may be on the same line or on consecutive ones, so
/// the pairing is "the next `descLanes` after this `descName`, if it comes before the next
/// `descName`". A `descName` with no following `descLanes` before the next `descName` is dropped
/// here and caught by the count floor in the test.
fn seam_end_pairs() -> BTreeSet<(String, String)> {
    let root = lean_root();
    let mut files = Vec::new();
    collect(&root, "lean", &mut files);
    let mut out = BTreeSet::new();
    for path in files {
        let Ok(raw) = std::fs::read_to_string(&path) else {
            continue;
        };
        let src = strip_line_comments(&raw);
        let mut from = 0usize;
        while let Some(rel) = src[from..].find("descName") {
            let at = from + rel + "descName".len();
            from = at;
            // `descName := "N"` — same whitespace tolerance as the pin scanner above.
            let after = src[at..].trim_start();
            let Some(after) = after.strip_prefix(":=") else {
                continue;
            };
            let after = after.trim_start();
            let Some(after) = after.strip_prefix('"') else {
                continue;
            };
            let Some(q) = after.find('"') else { break };
            let name = after[..q].to_string();
            let tail = &after[q..];
            let next_name = tail.find("descName").unwrap_or(tail.len());
            let Some(l) = tail.find("descLanes") else {
                continue;
            };
            if l > next_name {
                continue;
            }
            if let Some(base) = ident_after_assignment(&tail[l + "descLanes".len()..], false) {
                out.insert((name, base));
            }
        }
    }
    out
}

/// Every `ProofBind.vk_pin` in every served DescriptorIR-v2 record, as `lanes -> carriers`.
///
/// ⚑ Read through `parse_vm_descriptor2`, not by sniffing JSON keys, so this asks about the shape
/// the deployed reader sees. The carrier is the descriptor that CARRIES the pin, not the program
/// the pin names — a `vk_pin` says nothing about its own file, so it is reported only to make a
/// failure locatable.
fn served_vk_pins() -> BTreeMap<Vec<i64>, BTreeSet<String>> {
    let root = descriptor_root();
    let mut files = Vec::new();
    collect(&root, "json", &mut files);
    let mut out: BTreeMap<Vec<i64>, BTreeSet<String>> = BTreeMap::new();
    for path in files {
        if path.file_name().and_then(|n| n.to_str()) == Some("PROVENANCE.json") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        let Ok(d) = parse_vm_descriptor2(&text) else {
            continue;
        };
        for c in &d.constraints {
            if let VmConstraint2::ProofBind(spec) = c {
                if let Some(pin) = spec.vk_pin.as_ref() {
                    out.entry(pin.clone())
                        .or_default()
                        .insert(format!("vk_pin carried by {}", d.name));
                }
            }
        }
    }
    out
}

/// Every served seam END, as `lanes -> the descriptor names it is served under`.
///
/// Seam records are not DescriptorIR-v2 documents, so they are read as JSON. A seam end pairs the
/// pinned program's NAME with its lanes in one object — which is what makes the intent tooth
/// possible here and impossible in the closure gate.
fn served_seam_ends() -> BTreeMap<Vec<i64>, BTreeSet<String>> {
    let root = descriptor_root();
    let mut files = Vec::new();
    collect(&root, "json", &mut files);
    let mut out: BTreeMap<Vec<i64>, BTreeSet<String>> = BTreeMap::new();
    for path in files {
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        let Ok(v) = serde_json::from_str::<serde_json::Value>(&text) else {
            continue;
        };
        walk_seam_ends(&v, &mut out);
    }
    out
}

fn walk_seam_ends(v: &serde_json::Value, out: &mut BTreeMap<Vec<i64>, BTreeSet<String>>) {
    match v {
        serde_json::Value::Object(m) => {
            if let (Some(serde_json::Value::String(name)), Some(serde_json::Value::Array(lanes))) =
                (m.get("descriptor"), m.get("lanes"))
            {
                let parsed: Option<Vec<i64>> =
                    lanes.iter().map(serde_json::Value::as_i64).collect();
                if let Some(l) = parsed {
                    if l.len() == 9 {
                        out.entry(l).or_default().insert(name.clone());
                    }
                }
            }
            for child in m.values() {
                walk_seam_ends(child, out);
            }
        }
        serde_json::Value::Array(a) => {
            for child in a {
                walk_seam_ends(child, out);
            }
        }
        _ => {}
    }
}

/// The one literal a name resolves to, REFUSING if two files define it differently.
///
/// ⚠ A display name is not a key, and this tree has been bitten by that: two same-named constants
/// that agree today are two constants that disagree later. `ABSORB_VK_LANES` is defined twice on
/// purpose (the link AIR and the wrap-closing AIR pin the same absorb program); resolving it by
/// name is only sound while the definitions agree, so the disagreement is a REFUSAL rather than a
/// pick.
fn resolve(
    lits: &BTreeMap<String, Vec<(String, Vec<i64>)>>,
    ident: &str,
) -> Result<Vec<i64>, String> {
    let defs = lits
        .get(ident)
        .ok_or_else(|| format!("no `def {ident} : List ℤ := [nine ints]` in the Lean tree"))?;
    let first = &defs[0].1;
    for (file, lanes) in defs {
        if lanes != first {
            return Err(format!(
                "`{ident}` is defined more than once and the definitions DISAGREE: {} says \
                 {:?}, {file} says {lanes:?} — two spellings of one pin, which is the \
                 two-constants-drift shape this gate exists to catch",
                defs[0].0, first
            ));
        }
    }
    Ok(first.clone())
}

/// ⚑⚑ **TOOTH 1 — every pin literal a Lean AIR or seam references REACHED THE EMITTED BYTES.**
///
/// A failure reads: *Lean says this program's pin is X, and no artifact this tree serves carries
/// X.* Either the literal was edited and the descriptors were not re-emitted, or a re-emit moved
/// the pin and the literal did not follow. Both are the same flag day landed by halves, and neither
/// is visible to `vk_pin_closure_over_the_served_tree`, which never reads a `.lean` file.
#[test]
fn every_pin_literal_lean_references_reached_the_emitted_bytes() {
    let lits = nine_lane_literals();
    let refs = referenced_pin_idents();
    let pins = served_vk_pins();
    let seams = served_seam_ends();

    // ── Vacuity floors. Each one is a way this gate could report PASS having asked nothing. ──
    assert!(
        lits.len() >= 20,
        "only {} nine-lane `List ℤ` literals parsed out of {} — the Lean tree is not being read, \
         and a gate that reads no literals passes vacuously. Set DREGG_METATHEORY_DIR if the tree \
         is elsewhere.",
        lits.len(),
        lean_root().display()
    );
    assert!(
        !pins.is_empty(),
        "no `ProofBind.vk_pin` in any served descriptor under {} — the bytes side is empty",
        descriptor_root().display()
    );
    assert!(
        !seams.is_empty(),
        "no served seam end under {} — the seam side is empty",
        descriptor_root().display()
    );

    let mut resolved = Vec::new();
    let mut missing = Vec::new();
    let mut unresolvable = Vec::new();
    for ident in &refs {
        let lanes = match resolve(&lits, ident) {
            Ok(l) => l,
            Err(e) => {
                unresolvable.push(format!("  {ident}: {e}"));
                continue;
            }
        };
        let mut where_served: Vec<String> = Vec::new();
        if let Some(c) = pins.get(&lanes) {
            where_served.extend(c.iter().cloned());
        }
        if let Some(c) = seams.get(&lanes) {
            where_served.extend(c.iter().map(|n| format!("seam end for {n}")));
        }
        if where_served.is_empty() {
            missing.push(format!(
                "  `{ident}` = {lanes:?}\n    — referenced by a Lean `vkPin`/`descLanes`, and NO \
                 served vk_pin or seam end carries those lanes"
            ));
        } else {
            resolved.push(format!("  {ident} -> {}", where_served.join(" | ")));
        }
    }

    println!(
        "lean 9-lane literals: {}   referenced by vkPin/descLanes: {}   served vk_pins: {}   \
         served seam ends: {}",
        lits.len(),
        refs.len(),
        pins.len(),
        seams.len()
    );
    for line in &resolved {
        println!("  RESOLVED{line}");
    }

    assert!(
        unresolvable.is_empty(),
        "⚑ {} referenced pin identifier(s) could not be resolved to a Lean literal. A referenced \
         identifier this gate cannot read is NOT a row to skip — it is the population shrinking \
         under the gate, which is how a differential quietly stops differing:\n{}",
        unresolvable.len(),
        unresolvable.join("\n")
    );
    assert!(
        missing.is_empty(),
        "⚑ {} of {} Lean pin literal(s) name lanes NO served artifact carries — the literal and \
         the emit landed on opposite sides of a flag day:\n{}\n\nRe-emit the descriptors, or \
         recompute the literal from the bytes with:\n  cargo run -p dregg-circuit --release \
         --example conj_fingerprint -- circuit/descriptors/by-name/<name>.json",
        missing.len(),
        refs.len(),
        missing.join("\n")
    );
    assert!(
        resolved.len() >= 10,
        "only {} pin literals were checked — this gate has lost its population and is passing on \
         almost nothing. Measured 2026-08-11: ELEVEN referenced identifiers, all resolving.",
        resolved.len()
    );
}

/// ⚑⚑⚑ **TOOTH 2 — INTENT. Every seam end's literal is served under the descriptor Lean NAMES.**
///
/// The closure gate says outright what it cannot do: *"It says each pin names some descriptor here.
/// It does not say it names the intended one — a pin that resolves to the wrong descriptor is a
/// semantic error this cannot see."* On the seam surface that error IS visible, because Lean and
/// the artifact each carry the name and the lanes TOGETHER: `descName := "N", descLanes := L`
/// against `{descriptor: N, lanes: L}`. A literal copy-pasted from the wrong constant still lands
/// in the served tree and still resolves — and still breaks this pairing.
#[test]
fn every_seam_end_literal_names_the_descriptor_lean_pairs_it_with() {
    let lits = nine_lane_literals();
    let pairs = seam_end_pairs();
    let seams = served_seam_ends();

    assert!(
        pairs.len() >= 8,
        "only {} Lean (descName, descLanes) seam-end pair(s) parsed — measured 2026-08-11 there \
         were EIGHT. A pairing this gate cannot see is a pairing it cannot check.",
        pairs.len()
    );

    let mut agreed = Vec::new();
    let mut wrong = Vec::new();
    for (name, ident) in &pairs {
        let lanes = match resolve(&lits, ident) {
            Ok(l) => l,
            Err(e) => {
                wrong.push(format!("  {name} / {ident}: {e}"));
                continue;
            }
        };
        match seams.get(&lanes) {
            None => wrong.push(format!(
                "  Lean pairs `{ident}` = {lanes:?} with `{name}`, but NO served seam end carries \
                 those lanes at all"
            )),
            Some(names) if names.len() == 1 && names.contains(name) => {
                agreed.push(format!("  {name} <- {ident}"));
            }
            Some(names) => wrong.push(format!(
                "  Lean pairs `{ident}` = {lanes:?} with `{name}`, but the served seam ends \
                 carrying those lanes name {names:?} — the literal is pointed at a DIFFERENT \
                 program than Lean says it is"
            )),
        }
    }

    println!("seam-end intent pairs checked: {}", pairs.len());
    for line in &agreed {
        println!("  AGREED{line}");
    }
    assert!(
        wrong.is_empty(),
        "⚑ {} of {} seam-end pin literal(s) do not name the descriptor Lean pairs them with:\n{}",
        wrong.len(),
        pairs.len(),
        wrong.join("\n")
    );
}

/// ⚑⚑ **TOOTH 3 — THE RED ARM: a falsifier literal must name NOTHING this tree serves.**
///
/// `LightClientMinaAir` carries three deliberately-wrong pins (`FORGED_VK_LANES`,
/// `FORGED_LINK_VK_LANES`, `FORGED_CONJ_VK_LANES` — each the honest literal with lane 0 bumped by
/// one) whose whole job is to be REFUSED by the AIRs. They give this file a polarity that cannot
/// rot into a tautology: tooth 1 demands every real literal be served, and this demands every
/// forged one NOT be, so a change that made membership trivially true or trivially false breaks one
/// of the two.
///
/// It is also a live tooth on the falsifiers themselves. `FORGED_LINK_VK_LANES` has already caught
/// its own staleness twice by going red when `LINK_VK_LANES` moved and it did not; the failure this
/// test names is the opposite and quieter one — a forged constant that has drifted ONTO a real
/// served pin, at which point the Lean falsifier is asserting that a genuine program is refused.
#[test]
fn the_forged_falsifier_literals_name_no_served_pin() {
    let lits = nine_lane_literals();
    let pins = served_vk_pins();
    let seams = served_seam_ends();

    let forged: Vec<&String> = lits
        .keys()
        .filter(|n| n.starts_with("FORGED_") && n.ends_with("_VK_LANES"))
        .collect();
    assert_eq!(
        forged.len(),
        3,
        "expected the THREE `FORGED_*_VK_LANES` falsifier literals measured 2026-08-11, found {}: \
         {forged:?}. If a falsifier was added, this count is the place to say so; if one \
         DISAPPEARED, a polarity test lost its adversary and this gate lost its red arm.",
        forged.len()
    );

    let mut collided = Vec::new();
    for name in forged {
        let lanes = resolve(&lits, name).expect("a FORGED literal parsed above resolves");
        let mut hits: Vec<String> = Vec::new();
        if let Some(c) = pins.get(&lanes) {
            hits.extend(c.iter().cloned());
        }
        if let Some(c) = seams.get(&lanes) {
            hits.extend(c.iter().map(|n| format!("seam end for {n}")));
        }
        if !hits.is_empty() {
            collided.push(format!(
                "  `{name}` = {lanes:?} IS SERVED as {}",
                hits.join(" | ")
            ));
        }
    }
    assert!(
        collided.is_empty(),
        "⚑ {} falsifier literal(s) name a program this tree actually serves — the Lean polarity \
         test that 'refuses' them is now asserting a REAL pin is refused, and it stopped \
         falsifying anything:\n{}",
        collided.len(),
        collided.join("\n")
    );
}

/// ⚑ **TOOTH 4 — a pin defined twice is defined once.**
///
/// `ABSORB_VK_LANES` is authored in two modules and `MINA_HEAD_VK_LANES` / `HEAD_VK_LANES` are the
/// same nine digits under two names; the closure gate's own header counts *"two copies of one
/// fingerprint constant differing at HEAD"* among the defects that landed in one week. [`resolve`]
/// refuses a name whose definitions disagree, and this drives every name through it so the refusal
/// is a TEST rather than a helper nobody calls on the disagreeing one.
#[test]
fn same_named_pin_literals_are_one_value() {
    let lits = nine_lane_literals();
    let mut disagreements = Vec::new();
    let mut multiply_defined = 0usize;
    for (name, defs) in &lits {
        if defs.len() > 1 {
            multiply_defined += 1;
            if let Err(e) = resolve(&lits, name) {
                disagreements.push(format!("  {e}"));
            }
        }
    }
    println!("nine-lane literals defined in more than one file: {multiply_defined}");
    assert!(
        disagreements.is_empty(),
        "⚑ {} pin literal name(s) have disagreeing definitions:\n{}",
        disagreements.len(),
        disagreements.join("\n")
    );
}
