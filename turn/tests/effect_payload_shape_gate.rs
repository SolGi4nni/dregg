//! # The effect PAYLOAD-SHAPE gate — what the name-parity ratchet cannot see.
//!
//! `verb_registry_cover_gate.rs` pins the `Effect` variant NAMES against the
//! Lean `EffectTag` constructor names as ordered sequences. That is the whole
//! of what it can do: every `EffectTag` constructor is NULLARY
//! (`VerbRegistry.lean:224` — `| SetField | Transfer | …`, no parameters), so
//! there is no payload on that side to compare an arity against, and there
//! never will be. A variant can gain or lose a FIELD and the cover gate stays
//! green.
//!
//! A missing field is not hypothetical here. Established 2026-07-26 at source:
//!
//!  * the Lean kernel carries TWO parallel value models — scalar
//!    (`recTransfer (cell) (src dst) (amt)`, `Exec/RecordKernel.lean:527`) and
//!    asset-indexed (`recTransferBal (bal : CellId → AssetId → ℤ) … (a : AssetId)
//!    (amt)`, `:644`), with the same split on `recKExec`/`recKExecAsset`,
//!    `recTotal`/`recTotalAsset`, `recCredit`/`recBalCreditCell`;
//!  * `Effect::Transfer { from, to, amount }` (`src/action.rs`) has NO asset
//!    field — it refines the SCALAR kernel;
//!  * the executor guard at `src/executor/apply.rs:673` nevertheless CITES
//!    `recTransferBal`, the indexed one, and — having no asset on the effect —
//!    substitutes `from_cell.token_id() != to_cell.token_id()`, where
//!    `token_id` is really the CellId derivation nonce (`cell/src/cell.rs:314`:
//!    `id == derive_raw(public_key, token_id)`).
//!
//! That divergence was discoverable only by ~130 tests going red. This file
//! makes the CLASS detectable: it pins payload STRUCTURE, and it pins the
//! asset index specifically, so the next instance is a named red line rather
//! than an afternoon of bisecting.
//!
//! ## Why a sibling file and not an extension of the cover gate
//!
//! Different counterpart, different mechanism, different exemption discipline.
//! The cover gate's Lean counterpart is `Substrate/VerbRegistry.lean` (nullary
//! tags). The payload counterpart is a DIFFERENT file —
//! `Exec/TurnExecutorFull/PerAsset.lean`'s `FullActionA`, which
//! `Circuit/ExecutorApplyDifferential.lean` names as the field-level model
//! ("the full FIELD-level model of each variant lives in
//! `Exec.TurnExecutorFull.execFullA`"). Merging them would give one test with
//! two unrelated failure meanings and one merged exemption table.
//!
//! ## What correspondence is actually available (and what is not)
//!
//! There is NO field-by-field type-level correspondence in the tree to pin.
//! `FullActionA`'s parameters are the Lean model's own operands (`actor` is
//! carried explicitly, `Permissions` collapses to `Int`), not a transcription
//! of the Rust fields. `DeployedEffect`
//! (`Circuit/ExecutorApplyDifferential.lean:78`) is worse for this purpose and
//! says so in its own doc comment: it is "SELECTOR-faithful", payloads are
//! only "the primary operands the dispatcher branches on" (`transfer (t : Turn)`
//! — arity 1 against the Rust arity 3). Pinning arity against it would need an
//! exemption per variant, i.e. no gate at all.
//!
//! What IS available is stronger than arity and it is authored on the LEAN
//! side: each `FullActionA` constructor's doc comment opens by naming the Rust
//! variant it models TOGETHER WITH that variant's field list —
//!
//! ```text
//!   /-- `SetField { cell, index→field, value }` (dregg1 `apply_set_field`): …
//!   | setFieldA (actor cell : CellId) (field : FieldName) (v : Int)
//! ```
//!
//! — where `a→b` reads "Rust field `a` is Lean parameter `b`". So the Lean
//! model DECLARES, in machine-readable form, which Rust payload it believes it
//! is refining. This gate turns that declaration into a checked claim: the
//! declared field list must be the real one, ordered. Nobody hand-transcribes
//! either roster into this test — both sides are `include_str!`ed and
//! extracted, exactly as the cover gate does, so neither can move alone.
//!
//! Two doc conventions are honoured rather than graded:
//!  * a list containing `…` is DELIBERATELY abbreviated
//!    (`CreateCellFromFactory { factory_vk, … params }`) and is not compared;
//!  * empty braces (`RefreshDelegation { }`) read idiomatically as "payload
//!    elided", not "payload is empty", so they are treated as abbreviated too.
//! Everything else is read as a complete claim. `MIN_COMPARED` below stops the
//! abbreviated bucket from swallowing the gate.
//!
//! ## The three teeth
//!
//! 1. `lean_declared_effect_payloads_match_the_rust_fields` — the declared
//!    field list is the real field list, ordered. Catches an added/removed/
//!    renamed/reordered field on any modelled variant.
//! 2. `asset_index_parity_between_effects_and_the_lean_per_asset_model` — the
//!    specific wound: does the effect carry an asset index when its Lean
//!    counterpart is asset-indexed, and vice versa.
//! 3. `observations_do_not_name_an_index_the_effect_cannot_express` — the
//!    receipt layer (`dregg-query/src/receipt.rs`) publishes
//!    `EffectSummary::Transfer { from, to, asset, amount }` and
//!    `Burned { cell, asset, amount }`, naming an index the EFFECT has no
//!    field for. Same class, entirely inside Rust.
//!
//! ## Exemptions
//!
//! Known divergences are NAMED with a reason, never silently allowed, and each
//! is checked for STALENESS: an exemption that no longer diverges fails the
//! gate telling you to delete it. So closing one of these — which is a real
//! design decision across `turn/`, `cell/` and the node services, ember's call,
//! not this file's — is what retires its row.

/// The wire enum — the deployed payload shapes.
const ACTION_RS: &str = include_str!("../src/action.rs");

/// The Lean FIELD-level executor model. `FullActionA` is the per-asset op-set;
/// its constructor doc comments declare the Rust variant each one refines.
const PER_ASSET_LEAN: &str =
    include_str!("../../metatheory/Dregg2/Exec/TurnExecutorFull/PerAsset.lean");

/// The observation layer — what a receipt consumer is told an effect did.
const RECEIPT_RS: &str = include_str!("../../dregg-query/src/receipt.rs");

/// Floor: fewer declared field lists than this and the doc convention moved
/// under us — the gate would be passing on an empty comparison set.
const MIN_COMPARED: usize = 12;

// ───────────────────────── exemption tables ─────────────────────────
//
// Each row is a KNOWN divergence with the reason it exists. A divergence NOT
// listed here fails the gate. A row listed here that no longer diverges ALSO
// fails the gate (stale-exemption check) — closing a divergence must delete
// its row, so the tables cannot rot into permission slips.

/// Tooth 1: variants whose Lean-declared field list is knowingly not the Rust
/// field list.
const FIELD_SHAPE_EXEMPTIONS: &[(&str, &str)] = &[
    (
        "Introduce",
        "Lean declares {introducer, recipient, target}; Rust also carries \
         `permissions`. `introduceA` models the UNATTENUATED cap copy; the \
         rights-carrying refinement is the separate `delegateAttenA` \
         (`IntroduceAttenuated`), so the permission operand is deliberately \
         off the `introduceA` arm.",
    ),
    (
        "AttenuateCapability",
        "Lean declares {cell, slot, narrower_permissions}; Rust narrows on \
         THREE axes — `narrower_permissions`, `narrower_effects`, \
         `narrower_expiry`. `attenuateA`'s `keep : List Auth` collapses all \
         three into one authority list, so two of the three Rust narrowing \
         axes have no separate Lean operand.",
    ),
    (
        "BridgeMint",
        "Lean declares {cell, value, asset_type, nullifier}; Rust carries the \
         single opaque `portable_proof : PortableNoteProof`. The Lean list \
         names the fields INSIDE the portable proof, not the effect's own \
         payload — the foreign-finality Prop carrier sits off the executable \
         layer, so the decomposition is a model choice, not a wire shape.",
    ),
    (
        "NoteSpend",
        "Lean declares {nullifier, spending_proof}; Rust also carries \
         `note_tree_root`, `value`, `asset_type`, `value_commitment`. \
         `noteSpendA` models the nullifier-SET insert only; the note crypto \
         (membership, conservation, range) is the §8 theorem-level portal, \
         off the executable layer.",
    ),
    (
        "NoteCreate",
        "Lean declares {commitment}; Rust also carries `value`, `asset_type`, \
         `encrypted_note`, `value_commitment`, `range_proof`. Same reason as \
         NoteSpend: `noteCreateA` is the grow-only commitment-SET insert.",
    ),
];

/// Tooth 1: Lean constructors that declare a Rust variant name with no such
/// `Effect` variant. These are Lean-side refinements, not stale references.
const LEAN_ONLY_MODELS: &[(&str, &str)] = &[
    (
        "IntroduceAttenuated",
        "No wire variant of this name. It is the rights-carrying refinement of \
         `Introduce` — the Lean model splits the unattenuated cap copy \
         (`introduceA`) from the attenuated one (`delegateAttenA`); the wire \
         has one `Introduce` carrying `permissions`.",
    ),
    (
        "HeapWrite",
        "No wire variant of this name. The sorted-map / collection write \
         surface is modelled as a Lean op; on the wire it is reached through \
         the field/heap encoding, not a dedicated `Effect` constructor.",
    ),
];

/// Tooth 2: Lean constructors that carry an `AssetId` but whose Rust
/// counterpart the doc comment does NOT declare. These three are the value
/// verbs — the correspondence is unstated in the Lean source precisely where
/// the two models diverge, so it is stated here instead, as a divergence
/// record rather than a mapping the test invented.
const UNDECLARED_COUNTERPARTS: &[(&str, &str, &str)] = &[
    (
        "balanceA",
        "Transfer",
        "`balanceA (turn : Turn) (asset : AssetId)` routes to the asset-indexed \
         `recKExecAsset`; the wire `Effect::Transfer` is the only transfer \
         constructor and refines the SCALAR `recTransfer`. Doc declares no \
         Rust variant.",
    ),
    (
        "mintA",
        "Mint",
        "`mintA … (asset : AssetId) (amt : ℤ)` is the per-asset supply mint; \
         the wire `Effect::Mint { target, slot, amount }` is its only \
         counterpart. Doc declares no Rust variant.",
    ),
    (
        "burnA",
        "Burn",
        "`burnA … (asset : AssetId) (amt : ℤ)` is the per-asset supply burn; \
         the wire `Effect::Burn { target, slot, amount }` is its only \
         counterpart. Doc declares no Rust variant.",
    ),
];

/// Tooth 2: pairs where the asset index is present on exactly one side.
const ASSET_INDEX_EXEMPTIONS: &[(&str, &str)] = &[
    (
        "balanceA",
        "LEAN-ONLY INDEX. `Effect::Transfer { from, to, amount }` has no asset \
         field; the Lean counterpart is indexed. This is the instance this \
         gate exists for: `apply.rs:673` cites the indexed `recTransferBal` \
         and, lacking an asset operand, substitutes \
         `from_cell.token_id() != to_cell.token_id()` — and `token_id` is the \
         CellId derivation nonce (`cell/src/cell.rs:314`), not an asset id.",
    ),
    (
        "mintA",
        "LEAN-ONLY INDEX. `Effect::Mint { target, slot, amount }` has no asset \
         field; `mintA` takes `asset : AssetId`. The wire `slot` is a cap/\
         balance slot, not an asset index.",
    ),
    (
        "burnA",
        "LEAN-ONLY INDEX. `Effect::Burn { target, slot, amount }` has no asset \
         field; `burnA` takes `asset : AssetId`. Same shape as `mintA`.",
    ),
    (
        "bridgeMintA",
        "LEAN-ONLY INDEX. `Effect::BridgeMint { portable_proof }` carries one \
         opaque proof; the asset is inside it, not a field. `bridgeMintA` \
         takes `asset : AssetId` explicitly.",
    ),
    (
        "noteSpendA",
        "RUST-ONLY INDEX (the reverse direction). `Effect::NoteSpend` DOES \
         carry `asset_type : u64` while `noteSpendA (nf) (actor) (spendProof)` \
         is asset-blind — the Lean arm models the nullifier-set insert, which \
         is asset-independent. The shielded value model is asset-typed on the \
         wire and not in this executable arm.",
    ),
    (
        "noteCreateA",
        "RUST-ONLY INDEX. `Effect::NoteCreate` carries `asset_type : u64`; \
         `noteCreateA (cm) (actor)` is asset-blind. Same reason as \
         `noteSpendA`.",
    ),
];

/// Tooth 3: the receipt summaries that name an asset, paired with the effect
/// that produces them.
const OBSERVATION_TO_EFFECT: &[(&str, &str)] = &[("Transfer", "Transfer"), ("Burned", "Burn")];

/// Tooth 3: asset-naming summaries with no single producing effect.
const OBSERVATION_WITHOUT_EFFECT: &[(&str, &str)] = &[(
    "Balance",
    "A post-state balance STAMP, not an effect summary — it is emitted for a \
     touched cell rather than produced by one `Effect` constructor, so there \
     is no counterpart to compare against.",
)];

/// Tooth 3: summary/effect pairs where the summary names an asset the effect
/// has no field for.
const OBSERVATION_GAP_EXEMPTIONS: &[(&str, &str)] = &[
    (
        "Transfer",
        "`EffectSummary::Transfer { from, to, asset, amount }` publishes an \
         `asset` that `Effect::Transfer { from, to, amount }` cannot express. \
         Whatever the node fills it with is derived downstream (the cells' \
         `token_id`), not read off the signed effect — the observation is \
         strictly wider than the authorization.",
    ),
    (
        "Burned",
        "`EffectSummary::Burned { cell, asset, amount }` publishes an `asset` \
         that `Effect::Burn { target, slot, amount }` cannot express. Same \
         gap as Transfer; the summary's doc says `the supply of `asset` \
         strictly decreases`, which the effect does not name.",
    ),
];

// ───────────────────────── extraction ─────────────────────────

/// Strip `//`-to-EOL and `/* … */`. Same shape as the cover gate's: the enum
/// bodies here contain no string literals outside comments, and the floors +
/// anchors below fail loudly if that ever stops being true.
fn strip_rust_comments(src: &str) -> String {
    let b = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'/' && i + 1 < b.len() && b[i + 1] == b'/' {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
        } else if b[i] == b'/' && i + 1 < b.len() && b[i + 1] == b'*' {
            i += 2;
            while i + 1 < b.len() && !(b[i] == b'*' && b[i + 1] == b'/') {
                i += 1;
            }
            i += 2;
        } else {
            out.push(b[i] as char);
            i += 1;
        }
    }
    out
}

/// Split a struct-variant field block on top-level commas (bracket-aware, so
/// `Option<[u8; 32]>` and `Box<Action>` do not split).
fn split_top_level(block: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut cur = String::new();
    for ch in block.chars() {
        match ch {
            '{' | '[' | '(' | '<' => {
                depth += 1;
                cur.push(ch);
            }
            '}' | ']' | ')' | '>' => {
                depth -= 1;
                cur.push(ch);
            }
            ',' if depth == 0 => {
                parts.push(std::mem::take(&mut cur));
            }
            _ => cur.push(ch),
        }
    }
    parts.push(cur);
    parts
}

/// The field name of one `name: Type` entry, attributes stripped.
fn field_name(part: &str) -> Option<String> {
    let mut s = part.trim();
    // drop leading `#[...]` attributes (possibly several)
    while s.starts_with('#') {
        let close = s.find(']')?;
        s = s[close + 1..].trim();
    }
    let s = s.strip_prefix("pub ").unwrap_or(s).trim();
    let colon = s.find(':')?;
    let name: String = s[..colon]
        .trim()
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect();
    if name.is_empty() { None } else { Some(name) }
}

/// Ordered `(variant, field names)` of a struct-like Rust enum. Tuple and unit
/// variants come back with an empty field list — none exist in either enum
/// today, and the floors below catch it if the shape changes.
fn rust_enum_variant_fields(src: &str, header: &str) -> Vec<(String, Vec<String>)> {
    let clean = strip_rust_comments(src);
    let start = clean
        .find(header)
        .unwrap_or_else(|| panic!("gate: `{header}` not found — enum renamed or moved?"));
    let body = &clean[start + header.len() - 1..]; // start at the `{`
    let b = body.as_bytes();
    let mut out: Vec<(String, Vec<String>)> = Vec::new();
    let mut depth = 0i32;
    let mut expecting = false;
    let mut i = 0usize;
    while i < b.len() {
        match b[i] {
            b'{' => {
                depth += 1;
                if depth == 1 {
                    expecting = true;
                }
                i += 1;
            }
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    break;
                }
                if depth == 1 {
                    expecting = true;
                }
                i += 1;
            }
            b',' if depth == 1 => {
                expecting = true;
                i += 1;
            }
            b'#' if depth == 1 => {
                let mut bd = 0i32;
                while i < b.len() {
                    match b[i] {
                        b'[' => bd += 1,
                        b']' => {
                            bd -= 1;
                            if bd == 0 {
                                i += 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                    i += 1;
                }
            }
            c if depth == 1 && expecting && (c as char).is_ascii_uppercase() => {
                let mut j = i;
                while j < b.len() && ((b[j] as char).is_ascii_alphanumeric() || b[j] == b'_') {
                    j += 1;
                }
                let name = body[i..j].to_string();
                let mut k = j;
                while k < b.len() && (b[k] as char).is_whitespace() {
                    k += 1;
                }
                let mut fields = Vec::new();
                if k < b.len() && b[k] == b'{' {
                    let mut d = 0i32;
                    let mut m = k;
                    while m < b.len() {
                        if b[m] == b'{' {
                            d += 1;
                        } else if b[m] == b'}' {
                            d -= 1;
                            if d == 0 {
                                break;
                            }
                        }
                        m += 1;
                    }
                    for part in split_top_level(&body[k + 1..m]) {
                        if let Some(f) = field_name(&part) {
                            fields.push(f);
                        }
                    }
                    j = m + 1; // resume after the field block
                }
                out.push((name, fields));
                expecting = false;
                i = j;
            }
            _ => i += 1,
        }
    }
    out
}

/// One `FullActionA` constructor as the Lean source states it.
#[derive(Debug)]
struct LeanCtor {
    /// Constructor name, e.g. `setFieldA`.
    ctor: String,
    /// `(parameter name, parameter type)`, flattened over grouped binders.
    params: Vec<(String, String)>,
    /// The Rust `Effect` variant the doc comment says this arm models.
    declared_variant: Option<String>,
    /// The Rust field list the doc comment declares — `None` when the doc
    /// deliberately abbreviates (contains `…`, or the braces are empty).
    declared_fields: Option<Vec<String>>,
}

impl LeanCtor {
    fn is_asset_indexed(&self) -> bool {
        self.params.iter().any(|(_, ty)| ty.trim() == "AssetId")
    }
}

/// Pull `Variant` + its declared field list out of a constructor's doc
/// comment: the first backtick-delimited span that starts with an uppercase
/// identifier. `a→b` entries contribute the RUST name `a`; `name : Type`
/// entries contribute `name`.
fn declared_from_doc(doc: &str) -> (Option<String>, Option<Vec<String>>) {
    let mut rest = doc;
    while let Some(open) = rest.find('`') {
        let after = &rest[open + 1..];
        let Some(close) = after.find('`') else { break };
        let span = after[..close].trim();
        rest = &after[close + 1..];
        let ident: String = span
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        if ident.is_empty() || !ident.starts_with(|c: char| c.is_ascii_uppercase()) {
            continue;
        }
        let tail = span[ident.len()..].trim();
        if !tail.starts_with('{') {
            continue; // a bare type/name mention, not a payload declaration
        }
        let Some(end) = tail.find('}') else { continue };
        let inner = &tail[1..end];
        // deliberately abbreviated: an ellipsis, or elided entirely (`{ }`)
        if inner.contains('…') || inner.contains("...") || inner.trim().is_empty() {
            return (Some(ident), None);
        }
        let fields: Vec<String> = inner
            .split(',')
            .filter_map(|f| {
                let f = f.trim().trim_matches('`');
                let f = f.split('→').next().unwrap_or(f);
                let f = f.split(':').next().unwrap_or(f);
                let f: String = f
                    .trim()
                    .chars()
                    .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                    .collect();
                if f.is_empty() { None } else { Some(f) }
            })
            .collect();
        return (Some(ident), Some(fields));
    }
    (None, None)
}

/// Extract `inductive FullActionA` from the Lean source: each `| ctor (…)`
/// line plus the doc comment immediately above it.
fn lean_full_action_ctors(src: &str) -> Vec<LeanCtor> {
    let start = src
        .find("inductive FullActionA where")
        .expect("gate: `inductive FullActionA where` not found in PerAsset.lean");
    let body = &src[start..];
    // The inductive ends where the next top-level `def` begins.
    let end = body
        .find("\ndef ")
        .expect("gate: end of the `FullActionA` inductive not found");
    let body = &body[..end];

    let mut out = Vec::new();
    let mut doc = String::new();
    for line in body.lines().skip(1) {
        let t = line.trim();
        if let Some(after) = t.strip_prefix('|') {
            let after = after.trim();
            let ctor: String = after
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            let mut params = Vec::new();
            let mut rest = &after[ctor.len()..];
            while let Some(open) = rest.find('(') {
                let Some(close) = rest[open..].find(')') else {
                    break;
                };
                let binder = &rest[open + 1..open + close];
                if let Some((names, ty)) = binder.split_once(':') {
                    for n in names.split_whitespace() {
                        params.push((n.to_string(), ty.trim().to_string()));
                    }
                }
                rest = &rest[open + close + 1..];
            }
            let (declared_variant, declared_fields) = declared_from_doc(&doc);
            out.push(LeanCtor {
                ctor,
                params,
                declared_variant,
                declared_fields,
            });
            doc.clear();
        } else if t.starts_with("--") {
            // a section comment, not a doc comment — it belongs to no ctor
            doc.clear();
        } else {
            doc.push(' ');
            doc.push_str(t);
        }
    }
    out
}

fn reason_for<'a>(table: &'a [(&'a str, &'a str)], key: &str) -> Option<&'a str> {
    table.iter().find(|(k, _)| *k == key).map(|(_, r)| *r)
}

// ───────────────────────── tooth 1 ─────────────────────────

#[test]
fn lean_declared_effect_payloads_match_the_rust_fields() {
    let rust = rust_enum_variant_fields(ACTION_RS, "pub enum Effect {");
    let lean = lean_full_action_ctors(PER_ASSET_LEAN);

    // Anti-vacuity: a broken extractor must fail HERE, not pass on empty sets.
    assert!(
        rust.len() >= 36,
        "gate extractor floor: only {} `Effect` variants parsed — extractor broken?",
        rust.len()
    );
    assert!(
        lean.len() >= 30,
        "gate extractor floor: only {} `FullActionA` constructors parsed — extractor broken?",
        lean.len()
    );
    assert_eq!(
        rust.first().map(|(n, _)| n.as_str()),
        Some("SetField"),
        "gate anchor: first `Effect` variant should be SetField"
    );
    assert_eq!(
        rust.iter().find(|(n, _)| n == "Transfer").map(|(_, f)| f),
        Some(&vec!["from".into(), "to".into(), "amount".into()]),
        "gate anchor: the Rust field extractor must see Transfer's three fields"
    );

    let mut mismatched: Vec<String> = Vec::new();
    let mut unknown_variant: Vec<String> = Vec::new();
    let mut compared = 0usize;
    let mut exemptions_used: Vec<&str> = Vec::new();

    for c in &lean {
        let Some(v) = c.declared_variant.as_deref() else {
            continue;
        };
        let Some((_, actual)) = rust.iter().find(|(n, _)| n == v) else {
            if reason_for(LEAN_ONLY_MODELS, v).is_none() {
                unknown_variant.push(format!(
                    "  `{}` (Lean ctor `{}`) declares an `Effect` variant that does not exist \
                     — renamed, removed, or a new Lean-only model needing a LEAN_ONLY_MODELS row",
                    v, c.ctor
                ));
            }
            continue;
        };
        let Some(declared) = c.declared_fields.as_ref() else {
            continue; // doc deliberately abbreviates
        };
        compared += 1;
        let agrees = declared == actual;
        match (agrees, reason_for(FIELD_SHAPE_EXEMPTIONS, v)) {
            (true, None) => {}
            (false, Some(_)) => exemptions_used.push(v),
            (false, None) => mismatched.push(format!(
                "  {v} (Lean ctor `{}`)\n      Lean declares: {declared:?}\n      Rust  \
                 actually: {actual:?}",
                c.ctor
            )),
            (true, Some(_)) => mismatched.push(format!(
                "  {v} (Lean ctor `{}`) — STALE EXEMPTION: the field lists now AGREE ({actual:?}). \
                 Delete its FIELD_SHAPE_EXEMPTIONS row.",
                c.ctor
            )),
        }
    }

    assert!(
        compared >= MIN_COMPARED,
        "gate would be vacuous: only {compared} complete field-list declarations found in \
         `FullActionA` (floor {MIN_COMPARED}). The Lean doc convention \
         (``Variant {{ f, f }}`` opening each constructor's doc comment) moved — the gate is \
         comparing almost nothing. Fix the extractor, do not lower the floor."
    );

    // Every LEAN_ONLY_MODELS row must still be needed.
    let declared_names: Vec<&str> = lean
        .iter()
        .filter_map(|c| c.declared_variant.as_deref())
        .collect();
    for (name, _) in LEAN_ONLY_MODELS {
        assert!(
            declared_names.contains(name),
            "STALE LEAN_ONLY_MODELS row `{name}`: no `FullActionA` doc comment declares it any \
             more. Delete the row."
        );
        assert!(
            !rust.iter().any(|(n, _)| n == name),
            "STALE LEAN_ONLY_MODELS row `{name}`: an `Effect` variant of that name now EXISTS, so \
             it is no longer Lean-only. Delete the row and let the field lists be compared."
        );
    }

    assert!(
        mismatched.is_empty() && unknown_variant.is_empty(),
        "EFFECT PAYLOAD SHAPE drift — the Lean model declares a payload the wire does not have.\n\
         \n\
         A field was added to, removed from, renamed in, or reordered within an `Effect` variant \
         without the Lean model that refines it moving. The cover gate cannot see this: it \
         compares NAMES only.\n\
         \n\
         Field-list divergences ({}):\n{}\n\
         Declared variants with no `Effect` ({}):\n{}\n\
         Fix by updating the `FullActionA` constructor + its declaring doc comment in\n\
         metatheory/Dregg2/Exec/TurnExecutorFull/PerAsset.lean, or — if the divergence is \
         intended — add a NAMED row with its reason to FIELD_SHAPE_EXEMPTIONS in this file.\n\
         ({} declarations compared, {} exempt)",
        mismatched.len(),
        if mismatched.is_empty() {
            "  (none)".into()
        } else {
            mismatched.join("\n")
        },
        unknown_variant.len(),
        if unknown_variant.is_empty() {
            "  (none)".into()
        } else {
            unknown_variant.join("\n")
        },
        compared,
        exemptions_used.len(),
    );
}

// ───────────────────────── tooth 2 ─────────────────────────

/// Does this Rust variant carry an asset index? Field-NAME based, because the
/// types differ across variants (`u64` here, nothing there) while the naming
/// convention (`asset_type`) is uniform.
fn rust_carries_asset(fields: &[String]) -> bool {
    fields.iter().any(|f| f.contains("asset"))
}

#[test]
fn asset_index_parity_between_effects_and_the_lean_per_asset_model() {
    let rust = rust_enum_variant_fields(ACTION_RS, "pub enum Effect {");
    let lean = lean_full_action_ctors(PER_ASSET_LEAN);

    // Anti-vacuity, both directions: if either detector sees nothing, the
    // parity check below is trivially satisfiable and proves nothing.
    let rust_indexed: Vec<&str> = rust
        .iter()
        .filter(|(_, f)| rust_carries_asset(f))
        .map(|(n, _)| n.as_str())
        .collect();
    let lean_indexed: Vec<&str> = lean
        .iter()
        .filter(|c| c.is_asset_indexed())
        .map(|c| c.ctor.as_str())
        .collect();
    assert!(
        !rust_indexed.is_empty(),
        "gate would be vacuous: NO `Effect` variant carries an asset field. Either the naming \
         convention moved off `asset*` or the extractor broke."
    );
    assert!(
        !lean_indexed.is_empty(),
        "gate would be vacuous: NO `FullActionA` constructor takes an `AssetId`. Either the \
         per-asset model moved or the extractor broke."
    );

    let mut divergent: Vec<String> = Vec::new();
    let mut uncharted: Vec<String> = Vec::new();
    let mut checked = 0usize;

    for c in &lean {
        // Counterpart: declared by the Lean doc, else the named table.
        let counterpart: Option<&str> = c.declared_variant.as_deref().or_else(|| {
            UNDECLARED_COUNTERPARTS
                .iter()
                .find(|(ctor, _, _)| *ctor == c.ctor)
                .map(|(_, v, _)| *v)
        });
        let Some(v) = counterpart else {
            // An asset-indexed Lean arm with no known Rust counterpart is a
            // decision someone has to make, not something to skip past.
            if c.is_asset_indexed() {
                uncharted.push(format!(
                    "  `{}` takes an `AssetId` but declares no Rust counterpart and has no \
                     UNDECLARED_COUNTERPARTS row",
                    c.ctor
                ));
            }
            continue;
        };
        let Some((_, fields)) = rust.iter().find(|(n, _)| n == v) else {
            continue; // Lean-only model; tooth 1 adjudicates those
        };
        checked += 1;
        let agrees = rust_carries_asset(fields) == c.is_asset_indexed();
        match (agrees, reason_for(ASSET_INDEX_EXEMPTIONS, &c.ctor)) {
            (true, None) => {}
            (false, Some(_)) => {}
            (false, None) => divergent.push(format!(
                "  `{}` ({}): Lean asset-indexed = {}, Rust `Effect::{v}` carries an asset field \
                 = {} (fields {:?})",
                c.ctor,
                v,
                c.is_asset_indexed(),
                rust_carries_asset(fields),
                fields
            )),
            (true, Some(_)) => divergent.push(format!(
                "  `{}` ({v}) — STALE EXEMPTION: the asset index now AGREES on both sides. \
                 Delete its ASSET_INDEX_EXEMPTIONS row.",
                c.ctor
            )),
        }
    }

    assert!(
        checked >= 20,
        "gate would be vacuous: only {checked} Lean/Rust counterpart pairs resolved. The doc-\
         declared correspondence broke."
    );

    // No UNDECLARED_COUNTERPARTS row may name a constructor or variant that
    // has since vanished, or one the Lean doc now declares itself.
    for (ctor, variant, _) in UNDECLARED_COUNTERPARTS {
        let c = lean.iter().find(|c| c.ctor == *ctor).unwrap_or_else(|| {
            panic!(
                "STALE UNDECLARED_COUNTERPARTS row: no `FullActionA` \
                 constructor `{ctor}`. Delete or update the row."
            )
        });
        assert!(
            c.declared_variant.is_none(),
            "STALE UNDECLARED_COUNTERPARTS row `{ctor}`: the Lean doc comment now declares \
             `{}` itself. Delete the row — the source states the correspondence.",
            c.declared_variant.as_deref().unwrap_or("?")
        );
        assert!(
            rust.iter().any(|(n, _)| n == variant),
            "STALE UNDECLARED_COUNTERPARTS row `{ctor}` -> `{variant}`: no such `Effect` variant."
        );
    }

    assert!(
        divergent.is_empty() && uncharted.is_empty(),
        "ASSET-INDEX drift between the wire effect and the Lean per-asset model.\n\
         \n\
         One side commits an asset index and the other does not. This is the exact shape of the \
         `recTransfer` (scalar) vs `recTransferBal` (asset-indexed) split: an executor guard that \
         cites the indexed kernel while the effect it guards has no asset operand has to \
         substitute something else, and `apply.rs:673` substitutes `token_id`, which \
         `cell/src/cell.rs:314` defines as the CellId derivation nonce.\n\
         \n\
         Parity failures ({}):\n{}\n\
         Asset-indexed Lean arms with no charted counterpart ({}):\n{}\n\
         Either give both sides the index, or add a NAMED row with its reason to \
         ASSET_INDEX_EXEMPTIONS in this file. ({checked} pairs checked)",
        divergent.len(),
        if divergent.is_empty() {
            "  (none)".into()
        } else {
            divergent.join("\n")
        },
        uncharted.len(),
        if uncharted.is_empty() {
            "  (none)".into()
        } else {
            uncharted.join("\n")
        },
    );
}

// ───────────────────────── tooth 3 ─────────────────────────

#[test]
fn observations_do_not_name_an_index_the_effect_cannot_express() {
    let rust = rust_enum_variant_fields(ACTION_RS, "pub enum Effect {");
    let summaries = rust_enum_variant_fields(RECEIPT_RS, "pub enum EffectSummary {");

    assert!(
        summaries.len() >= 9,
        "gate extractor floor: only {} `EffectSummary` variants parsed — extractor broken?",
        summaries.len()
    );

    let asset_naming: Vec<&(String, Vec<String>)> = summaries
        .iter()
        .filter(|(_, f)| rust_carries_asset(f))
        .collect();
    assert!(
        !asset_naming.is_empty(),
        "gate would be vacuous: NO `EffectSummary` variant names an asset."
    );

    let mut gaps: Vec<String> = Vec::new();
    let mut uncharted: Vec<String> = Vec::new();

    for (name, fields) in &asset_naming {
        let mapped = OBSERVATION_TO_EFFECT
            .iter()
            .find(|(s, _)| s == name)
            .map(|(_, e)| *e);
        let Some(effect) = mapped else {
            if reason_for(OBSERVATION_WITHOUT_EFFECT, name).is_none() {
                uncharted.push(format!(
                    "  `EffectSummary::{name}` names an asset ({fields:?}) but is in neither \
                     OBSERVATION_TO_EFFECT nor OBSERVATION_WITHOUT_EFFECT"
                ));
            }
            continue;
        };
        let Some((_, efields)) = rust.iter().find(|(n, _)| n == effect) else {
            uncharted.push(format!(
                "  OBSERVATION_TO_EFFECT maps `{name}` -> `Effect::{effect}`, which does not exist"
            ));
            continue;
        };
        let gap = !rust_carries_asset(efields);
        match (gap, reason_for(OBSERVATION_GAP_EXEMPTIONS, name)) {
            (false, None) => {}
            (true, Some(_)) => {}
            (true, None) => gaps.push(format!(
                "  `EffectSummary::{name}` {fields:?} names an asset; `Effect::{effect}` \
                 {efields:?} has no asset field"
            )),
            (false, Some(_)) => gaps.push(format!(
                "  `{name}` -> `{effect}` — STALE EXEMPTION: the effect now carries an asset \
                 field ({efields:?}). Delete its OBSERVATION_GAP_EXEMPTIONS row."
            )),
        }
    }

    for (name, _) in OBSERVATION_WITHOUT_EFFECT {
        assert!(
            summaries.iter().any(|(n, _)| n == name),
            "STALE OBSERVATION_WITHOUT_EFFECT row `{name}`: no such `EffectSummary` variant."
        );
    }

    assert!(
        gaps.is_empty() && uncharted.is_empty(),
        "OBSERVATION/EFFECT index gap.\n\
         \n\
         The receipt layer publishes a field the signed effect cannot express, so what a consumer \
         reads is wider than what the actor authorized.\n\
         \n\
         Gaps ({}):\n{}\n\
         Uncharted asset-naming summaries ({}):\n{}\n\
         Either give the effect the field, or add a NAMED row with its reason to \
         OBSERVATION_GAP_EXEMPTIONS in this file.",
        gaps.len(),
        if gaps.is_empty() {
            "  (none)".into()
        } else {
            gaps.join("\n")
        },
        uncharted.len(),
        if uncharted.is_empty() {
            "  (none)".into()
        } else {
            uncharted.join("\n")
        },
    );
}
