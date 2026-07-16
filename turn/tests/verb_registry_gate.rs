//! # The wire↔registry classification ratchet.
//!
//! GATE: every `Effect` wire variant (`turn/src/action.rs`) MUST be classified in the
//! Lean verb registry (`metatheory/Dregg2/Substrate/VerbRegistry.lean`) under the
//! four-substance discipline. This test makes the cover un-driftable from the RUST side,
//! the direction the Lean compiler cannot see (Lean's own exhaustiveness check on
//! `classify` fires only when `EffectTag` grows — it cannot know `action.rs` grew).
//!
//! ## Mechanism (why this cannot drift silently)
//!
//! The chain has three links, each closing a distinct drift channel:
//!
//! 1. **Compile-time exhaustiveness anchor.** `effect_roster!` expands to BOTH the
//!    `EFFECT_TAGS` roster const AND an exhaustive wildcard-free `match` over `Effect`
//!    from the SAME token list. Adding a wire variant makes the match non-exhaustive —
//!    a COMPILE ERROR in this test — and the only fix (adding the variant to the macro
//!    invocation) necessarily extends `EFFECT_TAGS`. So the Rust roster cannot lag the
//!    Rust enum. (This is the reified-tag exhaustiveness check: no reflection, no deps.)
//!
//! 2. **Cross-language pin.** The test `include_str!`s the Lean registry SOURCE (the
//!    proven artifact itself — not an emitted mirror that could be regenerated stale)
//!    and asserts `EFFECT_TAGS` equals the `allEffectTags` roster EXACTLY, in order.
//!    A variant added to Rust without a Lean classification fails here; a tag deleted
//!    from Rust but kept in Lean fails here too (both drift directions).
//!
//! 3. **Lean-side closure.** In the registry, `classify` is total over `EffectTag` by
//!    compiler exhaustiveness, and `roster_complete` proves `∀ t : EffectTag,
//!    t ∈ allEffectTags` — so pinning against the roster TEXT is pinning against the
//!    TYPE, and every roster tag provably lands in a `Classification` bucket. The
//!    text-level checks below (classify-arm census + the count-theorem needle) are a
//!    redundant tooth that fires even when Lean CI is not in the loop.
//!
//! Net: wire variant added → (1) compile error → roster extended → (2) test red until
//! the Lean registry classifies it → (3) Lean will not compile a classification gap.
//! The cover cannot drift silently again.
//!
//! (Path note: `include_str!` resolves relative to THIS file, so the gate requires the
//! sibling `metatheory/` tree — true for the workspace checkout this gate protects.)

use dregg_turn::action::Effect;

/// One list of tokens → the roster const + the exhaustiveness anchor. The single
/// source of truth on the Rust side; see module header, link (1).
macro_rules! effect_roster {
    ($($variant:ident),* $(,)?) => {
        /// The wire roster, in `action.rs` declaration order.
        const EFFECT_TAGS: &[&str] = &[$(stringify!($variant)),*];

        /// THE RATCHET TOOTH — an exhaustive, wildcard-free match over `Effect`.
        /// A new wire variant makes this non-exhaustive: compile error, here, first.
        /// Never add a `_` arm; the whole point is that the compiler refuses a gap.
        #[allow(dead_code)]
        fn effect_tag_name(e: &Effect) -> &'static str {
            match e {
                $(Effect::$variant { .. } => stringify!($variant),)*
            }
        }
    };
}

effect_roster!(
    SetField,
    Transfer,
    GrantCapability,
    RevokeCapability,
    EmitEvent,
    IncrementNonce,
    CreateCell,
    SetPermissions,
    SetVerificationKey,
    SetProgram,
    NoteSpend,
    NoteCreate,
    SpawnWithDelegation,
    RefreshDelegation,
    RevokeDelegation,
    BridgeMint,
    Introduce,
    PipelinedSend,
    ExerciseViaCapability,
    MakeSovereign,
    CreateCellFromFactory,
    Refusal,
    CellSeal,
    CellUnseal,
    CellDestroy,
    Burn,
    AttenuateCapability,
    ReceiptArchive,
    Promise,
    Notify,
    React,
    Mint,
    ShieldedTransfer,
    Custom,
);

/// The Lean registry source — the pin target (see module header, link (2)).
const VERB_REGISTRY_LEAN: &str =
    include_str!("../../metatheory/Dregg2/Substrate/VerbRegistry.lean");

/// Extract the `.Tag` idents from the `allEffectTags` roster block, in order.
fn lean_roster() -> Vec<&'static str> {
    let start = VERB_REGISTRY_LEAN
        .find("def allEffectTags : List EffectTag :=")
        .expect("VerbRegistry.lean must define `allEffectTags : List EffectTag`");
    let block = &VERB_REGISTRY_LEAN[start..];
    let open = block
        .find('[')
        .expect("allEffectTags roster must open with `[`");
    let close = block[open..]
        .find(']')
        .map(|i| open + i)
        .expect("allEffectTags roster must close with `]`");
    dot_idents(&block[open..close])
}

/// Extract the `.Tag` idents of the `classify` match arms (`| .Tag => ...`), in order.
fn lean_classify_arms() -> Vec<&'static str> {
    let start = VERB_REGISTRY_LEAN
        .find("def classify : EffectTag → Classification")
        .expect("VerbRegistry.lean must define `classify : EffectTag → Classification`");
    let mut arms = Vec::new();
    for line in VERB_REGISTRY_LEAN[start..].lines().skip(1) {
        let t = line.trim_start();
        if t.starts_with("| .") {
            arms.extend(dot_idents(t.split("=>").next().unwrap_or(t)));
        } else if line.starts_with("/-!")
            || line.starts_with("def ")
            || line.starts_with("theorem ")
        {
            break; // end of the classify block (§8 follows)
        }
    }
    arms
}

/// All `.Ident` tokens in `s` (an ident is `[A-Za-z0-9_]+` right after a `.`).
fn dot_idents(s: &'static str) -> Vec<&'static str> {
    let bytes = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'.' {
            let start = i + 1;
            let mut end = start;
            while end < bytes.len() && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_') {
                end += 1;
            }
            // an EffectTag constructor is capitalized; skip `.length` etc.
            if end > start && bytes[start].is_ascii_uppercase() {
                out.push(&s[start..end]);
            }
            i = end;
        } else {
            i += 1;
        }
    }
    out
}

/// Link (2): the Rust wire roster and the Lean `allEffectTags` roster are IDENTICAL,
/// element for element, in declaration order. Fails on EITHER drift direction with a
/// diff naming the offending tags.
#[test]
fn rust_wire_roster_equals_lean_all_effect_tags() {
    let lean = lean_roster();
    let missing_in_lean: Vec<_> = EFFECT_TAGS.iter().filter(|t| !lean.contains(t)).collect();
    let stale_in_lean: Vec<_> = lean.iter().filter(|t| !EFFECT_TAGS.contains(t)).collect();
    assert!(
        missing_in_lean.is_empty() && stale_in_lean.is_empty(),
        "wire↔registry roster drift.\n  Rust variants with NO Lean registry tag \
         (classify them in VerbRegistry.lean): {missing_in_lean:?}\n  Lean tags with NO \
         live Rust variant (retire them): {stale_in_lean:?}"
    );
    assert_eq!(
        EFFECT_TAGS,
        lean.as_slice(),
        "same tag sets but DIFFERENT order — allEffectTags must mirror action.rs \
         declaration order"
    );
}

/// Redundant tooth for link (3), live even without Lean CI: every roster tag has a
/// `classify` match arm in the registry text, and no arm is stale.
#[test]
fn every_wire_variant_has_a_classify_arm() {
    let arms = lean_classify_arms();
    let unclassified: Vec<_> = EFFECT_TAGS.iter().filter(|t| !arms.contains(t)).collect();
    let stale: Vec<_> = arms.iter().filter(|t| !EFFECT_TAGS.contains(t)).collect();
    assert!(
        unclassified.is_empty() && stale.is_empty(),
        "classification cover drift.\n  wire variants with NO classify arm: \
         {unclassified:?}\n  classify arms over NO live wire variant: {stale:?}"
    );
}

/// The Lean count theorem (`effect_tag_count`) pins the SAME number this enum has —
/// so the human-facing census in the registry prose cannot silently understate the wire.
#[test]
fn lean_count_theorem_matches_wire_count() {
    let needle = format!("allEffectTags.length = {}", EFFECT_TAGS.len());
    assert!(
        VERB_REGISTRY_LEAN.contains(&needle),
        "VerbRegistry.lean must state `theorem effect_tag_count : {needle}` \
         (wire enum has {} variants)",
        EFFECT_TAGS.len()
    );
}
