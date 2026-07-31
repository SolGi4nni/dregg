//! # The crown board's trust root — **and where it came from.**
//!
//! Two crown boards rank the same cross-surface folds: `discord-bot`'s in-process
//! [`crate::GameBoard`] and `dreggnet-web`'s `/crown`. Both verify every submitted
//! `WholeChainProof` against a per-game [`ProofAnchor`] (VK + genesis root + WIN root), and
//! that anchor is the boards' **entire trust root**: read it off the proof under test and the
//! genesis binding and the WIN binding become self-comparisons, and the submitter picks their
//! own win.
//!
//! ## ⚑ MEASURED 2026-07-30 — WHAT THE BOARDS ACTUALLY DID
//!
//! Both surfaces had a `canonical_anchor(_game) -> Option<ProofAnchor>` that returned `None`
//! unconditionally, so both fell through to `row.anchor()` / `match_anchor(&proof)` — **the
//! anchor built from the FIRST submitter's own wire.** `ensure_open` is write-once, so that
//! anchor then **froze forever**. Every later fold on that board was checked against a trust
//! root one player minted, and the surfaces said, in public:
//!
//! * `POST /crown/ingest` → `"verified": true`, *"nothing was taken on the sender's word"*;
//! * the Discord crown post → *"You do not have to trust the winner."*
//!
//! You do. They chose the anchor. That is the most damaging shape this class takes, because a
//! stranger reads it and acts on it.
//!
//! ## THE REPAIR
//!
//! An anchor may come from **operator configuration** — an environment variable set by whoever
//! runs the board, which no submitter can write — via [`operator_anchor`]. When one is
//! configured, a ✓ on that board is a statement about the fold. When one is not, the board
//! still bootstraps (a board that refuses everything until an operator does paperwork is a
//! board nobody uses), but the provenance travels with **every verdict** as
//! [`AnchorProvenance::BootstrappedFromSubmission`], and the surfaces say plainly that they are
//! ranking self-reported claims.
//!
//! Both boards read the SAME variable through the SAME parser, deliberately: they must agree
//! about what they are pinned to, or a cross-surface fold can never rank on both.
//!
//! ## THE SPEC FORMAT
//!
//! ```text
//! CROWN_ANCHOR_AUTOMATAFL='<64 hex vk>:<g0,g1,…,g7>:<w0,w1,…,w7>'
//! ```
//!
//! * the VK fingerprint as 64 lowercase hex characters;
//! * the genesis state anchor as [`SEG_ANCHOR_WIDTH`] decimal `BabyBear` limbs;
//! * the WIN state anchor, same shape.
//!
//! A malformed spec is an **`Err`, never a fallback**: an operator who meant to pin a board and
//! typo'd the variable must not silently get the bootstrap they were trying to avoid. Callers
//! surface the error and refuse to start rather than downgrade.
//!
//! Emit a spec for a fold you trust with [`anchor_spec`].

use std::fmt;

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{RecursionVk, SEG_ANCHOR_WIDTH};

use crate::{Game, ProofAnchor};

/// The env-var prefix an operator sets to pin a game's board anchor. The full name is this
/// prefix plus the game's slug, uppercased with `-` → `_`: `CROWN_ANCHOR_MULTIWAY_TUG`,
/// `CROWN_ANCHOR_AUTOMATAFL`.
pub const CROWN_ANCHOR_ENV_PREFIX: &str = "CROWN_ANCHOR_";

/// **Where a board's trust root came from.** Rides on every verdict either board prints, so a
/// reader never has to go looking for the one fact that decides what a ✓ is worth.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AnchorProvenance {
    /// The anchor came from [`operator_anchor`] — configuration held by whoever runs the board,
    /// which no submitter can write. A fold accepted against it is a statement about the fold.
    OperatorConfigured,
    /// **No operator anchor was configured**, so the board pinned itself to the first fold that
    /// survived a probe, and froze there. Every later fold is checked against a trust root a
    /// submitter minted from their own wire. The board is ranking self-reported claims.
    BootstrappedFromSubmission,
}

impl AnchorProvenance {
    /// The stable machine-readable token — what a JSON consumer branches on.
    pub fn token(self) -> &'static str {
        match self {
            AnchorProvenance::OperatorConfigured => "operator-configured",
            AnchorProvenance::BootstrappedFromSubmission => "bootstrapped-from-first-submission",
        }
    }

    /// Whether an accept against this anchor is a **trust decision** rather than a consistency
    /// check. This is the ONE predicate a surface may gate the word "verified" on.
    pub fn is_trust_decision(self) -> bool {
        matches!(self, AnchorProvenance::OperatorConfigured)
    }

    /// The sentence a human-facing surface prints beside the verdict.
    pub fn sentence(self, game: Game) -> String {
        match self {
            AnchorProvenance::OperatorConfigured => format!(
                "the anchor this fold was checked against is operator configuration \
                 ({}{}), held before any submission arrived — no submitter can write it",
                CROWN_ANCHOR_ENV_PREFIX,
                env_suffix(game),
            ),
            AnchorProvenance::BootstrappedFromSubmission => format!(
                "⚠ no operator anchor is configured for this board, so its trust root was taken \
                 from the FIRST accepted fold's own wire and frozen there. Every row is checked \
                 against a genesis and a WIN root that a submitter chose, so this board is \
                 RANKING SELF-REPORTED CLAIMS. Pin it by setting {}{}",
                CROWN_ANCHOR_ENV_PREFIX,
                env_suffix(game),
            ),
        }
    }
}

impl fmt::Display for AnchorProvenance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.token())
    }
}

/// The env-var suffix for a game (`AUTOMATAFL`, `MULTIWAY_TUG`).
pub fn env_suffix(game: Game) -> String {
    game.slug().to_ascii_uppercase().replace('-', "_")
}

/// The full env-var name a board reads for `game`.
pub fn env_var_name(game: Game) -> String {
    format!("{CROWN_ANCHOR_ENV_PREFIX}{}", env_suffix(game))
}

/// **The operator-configured anchor for `game`, if one is set.**
///
/// `Ok(None)` = the variable is unset or empty: the caller bootstraps and MUST report
/// [`AnchorProvenance::BootstrappedFromSubmission`].
/// `Err` = the variable is set and malformed. **Never fall back on this arm** — an operator who
/// meant to pin a board and mistyped the spec would otherwise silently get exactly the
/// submitter-chosen anchor they were configuring their way out of.
pub fn operator_anchor(game: Game) -> Result<Option<ProofAnchor>, String> {
    match std::env::var(env_var_name(game)) {
        Err(_) => Ok(None),
        Ok(raw) if raw.trim().is_empty() => Ok(None),
        Ok(raw) => parse_anchor_spec(&raw)
            .map(Some)
            .map_err(|e| format!("{} is set but malformed: {e}", env_var_name(game))),
    }
}

/// Parse a `<64 hex vk>:<8 limbs>:<8 limbs>` spec. See the module docs.
pub fn parse_anchor_spec(spec: &str) -> Result<ProofAnchor, String> {
    let parts: Vec<&str> = spec.trim().split(':').collect();
    if parts.len() != 3 {
        return Err(format!(
            "want `<64 hex vk>:<{n} genesis limbs>:<{n} win limbs>` (three colon-separated \
             fields), got {} field(s)",
            parts.len(),
            n = SEG_ANCHOR_WIDTH,
        ));
    }
    let vk_hex = parts[0].trim();
    if vk_hex.len() != 64 || !vk_hex.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(format!(
            "the vk field must be exactly 64 hex characters, got {} character(s)",
            vk_hex.len()
        ));
    }
    let mut vk = [0u8; 32];
    for (i, byte) in vk.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&vk_hex[2 * i..2 * i + 2], 16)
            .map_err(|e| format!("the vk field is not hex: {e}"))?;
    }
    let genesis = parse_limbs(parts[1], "genesis")?;
    let win = parse_limbs(parts[2], "win")?;
    Ok(ProofAnchor::new(RecursionVk(vk), genesis, win))
}

/// Render an anchor back to the spec format, so an operator can pin a board to a fold they
/// have already checked: emit this from the fold, then set the env var.
pub fn anchor_spec(anchor: &ProofAnchor) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(64 + 2 + SEG_ANCHOR_WIDTH * 22);
    for b in anchor.vk.0.iter() {
        let _ = write!(out, "{b:02x}");
    }
    out.push(':');
    for (i, limb) in anchor.genesis_root.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let _ = write!(out, "{}", limb.0);
    }
    out.push(':');
    for (i, limb) in anchor.win_root.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let _ = write!(out, "{}", limb.0);
    }
    out
}

fn parse_limbs(field: &str, which: &str) -> Result<[BabyBear; SEG_ANCHOR_WIDTH], String> {
    let raw: Vec<&str> = field.trim().split(',').map(str::trim).collect();
    if raw.len() != SEG_ANCHOR_WIDTH {
        return Err(format!(
            "the {which} field must be exactly {SEG_ANCHOR_WIDTH} comma-separated decimal limbs, \
             got {}",
            raw.len()
        ));
    }
    let mut out = [BabyBear::new(0); SEG_ANCHOR_WIDTH];
    for (i, slot) in out.iter_mut().enumerate() {
        let v: u32 = raw[i].parse().map_err(|e| {
            format!(
                "the {which} field's limb {i} (`{}`) is not a u32: {e}",
                raw[i]
            )
        })?;
        // `BabyBear::new` reduces, so a spec limb at or above the modulus becomes its canonical
        // representative rather than a value the comparison could never match.
        *slot = BabyBear::new(v);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> ProofAnchor {
        ProofAnchor::new(
            RecursionVk([0xAB; 32]),
            [1, 2, 3, 4, 5, 6, 7, 8].map(BabyBear::new),
            [9, 10, 11, 12, 13, 14, 15, 16].map(BabyBear::new),
        )
    }

    #[test]
    fn a_spec_round_trips() {
        let a = sample();
        let parsed = parse_anchor_spec(&anchor_spec(&a)).expect("the emitted spec parses");
        assert_eq!(parsed.vk.0, a.vk.0);
        assert_eq!(
            parsed.genesis_root.map(|f| f.0),
            a.genesis_root.map(|f| f.0)
        );
        assert_eq!(parsed.win_root.map(|f| f.0), a.win_root.map(|f| f.0));
    }

    /// ⚑ A MALFORMED SPEC IS AN ERROR, NOT A FALLBACK. This is the whole point of returning
    /// `Result<Option<_>>` rather than `Option<_>`: an operator pinning a board and mistyping
    /// the value must not be silently handed the submitter-chosen anchor they were configuring
    /// their way out of.
    #[test]
    fn a_malformed_spec_is_refused_and_never_downgraded() {
        for bad in [
            "",
            "notanchor",
            "ab:1,2,3,4,5,6,7,8:1,2,3,4,5,6,7,8",
            "zz00:1,2,3,4,5,6,7,8:1,2,3,4,5,6,7,8",
            &format!("{}:1,2,3:1,2,3,4,5,6,7,8", "ab".repeat(32)),
            &format!("{}:1,2,3,4,5,6,7,8", "ab".repeat(32)),
        ] {
            assert!(
                parse_anchor_spec(bad).is_err(),
                "a malformed anchor spec must be REFUSED, not coerced: {bad:?}"
            );
        }
    }

    #[test]
    fn the_env_var_name_is_the_slug_upcased() {
        assert_eq!(env_var_name(Game::Automatafl), "CROWN_ANCHOR_AUTOMATAFL");
        assert_eq!(env_var_name(Game::MultiwayTug), "CROWN_ANCHOR_MULTIWAY_TUG");
    }

    /// The provenance's own contract: exactly one variant licenses the word "verified".
    #[test]
    fn only_an_operator_anchor_is_a_trust_decision() {
        assert!(AnchorProvenance::OperatorConfigured.is_trust_decision());
        assert!(!AnchorProvenance::BootstrappedFromSubmission.is_trust_decision());
        let warn = AnchorProvenance::BootstrappedFromSubmission.sentence(Game::Automatafl);
        assert!(
            warn.contains("SELF-REPORTED") && warn.contains("CROWN_ANCHOR_AUTOMATAFL"),
            "the bootstrap sentence must name what the board is doing AND how to stop it: {warn}"
        );
    }
}
