//! # attested-dm — the provably-honest, un-jailbreakable AI dungeon-master
//!
//! A **confined + attested LLM** narrates an on-chain interactive world. Each narration
//! / NPC-response is a **receipted attested turn** advancing a [`WorldCell`], carrying a
//! [`dregg_zkoracle_prove::ZkOracleAttestation`] proving the turn was:
//!
//! ```text
//!   authentic     — from a real model (a genuine `/v1/messages` session), not forged;
//!   well-formed   — the response body lies in the JSON context-free language;
//!   injection-free — the bound narration carries no `{{` handlebars delimiter.
//! ```
//!
//! ## The killer property — un-jailbreakable
//!
//! A player message that carries a **prompt-injection** (`{{`, or the handlebars
//! injection template) is **reflected into the DM's narration** — a game-master answers
//! *what the player said* — and there the **injection-free leg** catches it: the DM's
//! turn over that input **cannot be attested** ([`DmError::Injection`]), so the turn is
//! **refused** and the world advances not at all (the anti-ghost tooth — a refused turn
//! leaves no receipt). A player therefore **cannot prompt-inject the DM** into breaking
//! the game's rules. This is not a heuristic filter bolted on top; it is the same
//! verified `neg`-complement matcher `verify_zkoracle` runs, so a forged attestation
//! that smuggled a `{{` field would ALSO be rejected at verify.
//!
//! ## Cap-bounded authority
//!
//! The DM narrates freely but acts only within [`DmCaps`]: it may advance the scene /
//! set flags only if granted, and it may grant a player **only items it is permitted to
//! grant** — it cannot hand out the crown a player did not earn ([`DmError::OverCap`]).
//! An over-cap move is refused **fail-closed**, world unchanged, before any attestation.
//!
//! ## What is REAL vs modeled
//!
//! * **REAL — the attestation.** Produced by [`dregg_zkoracle_prove::prove_zkoracle`] and
//!   checked by [`dregg_zkoracle_prove::verify_zkoracle`] (authentic ∧ well-formed ∧
//!   injection-free). The SAME primitives `deos_hermes::attest::AttestationCarrier`
//!   wraps; composed here DIRECTLY so the DM stays light (the modeled ed25519 carrier +
//!   the JSON CFG parse-cert + the injection matcher — no HTTP/TLS). The real local
//!   MPC-TLS 2PC roundtrip is behind the `tlsn-live` feature.
//! * **REAL — the receipt ledger.** Every landed turn is appended to [`WorldCell::ledger`]
//!   with a 32-byte receipt commitment ([`attestation_commitment`]) over its attestation;
//!   [`WorldCell::verify_ledger`] re-verifies the whole chain and a tampered / forged
//!   entry is distinguishable.
//! * **REAL — the cap bound.** [`DmCaps::authorize`] gates every world-effect the DM
//!   proposes; an ungranted item-grant is refused.
//! * **MODELED — the brain.** A [`DmBrain`] turns the scene + the player's action into a
//!   narration; the default [`RecordedDm`] is a deterministic stand-in for a live LLM.
//!   The full OS-jailed confined body is `deos_hermes::DreggHost::run_hosted_agent_attested`
//!   (the crown) — the same attestation, run inside a firmament jail. The *confinement*
//!   (cap-bound), the *attestation*, and the *un-jailbreakable* tooth around the brain
//!   are real here.

use std::collections::{BTreeMap, BTreeSet};

use dregg_zkoracle_prove::{
    build_anthropic_fixture, prove_zkoracle, verify_zkoracle, AnthropicConfig, FixtureNotary,
    ProveError, VerifiedZkOracle, ZkOracleAttestation, ZkOracleError,
};

// ─────────────────────────────────────────────────────────────────────────────
// The attestation carrier — the real zkoracle-prove primitives, composed directly.
// ─────────────────────────────────────────────────────────────────────────────

/// Domain separator for [`attestation_commitment`] — the DM receipt-id domain.
const RECEIPT_COMMIT_DOMAIN: &[u8] = b"attested-dm-narration-receipt-v1";

/// The modeled session time stamped on the carrier's presentation (unix seconds). The
/// attestation is about the narration BODY; the exact timestamp is not load-bearing.
const ATTEST_CONNECTION_TIME: u64 = 1_700_000_000;

/// The default deterministic seed for the DM's modeled notary carrier, so a session's
/// narration attestations verify against a reproducible pinned anchor.
pub const DEFAULT_DM_SEED: [u8; 32] = [0xD3; 32];

/// **The DM's attestation carrier** — the modeled authentic anchor each narration is
/// attested under. Holds the notary that signs the presentation carrier and the pinned
/// [`AnthropicConfig`] a verifier checks against. The direct composition of the real
/// [`dregg_zkoracle_prove`] primitives (`build_anthropic_fixture` + `prove_zkoracle`) —
/// the same ones `deos_hermes::attest::AttestationCarrier` wraps — kept here so the DM
/// needs no HTTP/TLS / verified-Lean link for its default (modeled) path.
pub struct DmAttestationCarrier {
    notary: FixtureNotary,
    config: AnthropicConfig,
}

impl Default for DmAttestationCarrier {
    fn default() -> Self {
        DmAttestationCarrier::from_seed(&DEFAULT_DM_SEED)
    }
}

impl DmAttestationCarrier {
    /// A carrier from a 32-byte notary seed. Its [`Self::config`] pins that notary's
    /// verifying key — the anchor `verify_zkoracle` checks the attestation against.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        let notary = FixtureNotary::from_seed(seed);
        let config = AnthropicConfig::new(notary.verifying_key());
        DmAttestationCarrier { notary, config }
    }

    /// The pinned config a verifier uses: `verify_zkoracle(&att, carrier.config())`.
    pub fn config(&self) -> &AnthropicConfig {
        &self.config
    }

    /// PRODUCE a zkOracle attestation over an Anthropic messages RESPONSE BODY, binding
    /// `field` (which MUST be a substring of `response_body`) injection-free. The modeled
    /// carrier signs the presentation; [`prove_zkoracle`] proves the CFG (well-formed) and
    /// injection-free legs and binds them to this one response. Refuses a malformed body,
    /// an injecting field, or a field absent from the body.
    pub fn attest_body(
        &self,
        response_body: &str,
        field: &[u8],
    ) -> Result<ZkOracleAttestation, ProveError> {
        let pres = build_anthropic_fixture(&self.notary, response_body, ATTEST_CONNECTION_TIME);
        prove_zkoracle(pres, field.to_vec(), self.config())
    }

    /// ATTEST A NARRATION. Shapes the narration into an Anthropic messages object and
    /// binds that text injection-free — so the attestation certifies the model's ACTUAL
    /// narration this turn (authentic session + well-formed JSON + no `{{` in its own
    /// words). Returns the attestation and the exact field bound (the sanitized text).
    pub fn attest_narration(
        &self,
        narration: &str,
    ) -> Result<(ZkOracleAttestation, Vec<u8>), ProveError> {
        let field = clean_field(narration);
        let body = messages_body(&field);
        let att = self.attest_body(&body, field.as_bytes())?;
        Ok((att, field.into_bytes()))
    }

    /// THE CROWN, RUN REAL-LOCALLY. Attest `narration` over a GENUINE local MPC-TLS 2PC
    /// roundtrip (server + notary + prover in-process; the notary sees no plaintext; a
    /// real `presentation.verify()`) against an Anthropic-shaped endpoint — so the
    /// certified bytes came from a real 2PC session, not a fixture literal. `narration`
    /// must be JSON-string-safe and injection-free (no `{{`), since it is the field bound
    /// injection-free. The authentic *leg* is still the modeled ed25519 carrier over the
    /// (now really-authenticated) body; fusing the real tlsn presentation into that leg
    /// is the named operational remainder (mirrors `deos_hermes::attest::attest_turn_live`).
    #[cfg(feature = "tlsn-live")]
    pub fn attest_narration_live(
        &self,
        prompt: &str,
        narration: &str,
    ) -> Result<ZkOracleAttestation, String> {
        use dregg_zkoracle_prove::tlsn_live::{run_local_roundtrip_blocking, LiveExchange};
        let exchange = LiveExchange::messages(prompt, narration);
        let roundtrip = run_local_roundtrip_blocking(&exchange).map_err(|e| e.to_string())?;
        let body = String::from_utf8(roundtrip.verified.response_body.clone())
            .map_err(|e| format!("authenticated response body is not utf-8: {e}"))?;
        self.attest_body(&body, narration.as_bytes())
            .map_err(|e| e.to_string())
    }
}

/// **The canonical 32-byte receipt id for a landed narration turn** — a length-prefixed
/// BLAKE3 over the attestation's load-bearing, verifier-visible fields (the pinned
/// session identity + signed transcripts, the cross-leg content commitment, and the
/// injection-checked field span). A total fingerprint: a tampered session, a spliced
/// body, or a re-aimed field span all change it. A light client holding the attestation
/// recomputes this and checks it equals the receipt on the landed turn. Mirrors
/// `deos_hermes::attest::attestation_commitment`.
pub fn attestation_commitment(att: &ZkOracleAttestation) -> [u8; 32] {
    let pres = &att.presentation;
    let mut h = blake3::Hasher::new();
    h.update(RECEIPT_COMMIT_DOMAIN);
    h.update(&(pres.server_name.len() as u64).to_le_bytes());
    h.update(pres.server_name.as_bytes());
    h.update(&pres.connection_time.to_le_bytes());
    h.update(&(pres.sent.len() as u64).to_le_bytes());
    h.update(&pres.sent);
    h.update(&(pres.recv.len() as u64).to_le_bytes());
    h.update(&pres.recv);
    h.update(&pres.notary_sig);
    h.update(&att.content_commit.as_u32().to_le_bytes());
    h.update(&(att.field_span.offset as u64).to_le_bytes());
    h.update(&(att.field_span.len as u64).to_le_bytes());
    *h.finalize().as_bytes()
}

/// Shape a bound field into a well-formed Anthropic messages RESPONSE BODY (the shape
/// `/v1/messages` returns): the assistant `content[0].text` IS the field, so the field is
/// a verbatim, committed substring of the body.
fn messages_body(field: &str) -> String {
    format!(
        "{{\"id\":\"msg_dm\",\"type\":\"message\",\"role\":\"assistant\",\
         \"model\":\"claude-opus-4-8\",\
         \"content\":[{{\"type\":\"text\",\"text\":\"{field}\"}}],\
         \"stop_reason\":\"end_turn\",\"stop_sequence\":null,\
         \"usage\":{{\"input_tokens\":24,\"output_tokens\":12}}}}"
    )
}

/// Render `text` into a JSON-string-safe field that embeds verbatim (no escaping): drop
/// the two bytes JSON strings must escape (`"` and `\`) and the raw control chars, keeping
/// everything else — **crucially the `{` / `}` bytes**, so a genuine `{{` injection attempt
/// reflected from a player's message SURVIVES into the field and the injection-free leg
/// still fires on it (the load-bearing catch is preserved, not sanitized away). An empty
/// result falls back to a placeholder so the bound field is always a real substring.
fn clean_field(text: &str) -> String {
    let cleaned: String = text
        .chars()
        .filter(|c| *c != '"' && *c != '\\' && !c.is_control())
        .collect();
    let trimmed = cleaned.trim();
    if trimmed.is_empty() {
        "the dungeon master pauses".to_string()
    } else {
        trimmed.to_string()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The world-cell — world-state-as-cell; a turn advances it, leaving a receipt.
// ─────────────────────────────────────────────────────────────────────────────

/// A world-effect the DM proposes alongside a narration — the cap-gated affordance that
/// advances the world. Each is checked against [`DmCaps`] before it lands; an ungranted
/// one is refused fail-closed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WorldEffect {
    /// Advance the current scene to a named passage.
    AdvanceScene(String),
    /// Set a world flag / stat.
    SetFlag(String, i64),
    /// Grant a player an item. The DM may only grant items its caps whitelist — it
    /// cannot hand out an unearned item.
    GrantItem(String),
}

/// **The world-cell** — world-state-as-cell. The current scene, the world flags, the
/// granted inventory, and the tamper-evident receipt ledger of every landed DM turn. A
/// turn advances it and leaves a receipt; a refused turn advances nothing and leaves no
/// receipt (the anti-ghost tooth). Defined locally from the spween-on-dregg design
/// (`docs/deos/SPWEEN-ON-DREGG.md`); reconciled against the real `WorldCell` at
/// registration.
#[derive(Clone, Debug, Default)]
pub struct WorldCell {
    /// The current scene / passage name.
    pub scene: String,
    /// World flags / stats, written only by cap-gated DM turns.
    pub flags: BTreeMap<String, i64>,
    /// The items players have been granted (only earned / cap-permitted items land here).
    pub inventory: BTreeSet<String>,
    /// The receipt ledger — every landed narration turn, in order. Un-rewritable: a past
    /// turn cannot be secretly changed ([`WorldCell::verify_ledger`] catches it).
    pub ledger: Vec<LedgerEntry>,
}

/// One landed, attested, receipted DM turn on the ledger.
#[derive(Clone, Debug)]
pub struct LedgerEntry {
    /// The sequence number (the turn's index in the ledger).
    pub seq: u64,
    /// The narration the DM produced this turn (the exact bound field — a committed
    /// substring of the authenticated response body).
    pub narration: String,
    /// The world-effect this turn applied, if any (a pure-narration turn has `None`).
    pub effect: Option<WorldEffect>,
    /// THE ATTESTATION — a `verify_zkoracle`-checkable proof this narration was authentic
    /// (from a real model) ∧ well-formed ∧ injection-free.
    pub attestation: ZkOracleAttestation,
    /// The 32-byte receipt id ([`attestation_commitment`]) — the on-ledger fingerprint a
    /// light client recomputes.
    pub receipt: [u8; 32],
}

impl WorldCell {
    /// A fresh world-cell opened at `scene` with no flags, no inventory, empty ledger.
    pub fn new(scene: impl Into<String>) -> WorldCell {
        WorldCell {
            scene: scene.into(),
            ..Default::default()
        }
    }

    /// Apply a cap-authorized world-effect to the world state. (Called only after
    /// [`DmCaps::authorize`] admits it and the narration is attested.)
    fn apply(&mut self, effect: &WorldEffect) {
        match effect {
            WorldEffect::AdvanceScene(s) => self.scene = s.clone(),
            WorldEffect::SetFlag(k, v) => {
                self.flags.insert(k.clone(), *v);
            }
            WorldEffect::GrantItem(item) => {
                self.inventory.insert(item.clone());
            }
        }
    }

    /// The receipt id of every landed turn (the tamper-proof chain).
    pub fn receipts(&self) -> Vec<[u8; 32]> {
        self.ledger.iter().map(|e| e.receipt).collect()
    }

    /// **Re-verify the whole receipt ledger** against `config`: every entry's attestation
    /// `verify_zkoracle`-accepts (authentic ∧ well-formed ∧ injection-free), its displayed
    /// narration is the committed attested text (a swapped narration is caught), and its
    /// receipt commitment recomputes. A tampered / forged entry is distinguishable —
    /// [`LedgerError`] names which turn and why.
    pub fn verify_ledger(&self, config: &AnthropicConfig) -> Result<(), LedgerError> {
        for (i, entry) in self.ledger.iter().enumerate() {
            verify_turn(entry, config).map_err(|reason| LedgerError {
                seq: i as u64,
                reason,
            })?;
        }
        Ok(())
    }
}

/// **Verify one landed turn is authentic + on-ledger + un-forged.** Checks:
/// (1) `verify_zkoracle` accepts the attestation (authentic ∧ well-formed ∧
/// injection-free); (2) the displayed narration is a committed substring of the
/// authenticated response body (a swapped-out narration over a real attestation is
/// caught); (3) the receipt id recomputes ([`attestation_commitment`]). A fabricated
/// narration without a valid attestation, or a tampered session / re-aimed field span,
/// fails one of these — the forged-turn-distinguishable tooth.
pub fn verify_turn(
    entry: &LedgerEntry,
    config: &AnthropicConfig,
) -> Result<VerifiedZkOracle, TurnForgery> {
    let out = verify_zkoracle(&entry.attestation, config).map_err(TurnForgery::Attestation)?;
    let field = clean_field(&entry.narration);
    if !contains(&out.session.response_body, field.as_bytes()) {
        return Err(TurnForgery::NarrationNotAttested);
    }
    if attestation_commitment(&entry.attestation) != entry.receipt {
        return Err(TurnForgery::ReceiptMismatch);
    }
    Ok(out)
}

/// Why a landed turn failed re-verification — a forged / tampered turn is distinguishable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TurnForgery {
    /// The attestation itself does not verify (forged / tampered session, malformed body,
    /// or a smuggled `{{` field caught at verify).
    Attestation(ZkOracleError),
    /// The displayed narration is not the attested text — a narration swapped onto a real
    /// attestation (the text a player would read differs from what was certified).
    NarrationNotAttested,
    /// The receipt id does not recompute from the attestation — a fabricated receipt.
    ReceiptMismatch,
}

impl std::fmt::Display for TurnForgery {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TurnForgery::Attestation(e) => write!(f, "attestation does not verify: {e:?}"),
            TurnForgery::NarrationNotAttested => {
                write!(f, "displayed narration is not the attested text")
            }
            TurnForgery::ReceiptMismatch => write!(f, "receipt id does not recompute"),
        }
    }
}

impl std::error::Error for TurnForgery {}

/// A ledger re-verification failure, naming the offending turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LedgerError {
    /// The sequence number of the turn that failed.
    pub seq: u64,
    /// Why it failed.
    pub reason: TurnForgery,
}

impl std::fmt::Display for LedgerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ledger turn #{} is not authentic: {}",
            self.seq, self.reason
        )
    }
}

impl std::error::Error for LedgerError {}

// ─────────────────────────────────────────────────────────────────────────────
// The DM caps — cap-bounded authority.
// ─────────────────────────────────────────────────────────────────────────────

/// **The DM's granted affordances.** The DM narrates freely but acts only within these:
/// it may advance the scene / set flags only if granted, and it may grant a player only
/// the items on [`Self::grantable_items`]. An over-cap move is refused fail-closed — the
/// DM cannot hand a player the crown they did not earn.
#[derive(Clone, Debug, Default)]
pub struct DmCaps {
    /// Whether the DM may advance the scene.
    pub may_advance_scene: bool,
    /// Whether the DM may set world flags.
    pub may_set_flags: bool,
    /// The exact items the DM is permitted to grant (nothing outside this set).
    pub grantable_items: BTreeSet<String>,
}

impl DmCaps {
    /// A narrator with the two ordinary story affordances (advance the scene, set flags)
    /// and a whitelist of grantable items. The natural DM mandate.
    pub fn narrator(grantable_items: impl IntoIterator<Item = impl Into<String>>) -> DmCaps {
        DmCaps {
            may_advance_scene: true,
            may_set_flags: true,
            grantable_items: grantable_items.into_iter().map(Into::into).collect(),
        }
    }

    /// A pure narrator — may advance the scene / set flags but grant NOTHING (the tightest
    /// mandate; every item-grant is over-cap).
    pub fn pure_narrator() -> DmCaps {
        DmCaps {
            may_advance_scene: true,
            may_set_flags: true,
            grantable_items: BTreeSet::new(),
        }
    }

    /// **Authorize a proposed world-effect against this mandate.** `Ok(())` iff the DM is
    /// permitted the effect; `Err(OverCap)` names the reach it exceeded. The fail-closed
    /// cap tooth: an ungranted item-grant (or a forbidden scene/flag write) is refused.
    pub fn authorize(&self, effect: &WorldEffect) -> Result<(), OverCap> {
        match effect {
            WorldEffect::AdvanceScene(_) if !self.may_advance_scene => {
                Err(OverCap::SceneAdvanceForbidden)
            }
            WorldEffect::SetFlag(_, _) if !self.may_set_flags => Err(OverCap::FlagWriteForbidden),
            WorldEffect::GrantItem(item) if !self.grantable_items.contains(item) => {
                Err(OverCap::UngrantableItem(item.clone()))
            }
            _ => Ok(()),
        }
    }
}

/// The cap reach a DM move exceeded — the mandate leg that bit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OverCap {
    /// The DM tried to grant an item outside its whitelist (the crown-it-cannot-give).
    UngrantableItem(String),
    /// The DM tried to advance the scene without that affordance.
    SceneAdvanceForbidden,
    /// The DM tried to write a flag without that affordance.
    FlagWriteForbidden,
}

impl std::fmt::Display for OverCap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OverCap::UngrantableItem(i) => write!(f, "the DM may not grant `{i}` (unearned)"),
            OverCap::SceneAdvanceForbidden => write!(f, "the DM may not advance the scene"),
            OverCap::FlagWriteForbidden => write!(f, "the DM may not write world flags"),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The brain — how the DM turns scene + player action into a narration.
// ─────────────────────────────────────────────────────────────────────────────

/// A player's message to the DM — a spoken action / command. Its [`PlayerMessage::text`]
/// is reflected into the DM's narration (a game-master answers what the player said), so
/// a `{{`-bearing injection reaches the injection-free leg.
#[derive(Clone, Debug)]
pub struct PlayerMessage {
    /// The player's name / handle.
    pub player: String,
    /// The player's raw message text (reflected verbatim into the narration — this is how
    /// an injection reaches the attestation's injection-free leg).
    pub text: String,
}

impl PlayerMessage {
    /// A player message.
    pub fn new(player: impl Into<String>, text: impl Into<String>) -> PlayerMessage {
        PlayerMessage {
            player: player.into(),
            text: text.into(),
        }
    }
}

/// The DM's move this turn — the narration it will speak and the world-effect it proposes.
#[derive(Clone, Debug)]
pub struct DmMove {
    /// The narration / NPC response the DM speaks (reflects the player's action).
    pub narration: String,
    /// The world-effect the DM proposes (cap-checked before it lands); `None` for a
    /// pure-narration turn.
    pub effect: Option<WorldEffect>,
}

impl DmMove {
    /// A pure-narration move (no world-effect).
    pub fn say(narration: impl Into<String>) -> DmMove {
        DmMove {
            narration: narration.into(),
            effect: None,
        }
    }

    /// A narration that also proposes a world-effect.
    pub fn act(narration: impl Into<String>, effect: WorldEffect) -> DmMove {
        DmMove {
            narration: narration.into(),
            effect: Some(effect),
        }
    }
}

/// How the DM narrates. A stand-in for a live LLM brain: the DM's cap-bound, attestation,
/// and un-jailbreakable teeth are real around whatever brain drives the turn. The full
/// OS-jailed confined brain is `deos_hermes::DreggHost::run_hosted_agent_attested`.
pub trait DmBrain {
    /// Narrate the DM's response to `player` in the current `scene`, and propose a
    /// world-effect (or `None`). The narration MUST reflect the player's action verbatim
    /// (that is how the injection-free leg sees a player injection). A benign message
    /// yields a benign, attestable narration; a `{{`-bearing message yields a narration
    /// the injection-free leg refuses — the un-jailbreakable tooth.
    fn narrate(&self, scene: &str, player: &PlayerMessage) -> DmMove;
}

/// The default modeled DM brain: deterministically narrates a scene response that
/// **reflects the player's message verbatim** (so an injection reaches the attestation).
/// It proposes no world-effect by itself — effects are driven explicitly via
/// [`DungeonMaster::narrate_move`] so the cap tooth is exercised deliberately.
#[derive(Clone, Copy, Debug, Default)]
pub struct RecordedDm;

impl DmBrain for RecordedDm {
    fn narrate(&self, scene: &str, player: &PlayerMessage) -> DmMove {
        // Reflect the player's raw text verbatim — a game-master answers what was said.
        // Crucially NOT brace-sanitized: a `{{` injection survives so the injection-free
        // leg fires on it (the whole point). The DM's own framing carries no braces.
        DmMove::say(format!(
            "In the {scene}, {who} declares: {text} -- the dungeon master weighs the words and the scene turns.",
            who = player.player,
            text = player.text,
        ))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The dungeon master — attested + cap-bounded narrator.
// ─────────────────────────────────────────────────────────────────────────────

/// **The provably-honest, un-jailbreakable AI dungeon-master.** Reads the world-cell,
/// narrates via its [`DmBrain`], and fires a **receipted attested turn** advancing the
/// world — each narration carrying a [`ZkOracleAttestation`] (authentic ∧ well-formed ∧
/// injection-free). Its authority is cap-bounded by [`DmCaps`]. A player prompt-injection
/// is refused by the injection-free leg (un-jailbreakable); an over-cap move is refused
/// fail-closed.
pub struct DungeonMaster<B: DmBrain = RecordedDm> {
    carrier: DmAttestationCarrier,
    caps: DmCaps,
    brain: B,
}

impl<B: DmBrain> DungeonMaster<B> {
    /// A dungeon-master with the given attestation carrier, cap mandate, and brain.
    pub fn new(carrier: DmAttestationCarrier, caps: DmCaps, brain: B) -> DungeonMaster<B> {
        DungeonMaster {
            carrier,
            caps,
            brain,
        }
    }

    /// The pinned config a verifier checks this DM's turns against.
    pub fn config(&self) -> &AnthropicConfig {
        self.carrier.config()
    }

    /// The DM's cap mandate.
    pub fn caps(&self) -> &DmCaps {
        &self.caps
    }

    /// **NARRATE A TURN in response to a player message.** The brain narrates (reflecting
    /// the player's action); the narration is attested; the receipted attested turn is
    /// appended to the world's ledger.
    ///
    /// REFUSED — and the world advances not at all (anti-ghost) — when:
    /// * the narration carries a `{{` injection reflected from the player's message
    ///   ([`DmError::Injection`]) — the **un-jailbreakable tooth**;
    /// * the proposed world-effect exceeds the DM's caps ([`DmError::OverCap`]).
    ///
    /// On success returns the landed turn's [`Receipt`].
    pub fn narrate_turn(
        &self,
        world: &mut WorldCell,
        player: &PlayerMessage,
    ) -> Result<Receipt, DmError> {
        let mv = self.brain.narrate(&world.scene, player);
        self.land_move(world, mv)
    }

    /// **DRIVE AN EXPLICIT MOVE** (narration + a proposed world-effect). Same teeth as
    /// [`Self::narrate_turn`], but the caller supplies the move — used to exercise the
    /// cap tooth (an over-cap item-grant) and to advance the scene deliberately.
    pub fn narrate_move(&self, world: &mut WorldCell, mv: DmMove) -> Result<Receipt, DmError> {
        self.land_move(world, mv)
    }

    /// The one landing path: cap-check the effect (fail-closed), attest the narration
    /// (injection-free tooth), then apply the effect and append the receipted turn.
    fn land_move(&self, world: &mut WorldCell, mv: DmMove) -> Result<Receipt, DmError> {
        // (1) CAP-BOUND the proposed effect FIRST, fail-closed — an over-cap move never
        //     produces an attestation and never touches the world.
        if let Some(effect) = &mv.effect {
            self.caps.authorize(effect).map_err(DmError::OverCap)?;
        }
        // (2) ATTEST the narration: authentic ∧ well-formed ∧ injection-free. A `{{`
        //     reflected from a player's message is REFUSED here (the un-jailbreakable
        //     tooth) — the attestation cannot be produced.
        let (attestation, field) = self
            .carrier
            .attest_narration(&mv.narration)
            .map_err(DmError::from_prove)?;
        // (3) LAND the turn: apply the effect, append the receipted attested turn.
        let seq = world.ledger.len() as u64;
        let receipt = attestation_commitment(&attestation);
        if let Some(effect) = &mv.effect {
            world.apply(effect);
        }
        world.ledger.push(LedgerEntry {
            seq,
            narration: String::from_utf8_lossy(&field).into_owned(),
            effect: mv.effect,
            attestation,
            receipt,
        });
        Ok(Receipt { seq, id: receipt })
    }
}

impl DungeonMaster<RecordedDm> {
    /// A default modeled dungeon-master: the deterministic [`RecordedDm`] brain, the
    /// default attestation carrier, and the given cap mandate.
    pub fn recorded(caps: DmCaps) -> DungeonMaster<RecordedDm> {
        DungeonMaster::new(DmAttestationCarrier::default(), caps, RecordedDm)
    }
}

/// The receipt of a landed narration turn — its ledger sequence and its 32-byte id.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Receipt {
    /// The turn's sequence number in the ledger.
    pub seq: u64,
    /// The 32-byte receipt id ([`attestation_commitment`]).
    pub id: [u8; 32],
}

/// Why a narration turn was refused — the world advanced not at all.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DmError {
    /// **The un-jailbreakable tooth.** The narration carries a `{{` handlebars injection
    /// (reflected from a player's prompt-injection); the injection-free leg refuses to
    /// attest it, so the DM's turn over that input is refused. A player cannot inject the
    /// DM into breaking the rules.
    Injection,
    /// The DM's move exceeded its cap mandate (e.g. granting an unearned item); refused
    /// fail-closed.
    OverCap(OverCap),
    /// The narration could not be shaped into a well-formed attestable body (a modeling
    /// fault — should not arise from ordinary narration).
    NotAttestable(String),
}

impl DmError {
    fn from_prove(e: ProveError) -> DmError {
        match e {
            ProveError::Injection => DmError::Injection,
            other => DmError::NotAttestable(format!("{other:?}")),
        }
    }
}

impl std::fmt::Display for DmError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DmError::Injection => write!(
                f,
                "REFUSED (un-jailbreakable): the turn carries a `{{{{` prompt-injection"
            ),
            DmError::OverCap(o) => write!(f, "REFUSED (over-cap): {o}"),
            DmError::NotAttestable(m) => write!(f, "narration not attestable: {m}"),
        }
    }
}

impl std::error::Error for DmError {}

/// A byte-substring search (the displayed narration inside the authenticated body).
fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() || needle.len() > haystack.len() {
        return needle.is_empty();
    }
    haystack.windows(needle.len()).any(|w| w == needle)
}

#[cfg(test)]
mod tests;
