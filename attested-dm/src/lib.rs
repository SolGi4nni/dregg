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
//! * **REAL — the receipt HASH-CHAIN.** Every landed turn is appended to
//!   [`WorldCell::ledger`] with a 32-byte receipt id ([`chain_receipt_id`]) that binds its
//!   `seq`, its predecessor's receipt id, its narration, its effect, and its attestation —
//!   so the entries form a forward hash chain, not a bag of independently-signed rows.
//!   [`WorldCell::verify_ledger`] walks that chain: reordering, in-place mutation, and
//!   mid-history insertion are caught outright; truncation (and a wholesale re-link) is
//!   caught against a known [`WorldCell::head`] via [`WorldCell::verify_ledger_against_head`].
//!   Because the default `authentic` leg is a fixture, entry forgery is prevented by the
//!   chain-link + receipt-id binding + head anchor, not by attestation authenticity.
//! * **REAL — the cap bound.** [`DmCaps::authorize`] gates every world-effect the DM
//!   proposes; an ungranted item-grant is refused.
//! * **MODELED — the brain.** A [`DmBrain`] turns the scene + the player's action into a
//!   narration; the default [`RecordedDm`] is a deterministic stand-in for a live LLM.
//!   The full OS-jailed confined body is `deos_hermes::DreggHost::run_hosted_agent_attested`
//!   (the crown) — the same attestation, run inside a firmament jail. The *confinement*
//!   (cap-bound), the *attestation*, and the *un-jailbreakable* tooth around the brain
//!   are real here.

use std::collections::{BTreeMap, BTreeSet};

mod prompt_template;
pub use prompt_template::{
    slot_confined, verify_prompt_rendering, world_binding, PromptTemplate, Segment, SLOT_PLAYER,
    SLOT_WORLD,
};

pub mod game;
pub use game::{
    bramble_keep, starfall_spire, sunken_vault, CombatEnemy, DialogueGrant, DialogueRule, Exit,
    GameAction, GameBinding, GameBrain, GameRefusal, GameSession, GameStatus, GameWorld, Gate,
    GateReason, Hostile, LoseCondition, Npc, Objective, Outcome, PlayResult, Proposal, Resolution,
    Room, ScriptedGm, Spell, SpellEffect, SpellRule, UseRule, PLAYER_WOUNDS_FLAG,
};
// `PromptBinding` is defined below (it is tightly coupled to the chain-link hashing); re-exported
// here in the same neighbourhood as the other prompt-template surface for discoverability.

use dregg_node_target::{NodeTarget, SubmittedTurn};
use dregg_zkoracle_prove::{
    build_anthropic_fixture, prove_zkoracle, verify_zkoracle, AnthropicConfig, FixtureNotary,
    ProveError, VerifiedZkOracle, ZkOracleAttestation, ZkOracleError,
};

// ─────────────────────────────────────────────────────────────────────────────
// The attestation carrier — the real zkoracle-prove primitives, composed directly.
// ─────────────────────────────────────────────────────────────────────────────

/// Domain separator for [`attestation_commitment`] — the DM receipt-id domain.
const RECEIPT_COMMIT_DOMAIN: &[u8] = b"attested-dm-narration-receipt-v1";

/// Domain separator for the ledger genesis seed — the `prev` of the first entry.
const LEDGER_GENESIS_DOMAIN: &[u8] = b"attested-dm-ledger-genesis-v1";

/// Domain separator for [`chain_receipt_id`] — the hash-chain link domain, distinct from
/// [`RECEIPT_COMMIT_DOMAIN`] so a raw attestation commitment can never be mistaken for a
/// chain link id.
const LEDGER_CHAIN_DOMAIN: &[u8] = b"attested-dm-ledger-chain-link-v1";

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

/// **The ledger genesis seed** — the domain-separated `prev` of the first entry (and the
/// head of an empty ledger). Not all-zeros: a length-prefixed BLAKE3 of a genesis domain
/// separator, so `prev == [0u8;32]` is never a valid genuine link.
pub fn genesis_prev() -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(LEDGER_GENESIS_DOMAIN);
    *h.finalize().as_bytes()
}

/// **The INPUT-side prompt binding of a landed turn** — the commitment that the model saw
/// `render(committed_template, world, slot-confined-player)`. It records the committed
/// template's [`PromptTemplate::template_hash`], the exact `world` slot binding, and the
/// slot-confined `player` field. Bound into the turn's [`chain_receipt_id`] alongside the
/// narration + attestation, so `hash(template) ‖ world ‖ player` rides the SAME hash chain as
/// the (output-side) narration attestation. A verifier holding the committed template + the
/// rendered prompt re-checks integrity via [`verify_prompt_rendering`]; the on-ledger receipt
/// already commits to the template hash + world + player so none of the three can be swapped
/// after the fact without breaking the chain. A turn with no player input (an explicit
/// [`DungeonMaster::narrate_move`]) carries `None`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromptBinding {
    /// The committed template's identity — [`PromptTemplate::template_hash`].
    pub template_hash: [u8; 32],
    /// The exact `world` slot binding rendered into the prompt.
    pub world: String,
    /// The slot-confined `player` field rendered into the prompt (guaranteed `{{`-free by the
    /// input-side guard that admitted this turn).
    pub player: String,
}

impl PromptBinding {
    /// A prompt binding over the committed template hash, the world binding, and the player field.
    pub fn new(
        template_hash: [u8; 32],
        world: impl Into<String>,
        player: impl Into<String>,
    ) -> PromptBinding {
        PromptBinding {
            template_hash,
            world: world.into(),
            player: player.into(),
        }
    }
}

/// **The on-ledger receipt id of a landed turn — a HASH-CHAIN LINK.** Unlike the raw
/// [`attestation_commitment`] (a fingerprint of the attestation alone), this binds the
/// entry to its *position and predecessor*: it is a domain-separated BLAKE3 over
/// `(seq, prev, narration, effect, prompt_binding, attestation_commitment(att))`. Because
/// `prev` is the predecessor's own receipt id, the ids form a forward chain — the id of entry
/// `i` transitively commits to every earlier entry. The `prompt_binding` leg additionally binds
/// the INPUT integrity (`hash(template) ‖ world ‖ player`) into the same link. Recomputing this
/// and checking it equals the stored receipt (and that `prev` equals the real predecessor's id,
/// and `seq` equals the index) is what makes reorder / insertion / in-place mutation
/// distinguishable, and — against a known head — truncation too.
pub fn chain_receipt_id(
    seq: u64,
    prev: &[u8; 32],
    narration: &str,
    effect: &Option<WorldEffect>,
    prompt_binding: &Option<PromptBinding>,
    game_binding: &Option<GameBinding>,
    att: &ZkOracleAttestation,
) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(LEDGER_CHAIN_DOMAIN);
    h.update(&seq.to_le_bytes());
    h.update(prev);
    h.update(&(narration.len() as u64).to_le_bytes());
    h.update(narration.as_bytes());
    encode_effect(&mut h, effect);
    // Bind the INPUT integrity: hash(template) ‖ world ‖ player — a swapped template, world,
    // or player field changes this leg and therefore the whole link.
    encode_prompt_binding(&mut h, prompt_binding);
    // Bind the GAME MOVE: the closed typed action the DM proposed and the room it acted in.
    // A rewritten action (claiming a different move produced this turn) or a swapped room
    // changes this leg and therefore the whole link — the resolved move rides the chain.
    encode_game_binding(&mut h, game_binding);
    // Bind the attestation via its own committed fingerprint — a tampered / re-aimed
    // attestation changes this leg and therefore the whole link.
    h.update(&attestation_commitment(att));
    *h.finalize().as_bytes()
}

/// Tagged, length-prefixed encoding of the (optional) game binding into the chain hash, so a
/// rewritten game action or swapped room breaks the link. `None` (a non-game narration turn) is
/// tag `0`. The `GameAction` / room encoding lives on [`GameBinding::encode_into`] (game.rs).
fn encode_game_binding(h: &mut blake3::Hasher, gb: &Option<GameBinding>) {
    match gb {
        None => {
            h.update(&[0u8]);
        }
        Some(b) => {
            h.update(&[1u8]);
            b.encode_into(h);
        }
    }
}

/// Tagged, length-prefixed encoding of the (optional) prompt binding into the chain hash, so a
/// swapped template hash / world / player breaks the link. `None` (a no-input move) is tag `0`.
fn encode_prompt_binding(h: &mut blake3::Hasher, pb: &Option<PromptBinding>) {
    match pb {
        None => {
            h.update(&[0u8]);
        }
        Some(b) => {
            h.update(&[1u8]);
            h.update(&b.template_hash);
            h.update(&(b.world.len() as u64).to_le_bytes());
            h.update(b.world.as_bytes());
            h.update(&(b.player.len() as u64).to_le_bytes());
            h.update(b.player.as_bytes());
        }
    }
}

/// Length-tagged, discriminant-tagged encoding of the (optional) world-effect into the
/// chain hash, so two distinct effects never collide and a mutated effect breaks the link.
fn encode_effect(h: &mut blake3::Hasher, effect: &Option<WorldEffect>) {
    match effect {
        None => {
            h.update(&[0u8]);
        }
        Some(WorldEffect::AdvanceScene(s)) => {
            h.update(&[1u8]);
            h.update(&(s.len() as u64).to_le_bytes());
            h.update(s.as_bytes());
        }
        Some(WorldEffect::SetFlag(k, v)) => {
            h.update(&[2u8]);
            h.update(&(k.len() as u64).to_le_bytes());
            h.update(k.as_bytes());
            h.update(&v.to_le_bytes());
        }
        Some(WorldEffect::GrantItem(item)) => {
            h.update(&[3u8]);
            h.update(&(item.len() as u64).to_le_bytes());
            h.update(item.as_bytes());
        }
        Some(WorldEffect::Batch(v)) => {
            h.update(&[4u8]);
            h.update(&(v.len() as u64).to_le_bytes());
            for e in v {
                encode_effect(h, &Some(e.clone()));
            }
        }
    }
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
    /// **Apply several effects atomically as ONE turn.** The single-effect-per-turn shape
    /// cannot express a move that touches two counters at once — a combat exchange, say, where
    /// the same blow both wounds the foe and lets it wound you back. A `Batch` lands all of its
    /// sub-effects in order as one receipted turn. It is NOT a cap escape: [`DmCaps::authorize`]
    /// checks EVERY sub-effect (an ungrantable item nested in a batch is still refused
    /// fail-closed), and [`WorldCell::apply`] applies each in sequence. The whole batch is
    /// encoded into the chain link, so a rewritten sub-effect breaks the receipt.
    Batch(Vec<WorldEffect>),
}

/// **The world-cell** — world-state-as-cell. The current scene, the world flags, the
/// granted inventory, and the tamper-evident receipt ledger of every landed DM turn. A
/// turn advances it and leaves a receipt; a refused turn advances nothing and leaves no
/// receipt (the anti-ghost tooth). Defined locally from the spween-on-dregg design
/// (`docs/deos/SPWEEN-ON-DREGG.md`); reconciled against the real `WorldCell` at
/// registration.
#[derive(Clone, Default)]
pub struct WorldCell {
    /// The current scene / passage name.
    pub scene: String,
    /// World flags / stats, written only by cap-gated DM turns.
    pub flags: BTreeMap<String, i64>,
    /// The items players have been granted (only earned / cap-permitted items land here).
    pub inventory: BTreeSet<String>,
    /// The receipt ledger — every landed narration turn, in order, as a **hash chain**.
    /// Each entry's receipt id ([`chain_receipt_id`]) binds its `seq`, its predecessor's
    /// receipt id (`prev`), its narration, its effect, and its attestation, so the ids
    /// form a forward chain. [`WorldCell::verify_ledger`] walks that chain; what it does
    /// and does not catch is stated there. This is NOT a bag of independently-verified
    /// entries: reordering, in-place mutation, and mid-history insertion are caught by the
    /// chain walk, and truncation is caught against a known [`WorldCell::head`].
    pub ledger: Vec<LedgerEntry>,
    /// Where landed narration turns route. [`NodeTarget::Local`] (default) keeps them on
    /// this in-process ledger; [`NodeTarget::Federation`] additionally submits each
    /// landed turn's receipt commitment to a real `DREGG_NODE_URL` node + confirms it
    /// landed (a rejected submit refuses the turn, fail-closed).
    pub node_target: NodeTarget,
}

impl std::fmt::Debug for WorldCell {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WorldCell")
            .field("scene", &self.scene)
            .field("flags", &self.flags)
            .field("inventory", &self.inventory)
            .field("ledger", &self.ledger)
            .field(
                "node_target",
                &if self.node_target.is_local() {
                    "local"
                } else {
                    "federation"
                },
            )
            .finish()
    }
}

/// One landed, attested, receipted DM turn on the ledger.
#[derive(Clone, Debug)]
pub struct LedgerEntry {
    /// The sequence number (the turn's index in the ledger). The chain walk checks this
    /// equals the entry's actual index — a reordered or spliced entry is caught here.
    pub seq: u64,
    /// **The predecessor's receipt id — the back-link of the hash chain.** For the first
    /// entry this is [`genesis_prev`]. The chain walk checks it equals the real
    /// predecessor's receipt id, so an inserted / dropped / reordered entry breaks the link.
    pub prev: [u8; 32],
    /// The narration the DM produced this turn (the exact bound field — a committed
    /// substring of the authenticated response body).
    pub narration: String,
    /// The world-effect this turn applied, if any (a pure-narration turn has `None`).
    pub effect: Option<WorldEffect>,
    /// **The INPUT-side prompt binding** — `hash(template) ‖ world ‖ player` the model was
    /// prompted with (`Some` for a player turn admitted through the slot-confinement guard;
    /// `None` for an explicit no-input [`DungeonMaster::narrate_move`]). Rides the chain link.
    pub prompt_binding: Option<PromptBinding>,
    /// **The GAME MOVE this turn resolved** — the closed typed [`GameAction`] the DM proposed
    /// and the room it acted in ([`GameBinding`]). `Some` for a turn landed by a
    /// [`GameSession`] (the resolver admitted the move); `None` for a free narration turn. Rides
    /// the chain link, so the on-ledger receipt commits to WHICH typed move produced this turn.
    pub game_binding: Option<GameBinding>,
    /// THE ATTESTATION — a `verify_zkoracle`-checkable proof this narration was authentic
    /// (from a real model) ∧ well-formed ∧ injection-free.
    pub attestation: ZkOracleAttestation,
    /// The 32-byte receipt id ([`chain_receipt_id`]) — the hash-chain link over
    /// `(seq, prev, narration, effect, attestation)`, the on-ledger fingerprint a light
    /// client recomputes.
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

    /// **Make this world federation-capable.** By default a world runs `Local` (every
    /// landed narration turn stays on this in-process ledger). Pass a
    /// [`NodeTarget::Federation`] (e.g. from [`NodeTarget::from_env`], reading
    /// `DREGG_NODE_URL`) to additionally submit each landed turn's receipt commitment to
    /// a real federation node and confirm it landed — one flip from a live federation.
    pub fn with_node_target(mut self, target: NodeTarget) -> WorldCell {
        self.node_target = target;
        self
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
            WorldEffect::Batch(v) => {
                for e in v {
                    self.apply(e);
                }
            }
        }
    }

    /// The receipt id of every landed turn, in order — the hash-chain links.
    pub fn receipts(&self) -> Vec<[u8; 32]> {
        self.ledger.iter().map(|e| e.receipt).collect()
    }

    /// **The chain head — the 32-byte tip commitment.** The last entry's receipt id (or
    /// [`genesis_prev`] for an empty ledger). Because each receipt id transitively commits
    /// to every earlier entry, the head is a fingerprint of the ENTIRE history: a stranger
    /// who knows the honest head can hand it to [`WorldCell::verify_ledger_against_head`]
    /// to detect truncation — dropping entries from the tip yields a different head. Anchor
    /// this out of band (publish it, submit it to a federation node) to make the whole
    /// chain un-rewritable to anyone holding only the ledger.
    pub fn head(&self) -> [u8; 32] {
        self.ledger
            .last()
            .map(|e| e.receipt)
            .unwrap_or_else(genesis_prev)
    }

    /// **Re-verify the whole receipt ledger as a HASH CHAIN** against `config`. For every
    /// entry `i` it checks, in order:
    /// 1. `entry.seq == i` — else [`LedgerBreak::SeqMismatch`] (a reordered / spliced entry);
    /// 2. `entry.prev ==` the real predecessor's receipt id (or [`genesis_prev`] for `i = 0`)
    ///    — else [`LedgerBreak::LinkBroken`] (a broken back-link);
    /// 3. the entry itself is authentic via [`verify_turn`] — its attestation
    ///    `verify_zkoracle`-accepts, its displayed narration is the committed attested text,
    ///    and its receipt id **recomputes** from `(seq, prev, narration, effect, attestation)`
    ///    — else [`LedgerBreak::EntryInvalid`].
    ///
    /// **Caught (no external anchor needed):** in-place mutation of any entry (the receipt
    /// no longer recomputes, or the narration is no longer the attested text); reordering
    /// (a `seq`/index mismatch or a broken link); insertion / splice into the history (the
    /// displaced successor's `seq`/`prev` no longer line up).
    ///
    /// **NOT caught here:** truncation to a prefix, and a wholesale re-linked rewrite — both
    /// are *internally consistent* chains. Detecting those needs a known head:
    /// [`WorldCell::verify_ledger_against_head`]. Also: because the default `authentic`
    /// attestation leg is an in-tree FIXTURE (unless the `tlsn-live` feature is on), an
    /// adversary holding the fixture notary seed can mint fresh valid attestations — so what
    /// stops entry FORGERY here is the chain-link + receipt-id binding + head anchor, NOT
    /// attestation authenticity.
    pub fn verify_ledger(&self, config: &AnthropicConfig) -> Result<(), LedgerBreak> {
        let mut expected_prev = genesis_prev();
        for (i, entry) in self.ledger.iter().enumerate() {
            let index = i as u64;
            if entry.seq != index {
                return Err(LedgerBreak::SeqMismatch {
                    index,
                    found_seq: entry.seq,
                });
            }
            if entry.prev != expected_prev {
                return Err(LedgerBreak::LinkBroken { index });
            }
            verify_turn(entry, config).map_err(|reason| LedgerBreak::EntryInvalid {
                seq: entry.seq,
                reason,
            })?;
            expected_prev = entry.receipt;
        }
        Ok(())
    }

    /// **Re-verify the chain AND pin it to a known head.** Runs [`WorldCell::verify_ledger`]
    /// (all the internal-consistency teeth) and then checks `self.head() == expected_head`,
    /// returning [`LedgerBreak::Truncated`] on a mismatch. This is the complete anti-rewrite
    /// tooth: given the honest head anchored out of band, *any* history that differs from the
    /// one that produced it — a truncation, or a fully re-linked forgery — is caught, since
    /// it either fails the internal walk or lands on a different head.
    pub fn verify_ledger_against_head(
        &self,
        config: &AnthropicConfig,
        expected_head: [u8; 32],
    ) -> Result<(), LedgerBreak> {
        self.verify_ledger(config)?;
        let found_head = self.head();
        if found_head != expected_head {
            return Err(LedgerBreak::Truncated {
                expected_head,
                found_head,
            });
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
    // INPUT-side tooth: a landed player turn's bound field MUST be slot-confined (`{{`-free).
    // A landed entry whose recorded player field carries a `{{` is an inconsistency — the guard
    // that admits turns rejects it — so a verifier refuses it too, using the SAME verified matcher.
    if let Some(pb) = &entry.prompt_binding {
        if !slot_confined(&pb.player) {
            return Err(TurnForgery::SlotEscape);
        }
    }
    // The receipt id must recompute as the hash-chain link over the entry's OWN claimed
    // fields — a fabricated receipt, a mutated narration/effect/prompt-binding, or a re-aimed
    // attestation all break this. (The chain walk additionally checks `prev`/`seq` vs neighbours.)
    let recomputed = chain_receipt_id(
        entry.seq,
        &entry.prev,
        &entry.narration,
        &entry.effect,
        &entry.prompt_binding,
        &entry.game_binding,
        &entry.attestation,
    );
    if recomputed != entry.receipt {
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
    /// The turn's recorded player field is NOT slot-confined (carries a `{{`) — an input-side
    /// forgery: a landed entry whose player field could never have passed the slot guard.
    SlotEscape,
}

impl std::fmt::Display for TurnForgery {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TurnForgery::Attestation(e) => write!(f, "attestation does not verify: {e:?}"),
            TurnForgery::NarrationNotAttested => {
                write!(f, "displayed narration is not the attested text")
            }
            TurnForgery::ReceiptMismatch => write!(f, "receipt id does not recompute"),
            TurnForgery::SlotEscape => {
                write!(
                    f,
                    "recorded player field is not slot-confined (carries `{{{{`)"
                )
            }
        }
    }
}

impl std::error::Error for TurnForgery {}

/// **How a ledger hash-chain re-verification failed** — the precise break, mirroring
/// `spween_dregg::verify::VerifyBreak`. A `Vec` of independently-valid entries could only
/// ever report [`Self::EntryInvalid`]; the chain reports the *structural* breaks too.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LedgerBreak {
    /// The entry at `index` carries `found_seq != index` — a reordered or spliced entry
    /// (its sequence number no longer matches its position).
    SeqMismatch { index: u64, found_seq: u64 },
    /// The entry at `index` has a `prev` that is not its real predecessor's receipt id —
    /// the hash-chain back-link is broken (an inserted / dropped / reordered entry).
    LinkBroken { index: u64 },
    /// The chain is internally consistent but its head does not match the known anchor —
    /// entries were TRUNCATED from the tip, or the whole chain was re-linked into a
    /// different history. Only detectable against a known [`WorldCell::head`].
    Truncated {
        expected_head: [u8; 32],
        found_head: [u8; 32],
    },
    /// The entry at sequence `seq` is itself not authentic — its attestation does not
    /// verify, its narration is not the attested text, or its receipt id does not recompute.
    EntryInvalid { seq: u64, reason: TurnForgery },
}

impl std::fmt::Display for LedgerBreak {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LedgerBreak::SeqMismatch { index, found_seq } => write!(
                f,
                "ledger entry at index {index} carries seq {found_seq} (reordered / spliced)"
            ),
            LedgerBreak::LinkBroken { index } => write!(
                f,
                "ledger chain link broken at index {index} (prev != predecessor's receipt id)"
            ),
            LedgerBreak::Truncated { .. } => write!(
                f,
                "ledger head does not match the known anchor (truncated or re-linked)"
            ),
            LedgerBreak::EntryInvalid { seq, reason } => {
                write!(f, "ledger turn #{seq} is not authentic: {reason}")
            }
        }
    }
}

impl std::error::Error for LedgerBreak {}

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
            // A batch is authorized iff EVERY sub-effect is — the cap tooth is not escapable by
            // nesting (an ungrantable item inside a batch is still refused fail-closed).
            WorldEffect::Batch(v) => v.iter().try_for_each(|e| self.authorize(e)),
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
    /// **The committed prompt template.** The DM's prompt to the model is
    /// `template.render_dm(world, player)`; a `{{`-bearing player field is refused at the slot
    /// boundary BEFORE the brain (model) is called, and `template.template_hash()` is bound into
    /// every landed player turn (input integrity). Defaults to [`PromptTemplate::dungeon_master`].
    template: PromptTemplate,
}

impl<B: DmBrain> DungeonMaster<B> {
    /// A dungeon-master with the given attestation carrier, cap mandate, and brain, over the
    /// default committed [`PromptTemplate::dungeon_master`] template.
    pub fn new(carrier: DmAttestationCarrier, caps: DmCaps, brain: B) -> DungeonMaster<B> {
        DungeonMaster {
            carrier,
            caps,
            brain,
            template: PromptTemplate::dungeon_master(),
        }
    }

    /// Pin a specific committed prompt template (its hash is bound into every landed player turn).
    pub fn with_template(mut self, template: PromptTemplate) -> DungeonMaster<B> {
        self.template = template;
        self
    }

    /// The DM's committed prompt template — the model's prompt each turn is
    /// `template().render_dm(world, player)`. A verifier pins its [`PromptTemplate::template_hash`].
    pub fn template(&self) -> &PromptTemplate {
        &self.template
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
    /// * the player field is NOT slot-confined (carries a `{{`) — the **INPUT-side tooth**
    ///   ([`DmError::SlotEscape`]): the field cannot be pinned in its template slot, so it is
    ///   refused BEFORE the brain (model) is called. This is the load-bearing realization of the
    ///   Lean `slot_confinement` theorem: a `{{`-free slot binding adds zero control tokens, so
    ///   the committed template's rules survive verbatim;
    /// * the narration carries a `{{` injection reflected from the player's message
    ///   ([`DmError::Injection`]) — the **output-side un-jailbreakable tooth** (the injection-free
    ///   attestation leg over the DM's own words);
    /// * the proposed world-effect exceeds the DM's caps ([`DmError::OverCap`]).
    ///
    /// On success the landed turn binds `hash(template) ‖ world ‖ player` into its receipt (see
    /// [`PromptBinding`]) alongside the narration attestation, and returns the [`Receipt`].
    pub fn narrate_turn(
        &self,
        world: &mut WorldCell,
        player: &PlayerMessage,
    ) -> Result<Receipt, DmError> {
        // (0) INPUT-SIDE DEFENSE — the player field must be slot-confined (`{{`-free) BEFORE the
        //     brain runs. A `{{`-bearing field is refused here: the model is NOT called, the world
        //     advances not at all, no receipt lands. The verified matcher (`slot_confined`) decides.
        if !slot_confined(&player.text) {
            return Err(DmError::SlotEscape);
        }
        // The prompt the model is (conceptually) handed this turn is
        // `template.render_dm(world_binding, player)`; we bind its INPUT identity —
        // hash(template) ‖ world ‖ player — into the landed turn's receipt.
        let world_desc = world_binding(&world.scene);
        let binding = PromptBinding::new(
            self.template.template_hash(),
            world_desc,
            player.text.clone(),
        );
        let mv = self.brain.narrate(&world.scene, player);
        self.land_move(world, mv, Some(binding), None)
    }

    /// **DRIVE AN EXPLICIT MOVE** (narration + a proposed world-effect). Same output-side teeth as
    /// [`Self::narrate_turn`], but the caller supplies the move (no player input) — used to exercise
    /// the cap tooth (an over-cap item-grant) and to advance the scene deliberately. Carries no
    /// [`PromptBinding`] (there is no untrusted player field this turn).
    pub fn narrate_move(&self, world: &mut WorldCell, mv: DmMove) -> Result<Receipt, DmError> {
        self.land_move(world, mv, None, None)
    }

    /// **LAND A RESOLVED GAME MOVE.** Same landing path + teeth as [`Self::narrate_move`], but the
    /// turn additionally carries the closed typed [`GameBinding`] (the resolver-admitted action +
    /// room) and, if the move came from a player command, its input-side [`PromptBinding`]. Used by
    /// [`GameSession`]: the AI proposes the action + narrates, the resolver decides legality, and
    /// only a legal move reaches here to be cap-checked, attested, and appended to the chain — one
    /// verified turn carrying the move. The narration is still injection-free-attested (a jailbroken
    /// model's prose is bound honestly), and the effect is still cap-gated (a grant must be
    /// whitelisted). Refused exactly as the other paths (over-cap / injection / federation).
    pub fn narrate_game_move(
        &self,
        world: &mut WorldCell,
        mv: DmMove,
        prompt_binding: Option<PromptBinding>,
        game_binding: GameBinding,
    ) -> Result<Receipt, DmError> {
        self.land_move(world, mv, prompt_binding, Some(game_binding))
    }

    /// The one landing path: cap-check the effect (fail-closed), attest the narration
    /// (injection-free tooth), then apply the effect and append the receipted turn — binding the
    /// (optional) input-side [`PromptBinding`] and (optional) [`GameBinding`] into the chain link.
    fn land_move(
        &self,
        world: &mut WorldCell,
        mv: DmMove,
        prompt_binding: Option<PromptBinding>,
        game_binding: Option<GameBinding>,
    ) -> Result<Receipt, DmError> {
        // (1) CAP-BOUND the proposed effect FIRST, fail-closed — an over-cap move never
        //     produces an attestation and never touches the world.
        if let Some(effect) = &mv.effect {
            self.caps.authorize(effect).map_err(DmError::OverCap)?;
        }
        // (2) ATTEST the narration: authentic ∧ well-formed ∧ injection-free. A `{{`
        //     reflected from a player's message is REFUSED here (the output-side un-jailbreakable
        //     tooth) — the attestation cannot be produced.
        let (attestation, field) = self
            .carrier
            .attest_narration(&mv.narration)
            .map_err(DmError::from_prove)?;
        // (3) LAND the turn: apply the effect, append the receipted attested turn.
        let seq = world.ledger.len() as u64;
        let prev = world.head();
        let narration = String::from_utf8_lossy(&field).into_owned();
        // The on-ledger receipt id is a HASH-CHAIN LINK: it binds this turn's seq, its
        // predecessor's receipt id (`prev`), its narration, its effect, its input-side prompt
        // binding (hash(template) ‖ world ‖ player), and its attestation.
        let receipt = chain_receipt_id(
            seq,
            &prev,
            &narration,
            &mv.effect,
            &prompt_binding,
            &game_binding,
            &attestation,
        );
        // FEDERATION SEAM: route the receipt commitment to a real node BEFORE touching
        // the world. In `Local` mode this is a no-op; in `Federation` mode a rejected /
        // unreachable / non-landing submit refuses the turn here — the world advances not
        // at all and NO receipt lands (the anti-ghost tooth is preserved across the seam).
        world
            .node_target
            .route(&SubmittedTurn::new(world.scene.clone(), receipt))
            .map_err(|e| DmError::Federation(e.to_string()))?;
        if let Some(effect) = &mv.effect {
            world.apply(effect);
        }
        world.ledger.push(LedgerEntry {
            seq,
            prev,
            narration,
            effect: mv.effect,
            prompt_binding,
            game_binding,
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
    /// **The INPUT-side tooth.** The player field is not slot-confined — it carries a `{{`
    /// handlebars delimiter, so it cannot be pinned in the template slot. Refused BEFORE the
    /// model is called (the model never sees a rule-rewriting field); the world advances not at
    /// all, no receipt lands. Decided by the verified matcher ([`slot_confined`]). This is the
    /// load-bearing realization of the Lean `slot_confinement` theorem.
    SlotEscape,
    /// **The output-side un-jailbreakable tooth.** The narration carries a `{{` handlebars
    /// injection (reflected from a player's prompt-injection); the injection-free leg refuses to
    /// attest it, so the DM's turn over that input is refused. A player cannot inject the
    /// DM into breaking the rules.
    Injection,
    /// The DM's move exceeded its cap mandate (e.g. granting an unearned item); refused
    /// fail-closed.
    OverCap(OverCap),
    /// The narration could not be shaped into a well-formed attestable body (a modeling
    /// fault — should not arise from ordinary narration).
    NotAttestable(String),
    /// The narration attested, but a configured [`NodeTarget::Federation`] node refused
    /// it or could not confirm it landed (a rejected / unreachable / non-landing submit).
    /// Fail-closed: the turn is refused and no receipt lands (anti-ghost preserved).
    Federation(String),
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
            DmError::SlotEscape => write!(
                f,
                "REFUSED (slot-escape): the player field carries a `{{{{` — it cannot escape its template slot"
            ),
            DmError::Injection => write!(
                f,
                "REFUSED (un-jailbreakable): the turn carries a `{{{{` prompt-injection"
            ),
            DmError::OverCap(o) => write!(f, "REFUSED (over-cap): {o}"),
            DmError::NotAttestable(m) => write!(f, "narration not attestable: {m}"),
            DmError::Federation(m) => write!(f, "REFUSED (federation): {m}"),
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
