//! # `ugc-dregg` — a UGC registry + a NO-CHEAT verifiable leaderboard
//!
//! The platform flywheel. Authors **publish** universes; players **submit**
//! completions; the leaderboard accepts a completion ONLY if its recorded receipt
//! chain **verifies** — a stranger re-executes the same identically-seeded universe
//! with the submitted moves and it reaches the **WIN state**, and the chain links.
//! Leaderboards are therefore trustable **by construction**, not by honor.
//!
//! ## The two verbs
//!
//! * **PUBLISH** ([`Universe::authored`] / [`Universe::from_procgen`] →
//!   [`Registry::publish`]) — a universe is a *compiled spween world* (or a
//!   *committed procgen seed*, from which the same world regenerates byte-for-byte) +
//!   a name + an author. The registry is keyed by the **universe commitment**
//!   ([`UniverseId`]) — content-addressed, so the same universe has the same id.
//! * **SUBMIT** ([`Completion`] → [`Registry::submit`]) — a player submits a recorded
//!   [`Playthrough`](spween_dregg::Playthrough) (the ordered moves + their receipt
//!   chain) + a claimed turns-to-win. The board **verifies** it and only then
//!   accepts + ranks.
//!
//! ## The no-cheat tooth (why the board cannot be gamed)
//!
//! [`verify_completion`] is the whole guarantee, and it is spween-dregg's audited
//! re-verifier used verbatim:
//!
//! 1. **Re-execute.** Deploy a FRESH, identically-seeded world from the universe's
//!    scene and re-drive it through the submitted moves
//!    ([`verify`](spween_dregg::verify) = chain-linkage + `verify_by_replay`). A
//!    forged / edited / spliced move is **refused by the real executor on replay**,
//!    or diverges from the reproduced committed state. Either way it FAILS.
//! 2. **Require the WIN.** The replay must reach the universe's declared win state
//!    (the scene ENDED, plus any declared win-vars, e.g. `gold == 500`). An
//!    incomplete playthrough that never reaches the win is REJECTED.
//! 3. **Bind the result.** The claimed turns-to-win must equal the verified move
//!    count. A tampered result is REJECTED.
//!
//! Only a completion that passes all three is accepted and ranked (by turns). Anyone
//! can re-run [`verify_completion`] — or [`Registry::reverify_entry`] — against a
//! universe they reconstruct independently, and get the same verdict.
//!
//! ## The succinct (proof-backed) path — the ZK-leaderboard accept-path
//!
//! There is a SECOND, additive submission variant ([`ProofCompletion`] →
//! [`Registry::submit_proof`]) that does NOT post the moves. Instead of a
//! [`Playthrough`], it carries a **succinct fold proof** — a `WholeChainProof` byte
//! envelope — plus the attested public roots. The board verifies it in **O(1)** via
//! the REAL whole-history light client ([`verify_history_bytes`]), re-witnessing
//! nothing: no replay, no re-hash, no walk of the moves. Acceptance requires
//! ([`verify_proof_completion`]):
//!
//! 1. the light client ACCEPTS the proof under the universe's pinned VK anchor (a
//!    tampered / relabeled proof is refused here — the crypto tooth bites);
//! 2. the attested `genesis_root` equals the universe's pinned genesis anchor (binds
//!    THIS identically-seeded universe);
//! 3. the attested `final_root` equals the universe's pinned **win anchor** (binds the
//!    win predicate — the attested history reached the declared win state);
//! 4. the claimed turns equal the attested `num_turns`.
//!
//! A proof-backed [`Entry`] stores ONLY the proof envelope + the attested publics + the
//! id — **the moves are NOT stored** ([`Entry::has_moves`] is `false`;
//! [`Entry::playthrough`] is `None`). [`Registry::reverify_entry`] re-runs the O(1)
//! light client, never a replay. The two paths co-exist on one ranked board.
//!
//! ## Honest scope
//!
//! The replay path's verification is **O(N) replay** — a re-verifier re-executes every
//! move. The proof path's verification is **O(1)** and posts no moves.
//!
//! What is REAL here: the succinct proof-verify accept-path (the light client's own
//! verifier, consumed verbatim) and the *moves-not-posted* practical privacy. What is a
//! NAMED FRONTIER, not built:
//!
//! * **A real multi-turn Descent RUN → a fold proof.** The proof SOURCE the driven test
//!   folds is the light client's green in-tree recipe (a real recursive-turn chain), NOT
//!   yet a Descent playthrough compiled to per-turn leaves. That run→leaves→fold glue is
//!   Lane-D-blocked (the wide-carrier geometry, `WIDE_NUM_CARRIERS`; see
//!   `game-turn-slice`). The universe's pinned genesis/win anchors are therefore set from
//!   the fold's endpoints, standing in for a Descent run's genesis/win.
//! * **True crypto-ZK.** The deployed STARK is *succinct*, not *hiding* — "moves not
//!   posted" is a data-availability property, NOT "moves cryptographically hidden".
//!   Transcript masking (zero-knowledge) is a separate workstream.
//!
//! ## Creator-economy foundation (this crate)
//!
//! Two pieces of the creator economy are now VERIFIABLE, not merely labelled:
//!
//! * **Verified author identity.** A universe's author can be a real ed25519 signing
//!   identity ([`AuthorId`]) that **attests** the world with a signature over its
//!   content commitment ([`UniversePlan::attest`]). The pubkey is bound into the
//!   [`UniverseId`], so authorship is attributable + unforgeable: a publish claiming
//!   another author's key WITHOUT a valid signature is refused
//!   ([`PublishError::AuthorSignature`]). A legacy/anonymous universe (author = a bare
//!   name) is still supported ([`UniversePlan::anonymous`] / [`Universe::authored`]).
//! * **Remix / fork lineage.** A universe can declare a **parent**
//!   ([`UniversePlan`]'s `parent`) — a content-addressed edge forming a derivation
//!   graph. The parent is bound into the child's content address, and
//!   [`Registry::publish_derived`] refuses a remix whose parent is not a published
//!   universe. A root universe has no parent.
//!
//! What a fuller creator economy STILL needs (named, not built): **paid / premium
//! universes + a remix-royalty split** over the `$DREGG` rails, and **anti-sybil**
//! (staking / rate-limiting a publish or a submission). The no-cheat property — *a
//! ranked completion provably reaches the win* — holds regardless of those.

use std::collections::BTreeMap;
use std::fmt;

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{RecursionVk, SEG_ANCHOR_WIDTH};
use dregg_lightclient::{AttestedHistory, LightClientError, verify_history_bytes};
use ed25519_dalek::{Signature, VerifyingKey};
use procgen_dregg::CommittedSeed;
use spween_dregg::{
    CompiledStory, Driver, PASSAGE_ENDED, PASSAGE_SLOT, Playthrough, Scene, VerifyBreak, WorldCell,
    WorldError, compile_scene, parse, verify,
};

/// Domain tag for the universe commitment (content address).
const DOMAIN_UNIVERSE_ID: &[u8] = b"ugc-dregg/universe-id/v1";
/// Domain tag for a completion id.
const DOMAIN_COMPLETION_ID: &[u8] = b"ugc-dregg/completion-id/v1";
/// Domain tag for a PROOF-backed completion id (over the player + the succinct proof
/// envelope, since a proof-backed completion posts NO moves to hash).
const DOMAIN_PROOF_COMPLETION_ID: &[u8] = b"ugc-dregg/proof-completion-id/v1";
/// Domain tag for an author's **attestation** — the content commitment an author
/// ed25519-signs to bind their key to a universe (see [`AuthorId`] / [`UniversePlan`]).
const DOMAIN_AUTHOR_SIG: &[u8] = b"ugc-dregg/author-attestation/v1";

// ═══════════════════════════════════════════════════════════════════════════════
// Universe — a content-addressed publishable world.
// ═══════════════════════════════════════════════════════════════════════════════

/// The **universe commitment** — a content address. The same universe (same scene
/// source + name + author) always hashes to the same id, so a re-publish is
/// idempotent and any party can recompute it.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UniverseId([u8; 32]);

impl UniverseId {
    /// The raw 32-byte commitment.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
    /// Reconstruct an id from its 32 raw bytes (e.g. decoding a persisted parent link).
    pub fn from_bytes(bytes: [u8; 32]) -> UniverseId {
        UniverseId(bytes)
    }
}

/// A **verified author identity** — an ed25519 public key. When a universe is published
/// via [`UniversePlan::attest`], the author proves control of this key by signing the
/// universe's content commitment, and the key is bound into the [`UniverseId`]. So an
/// author is *attributable* (the key is public and stable across their universes) and
/// authorship is *unforgeable* (nobody can publish under this key without its secret).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AuthorId([u8; 32]);

impl AuthorId {
    /// Wrap a raw 32-byte ed25519 public key as an author identity. (The key is only
    /// *verified* — proven to sign the content — when it attests a [`UniversePlan`].)
    pub fn from_public_key(public_key: [u8; 32]) -> AuthorId {
        AuthorId(public_key)
    }
    /// The raw 32-byte ed25519 public key.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
    /// The public key as full lowercase hex.
    pub fn hex(&self) -> String {
        self.0.iter().map(|b| format!("{b:02x}")).collect()
    }
}

impl fmt::Display for AuthorId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in &self.0[..8] {
            write!(f, "{b:02x}")?;
        }
        write!(f, "…")
    }
}

impl fmt::Debug for AuthorId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AuthorId({self})")
    }
}

/// A detached ed25519 **attestation signature** by an author over a universe's content
/// commitment ([`UniversePlan::signing_commitment`]). Held alongside the universe so the
/// attestation can be *re-verified* independently (e.g. rebuilt from a durable store).
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AuthorSignature([u8; 64]);

impl AuthorSignature {
    /// Wrap 64 raw signature bytes.
    pub fn from_bytes(bytes: [u8; 64]) -> AuthorSignature {
        AuthorSignature(bytes)
    }
    /// The raw 64 signature bytes.
    pub fn as_bytes(&self) -> &[u8; 64] {
        &self.0
    }
}

impl fmt::Debug for AuthorSignature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AuthorSignature(")?;
        for b in &self.0[..8] {
            write!(f, "{b:02x}")?;
        }
        write!(f, "…)")
    }
}

impl fmt::Display for UniverseId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in &self.0[..8] {
            write!(f, "{b:02x}")?;
        }
        write!(f, "…")
    }
}

impl fmt::Debug for UniverseId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "UniverseId({self})")
    }
}

/// How a universe came to be — its provenance. Content-addressing means the WORLD is
/// the same regardless; provenance records where the world's scene came from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Provenance {
    /// An author wrote the spween scene directly.
    Authored,
    /// The scene was generated from a committed, verifiable procgen seed. Anyone can
    /// re-generate the byte-identical scene from this seed
    /// ([`Universe::regenerates_from_seed`]) — the seed→world binding is provable.
    Procgen {
        /// The committed 32-byte seed (a beacon output / a day's published root).
        committed_seed: [u8; 32],
    },
}

/// The win condition of a universe. A completion "wins" iff, after replay, the scene
/// has **ENDED** and every declared `(var, value)` holds on the final committed state.
/// The scene-ended requirement alone already refuses an incomplete playthrough; the
/// var checks strengthen it (e.g. the hoard was actually seized: `gold == 500`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WinCondition {
    /// Variable values that must hold on the final committed state to count as a win.
    pub vars: Vec<(String, u64)>,
}

impl WinCondition {
    /// The win requires only that the scene ENDED (reached a terminal `-> END`).
    pub fn ended() -> WinCondition {
        WinCondition { vars: Vec::new() }
    }

    /// The win requires the scene ENDED **and** the named vars hold.
    pub fn ended_with(vars: &[(&str, u64)]) -> WinCondition {
        WinCondition {
            vars: vars.iter().map(|(k, v)| (k.to_string(), *v)).collect(),
        }
    }
}

/// A **published universe** — a content-addressed, verifiable, winnable world.
#[derive(Clone)]
pub struct Universe {
    id: UniverseId,
    name: String,
    author: String,
    source: String,
    /// The deterministic deploy seed for the world-cell. Fixed per universe so a
    /// re-verifier deploys the identical world; the committed *state* the replay
    /// verifier compares is seed-independent, but the seed must match across
    /// record + replay, so it is pinned here.
    deploy_seed: u8,
    provenance: Provenance,
    win: WinCondition,
    /// The **parent** this universe is a remix/fork of, if any — a content-addressed edge
    /// in the derivation graph. Bound into [`UniverseId`]. `None` for a root universe.
    parent: Option<UniverseId>,
    /// The **verified author identity** — the ed25519 key that attested this universe.
    /// `Some` iff the universe was published via [`UniversePlan::attest`]; `None` for a
    /// legacy/anonymous universe whose author is a bare name label.
    author_id: Option<AuthorId>,
    /// The author's attestation signature (held so it can be re-verified from a store).
    /// `Some` exactly when `author_id` is.
    attestation: Option<AuthorSignature>,
    /// The parsed scene (playable + verifiable).
    scene: Scene,
    /// Compiled var→slot map, for evaluating the win condition off a committed state
    /// vector without re-driving.
    var_slots: BTreeMap<String, usize>,
    /// The **proof-backed leaderboard anchor**, if this universe accepts succinct
    /// [`ProofCompletion`]s. `None` for a replay-only universe. Attached as CONFIG (via
    /// [`Universe::with_proof_anchor`]); it does not change the content [`UniverseId`]
    /// (it is a verification channel, not world content — like a distributed SNARK VK).
    proof_anchor: Option<ProofAnchor>,
}

/// The trust anchor a **proof-backed** leaderboard pins for a universe: the light-client
/// VK fingerprint plus the genesis state anchor this universe's runs start from and the
/// final state anchor that encodes the **WIN**. A [`ProofCompletion`] is accepted only
/// when [`verify_history_bytes`] succeeds under `vk` AND the attested `genesis_root` /
/// `final_root` equal these pinned anchors ([`verify_proof_completion`]).
///
/// These are CONFIGURATION — held by whoever runs the board, distributed exactly like a
/// SNARK VK, and **never read from the submitted proof** (which the submitter controls).
/// A submitter cannot pick their own anchor to forge a win: the board compares the
/// attested roots against the pinned ones it configured.
#[derive(Clone, Debug)]
pub struct ProofAnchor {
    /// The light client's trust anchor — the honest root circuit's VK fingerprint.
    pub vk: RecursionVk,
    /// The genesis state anchor of this universe's identically-seeded runs. A verified
    /// proof MUST attest a history starting here.
    pub genesis_root: [BabyBear; SEG_ANCHOR_WIDTH],
    /// The final state anchor that encodes the WIN — the state a completed (won) run
    /// reaches. A verified proof MUST attest a history ENDING here to count as a win.
    pub win_root: [BabyBear; SEG_ANCHOR_WIDTH],
}

impl ProofAnchor {
    /// Pin a proof-backed anchor from a VK + the genesis and win state anchors.
    pub fn new(
        vk: RecursionVk,
        genesis_root: [BabyBear; SEG_ANCHOR_WIDTH],
        win_root: [BabyBear; SEG_ANCHOR_WIDTH],
    ) -> ProofAnchor {
        ProofAnchor {
            vk,
            genesis_root,
            win_root,
        }
    }
}

/// Why a universe could not be published (its scene is not a valid, deployable world).
#[derive(Clone, Debug)]
pub enum PublishError {
    /// The spween source did not parse.
    Parse(String),
    /// The scene did not compile to a world-cell (or deploy).
    Compile(String),
    /// The claimed author public key is not a valid ed25519 key (a bad curve point).
    AuthorKey(String),
    /// **The author's attestation signature did not verify** over the universe's content
    /// commitment — a publish claiming an author key it cannot sign for is REFUSED. This
    /// is the author-identity tooth biting (mismatched key, forged/absent signature, or a
    /// signature lifted from a different universe).
    AuthorSignature,
}

impl fmt::Display for PublishError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PublishError::Parse(e) => write!(f, "universe scene did not parse: {e}"),
            PublishError::Compile(e) => write!(f, "universe scene did not compile: {e}"),
            PublishError::AuthorKey(e) => write!(f, "author public key is invalid: {e}"),
            PublishError::AuthorSignature => write!(
                f,
                "author attestation signature did not verify over the universe content \
                 commitment — this key did not sign this universe"
            ),
        }
    }
}

impl std::error::Error for PublishError {}

impl Universe {
    /// **PUBLISH an anonymous authored universe** from spween DSL `source` (author = a
    /// bare name label; no verified signing key). Convenience for
    /// [`UniversePlan::authored`] + [`UniversePlan::anonymous`], a root (no parent).
    pub fn authored(
        name: &str,
        author: &str,
        source: &str,
        win: WinCondition,
    ) -> Result<Universe, PublishError> {
        Ok(UniversePlan::authored(name, author, source, win, None)?.anonymous())
    }

    /// **PUBLISH an anonymous procgen universe** from a committed verifiable seed. The
    /// scene is generated deterministically from the seed through procgen-dregg's VERIFIED
    /// `dregg-dice` draw stream (never `rand`), and anyone can re-generate the
    /// byte-identical scene from the seed alone ([`Universe::regenerates_from_seed`]).
    /// The win is "seize the hoard" (`gold == 500`) — the generated world's objective.
    pub fn from_procgen(author: &str, seed: CommittedSeed) -> Result<Universe, PublishError> {
        Ok(UniversePlan::procgen(author, seed, None)?.anonymous())
    }

    /// **PUBLISH the DAILY universe** for a committed epoch value — a fresh, fair,
    /// publishable dungeon that everyone who sees the epoch commitment derives
    /// identically (via procgen-dregg's [`daily_seed`](procgen_dregg::daily_seed)).
    pub fn daily(author: &str, epoch_commitment: &[u8; 32]) -> Result<Universe, PublishError> {
        Ok(UniversePlan::daily(author, epoch_commitment, None)?.anonymous())
    }

    /// **PUBLISH a SIGNED authored universe** — the author `author_public_key` attests
    /// the world with `signature` over its content commitment, and (optionally) declares
    /// a `parent` it remixes. Refused ([`PublishError::AuthorSignature`]) if the signature
    /// does not verify. Convenience for [`UniversePlan::authored`] + [`UniversePlan::attest`].
    pub fn authored_signed(
        name: &str,
        author: &str,
        source: &str,
        win: WinCondition,
        parent: Option<UniverseId>,
        author_public_key: [u8; 32],
        signature: AuthorSignature,
    ) -> Result<Universe, PublishError> {
        UniversePlan::authored(name, author, source, win, parent)?
            .attest(author_public_key, signature)
    }

    /// **PUBLISH a SIGNED daily/procgen universe** — as [`Universe::authored_signed`] but
    /// for a committed epoch (procgen) world.
    pub fn daily_signed(
        author: &str,
        epoch_commitment: &[u8; 32],
        parent: Option<UniverseId>,
        author_public_key: [u8; 32],
        signature: AuthorSignature,
    ) -> Result<Universe, PublishError> {
        UniversePlan::daily(author, epoch_commitment, parent)?.attest(author_public_key, signature)
    }

    /// The universe commitment (content address / registry key).
    pub fn id(&self) -> UniverseId {
        self.id
    }
    /// The universe's display name.
    pub fn name(&self) -> &str {
        &self.name
    }
    /// The author **label** (a display name). For a *verified* identity use
    /// [`Universe::author_id`]; a signed universe has both a label and a proven key.
    pub fn author(&self) -> &str {
        &self.author
    }
    /// The **verified author identity** (ed25519 pubkey) that attested this universe, or
    /// `None` for a legacy/anonymous universe. When `Some`, the key provably signed this
    /// universe's content and is bound into its [`UniverseId`].
    pub fn author_id(&self) -> Option<AuthorId> {
        self.author_id
    }
    /// The author's attestation signature (present exactly when [`Universe::author_id`]
    /// is) — retained so the attestation can be re-verified from a durable store.
    pub fn attestation(&self) -> Option<&AuthorSignature> {
        self.attestation.as_ref()
    }
    /// Whether this universe carries a verified author identity (vs. an anonymous label).
    pub fn is_signed(&self) -> bool {
        self.author_id.is_some()
    }
    /// The **parent** this universe remixes/forks, or `None` if it is a root. A
    /// content-addressed edge in the derivation graph, bound into the [`UniverseId`].
    pub fn parent(&self) -> Option<UniverseId> {
        self.parent
    }
    /// The spween DSL source of the world.
    pub fn source(&self) -> &str {
        &self.source
    }
    /// The provenance of the world's scene.
    pub fn provenance(&self) -> &Provenance {
        &self.provenance
    }
    /// The declared win condition.
    pub fn win(&self) -> &WinCondition {
        &self.win
    }

    /// Attach a [`ProofAnchor`], making this universe accept succinct
    /// [`ProofCompletion`]s alongside replay ones. Config only — it does NOT change the
    /// content [`UniverseId`] (a verification channel, not world content). Returns the
    /// universe so it can be chained into [`Registry::publish`].
    pub fn with_proof_anchor(mut self, anchor: ProofAnchor) -> Universe {
        self.proof_anchor = Some(anchor);
        self
    }

    /// The proof-backed anchor, if this universe accepts succinct proof completions.
    pub fn proof_anchor(&self) -> Option<&ProofAnchor> {
        self.proof_anchor.as_ref()
    }

    /// **Re-generate check** for a procgen universe: does its scene regenerate
    /// byte-for-byte from its committed seed? Returns `true` for an honest procgen
    /// universe, `false` if the source was tampered away from its committed seed.
    /// (Always `false` for an [`Provenance::Authored`] universe — there is no seed.)
    pub fn regenerates_from_seed(&self) -> bool {
        match &self.provenance {
            Provenance::Procgen { committed_seed } => {
                let seed = CommittedSeed::from_bytes(*committed_seed);
                let (regen, _) = generate::scene_source(&seed);
                regen == self.source
            }
            Provenance::Authored => false,
        }
    }

    /// Deploy a FRESH, identically-seeded world for this universe (what a re-verifier
    /// re-executes against). Deterministic in the pinned deploy seed.
    fn fresh_world(&self) -> Result<WorldCell, WorldError> {
        WorldCell::deploy(&self.scene, self.deploy_seed)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// UniversePlan — a validated, not-yet-published universe. Splits the two publish
// concerns: (1) is this a real, deployable world (parse/compile/deploy)? and (2) who
// authored it (anonymous label, or a signed identity)? A plan resolves (1) and exposes
// the exact bytes an author signs for (2), so the *bot* can sign with the author's
// cipherclerk BEFORE the universe exists, then attest it.
// ═══════════════════════════════════════════════════════════════════════════════

/// A **validated, unpublished universe** — a real deployable world (parse/compile/deploy
/// all passed) whose authorship is not yet fixed. Finish it with
/// [`UniversePlan::anonymous`] (author = a bare label) or [`UniversePlan::attest`] (a
/// verified ed25519 author identity). A plan can declare a `parent` it remixes.
pub struct UniversePlan {
    name: String,
    author_label: String,
    source: String,
    deploy_seed: u8,
    provenance: Provenance,
    win: WinCondition,
    parent: Option<UniverseId>,
    scene: Scene,
    var_slots: BTreeMap<String, usize>,
    /// The 32-byte content commitment an author signs — see [`Self::signing_commitment`].
    commitment: [u8; 32],
}

impl UniversePlan {
    /// Validate an authored (hand-written spween) world, optionally remixing `parent`.
    pub fn authored(
        name: &str,
        author_label: &str,
        source: &str,
        win: WinCondition,
        parent: Option<UniverseId>,
    ) -> Result<UniversePlan, PublishError> {
        Self::assemble(
            name,
            author_label,
            source,
            7,
            Provenance::Authored,
            win,
            parent,
        )
    }

    /// Validate a procgen world drawn from a committed verifiable seed, optionally
    /// remixing `parent`. The win is the generated world's objective (`gold == 500`).
    pub fn procgen(
        author_label: &str,
        seed: CommittedSeed,
        parent: Option<UniverseId>,
    ) -> Result<UniversePlan, PublishError> {
        let (source, title) = generate::scene_source(&seed);
        let deploy_seed = seed.as_bytes()[0];
        Self::assemble(
            &title,
            author_label,
            &source,
            deploy_seed,
            Provenance::Procgen {
                committed_seed: *seed.as_bytes(),
            },
            WinCondition::ended_with(&[("gold", 500)]),
            parent,
        )
    }

    /// Validate the DAILY procgen world for a committed epoch, optionally remixing
    /// `parent`.
    pub fn daily(
        author_label: &str,
        epoch_commitment: &[u8; 32],
        parent: Option<UniverseId>,
    ) -> Result<UniversePlan, PublishError> {
        Self::procgen(
            author_label,
            procgen_dregg::daily_seed(epoch_commitment),
            parent,
        )
    }

    fn assemble(
        name: &str,
        author_label: &str,
        source: &str,
        deploy_seed: u8,
        provenance: Provenance,
        win: WinCondition,
        parent: Option<UniverseId>,
    ) -> Result<UniversePlan, PublishError> {
        let scene = parse(source, &format!("{name}.scene"))
            .map_err(|e| PublishError::Parse(e.to_string()))?;
        // Compile up front: a scene that does not lower to a world-cell is not a
        // publishable universe. We keep the var→slot map for win evaluation.
        let compiled: CompiledStory =
            compile_scene(&scene).map_err(|e| PublishError::Compile(e.to_string()))?;
        // Deploy once to confirm it actually births a world (fail-closed on publish).
        WorldCell::deploy(&scene, deploy_seed).map_err(|e| PublishError::Compile(e.to_string()))?;

        let commitment = content_commitment(
            name,
            author_label,
            source,
            deploy_seed,
            &provenance,
            &win,
            parent,
        );
        Ok(UniversePlan {
            name: name.to_string(),
            author_label: author_label.to_string(),
            source: source.to_string(),
            deploy_seed,
            provenance,
            win,
            parent,
            scene,
            var_slots: compiled.var_slots,
            commitment,
        })
    }

    /// The **32-byte content commitment** an author signs to attest this universe. It
    /// binds everything that identifies the world (name, label, source, deploy identity,
    /// provenance, win, parent) EXCEPT the author key itself — so a valid signature over
    /// it proves the key's holder vouches for *this* exact world (and it cannot be lifted
    /// onto a different one).
    pub fn signing_commitment(&self) -> [u8; 32] {
        self.commitment
    }

    /// The declared parent of this remix, or `None` for a root.
    pub fn parent(&self) -> Option<UniverseId> {
        self.parent
    }

    /// Finish as an **anonymous** universe — the author is the bare label, with no
    /// verified signing key. (The legacy `Universe::authored`/`daily` path.)
    pub fn anonymous(self) -> Universe {
        self.finish(None, None)
    }

    /// Finish as a **signed** universe: verify `signature` is a valid ed25519 signature by
    /// `author_public_key` over [`Self::signing_commitment`], then bind the key into the
    /// content address. Refused with [`PublishError::AuthorSignature`] if it does not
    /// verify (a forged/absent/mismatched signature, or one lifted from another universe),
    /// or [`PublishError::AuthorKey`] if the key is not a valid ed25519 point.
    pub fn attest(
        self,
        author_public_key: [u8; 32],
        signature: AuthorSignature,
    ) -> Result<Universe, PublishError> {
        let vk = VerifyingKey::from_bytes(&author_public_key)
            .map_err(|e| PublishError::AuthorKey(e.to_string()))?;
        let sig = Signature::from_bytes(signature.as_bytes());
        vk.verify_strict(&self.commitment, &sig)
            .map_err(|_| PublishError::AuthorSignature)?;
        Ok(self.finish(Some(AuthorId(author_public_key)), Some(signature)))
    }

    fn finish(self, author_id: Option<AuthorId>, attestation: Option<AuthorSignature>) -> Universe {
        let id = universe_id(
            &self.name,
            &self.author_label,
            &self.source,
            self.deploy_seed,
            &self.provenance,
            &self.win,
            self.parent,
            author_id,
        );
        Universe {
            id,
            name: self.name,
            author: self.author_label,
            source: self.source,
            deploy_seed: self.deploy_seed,
            provenance: self.provenance,
            win: self.win,
            parent: self.parent,
            author_id,
            attestation,
            scene: self.scene,
            var_slots: self.var_slots,
            proof_anchor: None,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Completion — a submitted, to-be-verified playthrough.
// ═══════════════════════════════════════════════════════════════════════════════

/// A **submitted completion**: which universe, who played it, the recorded
/// [`Playthrough`] (the ordered moves + their receipt chain), and the claimed
/// turns-to-win. Nothing here is trusted — the board re-verifies it.
#[derive(Clone, Debug)]
pub struct Completion {
    /// The universe this completion is for.
    pub universe: UniverseId,
    /// The player's name.
    pub player: String,
    /// The recorded playthrough (the un-retconnable receipt chain).
    pub play: Playthrough,
    /// The player's claimed turns-to-win (verified against the actual move count).
    pub claimed_turns: usize,
}

/// Why a completion was rejected. Every arm is a real refusal — the board is
/// no-cheat by construction.
#[derive(Clone, Debug)]
pub enum RejectReason {
    /// No such universe is registered.
    UnknownUniverse,
    /// The completion names a different universe than the one it was submitted to.
    WrongUniverse,
    /// A fresh world could not be deployed (should not happen for a published universe).
    Deploy(String),
    /// **The recorded receipt chain did not re-verify** — a forged/edited/spliced
    /// playthrough refused by the real executor on replay, or diverging from the
    /// reproduced committed state. This is the no-cheat tooth biting.
    FailedVerification(VerifyBreak),
    /// The playthrough re-verified, but it **did not reach the win state** (the scene
    /// did not end, or a declared win-var did not hold). An incomplete playthrough.
    DidNotWin,
    /// The playthrough won, but the **claimed result was tampered** — the claimed
    /// turns-to-win did not equal the verified move count (or, for a proof completion,
    /// the attested `num_turns`).
    ResultMismatch {
        /// What the submitter claimed.
        claimed: usize,
        /// The verified move count (or attested turn count).
        actual: usize,
    },
    // ── proof-backed (succinct) path ──────────────────────────────────────────────
    /// A [`ProofCompletion`] was submitted to a universe with no [`ProofAnchor`]
    /// configured — it does not accept succinct proofs.
    NotProofBacked,
    /// **The succinct proof did not verify** — the whole-history light client REJECTED
    /// it (a tampered / relabeled / foreign proof). This is the crypto no-cheat tooth
    /// biting, at O(1), re-witnessing nothing.
    ProofRejected(LightClientError),
    /// The proof verified, but its attested `genesis_root` is not this universe's pinned
    /// genesis anchor — the proof attests a DIFFERENT universe's history.
    GenesisMismatch,
    /// The proof verified and starts from this universe's genesis, but its attested
    /// `final_root` is not the pinned **win anchor** — the attested history did NOT reach
    /// the win state (the proof-path analogue of [`RejectReason::DidNotWin`]).
    WinNotProven,
}

impl fmt::Display for RejectReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RejectReason::UnknownUniverse => write!(f, "no such universe is registered"),
            RejectReason::WrongUniverse => {
                write!(
                    f,
                    "completion is for a different universe than submitted to"
                )
            }
            RejectReason::Deploy(e) => write!(f, "could not deploy a fresh world: {e}"),
            RejectReason::FailedVerification(b) => {
                write!(f, "recorded playthrough failed re-verification: {b}")
            }
            RejectReason::DidNotWin => {
                write!(f, "playthrough re-verified but did not reach the win state")
            }
            RejectReason::ResultMismatch { claimed, actual } => write!(
                f,
                "tampered result: claimed {claimed} turns, verified {actual}"
            ),
            RejectReason::NotProofBacked => {
                write!(f, "universe does not accept succinct proof completions")
            }
            RejectReason::ProofRejected(e) => {
                write!(f, "succinct proof did not verify: {e}")
            }
            RejectReason::GenesisMismatch => write!(
                f,
                "proof attests a different universe's genesis than the one submitted to"
            ),
            RejectReason::WinNotProven => write!(
                f,
                "proof verified but its final root is not the universe's declared win state"
            ),
        }
    }
}

impl std::error::Error for RejectReason {}

/// **THE NO-CHEAT VERIFIER** — the whole guarantee, usable independently of any
/// [`Registry`]. Anyone holding the (public) universe and a completion can call this
/// and get the authoritative verdict:
///
/// 1. re-execute the submitted moves against a FRESH identically-seeded world and
///    require the recorded receipt chain re-verifies ([`verify`]);
/// 2. require the replay reaches the universe's WIN state;
/// 3. require the claimed turns equal the verified move count.
///
/// On success returns the verified turns-to-win (the ranking key).
pub fn verify_completion(universe: &Universe, c: &Completion) -> Result<usize, RejectReason> {
    if c.universe != universe.id {
        return Err(RejectReason::WrongUniverse);
    }

    // (1) Re-execute: chain-linkage + replay against a fresh, identically-seeded world.
    let fresh = universe
        .fresh_world()
        .map_err(|e| RejectReason::Deploy(e.to_string()))?;
    verify(fresh, &universe.scene, &c.play).map_err(RejectReason::FailedVerification)?;

    // (2) Require the WIN. `verify` above guarantees the recorded states are the
    // faithful reproduced states, so evaluating the win off the final recorded state
    // is sound. An empty playthrough (no moves) can never have reached a terminal.
    let Some(last) = c.play.steps.last() else {
        return Err(RejectReason::DidNotWin);
    };
    if !reached_win(universe, &last.state) {
        return Err(RejectReason::DidNotWin);
    }

    // (3) Bind the claimed result to the verified move count.
    let actual = c.play.steps.len();
    if c.claimed_turns != actual {
        return Err(RejectReason::ResultMismatch {
            claimed: c.claimed_turns,
            actual,
        });
    }

    Ok(actual)
}

// ═══════════════════════════════════════════════════════════════════════════════
// ProofCompletion — a submitted, to-be-verified SUCCINCT proof (no moves posted).
// ═══════════════════════════════════════════════════════════════════════════════

/// A **submitted proof-backed completion**: which universe, who played it, the succinct
/// fold-proof envelope (a `WholeChainProof` serialized via `to_bytes()`), and the claimed
/// turns-to-win. It carries **no moves** — the playthrough is not posted. Nothing here is
/// trusted; the board verifies the proof in O(1) ([`verify_proof_completion`]).
#[derive(Clone, Debug)]
pub struct ProofCompletion {
    /// The universe this completion is for (must have a [`ProofAnchor`]).
    pub universe: UniverseId,
    /// The player's name.
    pub player: String,
    /// The succinct whole-history proof envelope (`WholeChainProof::to_bytes()`). The
    /// board decodes + verifies it against the universe's pinned VK anchor — the moves
    /// are NOT here and never re-executed.
    pub proof_bytes: Vec<u8>,
    /// The player's claimed turns-to-win (verified against the attested `num_turns`).
    pub claimed_turns: usize,
}

/// **THE SUCCINCT NO-CHEAT VERIFIER** — the proof-path analogue of [`verify_completion`],
/// usable independently of any [`Registry`]. Verifies a proof-backed completion in
/// **O(1)**, re-witnessing NOTHING (no replay, no re-hash, no walk of the moves):
///
/// 1. the universe must be proof-backed (have a [`ProofAnchor`]);
/// 2. the whole-history light client ([`verify_history_bytes`]) must ACCEPT the proof
///    under the universe's pinned VK anchor — a tampered/relabeled/foreign proof is
///    refused HERE (the crypto tooth);
/// 3. the attested `genesis_root` must equal the pinned genesis anchor (this universe);
/// 4. the attested `final_root` must equal the pinned **win anchor** (the win predicate);
/// 5. the claimed turns must equal the attested `num_turns`.
///
/// On success returns `(turns-to-win, the attested publics)` — the ranking key + the
/// publics an [`Entry`] stores in place of the moves.
pub fn verify_proof_completion(
    universe: &Universe,
    c: &ProofCompletion,
) -> Result<(usize, AttestedHistory), RejectReason> {
    if c.universe != universe.id {
        return Err(RejectReason::WrongUniverse);
    }
    let anchor = universe
        .proof_anchor
        .as_ref()
        .ok_or(RejectReason::NotProofBacked)?;

    // (2) THE O(1) LIGHT-CLIENT CHECK — re-witnessing nothing. A relabeled/forged proof
    // is refused here (Fiat–Shamir binds the publics into the carried binding proof).
    let attested =
        verify_history_bytes(&c.proof_bytes, &anchor.vk).map_err(RejectReason::ProofRejected)?;

    // (3) Bind THIS universe's identically-seeded genesis.
    if attested.genesis_root != anchor.genesis_root {
        return Err(RejectReason::GenesisMismatch);
    }
    // (4) Bind the WIN predicate: the attested history reached the declared win state.
    if attested.final_root != anchor.win_root {
        return Err(RejectReason::WinNotProven);
    }
    // (5) Bind the claimed result to the attested turn count.
    if c.claimed_turns != attested.num_turns {
        return Err(RejectReason::ResultMismatch {
            claimed: c.claimed_turns,
            actual: attested.num_turns,
        });
    }

    Ok((attested.num_turns, attested))
}

/// Evaluate the universe's win condition against a final committed state vector: the
/// scene must have ENDED and every declared win-var must hold.
fn reached_win(universe: &Universe, state: &[u64]) -> bool {
    let ended = state.get(PASSAGE_SLOT).is_some_and(|&p| p == PASSAGE_ENDED);
    if !ended {
        return false;
    }
    universe.win.vars.iter().all(|(name, want)| {
        universe
            .var_slots
            .get(name)
            .and_then(|&slot| state.get(slot))
            .is_some_and(|&got| got == *want)
    })
}

// ═══════════════════════════════════════════════════════════════════════════════
// The leaderboard registry.
// ═══════════════════════════════════════════════════════════════════════════════

/// The evidence backing an accepted [`Entry`] — the two leaderboard variants.
#[derive(Clone, Debug)]
enum Evidence {
    /// The REPLAY path: the full recorded playthrough is kept, so anyone can re-execute
    /// it from scratch (O(N)).
    Replay(Playthrough),
    /// The SUCCINCT (ZK-leaderboard) path: **the moves are NOT stored** — only the fold
    /// proof envelope + the attested publics. Re-verification re-runs the O(1) light
    /// client, never a replay.
    Proof {
        /// The `WholeChainProof` byte envelope (`to_bytes()`).
        proof_bytes: Vec<u8>,
        /// The attested public roots the verified proof binds (genesis/final/digest/turns).
        publics: AttestedHistory,
    },
}

/// One accepted, verified entry on a universe's leaderboard. A REPLAY entry carries the
/// recorded playthrough (re-executable from scratch); a PROOF entry carries ONLY the
/// succinct proof envelope + the attested publics — **the moves are not stored**. Either
/// way it is INDEPENDENTLY re-verifiable ([`Registry::reverify_entry`]).
#[derive(Clone, Debug)]
pub struct Entry {
    /// The player's name.
    pub player: String,
    /// The verified turns-to-win (the rank key — lower is better).
    pub turns: usize,
    /// A content id for this completion (over the player + the receipt chain, or the
    /// player + the proof envelope for a proof entry).
    pub completion_id: [u8; 32],
    /// What backs this entry — a full playthrough (replay path) or a succinct proof
    /// (proof path, moves not posted).
    evidence: Evidence,
}

impl Entry {
    /// The recorded playthrough behind a REPLAY entry, or `None` for a PROOF entry
    /// (whose moves were never posted — the practical-privacy property).
    pub fn playthrough(&self) -> Option<&Playthrough> {
        match &self.evidence {
            Evidence::Replay(play) => Some(play),
            Evidence::Proof { .. } => None,
        }
    }

    /// The succinct proof envelope behind a PROOF entry, or `None` for a replay entry.
    pub fn proof_bytes(&self) -> Option<&[u8]> {
        match &self.evidence {
            Evidence::Proof { proof_bytes, .. } => Some(proof_bytes),
            Evidence::Replay(_) => None,
        }
    }

    /// The attested public roots behind a PROOF entry, or `None` for a replay entry.
    pub fn attested(&self) -> Option<&AttestedHistory> {
        match &self.evidence {
            Evidence::Proof { publics, .. } => Some(publics),
            Evidence::Replay(_) => None,
        }
    }

    /// Whether this entry stores the moves (a replay entry) — `false` for a proof-backed
    /// entry, whose moves are not posted.
    pub fn has_moves(&self) -> bool {
        matches!(self.evidence, Evidence::Replay(_))
    }

    /// Whether this entry is backed by a succinct proof (moves not posted).
    pub fn is_proof_backed(&self) -> bool {
        matches!(self.evidence, Evidence::Proof { .. })
    }
}

/// The outcome of an accepted submission.
#[derive(Clone, Debug)]
pub struct Accepted {
    /// The verified turns-to-win.
    pub turns: usize,
    /// The completion's content id.
    pub completion_id: [u8; 32],
    /// The entry's 1-based rank on the board after insertion.
    pub rank: usize,
}

/// Why a remix/fork could not be published into the derivation graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LineageError {
    /// The universe declares a parent that is not a published universe — a remix of a
    /// non-existent (or not-yet-published) parent is refused.
    UnknownParent(UniverseId),
}

impl fmt::Display for LineageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LineageError::UnknownParent(p) => {
                write!(f, "remix parent {p} is not a published universe")
            }
        }
    }
}

impl std::error::Error for LineageError {}

/// The **UGC registry + leaderboards**. Universes are keyed by their content address;
/// each has a leaderboard of verified completions, ranked by turns-to-win.
#[derive(Default)]
pub struct Registry {
    universes: BTreeMap<UniverseId, Universe>,
    boards: BTreeMap<UniverseId, Vec<Entry>>,
}

impl Registry {
    /// A fresh, empty registry.
    pub fn new() -> Registry {
        Registry::default()
    }

    /// **PUBLISH** a universe. Idempotent by content address: re-publishing the same
    /// universe returns the same id and does not duplicate it. Returns the id.
    ///
    /// Lineage guard: a remix whose declared `parent` is NOT already published is
    /// **dropped** (not inserted) — the derivation graph never dangles — though the id is
    /// still returned to preserve the infallible signature. Roots (no parent) always
    /// publish. Use [`Registry::publish_derived`] for the Result-returning path that
    /// surfaces an absent parent as [`LineageError::UnknownParent`].
    pub fn publish(&mut self, universe: Universe) -> UniverseId {
        let id = universe.id;
        if let Some(parent) = universe.parent {
            if !self.universes.contains_key(&parent) {
                return id;
            }
        }
        self.universes.entry(id).or_insert(universe);
        self.boards.entry(id).or_default();
        id
    }

    /// **PUBLISH a remix / fork.** Like [`Registry::publish`], but a universe that
    /// declares a `parent` is accepted ONLY if that parent is already a published
    /// universe — otherwise it is refused with [`LineageError::UnknownParent`] and nothing
    /// is inserted. A root (no parent) always succeeds. This is the lineage tooth: a remix
    /// of a non-existent parent cannot enter the derivation graph.
    pub fn publish_derived(&mut self, universe: Universe) -> Result<UniverseId, LineageError> {
        if let Some(parent) = universe.parent {
            if !self.universes.contains_key(&parent) {
                return Err(LineageError::UnknownParent(parent));
            }
        }
        Ok(self.publish(universe))
    }

    /// Look up a published universe.
    pub fn universe(&self, id: UniverseId) -> Option<&Universe> {
        self.universes.get(&id)
    }

    /// Every published universe.
    pub fn universes(&self) -> impl Iterator<Item = &Universe> {
        self.universes.values()
    }

    /// The **parent** of a published universe (the universe it remixes), or `None` if it
    /// is a root or not registered.
    pub fn parent_of(&self, id: UniverseId) -> Option<UniverseId> {
        self.universes.get(&id).and_then(|u| u.parent)
    }

    /// Every published **child** (direct remix/fork) of `id`.
    pub fn children_of(&self, id: UniverseId) -> Vec<UniverseId> {
        self.universes
            .values()
            .filter(|u| u.parent == Some(id))
            .map(|u| u.id)
            .collect()
    }

    /// Whether a published universe is a root (no parent). `None` if not registered.
    pub fn is_root(&self, id: UniverseId) -> Option<bool> {
        self.universes.get(&id).map(|u| u.parent.is_none())
    }

    /// **Re-verify the derivation graph**: every published universe's declared parent is
    /// itself published (no dangling edge). Holds by construction ([`Registry::publish`]
    /// drops a child with an absent parent); call it after a boot replay to confirm the
    /// reconstructed lineage is sound.
    pub fn lineage_holds(&self) -> bool {
        self.universes.values().all(|u| match u.parent {
            None => true,
            Some(parent) => self.universes.contains_key(&parent),
        })
    }

    /// **SUBMIT a completion.** The board re-verifies it ([`verify_completion`]) and
    /// ONLY on success accepts + ranks it. A forged / incomplete / result-tampered
    /// completion is REJECTED (nothing is added to the board).
    pub fn submit(&mut self, c: Completion) -> Result<Accepted, RejectReason> {
        let universe = self
            .universes
            .get(&c.universe)
            .ok_or(RejectReason::UnknownUniverse)?;

        // The no-cheat gate. Only a verified win, with a truthful result, gets past.
        let turns = verify_completion(universe, &c)?;

        let completion_id = completion_id(&c.player, &c.play);
        let entry = Entry {
            player: c.player,
            turns,
            completion_id,
            evidence: Evidence::Replay(c.play),
        };
        Ok(self.rank_entry(c.universe, entry))
    }

    /// **SUBMIT a succinct proof-backed completion** — the ZK-leaderboard accept-path.
    /// The board verifies the fold proof in **O(1)** ([`verify_proof_completion`]) and
    /// ONLY on success accepts + ranks it — WITHOUT re-executing any move. The accepted
    /// [`Entry`] stores ONLY the proof + attested publics; **the moves are not posted**.
    /// A tampered/forged proof, a wrong genesis, an unproven win, or a lied turn count is
    /// REJECTED (nothing is added to the board).
    pub fn submit_proof(&mut self, c: ProofCompletion) -> Result<Accepted, RejectReason> {
        let universe = self
            .universes
            .get(&c.universe)
            .ok_or(RejectReason::UnknownUniverse)?;

        // The succinct no-cheat gate — O(1), re-witnessing nothing.
        let (turns, publics) = verify_proof_completion(universe, &c)?;

        let completion_id = proof_completion_id(&c.player, &c.proof_bytes);
        let entry = Entry {
            player: c.player,
            turns,
            completion_id,
            // THE PRIVACY: only the proof envelope + attested publics. NO moves.
            evidence: Evidence::Proof {
                proof_bytes: c.proof_bytes,
                publics,
            },
        };
        Ok(self.rank_entry(c.universe, entry))
    }

    /// Insert a verified entry onto a universe's board and return its rank (shared by the
    /// replay + proof submit paths — both rank by turns ascending on one board).
    fn rank_entry(&mut self, universe: UniverseId, entry: Entry) -> Accepted {
        let completion_id = entry.completion_id;
        let turns = entry.turns;
        let board = self.boards.entry(universe).or_default();
        board.push(entry);
        // Rank by turns ascending; stable for equal turns (insertion order preserved).
        board.sort_by_key(|e| e.turns);
        let rank = board
            .iter()
            .position(|e| e.completion_id == completion_id)
            .map(|i| i + 1)
            .unwrap_or(board.len());
        Accepted {
            turns,
            completion_id,
            rank,
        }
    }

    /// The **leaderboard** for a universe — accepted entries ranked by turns-to-win
    /// (lower first). Every entry here provably reaches the win.
    pub fn leaderboard(&self, id: UniverseId) -> Vec<&Entry> {
        self.boards
            .get(&id)
            .map(|b| b.iter().collect())
            .unwrap_or_default()
    }

    /// **INDEPENDENTLY re-verify** a leaderboard entry. For a REPLAY entry: re-execute its
    /// recorded playthrough from scratch against a fresh world and confirm it still
    /// verifies to the claimed win in the claimed turns (O(N)). For a PROOF entry: re-run
    /// the O(1) whole-history light client on the stored proof against the universe's
    /// pinned anchor — **never a replay** (the moves were never posted). Anyone can do
    /// this; a tampered board cannot survive it either way.
    pub fn reverify_entry(
        &self,
        id: UniverseId,
        completion_id: &[u8; 32],
    ) -> Result<usize, RejectReason> {
        let universe = self
            .universes
            .get(&id)
            .ok_or(RejectReason::UnknownUniverse)?;
        let board = self.boards.get(&id).ok_or(RejectReason::UnknownUniverse)?;
        let entry = board
            .iter()
            .find(|e| &e.completion_id == completion_id)
            .ok_or(RejectReason::UnknownUniverse)?;
        match &entry.evidence {
            Evidence::Replay(play) => {
                let c = Completion {
                    universe: id,
                    player: entry.player.clone(),
                    play: play.clone(),
                    claimed_turns: entry.turns,
                };
                verify_completion(universe, &c)
            }
            Evidence::Proof { proof_bytes, .. } => {
                // Re-verify via the O(1) light client — re-witnessing nothing, no replay.
                let c = ProofCompletion {
                    universe: id,
                    player: entry.player.clone(),
                    proof_bytes: proof_bytes.clone(),
                    claimed_turns: entry.turns,
                };
                verify_proof_completion(universe, &c).map(|(turns, _)| turns)
            }
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Recording helper — a player drives their OWN copy to produce a playthrough.
// ═══════════════════════════════════════════════════════════════════════════════

/// **Record a playthrough** by driving a fresh copy of `universe` through `moves`
/// (each `usize` is a choice index at the current passage). This is what a player runs
/// locally to produce the [`Playthrough`] they submit. The leaderboard does NOT trust
/// its output — it re-verifies it. A move refused by the real executor (an ineligible
/// pick) fails here with the executor's refusal.
pub fn record_playthrough(universe: &Universe, moves: &[usize]) -> Result<Playthrough, WorldError> {
    let world = WorldCell::deploy(&universe.scene, universe.deploy_seed)?;
    let mut driver = Driver::start(world, &universe.scene)?;
    for &m in moves {
        driver.advance(m)?;
    }
    Ok(driver.playthrough())
}

// ═══════════════════════════════════════════════════════════════════════════════
// Content addressing.
// ═══════════════════════════════════════════════════════════════════════════════

fn domain_hasher(tag: &[u8]) -> blake3::Hasher {
    let mut h = blake3::Hasher::new();
    h.update(&(tag.len() as u64).to_le_bytes());
    h.update(tag);
    h
}

fn field(h: &mut blake3::Hasher, bytes: &[u8]) {
    h.update(&(bytes.len() as u64).to_le_bytes());
    h.update(bytes);
}

/// The **core** of the content address: every rule that changes verification (scene
/// bytes, deploy identity, provenance, the declared win predicate) plus the derivation
/// edge (`parent`). Shared by [`universe_id`] (which additionally binds the author key)
/// and [`content_commitment`] (what the author signs — no author key, to avoid
/// circularity). Omitting `win` would let `gold == 500` and merely `ENDED` share an id;
/// omitting `parent` would let a remix collide with its own root.
fn hash_universe_core(
    h: &mut blake3::Hasher,
    name: &str,
    author_label: &str,
    source: &str,
    deploy_seed: u8,
    provenance: &Provenance,
    win: &WinCondition,
    parent: Option<UniverseId>,
) {
    field(h, name.as_bytes());
    field(h, author_label.as_bytes());
    field(h, source.as_bytes());
    field(h, &[deploy_seed]);
    match provenance {
        Provenance::Authored => field(h, b"authored"),
        Provenance::Procgen { committed_seed } => {
            field(h, b"procgen");
            field(h, committed_seed);
        }
    }
    // A win condition is a conjunction, so canonicalize the caller's order.
    let mut vars = win.vars.clone();
    vars.sort();
    h.update(&(vars.len() as u64).to_le_bytes());
    for (name, value) in vars {
        field(h, name.as_bytes());
        h.update(&value.to_le_bytes());
    }
    // The derivation edge: a root and a remix of it are distinct content addresses.
    match parent {
        None => field(h, b"root"),
        Some(p) => {
            field(h, b"child");
            field(h, p.as_bytes());
        }
    }
}

/// The 32-byte **author content commitment** — the message an author ed25519-signs to
/// attest a universe. Binds the core (including the parent) but NOT the author key, so a
/// valid signature over it proves the key vouches for this exact world and cannot be
/// replayed onto a different one.
fn content_commitment(
    name: &str,
    author_label: &str,
    source: &str,
    deploy_seed: u8,
    provenance: &Provenance,
    win: &WinCondition,
    parent: Option<UniverseId>,
) -> [u8; 32] {
    let mut h = domain_hasher(DOMAIN_AUTHOR_SIG);
    hash_universe_core(
        &mut h,
        name,
        author_label,
        source,
        deploy_seed,
        provenance,
        win,
        parent,
    );
    *h.finalize().as_bytes()
}

/// The universe commitment: the core, plus the verified author identity (so a signed
/// universe and its anonymous twin — or a fork under a different author key — are
/// distinct content addresses, and the id *binds the real author key*).
#[allow(clippy::too_many_arguments)]
fn universe_id(
    name: &str,
    author_label: &str,
    source: &str,
    deploy_seed: u8,
    provenance: &Provenance,
    win: &WinCondition,
    parent: Option<UniverseId>,
    author_id: Option<AuthorId>,
) -> UniverseId {
    let mut h = domain_hasher(DOMAIN_UNIVERSE_ID);
    hash_universe_core(
        &mut h,
        name,
        author_label,
        source,
        deploy_seed,
        provenance,
        win,
        parent,
    );
    match author_id {
        None => field(&mut h, b"anon"),
        Some(a) => {
            field(&mut h, b"signed");
            field(&mut h, a.as_bytes());
        }
    }
    UniverseId(*h.finalize().as_bytes())
}

/// A completion id over the player + the whole receipt chain (each turn hash).
fn completion_id(player: &str, play: &Playthrough) -> [u8; 32] {
    let mut h = domain_hasher(DOMAIN_COMPLETION_ID);
    field(&mut h, player.as_bytes());
    for r in play.receipts() {
        h.update(&r.turn_hash);
    }
    *h.finalize().as_bytes()
}

/// The content id of a **proof-backed** completion: the player + the succinct proof
/// envelope (there are no moves to hash — the whole point of the proof path).
fn proof_completion_id(player: &str, proof_bytes: &[u8]) -> [u8; 32] {
    let mut h = domain_hasher(DOMAIN_PROOF_COMPLETION_ID);
    field(&mut h, player.as_bytes());
    field(&mut h, proof_bytes);
    *h.finalize().as_bytes()
}

// ═══════════════════════════════════════════════════════════════════════════════
// The procgen → playable spween world generator.
// ═══════════════════════════════════════════════════════════════════════════════

/// Generate a **playable, winnable spween world** deterministically from a committed
/// procgen seed, drawing every choice from procgen-dregg's VERIFIED `dregg-dice`
/// stream (its fairness; never `rand`). A verifier who holds the committed seed
/// re-derives the identical stream and re-generates the byte-identical scene — that is
/// what content-addresses a procgen universe to its seed.
///
/// The emitted world is a linear dungeon: room 0 holds the key (take it or leave it),
/// a chain of rooms leads to a gated descent (`{ has_key >= 1 }` — a REAL executor
/// tooth once compiled), and the final room's hoard (`gold += 500`) ends the scene.
/// So it is genuinely winnable, and only by holding the key — a real no-cheat puzzle.
mod generate {
    use procgen_dregg::{CommittedSeed, verified_stream};

    struct Theme {
        title: &'static str,
        key_item: &'static str,
        win_item: &'static str,
        descs: &'static [&'static str],
    }

    const THEMES: [Theme; 4] = [
        Theme {
            title: "The Sunken Vault",
            key_item: "brass_key",
            win_item: "fen_heart",
            descs: &[
                "Cold fen-water laps at the stones; a warden's lantern hangs from an iron hook.",
                "A roofless hall choked with sedge, its floor a slick of green tide-weed.",
                "Drip and echo; something pale drifts in the black water below.",
            ],
        },
        Theme {
            title: "The Clockwork Orchard",
            key_item: "winding_key",
            win_item: "orrery_core",
            descs: &[
                "Trees of hammered copper stand in dead rows; a great gear lies canted across the aisle.",
                "The air smells of oil and cold metal; something ticks, slow, out of sight.",
                "Automaton birds hang frozen mid-song from wire branches overhead.",
            ],
        },
        Theme {
            title: "The Ember Observatory",
            key_item: "sun_sigil",
            win_item: "ember_lens",
            descs: &[
                "Warm ash sifts from a cracked dome; the floor is warm underfoot.",
                "A great brass telescope points at a shuttered sky, its lens gone dark.",
                "Embers glow in a cold hearth that no one has tended in an age.",
            ],
        },
        Theme {
            title: "The Venom Warren",
            key_item: "chitin_key",
            win_item: "brood_pearl",
            descs: &[
                "Fat pale mushrooms crowd the walls; the air is thick and green and still.",
                "Silk hangs in grey ropes from a low ceiling; something skitters and is gone.",
                "Roots have broken the floor into a maze of damp black hollows.",
            ],
        },
    ];

    const MIN_ROOMS: usize = 4;
    const MAX_ROOMS: usize = 7;

    /// Emit the `.dungeon`-equivalent spween scene source + its title. Deterministic
    /// in the committed seed. Draw indices stay well under procgen's committed
    /// `DRAW_COUNT` (~46), so every draw is within the transcript-bound budget.
    pub(super) fn scene_source(seed: &CommittedSeed) -> (String, String) {
        // procgen's VERIFIED stream: a producer emits evidence, the pure verifier
        // re-derives the seed + checks the transcript commitment. Grinding is refused.
        let (_req, _ev, stream) = verified_stream(seed);
        let pick = |index: u32, n: usize| -> usize {
            stream
                .draw_bounded(index, n as u64)
                .expect("draw index within the committed budget and n > 0") as usize
        };

        let theme = &THEMES[pick(0, THEMES.len())];
        let span = MAX_ROOMS - MIN_ROOMS + 1;
        let n = MIN_ROOMS + pick(1, span);

        // A short hex tag of the seed for a unique scene id.
        let sid: String = seed.as_bytes()[..4]
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();

        // The gated room is the second-to-last; the last room holds the hoard.
        let gate = n - 2;
        let last = n - 1;

        let desc = |i: usize| theme.descs[pick(2 + i as u32, theme.descs.len())];

        let mut out = String::new();
        out.push_str(&format!(
            "---\nid: procgen-{sid}\ntitle: {}\nweight: 1\n---\n\n",
            theme.title
        ));

        for i in 0..n {
            out.push_str(&format!("=== room{i}\n\n{}\n\n", desc(i)));
            if i == 0 {
                // Take the key, or leave it — both step forward, but only the key opens the gate.
                out.push_str(&format!(
                    "* [Take the {key} and press on]\n  ~ has_key = 1\n  -> room1\n\n",
                    key = theme.key_item
                ));
                out.push_str("* [Press on empty-handed]\n  -> room1\n\n");
            } else if i == gate {
                // The gated descent — a REAL executor `FieldGte(has_key, 1)` tooth once compiled.
                out.push_str(&format!(
                    "* [Descend into the depths] {{ has_key >= 1 }}\n  ~ depth += 1\n  -> room{last}\n\n"
                ));
                out.push_str(&format!(
                    "* [Retreat the way you came]\n  -> room{}\n\n",
                    gate - 1
                ));
            } else if i == last {
                // Seize the hoard — the win: gold += 500 and the scene ENDS.
                out.push_str(&format!(
                    "* [Seize the {win} and escape]\n  ~ gold += 500\n  -> END\n\n",
                    win = theme.win_item
                ));
            } else {
                // A linear connecting room.
                out.push_str(&format!("* [Press onward]\n  -> room{}\n\n", i + 1));
            }
        }
        (out, theme.title.to_string())
    }
}
