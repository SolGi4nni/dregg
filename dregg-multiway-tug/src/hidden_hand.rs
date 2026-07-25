//! # Phase 2 — the zk HIDDEN-HAND (the differentiated "nobody sees your hand,
//! nobody cheats" layer).
//!
//! Phase 0 hid the hand only by NON-REVEAL on a trusted host (the card counts are
//! public, the identities live in the [`crate::reference`] mover). Phase 2 makes the
//! hidden hand **cryptographic**:
//!
//! * **At DEAL, each player's private round inventory is COMMITTED as a Poseidon2 4-ary
//!   Merkle root** ([`HandTree`]) — opening hand plus deterministic later draws, ten distinct
//!   cards total. Each leaf is a blinded
//!   commitment `Poseidon2(DOMAIN, card, nonce, 0)`, so the root HIDES which cards are
//!   in the inventory (the per-card nonce blinds even the small card space) and BINDS the
//!   player to exactly that round multiset. The current six-or-fewer-card UI hand is a separate
//!   private commitment rebuilt from the reference engine; it never leaks the future draws.
//!
//! * **Each PLAY carries a [`StateConstraint::Witnessed`] `{ MerkleMembership }` proof**
//!   ([`PlayProof`]) — a Poseidon2 Merkle authentication path from the played card's
//!   leaf to the committed root. It is verified through the cell's REAL
//!   [`WitnessedPredicateRegistry`] by the REAL [`CellProgram::evaluate_full`] — the
//!   exact evaluator + the exact `registry.verify` the executor runs
//!   (`cell/src/program/eval.rs`, the `Witnessed` arm). A play whose card genuinely
//!   sits under the committed root VERIFIES while revealing NOTHING about the other
//!   cards; a play of a FABRICATED card (one not under the root, or a wrong opening)
//!   cannot produce a path to the root (Poseidon2 collision-resistance) and is
//!   REFUSED.
//!
//! * **The remaining-inventory root UPDATES** each play ([`HandTree::without`]): every exact
//!   card consumed by the 4/3/2/1-card action is removed and the private remainder is
//!   recommitted. Live membership is executor-enforced against the DEAL-pinned inventory root;
//!   duplicate consumption is presently an exact-card host ratchet mirrored by fresh replay.
//!   A protocol-native dynamic-root/nullifier constraint is a named residual — do not mistake
//!   the host ratchet for an executor-proven non-replay theorem.
//!
//! * **The Gift / Competition BLIND PICK + the concealed SECRET ride a commit→reveal**
//!   ([`BlindPick`]) — the identical construction the sealed-auction / tussle apps use
//!   (`seal = BLAKE3(domain || payload || nonce)`): the opponent COMMITS their pick
//!   (only the seal is public — the pick is unreadable from it), then REVEALS. A
//!   pre-reveal peek reads only the seal; a post-reveal SWAP (revealing a pick whose
//!   seal is not the committed one) is REFUSED.
//!
//! ## What is cryptographic NOW vs the named next phases
//!
//! The Merkle-committed hand, the membership-proven play, and the commit→reveal picks
//! run on the EXECUTOR: every membership proof is **executor-checked** — the real
//! [`WitnessedPredicateRegistry`] verifier, dispatched by the real cell evaluator, is
//! the acceptance gate (not a side check). [`HiddenHandLedger`] installs the Lean-authored
//! rules cell and the hidden-hand cell in one embedded executor; the Offering submits their
//! signed actions as one atomic turn, so either both land or neither does. On the hidden cell,
//! the executor's own `WriteOnce` / `StrictMonotonic` / `Monotonic` teeth bite the
//! committed hand root, the play generation, and the phase.
//!
//! NAMED NEXT (honest scope, `docs/VERIFIED-GAME-PORTFOLIO.md`): **Phase 3** — the
//! STARK fold, lowering this `Witnessed { MerkleMembership }` tooth into the
//! now-Lane-D-unblocked fold (the `MerkleAir` — `circuit/src/merkle_types.rs` — proves
//! the SAME 4-ary Poseidon2 path this module checks in the clear; a whole private
//! match → one succinct proof; the Witnessed lowering is the game-turn-slice residual
//! to wire). **Phase 4** the Lean refinement. The Offering surface and fresh-seed replay are
//! live; transport-specific private delivery remains a frontend responsibility.

use std::sync::Arc;

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, Effect, EmbeddedExecutor, TurnReceipt,
};
use dregg_cell::program::{TransitionMeta, WitnessBlobView, WitnessBundle, WitnessKindTag};
use dregg_cell::{
    Cell, CellProgram, CellState, InputRef, PredicateInput, StateConstraint, WitnessedPredicate,
    WitnessedPredicateError, WitnessedPredicateKind, WitnessedPredicateRegistry,
    WitnessedPredicateVerifier, field_from_u64,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::merkle_types::compute_parent_poseidon2;
use dregg_circuit::poseidon2::hash_4_to_1;
use dregg_schema::layout::{CheckedLayout, Slot, allocate_checked};
use dregg_schema::schema::Schema;
use dregg_schema::{genesis_oneshot_teeth, genesis_sentinel_freeze};
use dregg_turn::action::{Action, WitnessBlob, WitnessKind};
use spween_dregg::{CompiledStory, GENESIS_DONE_EXT_KEY, WorldError};

use crate::reference::{ActionKind, N_GUILDS, Player, Projection};
use crate::state::{Deployment as GameDeployment, SCENE_ID as GAME_SCENE_ID, SCORE as GAME_SCORE};

pub use crate::reference::deck_guild;

// ===========================================================================
// The deck: 21 distinct favor cards, each bound to a guild.
// ===========================================================================

/// The full deck size (== total influence == the conservation constant).
pub const DECK_SIZE: usize = 21;

// `deck_guild` is re-exported from the reference engine so the deal, strategy, surface, and
// Merkle vocabulary share one card-id → guild projection.

// ===========================================================================
// Poseidon2 field encoding — the leaf commitment + the root ↔ 32-byte forms.
// ===========================================================================

/// Domain tag separating real card leaves from padding (and from any other Poseidon2
/// hash-site). A fabricated "card" cannot masquerade as a pad leaf.
const DOMAIN_LEAF: u32 = 0x6d746c66; // "mtlf"
const DOMAIN_PAD: u32 = 0x70616421; // "pad!"
const DOMAIN_CARD: u32 = 0x63617264; // "card"
const DOMAIN_NONCE: u32 = 0x6e6f6e63; // "nonc"

/// Commit a full `u64` into one field element without first squeezing it into a single
/// BabyBear lane. Three 30/30/4-bit limbs are individually canonical, so changing any bit of
/// the opening changes the Poseidon2 preimage (up to the hash's collision-resistance).
fn u64_digest(domain: u32, value: u64) -> BabyBear {
    let limb0 = (value & ((1u64 << 30) - 1)) as u32;
    let limb1 = ((value >> 30) & ((1u64 << 30) - 1)) as u32;
    let limb2 = (value >> 60) as u32;
    hash_4_to_1(&[
        BabyBear::new_canonical(domain),
        BabyBear::new_canonical(limb0),
        BabyBear::new_canonical(limb1),
        BabyBear::new_canonical(limb2),
    ])
}

/// The blinded Merkle **leaf** committing to one dealt card:
/// `Poseidon2(DOMAIN_LEAF, digest64(card), digest64(nonce), 0)`. The two staged digests
/// faithfully carry all 64 bits rather than aliasing openings modulo the ~31-bit native field.
/// The per-card `nonce` blinds the small card space (identical guild-copies get distinct leaves;
/// the leaf hides `card`).
pub fn card_leaf(card_id: u64, nonce: u64) -> BabyBear {
    hash_4_to_1(&[
        BabyBear::new_canonical(DOMAIN_LEAF),
        u64_digest(DOMAIN_CARD, card_id),
        u64_digest(DOMAIN_NONCE, nonce),
        BabyBear::ZERO,
    ])
}

/// The padding leaf for the unused slots of a fixed-arity tree.
fn pad_leaf() -> BabyBear {
    hash_4_to_1(&[
        BabyBear::new_canonical(DOMAIN_PAD),
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
    ])
}

/// Encode a root felt as the 32-byte commitment the `Witnessed { MerkleMembership }`
/// predicate carries (canonical `u32` in the low four bytes, the rest zero — the same
/// felt-in-a-slot shape `turn::executor::membership_verifier::root_felt_from_slot`
/// reads).
pub fn root_to_bytes(root: BabyBear) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0..4].copy_from_slice(&root.as_u32().to_le_bytes());
    out
}

/// Decode a root felt from its 32-byte commitment form (the inverse of
/// [`root_to_bytes`]).
fn root_from_bytes(bytes: &[u8; 32]) -> Option<BabyBear> {
    if bytes[4..].iter().any(|&byte| byte != 0) {
        return None;
    }
    let mut b = [0u8; 4];
    b.copy_from_slice(&bytes[0..4]);
    let raw = u32::from_le_bytes(b);
    (raw < BABYBEAR_P).then(|| BabyBear::from_canonical(raw))
}

/// The `u64` register lane a root occupies inside the committed cell (its canonical
/// felt). The `WriteOnce` / free-write register teeth compare this scalar.
fn root_to_u64(root: BabyBear) -> u64 {
    root.as_u32() as u64
}

// ===========================================================================
// HandTree — a hand committed as a Poseidon2 4-ary Merkle root.
// ===========================================================================

/// The fixed 4-ary tree depth (`4^2 = 16` leaves) — enough for a full six-card hand and
/// every smaller remaining subset. A CONSTANT depth keeps the membership circuit a
/// single VK-distinct descriptor (the Phase-3 fold's `descriptor_by_name`), so a play
/// early in the round and a play late in the round prove against the same shape.
pub const HAND_TREE_DEPTH: usize = 2;

/// The leaf capacity of a [`HAND_TREE_DEPTH`] tree.
pub const HAND_TREE_LEAVES: usize = 16; // 4^2

/// One level of a Poseidon2 membership authentication path: the played node's position
/// among its four siblings, plus the three sibling node values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PathLevel {
    /// The node's position in its 4-group (`0..=3`).
    pub position: u8,
    /// The three sibling node values at this level.
    pub siblings: [BabyBear; 3],
}

/// A hand, COMMITTED as a Poseidon2 4-ary Merkle root. Holds the (card, nonce) openings
/// PRIVATELY; only [`HandTree::root`] is ever published. Recommitting after a play
/// ([`HandTree::without`]) is the remaining-hand update.
#[derive(Clone, Debug)]
pub struct HandTree {
    /// The dealt (card_id, nonce) pairs — SECRET, never leave the owner.
    cards: Vec<(u64, u64)>,
    /// The 4-ary tree layers, `layers[0]` = the padded leaves, `layers[depth][0]` = root.
    layers: Vec<Vec<BabyBear>>,
}

impl HandTree {
    /// Commit a hand from its dealt (card_id, nonce) openings.
    pub fn commit(cards: Vec<(u64, u64)>) -> Self {
        assert!(
            cards.len() <= HAND_TREE_LEAVES,
            "hand exceeds the {HAND_TREE_LEAVES}-leaf tree capacity"
        );
        let mut leaves: Vec<BabyBear> = cards.iter().map(|&(c, n)| card_leaf(c, n)).collect();
        let pad = pad_leaf();
        leaves.resize(HAND_TREE_LEAVES, pad);

        let mut layers = vec![leaves];
        for _ in 0..HAND_TREE_DEPTH {
            let prev = layers.last().unwrap();
            let mut next = Vec::with_capacity(prev.len() / 4);
            for group in prev.chunks(4) {
                let four = [group[0], group[1], group[2], group[3]];
                next.push(hash_4_to_1(&four));
            }
            layers.push(next);
        }
        HandTree { cards, layers }
    }

    /// The committed hand root.
    pub fn root(&self) -> BabyBear {
        self.layers[HAND_TREE_DEPTH][0]
    }

    /// The 32-byte commitment form of the root ([`root_to_bytes`]).
    pub fn root_bytes(&self) -> [u8; 32] {
        root_to_bytes(self.root())
    }

    /// The dealt card ids (for the OWNER's own bookkeeping — never published).
    pub fn card_ids(&self) -> Vec<u64> {
        self.cards.iter().map(|&(c, _)| c).collect()
    }

    /// The leaf index of a dealt `card_id`, if present.
    fn index_of(&self, card_id: u64) -> Option<usize> {
        self.cards.iter().position(|&(c, _)| c == card_id)
    }

    /// The (card_id, nonce) opening of a dealt card, if present.
    pub fn opening(&self, card_id: u64) -> Option<(u64, u64)> {
        self.index_of(card_id).map(|i| self.cards[i])
    }

    /// Build the Poseidon2 membership authentication path for the leaf at `leaf_index`.
    fn path_for_index(&self, leaf_index: usize) -> Vec<PathLevel> {
        let mut path = Vec::with_capacity(HAND_TREE_DEPTH);
        let mut idx = leaf_index;
        for level in 0..HAND_TREE_DEPTH {
            let position = (idx % 4) as u8;
            let group = idx / 4;
            let mut siblings = [BabyBear::ZERO; 3];
            let mut s = 0;
            for j in 0..4usize {
                if j != position as usize {
                    siblings[s] = self.layers[level][group * 4 + j];
                    s += 1;
                }
            }
            path.push(PathLevel { position, siblings });
            idx = group;
        }
        path
    }

    /// Produce the [`PlayProof`] for playing `card_id` out of this (remaining) hand:
    /// the opening + the membership path to THIS tree's root. `None` if the card is not
    /// under this root (already played, or never dealt).
    pub fn prove_play(&self, card_id: u64) -> Option<PlayProof> {
        let leaf_index = self.index_of(card_id)?;
        let (card, nonce) = self.cards[leaf_index];
        Some(PlayProof {
            card_id: card,
            nonce,
            path: self.path_for_index(leaf_index),
            root: self.root_bytes(),
        })
    }

    /// The remaining-hand tree after `card_id` is played (removed + recommitted). The
    /// played card's leaf is no longer under the new root, so a re-play against it fails
    /// membership.
    pub fn without(&self, card_id: u64) -> HandTree {
        let mut cards = self.cards.clone();
        if let Some(i) = cards.iter().position(|&(c, _)| c == card_id) {
            cards.remove(i);
        }
        HandTree::commit(cards)
    }
}

// ===========================================================================
// PlayProof — the wire form of a Witnessed { MerkleMembership } play.
// ===========================================================================

/// A provably-LEGAL play: the played card's opening + the Poseidon2 membership path to
/// the committed hand root. This is the ENTIRE public content of a play. It reveals the
/// played card (as Hanamikoji does — a Gift/Competition/board card lands face-up) and
/// NOTHING about the rest of the hand: the path carries only sibling *hashes*, from
/// which the other cards are unrecoverable.
#[derive(Clone, Debug)]
pub struct PlayProof {
    /// The played card id (revealed — a face-up play).
    pub card_id: u64,
    /// The played card's blinding nonce (revealed to open its leaf).
    pub nonce: u64,
    /// The Poseidon2 authentication path from the leaf to the committed root.
    pub path: Vec<PathLevel>,
    /// The committed hand root this play proves membership under (32-byte form).
    pub root: [u8; 32],
}

impl PlayProof {
    /// Serialize the leaf OPENING (card_id ‖ nonce) — the `Witnessed` predicate's
    /// `InputRef::Witness` blob.
    pub fn opening_bytes(&self) -> Vec<u8> {
        let mut b = Vec::with_capacity(16);
        b.extend_from_slice(&self.card_id.to_le_bytes());
        b.extend_from_slice(&self.nonce.to_le_bytes());
        b
    }

    /// Serialize the membership PATH — the `Witnessed` predicate's proof blob
    /// (`depth ‖ [position ‖ sib0 ‖ sib1 ‖ sib2]*`, each felt a canonical `u32`).
    pub fn path_bytes(&self) -> Vec<u8> {
        let mut b = Vec::with_capacity(1 + self.path.len() * 13);
        b.push(self.path.len() as u8);
        for lvl in &self.path {
            b.push(lvl.position);
            for sib in &lvl.siblings {
                b.extend_from_slice(&sib.as_u32().to_le_bytes());
            }
        }
        b
    }
}

/// Decode the opening blob (`card_id ‖ nonce`).
fn decode_opening(bytes: &[u8]) -> Option<(u64, u64)> {
    if bytes.len() != 16 {
        return None;
    }
    let card = u64::from_le_bytes(bytes[0..8].try_into().ok()?);
    let nonce = u64::from_le_bytes(bytes[8..16].try_into().ok()?);
    Some((card, nonce))
}

/// Decode the path blob into `(position, siblings)` levels.
fn decode_path(bytes: &[u8]) -> Option<Vec<PathLevel>> {
    let mut it = bytes.iter().copied();
    let depth = it.next()? as usize;
    let mut path = Vec::with_capacity(depth);
    for _ in 0..depth {
        let position = it.next()?;
        let mut siblings = [BabyBear::ZERO; 3];
        for sib in siblings.iter_mut() {
            let mut w = [0u8; 4];
            for byte in w.iter_mut() {
                *byte = it.next()?;
            }
            *sib = BabyBear::new_canonical(u32::from_le_bytes(w));
        }
        path.push(PathLevel { position, siblings });
    }
    if it.next().is_some() {
        return None; // trailing bytes — malformed
    }
    Some(path)
}

// ===========================================================================
// The MerkleMembership verifier — registered into the cell's real registry.
// ===========================================================================

/// A real `MerkleMembership` [`WitnessedPredicateVerifier`]: recomputes the played
/// card's Poseidon2 leaf from its opening and walks the 4-ary authentication path to the
/// committed root. Accepts iff the walk lands on the predicate's `commitment` root. This
/// is the cell-side, executor-checked form of the Phase-3 `MerkleAir` STARK
/// (`circuit/src/merkle_types.rs` proves the SAME `compute_parent_poseidon2` recurrence).
///
/// A fabricated card (a leaf not under the root) or a tampered path cannot land on the
/// committed root — Poseidon2 collision-resistance is the security. Registered on a
/// [`WitnessedPredicateRegistry`] as the `MerkleMembership` built-in, it IS the gate the
/// cell evaluator calls.
pub struct HandMembershipVerifier;

impl WitnessedPredicateVerifier for HandMembershipVerifier {
    fn name(&self) -> &'static str {
        "multiway-tug-hand-membership-poseidon2"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::MerkleMembership
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        // The played card's opening arrives as the resolved Witness input.
        let opening = match input {
            PredicateInput::Bytes(b) => *b,
            other => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: "MerkleMembership",
                    expected: "Witness bytes (card ‖ nonce)",
                    actual: predicate_input_tag(other),
                });
            }
        };
        let (card, nonce) =
            decode_opening(opening).ok_or_else(|| WitnessedPredicateError::Rejected {
                kind_name: "MerkleMembership",
                reason: "malformed leaf opening (expected card ‖ nonce, 16 bytes)".into(),
            })?;
        let path = decode_path(proof_bytes).ok_or_else(|| WitnessedPredicateError::Rejected {
            kind_name: "MerkleMembership",
            reason: "malformed membership path".into(),
        })?;

        // Recompute the leaf and walk the Poseidon2 path to the root.
        let mut current = card_leaf(card, nonce);
        for lvl in &path {
            if lvl.position > 3 {
                return Err(WitnessedPredicateError::Rejected {
                    kind_name: "MerkleMembership",
                    reason: format!("path position {} out of range 0..=3", lvl.position),
                });
            }
            current = compute_parent_poseidon2(current, lvl.position, &lvl.siblings);
        }
        let expected =
            root_from_bytes(commitment).ok_or_else(|| WitnessedPredicateError::Rejected {
                kind_name: "MerkleMembership",
                reason: "non-canonical hand-root commitment".into(),
            })?;
        if current == expected {
            Ok(())
        } else {
            Err(WitnessedPredicateError::Rejected {
                kind_name: "MerkleMembership",
                reason: "played card is not a member of the committed hand root \
                         (fabricated card / tampered path / wrong opening)"
                    .into(),
            })
        }
    }
}

fn predicate_input_tag(input: &PredicateInput<'_>) -> &'static str {
    match input {
        PredicateInput::Slot(_) => "Slot",
        PredicateInput::Bytes(_) => "Bytes",
        PredicateInput::PublicInput(_) => "PublicInput",
        PredicateInput::Sender(_) => "Sender",
        PredicateInput::SigningMessage(_) => "SigningMessage",
        PredicateInput::AuthContext { .. } => "AuthContext",
    }
}

/// A [`WitnessedPredicateRegistry`] with the hand-membership verifier installed as the
/// `MerkleMembership` built-in — the registry the cell evaluator dispatches through.
pub fn membership_registry() -> WitnessedPredicateRegistry {
    let mut r = WitnessedPredicateRegistry::empty();
    r.register_builtin(Arc::new(HandMembershipVerifier));
    r
}

/// The one-tooth [`CellProgram`] that gates a play on `Witnessed { MerkleMembership }`
/// against `root`: the leaf opening rides `witness_blobs[0]`, the path rides
/// `witness_blobs[1]`.
pub fn membership_program(root: &[u8; 32]) -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::Witnessed {
        wp: WitnessedPredicate::merkle_membership(*root, InputRef::Witness { index: 0 }, 1),
    }])
}

/// Whether a play is legal — the play's card is a member of the committed hand `root`.
///
/// This runs the play's `Witnessed { MerkleMembership }` tooth through the REAL
/// [`CellProgram::evaluate_full`] and the REAL [`WitnessedPredicateRegistry`] — the same
/// evaluator + the same `registry.verify` the executor runs on every touching turn
/// (`cell/src/program/eval.rs`, the `Witnessed` arm). `Ok(())` = a provably-legal play
/// revealing nothing but the played card; `Err(reason)` = REFUSED (a fabricated card, a
/// tampered path, or a card already played out of the remaining root).
pub fn check_play(proof: &PlayProof) -> Result<(), String> {
    let registry = membership_registry();
    let opening = proof.opening_bytes();
    let path = proof.path_bytes();
    let blobs = [
        WitnessBlobView {
            kind: WitnessKindTag::Cleartext,
            bytes: &opening,
        },
        WitnessBlobView {
            kind: WitnessKindTag::ProofBytes,
            bytes: &path,
        },
    ];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
        finalized_roots: None,
    };
    let program = membership_program(&proof.root);
    // The Witnessed arm reads only the witness blobs + the registry; the state pair is
    // a placeholder (no `InputRef::Slot`). This is the executor's own eval path.
    let state = CellState::new(0);
    program
        .evaluate_full(
            &state,
            Some(&state),
            None,
            &TransitionMeta::wildcard(),
            &bundle,
        )
        .map_err(|e| e.to_string())
}

// ===========================================================================
// BlindPick — the Gift/Competition/Secret commit → reveal (tussle/sealed-auction).
// ===========================================================================

/// The phase of a blind pick — `Commit → Reveal → Bound`, the sealed-auction/tussle
/// phase gate. A reveal before the commit phase closes, or after it binds, is refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PickPhase {
    /// Collecting the sealed pick (the opponent's choice is fog).
    Commit,
    /// The seal is locked; the reveal is accepted and must match.
    Reveal,
    /// The reveal bound; terminal.
    Bound,
}

/// Errors from the blind-pick / secret commit→reveal protocol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlindPickError {
    /// A commit was attempted outside the commit phase (no late seals).
    NotCommitPhase,
    /// A reveal was attempted before the commit phase closed.
    NotRevealPhase,
    /// The pick is already bound (terminal).
    AlreadyBound,
    /// The revealed pick's seal is not the committed one — a peek-then-switch, a swap
    /// after seeing the board (the binding tooth).
    SealMismatch,
}

impl std::fmt::Display for BlindPickError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotCommitPhase => {
                write!(f, "blind-pick commit attempted outside the commit phase")
            }
            Self::NotRevealPhase => {
                write!(f, "blind-pick reveal attempted before the commit closed")
            }
            Self::AlreadyBound => write!(f, "this blind pick is already bound"),
            Self::SealMismatch => write!(
                f,
                "revealed pick does not open the committed seal (a peek-then-switch / post-reveal swap)"
            ),
        }
    }
}

impl std::error::Error for BlindPickError {}

/// A blind Gift/Competition pick (or the concealed Secret) as a commit→reveal. The
/// `payload` is the opponent's choice (which cards they keep) — SECRET until reveal;
/// only [`BlindPick::seal`] is public during the commit phase. The identical
/// construction the sealed-auction (`Bid::seal`) and tussle (`MoveCommit::seal`) apps
/// use: `seal = BLAKE3(domain ‖ picker ‖ payload ‖ nonce)`, hiding the pick and binding
/// the picker to exactly one choice.
#[derive(Clone, Debug)]
pub struct BlindPick {
    /// Who makes the concealed choice (the opponent, for a Gift/Competition; the owner,
    /// for a Secret).
    pub picker: Player,
    /// The public seal — all an observer sees during the commit phase.
    seal: [u8; 32],
    /// The current phase.
    pub phase: PickPhase,
    /// The bound payload after a valid reveal (the choice, now on the table).
    revealed: Option<Vec<u8>>,
}

impl BlindPick {
    /// The seal of a `(picker, payload, nonce)` pick — `BLAKE3(domain ‖ …)`. Binding
    /// (opens to exactly its payload) and hiding (the nonce blinds the choice).
    pub fn compute_seal(picker: Player, payload: &[u8], nonce: u64) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dregg-multiway-tug blind-pick v1");
        h.update(&[picker.idx() as u8]);
        h.update(&(payload.len() as u64).to_le_bytes());
        h.update(payload);
        h.update(&nonce.to_le_bytes());
        *h.finalize().as_bytes()
    }

    /// Open a blind pick in the commit phase from a picker's sealed choice.
    pub fn commit(picker: Player, seal: [u8; 32]) -> Self {
        BlindPick {
            picker,
            seal,
            phase: PickPhase::Commit,
            revealed: None,
        }
    }

    /// The public seal (the fog datum — the pick is unreadable from it).
    pub fn seal(&self) -> [u8; 32] {
        self.seal
    }

    /// **The fog tooth** — is the pick readable from the public state? It is NOT: the
    /// only public datum before the reveal is the 32-byte seal, from which the payload
    /// is computationally unrecoverable. Returns the seal (all a peeker sees) while the
    /// pick is still concealed.
    pub fn peek(&self) -> Option<[u8; 32]> {
        match self.phase {
            PickPhase::Commit | PickPhase::Reveal => Some(self.seal),
            PickPhase::Bound => None,
        }
    }

    /// Close the commit phase (`Commit → Reveal`).
    pub fn close_commit(&mut self) -> Result<(), BlindPickError> {
        match self.phase {
            PickPhase::Commit => {
                self.phase = PickPhase::Reveal;
                Ok(())
            }
            _ => Err(BlindPickError::AlreadyBound),
        }
    }

    /// **Reveal** — open the pick. Accepted IFF (1) the pick is in the reveal phase and
    /// (2) the revealed `(payload, nonce)` opens the committed seal. A pre-reveal peek
    /// reads only the seal; a post-reveal SWAP (a payload whose seal ≠ the committed
    /// one) is [`BlindPickError::SealMismatch`].
    pub fn reveal(&mut self, payload: &[u8], nonce: u64) -> Result<(), BlindPickError> {
        match self.phase {
            PickPhase::Commit => return Err(BlindPickError::NotRevealPhase),
            PickPhase::Bound => return Err(BlindPickError::AlreadyBound),
            PickPhase::Reveal => {}
        }
        let seal = BlindPick::compute_seal(self.picker, payload, nonce);
        if seal != self.seal {
            return Err(BlindPickError::SealMismatch);
        }
        self.revealed = Some(payload.to_vec());
        self.phase = PickPhase::Bound;
        Ok(())
    }

    /// The bound payload after a valid reveal.
    pub fn bound_payload(&self) -> Option<&[u8]> {
        self.revealed.as_deref()
    }
}

// ===========================================================================
// HiddenHandLedger — atomic rules + witnessed hidden state on one real executor.
// ===========================================================================
//
// The crypto above is the acceptance gate. The hidden cell and the Lean-authored game
// cell share one embedded executor, so an Offering play is an atomic multi-action receipt.
// The committed hand root, play generation, and phase are guarded by the executor's own
// teeth: `WriteOnce` freezes the
// committed hand root + each committed pick seal (a hand-swap / a post-reveal seal-swap
// is a real refusal), `StrictMonotonic` advances the play generation, `Monotonic` keeps
// the phase from rewinding. Each deal / play / pick is one cap-bounded turn the
// executor admits IFF the teeth pass.

/// The scene id fixing the deterministic hidden-hand cell identity.
pub const LEDGER_SCENE_ID: &str = "dregg-multiway-tug/phase2-hidden-hand";
/// The permissive seeding method (the deal).
pub const GENESIS: &str = "genesis";
/// The play method (a card played out of the remaining hand).
pub const PLAY: &str = "play";
/// The blind-pick commit method.
pub const COMMIT_PICK: &str = "commit_pick";
/// The blind-pick reveal method.
pub const REVEAL_PICK: &str = "reveal_pick";
/// The terminal ledger transition paired atomically with the game's scoring action.
pub const SCORE: &str = "score";

/// Phase codes written into the `phase` register (strictly ordered so `Monotonic`
/// keeps the round from rewinding).
pub const PHASE_DEAL: u64 = 1;
pub const PHASE_PLAY: u64 = 2;
pub const PHASE_PICK: u64 = 3;
pub const PHASE_SCORE: u64 = 4;

const LEDGER_FEDERATION: [u8; 32] = [0xD6; 32];

fn witnessed_play_method(player: Player, count: usize) -> String {
    format!(
        "{PLAY}:{}:{count}",
        if player == Player::A { "a" } else { "b" }
    )
}

/// The twelve register components, in allocation order.
const LEDGER_REGISTERS: [&str; 12] = [
    "a_hand_root",
    "b_hand_root",
    "a_rem_root",
    "b_rem_root",
    "phase",
    "gen",
    "a_pick_seal",
    "b_pick_seal",
    "a_secret_seal",
    "b_secret_seal",
    "a_played",
    "b_played",
];

/// The full committed register state (rewritten in whole each turn, one field mutated).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LedgerState {
    pub a_hand_root: u64,
    pub b_hand_root: u64,
    pub a_rem_root: u64,
    pub b_rem_root: u64,
    pub phase: u64,
    pub generation: u64,
    pub a_pick_seal: u64,
    pub b_pick_seal: u64,
    pub a_secret_seal: u64,
    pub b_secret_seal: u64,
    pub a_played: u64,
    pub b_played: u64,
}

/// The low 8 bytes of a 32-byte seal, as the `u64` register lane the `WriteOnce` tooth
/// freezes.
pub fn seal_to_u64(seal: &[u8; 32]) -> u64 {
    u64::from_le_bytes(seal[0..8].try_into().unwrap())
}

/// The declared schema + the Legal-checked layout + the phase-machine teeth.
pub struct LedgerDeployment {
    pub layout: CheckedLayout,
}

impl LedgerDeployment {
    /// Allocate + Legal-check the hidden-hand schema.
    pub fn new() -> Self {
        // Built in the same order as LEDGER_REGISTERS so the slots resolve cleanly.
        let s = Schema::new(LEDGER_SCENE_ID)
            .identity("a_hand_root")
            .identity("b_hand_root")
            .identity("a_rem_root")
            .identity("b_rem_root")
            .stat("phase", 0, 8)
            .stat("gen", 0, 255)
            .identity("a_pick_seal")
            .identity("b_pick_seal")
            .identity("a_secret_seal")
            .identity("b_secret_seal")
            .stat("a_played", 0, 8)
            .stat("b_played", 0, 8);
        let layout = allocate_checked(&s).expect("hidden-hand layout is Legal");
        LedgerDeployment { layout }
    }

    /// Resolve a register component to its slot index.
    pub fn reg(&self, name: &str) -> u8 {
        match self.layout.resolve(name) {
            Some(Slot::Register(r)) => r,
            other => panic!("`{name}` is not a register: {other:?}"),
        }
    }

    /// The teeth shared by every non-genesis method: the committed hand roots + each
    /// committed pick seal are `WriteOnce` (a swap is refused) and the phase is
    /// `Monotonic` (no rewind).
    fn common_teeth(&self) -> Vec<StateConstraint> {
        let mut teeth = Vec::new();
        for name in [
            "a_hand_root",
            "b_hand_root",
            "a_pick_seal",
            "b_pick_seal",
            "a_secret_seal",
            "b_secret_seal",
        ] {
            teeth.push(StateConstraint::WriteOnce {
                index: self.reg(name),
            });
        }
        teeth.push(StateConstraint::Monotonic {
            index: self.reg("phase"),
        });
        // GENESIS ONE-SHOT (write-hatch close): freeze the genesis-done sentinel on every
        // non-genesis case — `Immutable` admits the unchanged key, refuses any reset.
        teeth.push(genesis_sentinel_freeze());
        teeth
    }

    /// The phase-machine program.
    pub fn program(&self) -> CellProgram {
        use dregg_app_framework::{TransitionCase, TransitionGuard, symbol};
        let gen_slot = self.reg("gen");
        let action_case = |dep: &LedgerDeployment, method: &str| {
            let mut constraints = dep.common_teeth();
            constraints.push(StateConstraint::StrictMonotonic { index: gen_slot });
            // Non-play methods cannot smuggle a private-inventory consumption alongside a pick
            // or score transition. Witnessed play cases below replace this base PLAY case.
            for name in ["a_rem_root", "b_rem_root", "a_played", "b_played"] {
                constraints.push(StateConstraint::Immutable {
                    index: dep.reg(name),
                });
            }
            TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol(method),
                },
                constraints,
            }
        };
        let cases = vec![
            // GENESIS ONE-SHOT: the `0 → 1` write on `GENESIS_DONE_EXT_KEY` — admissible exactly
            // once at deploy, jointly UNSAT for every post-deploy genesis staple. No longer the
            // permissive `constraints: vec![]` write-hatch.
            TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol(GENESIS),
                },
                constraints: genesis_oneshot_teeth(),
            },
            action_case(self, COMMIT_PICK),
            action_case(self, REVEAL_PICK),
            action_case(self, SCORE),
        ];
        CellProgram::Cases(cases)
    }

    /// The phase-machine program after DEAL pins each player's private full-round inventory root.
    /// A witnessed play method carries exactly `count` opening/path pairs; every pair is an
    /// executor-dispatched `MerkleMembership` predicate against that player's committed root.
    fn program_with_inventory_roots(&self, roots: [[u8; 32]; 2]) -> CellProgram {
        use dregg_app_framework::{TransitionCase, TransitionGuard, symbol};

        let mut cases = match self.program() {
            CellProgram::Cases(cases) => cases,
            _ => unreachable!("ledger program is case-dispatched"),
        };
        // Remove the legacy proof-free PLAY case. `PLAY` itself becomes default-deny; only an
        // arity- and player-specific method carrying every required proof can land.
        cases.retain(|case| {
            !matches!(
                &case.guard,
                TransitionGuard::MethodIs { method } if *method == symbol(PLAY)
            )
        });

        for player in [Player::A, Player::B] {
            for count in 1..=4usize {
                let mut constraints = self.common_teeth();
                constraints.push(StateConstraint::StrictMonotonic {
                    index: self.reg("gen"),
                });
                // The committed per-seat played count must advance by the exact action arity.
                constraints.push(StateConstraint::FieldDelta {
                    index: self.reg(if player == Player::A {
                        "a_played"
                    } else {
                        "b_played"
                    }),
                    delta: field_from_u64(count as u64),
                });
                constraints.push(StateConstraint::Immutable {
                    index: self.reg(if player == Player::A {
                        "b_played"
                    } else {
                        "a_played"
                    }),
                });
                constraints.push(StateConstraint::Immutable {
                    index: self.reg(if player == Player::A {
                        "b_rem_root"
                    } else {
                        "a_rem_root"
                    }),
                });
                for proof_index in 0..count {
                    constraints.push(StateConstraint::Witnessed {
                        wp: WitnessedPredicate::merkle_membership(
                            roots[player.idx()],
                            InputRef::Witness {
                                index: proof_index * 2,
                            },
                            proof_index * 2 + 1,
                        ),
                    });
                }
                cases.push(TransitionCase {
                    guard: TransitionGuard::MethodIs {
                        method: symbol(&witnessed_play_method(player, count)),
                    },
                    constraints,
                });
            }
        }
        CellProgram::Cases(cases)
    }

    /// The compiled story to install on the world-cell.
    pub fn story(&self) -> CompiledStory {
        let mut var_slots = std::collections::BTreeMap::new();
        for name in LEDGER_REGISTERS {
            var_slots.insert(name.to_string(), self.reg(name) as u64);
        }
        CompiledStory {
            scene_id: LEDGER_SCENE_ID.to_string(),
            var_slots,
            has_slots: std::collections::BTreeMap::new(),
            passage_index: std::collections::BTreeMap::new(),
            program: self.program(),
            fully_gated: std::collections::BTreeMap::new(),
        }
    }
}

impl Default for LedgerDeployment {
    fn default() -> Self {
        Self::new()
    }
}

/// A deployed hidden-hand ledger on a real world-cell: the committed roots + the phase
/// machine, each move a cap-bounded turn the executor admits IFF the teeth pass.
pub struct HiddenHandLedger {
    dep: LedgerDeployment,
    game_dep: GameDeployment,
    exec: EmbeddedExecutor,
    cclerk: AppCipherclerk,
    cell: CellId,
    game_cell: CellId,
    state: LedgerState,
    inventory_roots: Option<[[u8; 32]; 2]>,
    played_cards: [std::collections::BTreeSet<u64>; 2],
}

struct PreparedPlay {
    state: LedgerState,
    method: String,
    witnesses: Vec<WitnessBlob>,
}

impl HiddenHandLedger {
    /// Deploy the hidden-hand story on a real world-cell.
    pub fn deploy(seed: u8) -> Result<Self, WorldError> {
        let dep = LedgerDeployment::new();
        let game_dep = GameDeployment::new();
        let mut seed_material = [0u8; 64];
        let mut h = blake3::Hasher::new_derive_key("dregg-multiway-tug hidden-ledger owner v2");
        h.update(LEDGER_SCENE_ID.as_bytes());
        h.update(&[seed]);
        seed_material[..32].copy_from_slice(h.finalize().as_bytes());
        let second = blake3::hash(&seed_material[..32]);
        seed_material[32..].copy_from_slice(second.as_bytes());
        let cclerk = AppCipherclerk::new(
            AgentCipherclerk::from_seed(seed_material),
            LEDGER_FEDERATION,
        );
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        exec.set_witnessed_registry(membership_registry());

        let owner = cclerk.public_key().0;
        let token = *blake3::hash(LEDGER_SCENE_ID.as_bytes()).as_bytes();
        let cell = CellId::derive_raw(&owner, &token);
        exec.ensure_cell(Cell::new(owner, token))
            .map_err(WorldError::Refused)?;
        let game_token = *blake3::hash(GAME_SCENE_ID.as_bytes()).as_bytes();
        let game_cell = CellId::derive_raw(&owner, &game_token);
        exec.ensure_cell(Cell::new(owner, game_token))
            .map_err(WorldError::Refused)?;
        let agent = cclerk.cell_id();
        exec.with_ledger_mut(|ledger| {
            if let Some(agent_cell) = ledger.get_mut(&agent) {
                agent_cell.capabilities.grant(cell, AuthRequired::Signature);
                agent_cell
                    .capabilities
                    .grant(game_cell, AuthRequired::Signature);
            }
            // Direct executor deployment has no WorldCell wrapper to birth the one-shot
            // genesis sentinel. Both installed programs fail closed on an absent heap key, so
            // birth it explicitly at zero; the first genesis action atomically writes it 0 → 1.
            for target in [cell, game_cell] {
                if let Some(target_cell) = ledger.get_mut(&target) {
                    target_cell
                        .state
                        .set_field_ext(GENESIS_DONE_EXT_KEY, field_from_u64(0));
                }
            }
        });
        exec.install_program(cell, dep.program());
        exec.install_program(game_cell, game_dep.program());
        Ok(HiddenHandLedger {
            dep,
            game_dep,
            exec,
            cclerk,
            cell,
            game_cell,
            state: LedgerState::default(),
            inventory_roots: None,
            played_cards: [
                std::collections::BTreeSet::new(),
                std::collections::BTreeSet::new(),
            ],
        })
    }

    fn cell(&self) -> CellId {
        self.cell
    }

    fn effects(&self, s: &LedgerState) -> Vec<Effect> {
        let cell = self.cell();
        let mut effects = Vec::with_capacity(LEDGER_REGISTERS.len());
        let mut set = |name: &str, v: u64| {
            effects.push(Effect::SetField {
                cell,
                index: self.dep.reg(name) as u64,
                value: field_from_u64(v),
            });
        };
        set("a_hand_root", s.a_hand_root);
        set("b_hand_root", s.b_hand_root);
        set("a_rem_root", s.a_rem_root);
        set("b_rem_root", s.b_rem_root);
        set("phase", s.phase);
        set("gen", s.generation);
        set("a_pick_seal", s.a_pick_seal);
        set("b_pick_seal", s.b_pick_seal);
        set("a_secret_seal", s.a_secret_seal);
        set("b_secret_seal", s.b_secret_seal);
        set("a_played", s.a_played);
        set("b_played", s.b_played);
        effects
    }

    /// Every effect that writes the Lean-authored Tug projection in full. This is the same
    /// projection shape [`crate::game::MultiwayTug`] writes; it lives here as well so the game
    /// action and its hidden-hand admission action can share one executor and one atomic turn.
    fn game_effects(&self, proj: &Projection) -> Vec<Effect> {
        let cell = self.game_cell;
        let mut effects = Vec::with_capacity(16 + 8 + 2 * N_GUILDS);
        let mut set = |name: &str, value: u64| {
            effects.push(Effect::SetField {
                cell,
                index: self.game_dep.reg(name) as u64,
                value: field_from_u64(value),
            });
        };
        set("deck", proj.deck);
        set("oop", proj.oop);
        set("a_hand", proj.hand[0]);
        set("b_hand", proj.hand[1]);
        set("a_secret", proj.secret_count[0]);
        set("b_secret", proj.secret_count[1]);
        set("a_board", proj.board[0]);
        set("b_board", proj.board[1]);
        set("a_charm", proj.charm[0]);
        set("b_charm", proj.charm[1]);
        set("a_guilds", proj.guilds_controlled[0]);
        set("b_guilds", proj.guilds_controlled[1]);
        set("winner", proj.winner);
        set("current", proj.current);
        set("round_actions", proj.round_actions);
        set("scored", proj.scored);
        drop(set);
        for player in [Player::A, Player::B] {
            for action in [
                ActionKind::Secret,
                ActionKind::Discard,
                ActionKind::Gift,
                ActionKind::Competition,
            ] {
                effects.push(Effect::SetField {
                    cell,
                    index: self.game_dep.flag_key(player, action) as u64,
                    value: field_from_u64(proj.flag[player.idx()][action.idx()]),
                });
            }
        }
        for guild in 0..N_GUILDS {
            for player in [Player::A, Player::B] {
                effects.push(Effect::SetField {
                    cell,
                    index: self.game_dep.score_key(guild, player) as u64,
                    value: field_from_u64(proj.score[guild][player.idx()]),
                });
            }
        }
        // The offer on the table (0 none, 1 gift, 2 competition).
        effects.push(Effect::SetField {
            cell,
            index: self.game_dep.pending_kind_key(),
            value: field_from_u64(proj.pending_kind),
        });
        effects
    }

    fn genesis_effects(&self, target: CellId, mut effects: Vec<Effect>) -> Vec<Effect> {
        effects.push(Effect::SetField {
            cell: target,
            index: GENESIS_DONE_EXT_KEY as u64,
            value: field_from_u64(1),
        });
        effects
    }

    fn deal_state(a_root: BabyBear, b_root: BabyBear) -> LedgerState {
        let ar = root_to_u64(a_root);
        let br = root_to_u64(b_root);
        LedgerState {
            a_hand_root: ar,
            b_hand_root: br,
            a_rem_root: ar,
            b_rem_root: br,
            phase: PHASE_DEAL,
            ..LedgerState::default()
        }
    }

    fn finish_deal(&mut self, state: LedgerState, roots: [[u8; 32]; 2]) {
        self.state = state;
        self.inventory_roots = Some(roots);
        self.exec
            .install_program(self.cell, self.dep.program_with_inventory_roots(roots));
    }

    /// **The deal** — commit both players' hand roots under genesis (also seeding the
    /// remaining roots = the hand roots, `phase = DEAL`, `gen = 0`).
    pub fn deal(&mut self, a_root: BabyBear, b_root: BabyBear) -> Result<TurnReceipt, WorldError> {
        let s = Self::deal_state(a_root, b_root);
        let effects = self.genesis_effects(self.cell, self.effects(&s));
        let receipt = self.commit(GENESIS, effects, Vec::new())?;
        let roots = [root_to_bytes(a_root), root_to_bytes(b_root)];
        self.finish_deal(s, roots);
        Ok(receipt)
    }

    /// Seed the Lean-authored game cell and DEAL-pin both private inventory roots in one atomic
    /// genesis turn. Either both cells commit or neither does.
    pub fn start_round(
        &mut self,
        projection: &Projection,
        a_root: BabyBear,
        b_root: BabyBear,
    ) -> Result<TurnReceipt, WorldError> {
        let state = Self::deal_state(a_root, b_root);
        let game = self.action(
            self.game_cell,
            GENESIS,
            self.genesis_effects(self.game_cell, self.game_effects(projection)),
            Vec::new(),
        );
        let hidden = self.action(
            self.cell,
            GENESIS,
            self.genesis_effects(self.cell, self.effects(&state)),
            Vec::new(),
        );
        let receipt = self.commit_actions(vec![game, hidden])?;
        self.finish_deal(state, [root_to_bytes(a_root), root_to_bytes(b_root)]);
        Ok(receipt)
    }

    /// **A witnessed play admission** — every card consumed by one Tug action must carry its
    /// opening + Poseidon authentication path. The signed action carries those witness blobs and
    /// the executor dispatches every `MerkleMembership` tooth against the player's DEAL-pinned
    /// private inventory root before the remaining root/count/generation can commit.
    ///
    /// The host-side exact-card and duplicate checks are defense in depth around the executor
    /// witness gate: they bind the proofs to the reference move and keep a static inventory proof
    /// from being replayed. The latter is not yet a circuit/nullifier tooth (see module scope).
    pub fn play(
        &mut self,
        player: Player,
        proofs: &[PlayProof],
        new_remaining_root: BabyBear,
    ) -> Result<TurnReceipt, WorldError> {
        let prepared = self.prepare_play(player, proofs, new_remaining_root)?;
        let receipt = self.commit(
            &prepared.method,
            self.effects(&prepared.state),
            prepared.witnesses,
        )?;
        self.finish_play(player, proofs, prepared.state);
        Ok(receipt)
    }

    /// Commit one Tug projection and all exact-card membership admissions in one atomic turn.
    /// The action targeting the game cell is checked by the Lean-authored rule program; the
    /// action targeting the hidden cell is checked by the witnessed Merkle predicates. A
    /// refusal in either action rolls the whole turn back.
    pub(crate) fn play_projection(
        &mut self,
        player: Player,
        expected_cards: &[u64],
        proofs: &[PlayProof],
        new_remaining_root: BabyBear,
        action: ActionKind,
        projection: &Projection,
    ) -> Result<TurnReceipt, WorldError> {
        if expected_cards.len() != action.card_count() {
            return Err(WorldError::Refused(format!(
                "action `{}` consumes exactly {} cards, got {}",
                action.method(),
                action.card_count(),
                expected_cards.len()
            )));
        }
        let proved_cards: Vec<u64> = proofs.iter().map(|proof| proof.card_id).collect();
        if proved_cards != expected_cards {
            return Err(WorldError::Refused(format!(
                "membership openings do not match the exact cards consumed by `{}`",
                action.method()
            )));
        }
        let prepared = self.prepare_play(player, proofs, new_remaining_root)?;
        let game = self.action(
            self.game_cell,
            action.method(),
            self.game_effects(projection),
            Vec::new(),
        );
        let hidden = self.action(
            self.cell,
            &prepared.method,
            self.effects(&prepared.state),
            prepared.witnesses,
        );
        let receipt = self.commit_actions(vec![game, hidden])?;
        self.finish_play(player, proofs, prepared.state);
        Ok(receipt)
    }

    /// **A RESPONSE turn** — the other seat's answer to a pending offer. It consumes NO card
    /// from any hand (the escrow was funded when the offer was cut), so there is no
    /// membership witness to carry and no hidden-cell action: the whole move is the rules
    /// cell's projection under `method` (`respond_gift` / `respond_comp`), whose Lean-emitted
    /// case is also the only one permitted to lower the `pending_kind` escrow marker.
    pub(crate) fn respond_projection(
        &mut self,
        method: &str,
        projection: &Projection,
    ) -> Result<TurnReceipt, WorldError> {
        let game = self.action(
            self.game_cell,
            method,
            self.game_effects(projection),
            Vec::new(),
        );
        self.commit_actions(vec![game])
    }

    fn prepare_play(
        &self,
        player: Player,
        proofs: &[PlayProof],
        new_remaining_root: BabyBear,
    ) -> Result<PreparedPlay, WorldError> {
        if proofs.is_empty() || proofs.len() > 4 {
            return Err(WorldError::Refused(format!(
                "a Tug action must carry 1..=4 card membership proofs, got {}",
                proofs.len()
            )));
        }
        let roots = self.inventory_roots.ok_or_else(|| {
            WorldError::Refused("hidden-hand play before the committed deal".to_string())
        })?;
        let expected_root = roots[player.idx()];
        let mut newly_played = std::collections::BTreeSet::new();
        for proof in proofs {
            if proof.root != expected_root {
                return Err(WorldError::Refused(
                    "membership proof is bound to the wrong private inventory root".to_string(),
                ));
            }
            if self.played_cards[player.idx()].contains(&proof.card_id)
                || !newly_played.insert(proof.card_id)
            {
                return Err(WorldError::Refused(format!(
                    "card {} was already consumed from this private inventory",
                    proof.card_id
                )));
            }
        }

        let mut s = self.state;
        let r = root_to_u64(new_remaining_root);
        match player {
            Player::A => {
                s.a_rem_root = r;
                s.a_played += proofs.len() as u64;
            }
            Player::B => {
                s.b_rem_root = r;
                s.b_played += proofs.len() as u64;
            }
        }
        s.generation += 1;
        s.phase = s.phase.max(PHASE_PLAY);
        let mut witnesses = Vec::with_capacity(proofs.len() * 2);
        for proof in proofs {
            witnesses.push(WitnessBlob::new(
                WitnessKind::Cleartext,
                proof.opening_bytes(),
            ));
            witnesses.push(WitnessBlob::new(
                WitnessKind::ProofBytes,
                proof.path_bytes(),
            ));
        }
        Ok(PreparedPlay {
            state: s,
            method: witnessed_play_method(player, proofs.len()),
            witnesses,
        })
    }

    fn finish_play(&mut self, player: Player, proofs: &[PlayProof], state: LedgerState) {
        self.state = state;
        self.played_cards[player.idx()].extend(proofs.iter().map(|proof| proof.card_id));
    }

    /// **Commit a blind pick / secret seal** — write `player`'s seal once (a later commit
    /// onto an already-set seal is refused by `WriteOnce`), advancing the generation +
    /// the phase to PICK.
    pub fn commit_pick(
        &mut self,
        player: Player,
        seal: &[u8; 32],
        secret: bool,
    ) -> Result<TurnReceipt, WorldError> {
        let mut s = self.state;
        let v = seal_to_u64(seal);
        match (player, secret) {
            (Player::A, false) => s.a_pick_seal = v,
            (Player::B, false) => s.b_pick_seal = v,
            (Player::A, true) => s.a_secret_seal = v,
            (Player::B, true) => s.b_secret_seal = v,
        }
        s.generation += 1;
        s.phase = s.phase.max(PHASE_PICK);
        let receipt = self.commit(COMMIT_PICK, self.effects(&s), Vec::new())?;
        self.state = s;
        Ok(receipt)
    }

    /// **Reveal a blind pick** — advance the generation (the reveal's seal binding is the
    /// app-seam [`BlindPick::reveal`] tooth; the committed seal stays frozen). Returns
    /// the executor receipt for the reveal turn.
    pub fn reveal_pick(&mut self, _player: Player) -> Result<TurnReceipt, WorldError> {
        let mut s = self.state;
        s.generation += 1;
        let receipt = self.commit(REVEAL_PICK, self.effects(&s), Vec::new())?;
        self.state = s;
        Ok(receipt)
    }

    /// Score the Lean-authored game cell and close the hidden ledger in one atomic turn.
    pub fn score_projection(&mut self, projection: &Projection) -> Result<TurnReceipt, WorldError> {
        let mut state = self.state;
        state.generation += 1;
        state.phase = PHASE_SCORE;
        let game = self.action(
            self.game_cell,
            GAME_SCORE,
            self.game_effects(projection),
            Vec::new(),
        );
        let hidden = self.action(self.cell, SCORE, self.effects(&state), Vec::new());
        let receipt = self.commit_actions(vec![game, hidden])?;
        self.state = state;
        Ok(receipt)
    }

    /// Drive a RAW turn under `method` from an explicit next state — the refusal-test
    /// builder (a hand-root swap, a phase rewind, a stale generation).
    pub fn commit_raw(&self, method: &str, next: &LedgerState) -> Result<TurnReceipt, WorldError> {
        self.commit(method, self.effects(next), Vec::new())
    }

    /// Executor-refusal test seam: submit an explicit witnessed-play post-state without running
    /// the host preflight/mirror update. Production callers use [`Self::play`] or
    /// [`Self::play_projection`].
    #[cfg(test)]
    fn commit_raw_play(
        &self,
        player: Player,
        proofs: &[PlayProof],
        next: &LedgerState,
    ) -> Result<TurnReceipt, WorldError> {
        let witnesses = proofs
            .iter()
            .flat_map(|proof| {
                [
                    WitnessBlob::new(WitnessKind::Cleartext, proof.opening_bytes()),
                    WitnessBlob::new(WitnessKind::ProofBytes, proof.path_bytes()),
                ]
            })
            .collect();
        self.commit(
            &witnessed_play_method(player, proofs.len()),
            self.effects(next),
            witnesses,
        )
    }

    /// The current mirrored register state.
    pub fn state(&self) -> LedgerState {
        self.state
    }

    /// Reconstruct the projection committed by the Lean-authored Tug rules cell sharing this
    /// executor. This is the Offering's public state, not a mirror maintained by the host.
    pub fn read_projection(&self) -> Projection {
        let mut score = [[0u64; 2]; N_GUILDS];
        for (guild, row) in score.iter_mut().enumerate() {
            for player in [Player::A, Player::B] {
                row[player.idx()] = self.read_game_heap(self.game_dep.score_key(guild, player));
            }
        }
        let mut flag = [[0u64; 4]; 2];
        for player in [Player::A, Player::B] {
            for action in [
                ActionKind::Secret,
                ActionKind::Discard,
                ActionKind::Gift,
                ActionKind::Competition,
            ] {
                flag[player.idx()][action.idx()] =
                    self.read_game_heap(self.game_dep.flag_key(player, action));
            }
        }
        Projection {
            deck: self.read_game_reg("deck"),
            oop: self.read_game_reg("oop"),
            hand: [self.read_game_reg("a_hand"), self.read_game_reg("b_hand")],
            secret_count: [
                self.read_game_reg("a_secret"),
                self.read_game_reg("b_secret"),
            ],
            board: [self.read_game_reg("a_board"), self.read_game_reg("b_board")],
            charm: [self.read_game_reg("a_charm"), self.read_game_reg("b_charm")],
            guilds_controlled: [
                self.read_game_reg("a_guilds"),
                self.read_game_reg("b_guilds"),
            ],
            winner: self.read_game_reg("winner"),
            current: self.read_game_reg("current"),
            round_actions: self.read_game_reg("round_actions"),
            scored: self.read_game_reg("scored"),
            pending_kind: self.read_game_heap(self.game_dep.pending_kind_key()),
            score,
            flag,
        }
    }

    /// Read a committed register off the cell.
    pub fn read(&self, name: &str) -> u64 {
        self.exec
            .cell_state(self.cell)
            .map(|state| {
                let bytes = state.fields[self.dep.reg(name) as usize];
                u64::from_be_bytes(bytes[24..32].try_into().expect("8-byte field lane"))
            })
            .unwrap_or(0)
    }

    fn read_game_reg(&self, name: &str) -> u64 {
        self.exec
            .cell_state(self.game_cell)
            .map(|state| field_lane(&state.fields[self.game_dep.reg(name) as usize]))
            .unwrap_or(0)
    }

    fn read_game_heap(&self, key: u64) -> u64 {
        self.exec
            .cell_state(self.game_cell)
            .and_then(|state| state.get_field_ext(key))
            .map(|field| field_lane(&field))
            .unwrap_or(0)
    }

    fn action(
        &self,
        target: CellId,
        method: &str,
        effects: Vec<Effect>,
        witness_blobs: Vec<WitnessBlob>,
    ) -> Action {
        let mut action = self.cclerk.make_action(target, method, effects);
        action.witness_blobs = witness_blobs;
        self.cclerk.sign_action(action)
    }

    fn commit_actions(&self, actions: Vec<Action>) -> Result<TurnReceipt, WorldError> {
        let turn = self.cclerk.make_turn_with_actions(actions);
        self.exec
            .submit_turn(&turn)
            .map_err(|error| WorldError::Refused(error.to_string()))
    }

    fn commit(
        &self,
        method: &str,
        effects: Vec<Effect>,
        witness_blobs: Vec<WitnessBlob>,
    ) -> Result<TurnReceipt, WorldError> {
        self.commit_actions(vec![self.action(self.cell, method, effects, witness_blobs)])
    }
}

fn field_lane(field: &[u8; 32]) -> u64 {
    u64::from_be_bytes(field[24..32].try_into().expect("8-byte field lane"))
}

#[cfg(test)]
mod tests;
