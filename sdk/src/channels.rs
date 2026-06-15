//! # Channels — the group-key lift as an SDK noun (docs/ORGANS.md §4,
//! W-organ-3's keystone; blueprint twin `dregg_cell::blueprint` channel
//! section).
//!
//! A group is a CELL: the membership commitment, the key-epoch counter, and
//! the epoch key commitment live on-cell; joins / removals / rekeys are
//! ordinary turns under the group's installed program, riding the owner
//! runtime's normal `.turn()` path exactly like [`crate::trustline`].
//! Message bodies NEVER touch the chain — control plane on-cell, data plane
//! ciphertext over any transport (mailboxes, SSE, captp store-and-forward).
//!
//! ## THE KEYSTONE — epoch unification, both counters in ONE turn
//!
//! The group's key epoch and the capability freshness epoch are THE SAME
//! counter. Every epoch-stepping turn built here ([`Channel::join`] /
//! [`Channel::remove`] / [`Channel::rekey`]) is ONE atomic turn carrying:
//!
//! 1. `SetField member_root` — the new openable membership commitment;
//! 2. `SetField epoch` — the counter steps by exactly one (the program's
//!    unification triple makes a membership change without this UNSAT);
//! 3. `SetField key_commit` — the FRESH epoch key's commitment (an epoch
//!    step keeping the old key is UNSAT);
//! 4. `RevokeDelegation { child: epoch_anchor }` — the one kernel verb that
//!    bumps the group cell's `delegation_epoch`, so the executor's R7
//!    epoch-at-retrieval check (`turn/src/executor/apply.rs`, the
//!    `CapabilityStale` refusal) stales every group-held capability minted
//!    at an earlier epoch;
//! 5. `GrantCapability` ×(remaining members) — fresh group-held caps minted
//!    at `stored_epoch: Some(new_epoch)` (the survivors' refresh rides the
//!    rekey fan-out; the REMOVED member is simply not re-granted).
//!
//! So `remove(m)` ends, in one epoch step, BOTH m's forward-read ability
//! (they never receive the epoch-e+1 key) and m's group-held capabilities
//! (their freshest cap is stamped ≤ e, and e < e+1 = `delegation_epoch` ⇒
//! `CapabilityStale`). The e2e tests below are that theorem in Rust form.
//!
//! The **epoch anchor** is a zero-balance child cell spawned (via
//! `SpawnWithDelegation`) from the group cell at creation; its only role is
//! to be the standing `RevokeDelegation` target ("bump my own freshness
//! epoch" has no dedicated verb — revoking the anchor IS that verb, and it
//! is repeatable because revocation clears `delegation`, not `delegate`).
//!
//! ## The key schedule (honest minimal; MLS is the named successor)
//!
//! Sender-keys style: each epoch has ONE fresh random 32-byte group key.
//! Rekey seals it to every remaining member individually over the existing
//! seal-pair machinery (X25519 → HKDF-SHA256 → ChaCha20-Poly1305,
//! `dregg_captp::store_forward`) — O(n) per rekey, correct forward
//! darkness: a removed member holds keys ≤ e and epoch-(e+1) ciphertext is
//! AEAD-opaque to them. RFC 9420 MLS (TreeKEM) gives O(log n) rekeys and a
//! PCS ratchet; adopting it replaces ONLY the fan-out in this module — the
//! cell interface (commitments) is UNCHANGED, which is exactly why the
//! blueprint stores commitments and never key material. That swap point is
//! named as the [`KeySchedule`] trait ([`SenderKeys`] today, [`TreeKem`] the
//! RFC 9420 successor stub); the [`Channel`] driver routes every rekey
//! through it, so the upgrade is a type swap, not a rewrite.
//!
//! ## Honest residues (named)
//!
//! * `epoch slot ≡ delegation_epoch` is carried by these canonical builders
//!   (and checked fail-closed in [`Channel::epoch_step`] before every step +
//!   asserted by the tests), not by the program — a cell program cannot
//!   read `delegation_epoch` yet (the closure lane is an executor +
//!   `Exec.Program` atom; the executor lane owns those files).
//! * Re-granting survivors each epoch grows their c-lists (the stale
//!   entries refuse forever but are not yet garbage-collected; a
//!   `RevokeCapability` sweep is a follow-up).
//! * The admin's own driving capability (minted at adopt with
//!   `stored_epoch: None`) is a DIRECT grant, exempt from the freshness
//!   check by R7 semantics — the governor does not lose the group on every
//!   rekey.

use std::collections::{BTreeMap, BTreeSet};

use chacha20poly1305::aead::{Aead, KeyInit, Payload};
use chacha20poly1305::{ChaCha20Poly1305, Nonce};

use dregg_captp::store_forward::{decrypt_from_sender, encrypt_for_destination};
use dregg_cell::blueprint::{
    CH_ADMIN_SLOT, CH_EPOCH_SLOT, CH_KEY_COMMIT_SLOT, CH_MEMBER_ROOT_SLOT, CH_STATE_SLOT,
    CH_TAG_SLOT, ChannelTerms, STATE_OPEN, channel_factory_descriptor, channel_key_commitment,
    channel_member_leaf, channel_member_root,
};
use dregg_cell::factory::{FactoryCreationParams, FactoryDescriptor};
use dregg_cell::program::field_from_u64;
use dregg_cell::state::FieldElement;
use dregg_cell::{CapabilityRef, CellId, CellMode};
use dregg_turn::Effect;
use dregg_turn::action::{Event, symbol};
use dregg_turn::turn::TurnReceipt;

use crate::error::SdkError;
use crate::factories::ADOPT_TURN_FEE;
use crate::runtime::AgentRuntime;

/// Domain tag for the sealed epoch-key payload.
const EPOCH_KEY_PAYLOAD_DOMAIN: &[u8] = b"dregg-channel-epoch-key-v1";
/// Domain tag for the channel token id (group cell derivation).
const CHANNEL_TOKEN_DOMAIN: &str = "dregg-channel-token-v1";
/// Domain tag for the epoch-anchor token id.
const ANCHOR_TOKEN_DOMAIN: &str = "dregg-channel-epoch-anchor-v1";
/// Domain tag for message AEAD associated data.
const MESSAGE_AAD_DOMAIN: &[u8] = b"dregg-channel-msg-v1";

/// Decode a slot's trailing big-endian u64 (the cell-program encoding).
fn field_to_u64(f: FieldElement) -> u64 {
    u64::from_be_bytes(f[24..32].try_into().expect("8-byte tail"))
}

// =============================================================================
// The roster (the openable membership set)
// =============================================================================

/// The open membership roster: member cell → member X25519 seal public key.
/// The on-cell commitment ([`CH_MEMBER_ROOT_SLOT`]) is recomputable from
/// this by anyone holding it; a stale or foreign roster fails closed.
pub type Roster = BTreeMap<CellId, [u8; 32]>;

/// The openable commitment over a roster (the blueprint's leaf/root shape).
pub fn roster_root(roster: &Roster) -> FieldElement {
    let leaves: BTreeSet<[u8; 32]> = roster
        .iter()
        .map(|(cell, seal_pk)| channel_member_leaf(cell.as_bytes(), seal_pk))
        .collect();
    channel_member_root(&leaves)
}

// =============================================================================
// Canonical derivations + turn builders (shared with the node service —
// `node/src/channels_service.rs` drives the SAME effect lists through the
// node's authoritative executor)
// =============================================================================

/// The group cell's token id: deterministic over (admin pk, tag).
pub fn channel_token_id(admin_pk: &[u8; 32], tag: &FieldElement) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(CHANNEL_TOKEN_DOMAIN);
    hasher.update(admin_pk);
    hasher.update(tag);
    *hasher.finalize().as_bytes()
}

/// The epoch anchor's token id: deterministic over the group cell.
pub fn anchor_token_id(channel: &CellId) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(ANCHOR_TOKEN_DOMAIN);
    hasher.update(channel.as_bytes());
    *hasher.finalize().as_bytes()
}

/// The per-member group-capability grants of one epoch: every CURRENT
/// member gets a fresh cap stamped `stored_epoch: Some(epoch)` — the
/// executor's R7 check stales it the moment the group's `delegation_epoch`
/// moves past `epoch`.
pub fn member_cap_grants(cell: CellId, roster: &Roster, epoch: u64) -> Vec<Effect> {
    roster
        .keys()
        .map(|member| Effect::GrantCapability {
            from: cell,
            to: *member,
            cap: CapabilityRef {
                target: cell,
                slot: 0,
                permissions: dregg_cell::AuthRequired::Signature,
                breadstuff: None,
                expires_at: None,
                allowed_effects: None,
                stored_epoch: Some(epoch),
            },
        })
        .collect()
}

/// The OPEN turn's effect list — the first epoch step (slot epoch 0→1 AND
/// `delegation_epoch` 0→1 via the anchor revocation, one turn).
pub fn open_effects(
    cell: CellId,
    anchor: CellId,
    admin_pk: [u8; 32],
    tag: FieldElement,
    roster: &Roster,
    key: &[u8; 32],
) -> Vec<Effect> {
    let root = roster_root(roster);
    let mut effects = vec![
        Effect::SetField {
            cell,
            index: CH_MEMBER_ROOT_SLOT as usize,
            value: root,
        },
        Effect::SetField {
            cell,
            index: CH_EPOCH_SLOT as usize,
            value: field_from_u64(1),
        },
        Effect::SetField {
            cell,
            index: CH_KEY_COMMIT_SLOT as usize,
            value: channel_key_commitment(1, key),
        },
        Effect::SetField {
            cell,
            index: CH_ADMIN_SLOT as usize,
            value: admin_pk,
        },
        Effect::SetField {
            cell,
            index: CH_TAG_SLOT as usize,
            value: tag,
        },
        Effect::SetField {
            cell,
            index: CH_STATE_SLOT as usize,
            value: field_from_u64(STATE_OPEN),
        },
        Effect::RevokeDelegation { child: anchor },
    ];
    effects.extend(member_cap_grants(cell, roster, 1));
    effects.push(Effect::EmitEvent {
        cell,
        event: Event::new(symbol("channel-opened"), vec![tag, root, field_from_u64(1)]),
    });
    effects
}

/// THE ONE EPOCH-STEP TURN's effect list (join / remove / rekey): new
/// membership root + stepped epoch + fresh key commitment + the
/// `delegation_epoch` bump (anchor revocation) + the surviving members' cap
/// refresh — atomically, or the program refuses the whole turn.
pub fn epoch_step_effects(
    cell: CellId,
    anchor: CellId,
    new_roster: &Roster,
    new_epoch: u64,
    key: &[u8; 32],
    event: &str,
) -> Vec<Effect> {
    let root = roster_root(new_roster);
    let mut effects = vec![
        Effect::SetField {
            cell,
            index: CH_MEMBER_ROOT_SLOT as usize,
            value: root,
        },
        Effect::SetField {
            cell,
            index: CH_EPOCH_SLOT as usize,
            value: field_from_u64(new_epoch),
        },
        Effect::SetField {
            cell,
            index: CH_KEY_COMMIT_SLOT as usize,
            value: channel_key_commitment(new_epoch, key),
        },
        // THE UNIFICATION: the same turn bumps the capability freshness
        // counter.
        Effect::RevokeDelegation { child: anchor },
    ];
    effects.extend(member_cap_grants(cell, new_roster, new_epoch));
    effects.push(Effect::EmitEvent {
        cell,
        event: Event::new(symbol(event), vec![root, field_from_u64(new_epoch)]),
    });
    effects
}

// =============================================================================
// The key schedule (sender-keys; the MLS-upgrade seam)
// =============================================================================

/// One member's sealed copy of an epoch group key (the rekey fan-out unit).
/// Transportable over any channel — mailbox, SSE, captp store-and-forward —
/// it is ciphertext to everyone but `member`.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct SealedEpochKey {
    /// The member this copy is sealed to.
    pub member: CellId,
    /// The epoch the enclosed key serves.
    pub epoch: u64,
    /// Sender's ephemeral X25519 public key (X25519→HKDF→ChaCha20 shape).
    pub ephemeral_pk: [u8; 32],
    /// The sealed `domain ‖ epoch ‖ key` payload.
    pub ciphertext: Vec<u8>,
}

/// The rekey fan-out as a swappable strategy — THE MLS-UPGRADE SEAM.
///
/// An epoch step mints one fresh group key and must deliver it to every
/// remaining member; *how* it is delivered is the only thing MLS changes.
/// This trait names that join point so the cell interface (commitments) and
/// the [`Channel`] driver stay untouched across the upgrade:
///
/// * [`SenderKeys`] — today's honest-minimal schedule. ONE fresh random key
///   per epoch, sealed to each member individually over the seal-pair
///   machinery (X25519 → HKDF-SHA256 → ChaCha20-Poly1305). O(n) per rekey,
///   correct forward darkness (a removed member holds keys ≤ e and
///   epoch-(e+1) ciphertext is AEAD-opaque to them).
/// * [`TreeKem`] — the RFC 9420 (MLS) successor (stub). TreeKEM gives
///   O(log n) rekeys and a PCS (post-compromise security) ratchet; adopting
///   it replaces ONLY this fan-out — the blueprint stores commitments and
///   never key material, which is exactly what makes the swap local.
///
/// The chain sees only the key COMMITMENT ([`CH_KEY_COMMIT_SLOT`]); the
/// schedule produces the off-chain sealed copies that let members recover the
/// key whose commitment the turn pinned.
pub trait KeySchedule {
    /// Seal `key` (serving `epoch`) to every roster member, producing the
    /// per-member fan-out the epoch step delivers off-chain.
    fn seal_epoch_key(&self, epoch: u64, key: &[u8; 32], roster: &Roster) -> Vec<SealedEpochKey>;
}

/// Today's schedule: a fresh random group key per epoch, sealed pairwise to
/// each member. O(n) per rekey — the honest-minimal point on the seam.
#[derive(Clone, Copy, Debug, Default)]
pub struct SenderKeys;

impl KeySchedule for SenderKeys {
    fn seal_epoch_key(&self, epoch: u64, key: &[u8; 32], roster: &Roster) -> Vec<SealedEpochKey> {
        let mut payload = Vec::with_capacity(EPOCH_KEY_PAYLOAD_DOMAIN.len() + 8 + 32);
        payload.extend_from_slice(EPOCH_KEY_PAYLOAD_DOMAIN);
        payload.extend_from_slice(&epoch.to_le_bytes());
        payload.extend_from_slice(key);
        roster
            .iter()
            .map(|(member, seal_pk)| {
                let (ephemeral_pk, ciphertext) =
                    encrypt_for_destination(&payload, seal_pk, &[0u8; 32]);
                SealedEpochKey {
                    member: *member,
                    epoch,
                    ephemeral_pk,
                    ciphertext,
                }
            })
            .collect()
    }
}

/// The RFC 9420 (MLS) TreeKEM schedule — the named successor (STUB).
///
/// MLS arranges members as the leaves of a left-balanced binary tree of
/// HPKE key pairs (RFC 9420 §7); a member rekeys by sending one `Commit`
/// carrying `UpdatePath` ciphertexts along its root path (§7.5, §12.4), so a
/// rekey is O(log n) sealed copies, not O(n), and the ratchet up the tree's
/// `secret_tree`/`key_schedule` (§9, §8) gives post-compromise security: a
/// transiently-leaked member key heals at the next commit.
///
/// Adopting it is LOCAL to this module: the on-cell key commitment stays the
/// epoch's `joiner_secret`/`epoch_secret` commitment (the cell interface is
/// unchanged), and only [`KeySchedule::seal_epoch_key`] changes from a flat
/// pairwise fan-out to a tree `UpdatePath`. The stub carries the design refs
/// so the seam is a doer lane, not a wall; it is not yet wired (the tree
/// state — ratchet tree, leaf HPKE keys, the `secret_tree` — has no home in
/// this struct yet, so it cannot produce a real `UpdatePath`).
#[derive(Clone, Copy, Debug, Default)]
pub struct TreeKem;

impl KeySchedule for TreeKem {
    fn seal_epoch_key(
        &self,
        _epoch: u64,
        _key: &[u8; 32],
        _roster: &Roster,
    ) -> Vec<SealedEpochKey> {
        // RFC 9420 §7.5/§12.4: this is where the flat fan-out becomes a
        // TreeKEM `UpdatePath` along the committer's root path. The ratchet
        // tree + per-leaf HPKE key state it needs is not modeled here yet.
        unimplemented!(
            "TreeKem (RFC 9420 MLS) key schedule is the named successor seam, not yet wired: \
             needs the ratchet tree + leaf HPKE key state to emit an UpdatePath"
        )
    }
}

/// Seal `key` (serving `epoch`) to every roster member under the deployed
/// schedule ([`SenderKeys`] today). Thin compatibility wrapper over
/// [`KeySchedule::seal_epoch_key`] — byte-identical to the historical
/// fan-out; the [`Channel`] driver routes through this so swapping the
/// schedule type swaps the rekey strategy without touching the cell or the
/// turn shapes.
pub fn seal_epoch_key_to_roster(
    epoch: u64,
    key: &[u8; 32],
    roster: &Roster,
) -> Vec<SealedEpochKey> {
    SenderKeys.seal_epoch_key(epoch, key, roster)
}

/// A group-key epoch ledger held by one party (the admin holds all epochs
/// it minted; a member holds the epochs it was sealed).
#[derive(Clone, Debug, Default)]
pub struct EpochKeys {
    keys: BTreeMap<u64, [u8; 32]>,
}

impl EpochKeys {
    pub fn insert(&mut self, epoch: u64, key: [u8; 32]) {
        self.keys.insert(epoch, key);
    }
    pub fn get(&self, epoch: u64) -> Option<&[u8; 32]> {
        self.keys.get(&epoch)
    }
    pub fn latest(&self) -> Option<(u64, &[u8; 32])> {
        self.keys.iter().next_back().map(|(e, k)| (*e, k))
    }
}

// =============================================================================
// The data plane (never on-cell)
// =============================================================================

/// One encrypted group message: AEAD ciphertext under the epoch group key,
/// bound to (channel, epoch) via associated data. Carried over any
/// transport; the chain never sees it.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ChannelEnvelope {
    /// The group cell this message belongs to.
    pub channel: CellId,
    /// The key epoch the body is encrypted under.
    pub epoch: u64,
    /// Fresh random AEAD nonce.
    pub nonce: [u8; 12],
    /// ChaCha20-Poly1305 ciphertext (tag appended).
    pub ciphertext: Vec<u8>,
}

fn message_aad(channel: &CellId, epoch: u64) -> Vec<u8> {
    let mut aad = Vec::with_capacity(MESSAGE_AAD_DOMAIN.len() + 32 + 8);
    aad.extend_from_slice(MESSAGE_AAD_DOMAIN);
    aad.extend_from_slice(channel.as_bytes());
    aad.extend_from_slice(&epoch.to_le_bytes());
    aad
}

/// Encrypt a message body under an epoch group key. Any key holder (any
/// current member) can post — posting is purely off-cell.
pub fn seal_message(
    channel: &CellId,
    epoch: u64,
    key: &[u8; 32],
    plaintext: &[u8],
) -> ChannelEnvelope {
    let mut nonce = [0u8; 12];
    getrandom::fill(&mut nonce).expect("getrandom failed");
    let cipher = ChaCha20Poly1305::new(key.into());
    let ciphertext = cipher
        .encrypt(
            Nonce::from_slice(&nonce),
            Payload {
                msg: plaintext,
                aad: &message_aad(channel, epoch),
            },
        )
        .expect("ChaCha20-Poly1305 encryption never fails");
    ChannelEnvelope {
        channel: *channel,
        epoch,
        nonce,
        ciphertext,
    }
}

/// Decrypt a message body with the epoch key the envelope names. Fails on a
/// wrong/old key or any tamper (AEAD), and on an epoch the holder lacks —
/// the forward-darkness refusal surfaces here.
pub fn open_message(key: &[u8; 32], envelope: &ChannelEnvelope) -> Result<Vec<u8>, SdkError> {
    let cipher = ChaCha20Poly1305::new(key.into());
    cipher
        .decrypt(
            Nonce::from_slice(&envelope.nonce),
            Payload {
                msg: &envelope.ciphertext,
                aad: &message_aad(&envelope.channel, envelope.epoch),
            },
        )
        .map_err(|_| {
            SdkError::Rejected("channel message AEAD refused (wrong key or tampered)".into())
        })
}

// =============================================================================
// The member's view
// =============================================================================

/// A member-side keyring: the member's X25519 seal secret + every epoch key
/// they have been sealed. A REMOVED member's ring stops at their last
/// epoch — that is the forward-darkness property, witnessed by the tests.
#[derive(Debug)]
pub struct MemberKeyring {
    /// The member cell this ring belongs to.
    pub cell: CellId,
    seal_secret: [u8; 32],
    keys: EpochKeys,
}

impl MemberKeyring {
    pub fn new(cell: CellId, seal_secret: [u8; 32]) -> Self {
        MemberKeyring {
            cell,
            seal_secret,
            keys: EpochKeys::default(),
        }
    }

    /// The X25519 public key the roster carries for this member (derived
    /// through the cell crate's seal-pair machinery — same curve, same
    /// clamping as the fan-out encryption).
    pub fn seal_pk(&self) -> [u8; 32] {
        dregg_cell::SealPair::from_secret(self.seal_secret).sealer_public
    }

    /// Accept one sealed epoch key addressed to this member. Refuses keys
    /// sealed to someone else (DH failure), tampered payloads, and payload
    /// epochs disagreeing with the envelope's claim.
    pub fn accept(&mut self, sealed: &SealedEpochKey) -> Result<u64, SdkError> {
        let payload =
            decrypt_from_sender(&sealed.ciphertext, &sealed.ephemeral_pk, &self.seal_secret)
                .map_err(|e| SdkError::Rejected(format!("sealed epoch key refused: {e:?}")))?;
        let dlen = EPOCH_KEY_PAYLOAD_DOMAIN.len();
        if payload.len() != dlen + 8 + 32 || &payload[..dlen] != EPOCH_KEY_PAYLOAD_DOMAIN {
            return Err(SdkError::Rejected(
                "sealed epoch key payload malformed".into(),
            ));
        }
        let epoch = u64::from_le_bytes(payload[dlen..dlen + 8].try_into().unwrap());
        if epoch != sealed.epoch {
            return Err(SdkError::Rejected(
                "sealed epoch key epoch mismatch (envelope vs payload)".into(),
            ));
        }
        let mut key = [0u8; 32];
        key.copy_from_slice(&payload[dlen + 8..]);
        self.keys.insert(epoch, key);
        Ok(epoch)
    }

    /// The epoch group key this ring has unsealed for `epoch`, if any.
    pub fn epoch_key(&self, epoch: u64) -> Option<&[u8; 32]> {
        self.keys.get(epoch)
    }

    /// Open a group message with this ring. An epoch this member was never
    /// sealed (e.g. every epoch after their removal) refuses.
    pub fn open(&self, envelope: &ChannelEnvelope) -> Result<Vec<u8>, SdkError> {
        let key = self.keys.get(envelope.epoch).ok_or_else(|| {
            SdkError::Rejected(format!(
                "no group key for epoch {} (removed members stay dark forward)",
                envelope.epoch
            ))
        })?;
        open_message(key, envelope)
    }

    /// Post a message as this member (any current key holder can post).
    pub fn post(
        &self,
        channel: &CellId,
        epoch: u64,
        plaintext: &[u8],
    ) -> Result<ChannelEnvelope, SdkError> {
        let key = self
            .keys
            .get(epoch)
            .ok_or_else(|| SdkError::Rejected(format!("no group key for epoch {epoch}")))?;
        Ok(seal_message(channel, epoch, key, plaintext))
    }
}

// =============================================================================
// The Channel noun (admin / operator side)
// =============================================================================

/// The live on-cell position of a channel group.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChannelStatus {
    /// The key/freshness epoch (slot 2).
    pub epoch: u64,
    /// The group cell's `delegation_epoch` — the capability freshness
    /// counter. INVARIANT under the canonical builders: equals `epoch`.
    pub delegation_epoch: u64,
    /// The openable membership commitment (slot 1).
    pub member_root: FieldElement,
    /// The epoch key commitment (slot 3).
    pub key_commit: FieldElement,
    /// Whether the group is OPEN.
    pub open: bool,
}

/// An open channel-group handle: the admin-side driving surface over the
/// owner runtime's `.turn()` path. Holds the open roster and the epoch keys
/// this admin minted.
#[derive(Debug)]
pub struct Channel {
    /// The group cell.
    pub cell: CellId,
    /// The epoch anchor (the standing `RevokeDelegation` target).
    pub anchor: CellId,
    /// The group tag.
    pub tag: FieldElement,
    /// The open roster (cell → seal pk). Re-commits to slot 1 at all times.
    pub roster: Roster,
    /// Every epoch key this admin minted.
    pub keys: EpochKeys,
}

impl Channel {
    /// **Create a group**: birth the per-group cell from its
    /// content-addressed factory, spawn the epoch anchor, and OPEN at epoch
    /// 1 with the initial roster committed, the first group key committed,
    /// and every founding member granted an epoch-1 group capability —
    /// the open turn IS the first epoch step (slot epoch 0→1 and
    /// `delegation_epoch` 0→1 together).
    ///
    /// Returns the handle plus the epoch-1 sealed-key fan-out.
    pub fn create(
        runtime: &mut AgentRuntime,
        tag: FieldElement,
        roster: Roster,
    ) -> Result<(Self, Vec<SealedEpochKey>), SdkError> {
        let admin_cell = runtime.cell_id();
        let admin_pk = runtime
            .cipherclerk()
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .public_key()
            .0;
        let terms = ChannelTerms {
            admin: admin_pk,
            tag,
        };
        let descriptor: FactoryDescriptor = channel_factory_descriptor(&terms)
            .map_err(|e| SdkError::Rejected(format!("channel terms refused: {e}")))?;

        let token_id = channel_token_id(&admin_pk, &tag);
        let cell_id = CellId::derive_raw(&admin_pk, &token_id);
        let anchor_token = anchor_token_id(&cell_id);
        let anchor = CellId::derive_raw(&admin_pk, &anchor_token);

        // Turn 1 — birth from the per-group factory.
        runtime.deploy_factory(descriptor.clone());
        runtime.execute(vec![Effect::CreateCellFromFactory {
            factory_vk: descriptor.factory_vk,
            owner_pubkey: admin_pk,
            token_id,
            params: FactoryCreationParams {
                mode: CellMode::Hosted,
                program_vk: descriptor.child_program_vk,
                initial_fields: vec![],
                initial_caps: vec![],
                owner_pubkey: admin_pk,
            },
        }])?;

        // Turn 2 — fund the adopt turn's fee.
        runtime.execute(vec![Effect::Transfer {
            from: admin_cell,
            to: cell_id,
            amount: ADOPT_TURN_FEE,
        }])?;

        // Turn 3 — the adopt (cell-agent turn): spawn the EPOCH ANCHOR and
        // grant the admin their driving capability (a DIRECT grant,
        // `stored_epoch: None` — the governor's reach survives rekeys).
        runtime.execute_as(
            cell_id,
            vec![
                Effect::SpawnWithDelegation {
                    child_public_key: admin_pk,
                    child_token_id: anchor_token,
                    max_staleness: u64::MAX,
                },
                Effect::GrantCapability {
                    from: cell_id,
                    to: admin_cell,
                    cap: CapabilityRef {
                        target: cell_id,
                        slot: 0,
                        permissions: dregg_cell::AuthRequired::Signature,
                        breadstuff: None,
                        expires_at: None,
                        allowed_effects: None,
                        stored_epoch: None,
                    },
                },
            ],
            ADOPT_TURN_FEE,
        )?;

        // Turn 4 — OPEN at epoch 1: the first epoch step (both counters).
        let mut key = [0u8; 32];
        getrandom::fill(&mut key).expect("getrandom failed");
        runtime.execute_on(
            cell_id,
            open_effects(cell_id, anchor, admin_pk, tag, &roster, &key),
        )?;

        let fan_out = seal_epoch_key_to_roster(1, &key, &roster);
        let mut keys = EpochKeys::default();
        keys.insert(1, key);
        Ok((
            Channel {
                cell: cell_id,
                anchor,
                tag,
                roster,
                keys,
            },
            fan_out,
        ))
    }

    /// Read the live position from the cell's registers.
    pub fn status(&self, runtime: &AgentRuntime) -> Result<ChannelStatus, SdkError> {
        let ledger = runtime.ledger().lock().unwrap();
        let cell = ledger
            .get(&self.cell)
            .ok_or_else(|| SdkError::Rejected("channel cell not in ledger".into()))?;
        Ok(ChannelStatus {
            epoch: field_to_u64(cell.state.fields[CH_EPOCH_SLOT as usize]),
            delegation_epoch: cell.state.delegation_epoch(),
            member_root: cell.state.fields[CH_MEMBER_ROOT_SLOT as usize],
            key_commit: cell.state.fields[CH_KEY_COMMIT_SLOT as usize],
            open: field_to_u64(cell.state.fields[CH_STATE_SLOT as usize]) == STATE_OPEN,
        })
    }

    /// THE ONE EPOCH-STEP TURN (shared by join / remove / rekey): commit the
    /// new roster + the stepped epoch + the fresh key commitment + the
    /// `delegation_epoch` bump + the surviving members' cap refresh — all
    /// atomically. Fails closed BEFORE building anything if the two epoch
    /// counters have diverged (a foreign turn moved one without the other).
    fn epoch_step(
        &mut self,
        runtime: &AgentRuntime,
        new_roster: Roster,
        event: &str,
    ) -> Result<(TurnReceipt, Vec<SealedEpochKey>), SdkError> {
        let status = self.status(runtime)?;
        if !status.open {
            return Err(SdkError::Rejected("channel is not open".into()));
        }
        if status.epoch != status.delegation_epoch {
            return Err(SdkError::Rejected(format!(
                "channel epoch divergence: slot epoch {} ≠ delegation_epoch {} — refusing to step",
                status.epoch, status.delegation_epoch
            )));
        }
        if roster_root(&self.roster) != status.member_root {
            return Err(SdkError::Rejected(
                "open roster does not re-commit to the on-cell membership root".into(),
            ));
        }
        let new_epoch = status.epoch + 1;
        let mut key = [0u8; 32];
        getrandom::fill(&mut key).expect("getrandom failed");

        // ONE turn. A rejection leaves roster, keys, and both counters
        // exactly where they were (executor atomicity).
        let receipt = runtime.execute_on(
            self.cell,
            epoch_step_effects(self.cell, self.anchor, &new_roster, new_epoch, &key, event),
        )?;

        self.roster = new_roster;
        self.keys.insert(new_epoch, key);
        let fan_out = seal_epoch_key_to_roster(new_epoch, &key, &self.roster);
        Ok((receipt, fan_out))
    }

    /// **Join**: admit a member. One epoch-step turn — the new member gets
    /// keys only from their join epoch forward (no read-back into earlier
    /// epochs), and every member's capability is refreshed at the new epoch.
    pub fn join(
        &mut self,
        runtime: &AgentRuntime,
        member: CellId,
        seal_pk: [u8; 32],
    ) -> Result<(TurnReceipt, Vec<SealedEpochKey>), SdkError> {
        if self.roster.contains_key(&member) {
            return Err(SdkError::Rejected("member already in the group".into()));
        }
        let mut next = self.roster.clone();
        next.insert(member, seal_pk);
        self.epoch_step(runtime, next, "channel-join")
    }

    /// **Remove**: THE KEYSTONE OP — drop the member, step the epoch, commit
    /// the fresh key, bump the freshness counter, refresh the survivors: ONE
    /// turn. After this commits, the removed member can neither decrypt
    /// epoch-(e+1) ciphertext NOR exercise any group-held capability minted
    /// at epoch ≤ e.
    pub fn remove(
        &mut self,
        runtime: &AgentRuntime,
        member: CellId,
    ) -> Result<(TurnReceipt, Vec<SealedEpochKey>), SdkError> {
        if !self.roster.contains_key(&member) {
            return Err(SdkError::Rejected("not a member".into()));
        }
        let mut next = self.roster.clone();
        next.remove(&member);
        self.epoch_step(runtime, next, "channel-remove")
    }

    /// **Rekey**: step the epoch with the membership unchanged (compromise
    /// recovery / key hygiene). Same one-turn shape.
    pub fn rekey(
        &mut self,
        runtime: &AgentRuntime,
    ) -> Result<(TurnReceipt, Vec<SealedEpochKey>), SdkError> {
        let next = self.roster.clone();
        self.epoch_step(runtime, next, "channel-rekey")
    }

    /// Post a message under the current epoch key (admin side; members post
    /// via [`MemberKeyring::post`]). Purely off-cell.
    pub fn post(&self, plaintext: &[u8]) -> Result<ChannelEnvelope, SdkError> {
        let (epoch, key) = self
            .keys
            .latest()
            .ok_or_else(|| SdkError::Rejected("no group key minted yet".into()))?;
        Ok(seal_message(&self.cell, epoch, key, plaintext))
    }
}

// =============================================================================
// Tests — the keystone theorem in Rust form, on the REAL executor
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cipherclerk::AgentCipherclerk;
    use dregg_turn::TurnError;

    const FUNDING: u64 = 10_000_000;
    const MEMBER_FUNDING: i64 = 200_000;

    /// A funded admin runtime + four funded member cells (owned by the same
    /// operator key — the single-machine collapse; distinct cells, distinct
    /// seal secrets) on the same ledger. NOTE: a cell-agent turn does not
    /// link the runtime's receipt chain, so each member cell spends at most
    /// ONE exercise turn per test (the executor's per-agent receipt-chain
    /// head demands linkage from the second turn on) — the tests therefore
    /// use distinct member cells as distinct probes.
    fn setup() -> (AgentRuntime, Vec<(CellId, MemberKeyring)>) {
        let cclerk = AgentCipherclerk::new();
        let admin_pk = cclerk.public_key().0;
        let runtime = AgentRuntime::new_simple(cclerk, "channel-test");
        let mut members = Vec::new();
        {
            let mut ledger = runtime.ledger().lock().unwrap();
            let admin = runtime.cell_id();
            if ledger.get(&admin).is_none() {
                let token = *blake3::hash(b"default").as_bytes();
                let cell = dregg_cell::Cell::with_balance(admin_pk, token, 0);
                assert_eq!(cell.id(), admin, "derivation must match runtime");
                ledger.insert_cell(cell).unwrap();
            }
            assert!(
                ledger
                    .get_mut(&admin)
                    .unwrap()
                    .state
                    .credit_balance(FUNDING),
                "admin accepts funding"
            );
            for i in 0u8..4 {
                let token = *blake3::Hasher::new_derive_key("channel-test-member-v1")
                    .update(&[i])
                    .finalize()
                    .as_bytes();
                let cell = dregg_cell::Cell::with_balance(admin_pk, token, MEMBER_FUNDING);
                let id = cell.id();
                ledger.insert_cell(cell).unwrap();
                let mut secret = [0u8; 32];
                secret[0] = 0x40 + i;
                secret[31] = 0xA0 + i;
                members.push((id, MemberKeyring::new(id, secret)));
            }
        }
        (runtime, members)
    }

    fn roster_of(members: &[(CellId, MemberKeyring)]) -> Roster {
        members
            .iter()
            .map(|(id, ring)| (*id, ring.seal_pk()))
            .collect()
    }

    /// Every group-held capability slot a member holds over `channel`,
    /// paired with its R7 stamp.
    fn member_cap_slots(
        runtime: &AgentRuntime,
        member: CellId,
        channel: CellId,
    ) -> Vec<(u32, Option<u64>)> {
        let ledger = runtime.ledger().lock().unwrap();
        let cell = ledger.get(&member).expect("member cell");
        (0u32..512)
            .filter_map(|slot| {
                cell.capabilities
                    .lookup(slot)
                    .filter(|cap| cap.target == channel)
                    .map(|cap| (slot, cap.stored_epoch))
            })
            .collect()
    }

    /// Exercise a member's group capability through the REAL executor (the
    /// R7 epoch-at-retrieval gate is on this path).
    fn exercise(
        runtime: &AgentRuntime,
        member: CellId,
        channel: CellId,
        cap_slot: u32,
    ) -> Result<dregg_turn::turn::TurnReceipt, SdkError> {
        runtime.execute_as(
            member,
            vec![Effect::ExerciseViaCapability {
                cap_slot,
                inner_effects: vec![Effect::EmitEvent {
                    cell: channel,
                    event: Event::new(symbol("member-ping"), vec![]),
                }],
            }],
            10_000,
        )
    }

    fn open_channel(
        runtime: &mut AgentRuntime,
        members: &[(CellId, MemberKeyring)],
    ) -> (Channel, Vec<SealedEpochKey>) {
        let roster = roster_of(members);
        Channel::create(runtime, field_from_u64(0xC0FFEE), roster).expect("create channel")
    }

    fn accept_fan_out(members: &mut [(CellId, MemberKeyring)], fan_out: &[SealedEpochKey]) {
        for sealed in fan_out {
            if let Some((_, ring)) = members.iter_mut().find(|(id, _)| *id == sealed.member) {
                ring.accept(sealed).expect("member accepts their key");
            }
        }
    }

    // ── create: the group cell opens at epoch 1, both counters agree ──

    #[test]
    fn create_opens_at_epoch_one_with_unified_counters() {
        let (mut runtime, mut members) = setup();
        let (ch, fan_out) = open_channel(&mut runtime, &members);

        let status = ch.status(&runtime).unwrap();
        assert!(status.open);
        assert_eq!(status.epoch, 1, "open IS the first epoch step");
        assert_eq!(
            status.delegation_epoch, 1,
            "THE UNIFICATION: delegation_epoch stepped in the same turn"
        );
        assert_eq!(status.member_root, roster_root(&ch.roster));

        // Every founding member can accept their sealed key and read a
        // posted message; cross-member sealed keys refuse.
        assert_eq!(fan_out.len(), 4);
        accept_fan_out(&mut members, &fan_out);
        let envelope = ch.post(b"hello, group").unwrap();
        for (_, ring) in &members {
            assert_eq!(ring.open(&envelope).unwrap(), b"hello, group");
        }
        let foreign = &fan_out[0];
        assert!(
            members
                .iter_mut()
                .find(|(id, _)| *id != foreign.member)
                .unwrap()
                .1
                .accept(foreign)
                .is_err(),
            "a sealed key addressed to another member must refuse"
        );

        // Members post too (sender-keys: any key holder).
        let m_env = members[1].1.post(&ch.cell, 1, b"from a member").unwrap();
        assert_eq!(members[2].1.open(&m_env).unwrap(), b"from a member");
    }

    // ── THE KEYSTONE THEOREM: remove(m) ⇒ ciphertext AND capability
    //    darkness, one epoch step, ONE turn ──

    #[test]
    fn remove_is_one_turn_and_darkens_both_planes() {
        let (mut runtime, mut members) = setup();
        let (mut ch, fan_out) = open_channel(&mut runtime, &members);
        accept_fan_out(&mut members, &fan_out);
        // One exercise turn per member cell (see `setup` docs): distinct
        // members serve as distinct probes.
        let removed = members[0].0; // exercises their stale cap POST-remove
        let fresh_probe = members[1].0; // exercises their REFRESHED cap post-remove
        let stale_probe = members[2].0; // exercises their epoch-1 entry post-remove
        let pre_probe = members[3].0; // proves an epoch-1 cap exercises PRE-remove

        // Pre-remove: a founding epoch-1 capability exercises at epoch 1.
        let slots = member_cap_slots(&runtime, pre_probe, ch.cell);
        assert_eq!(slots.len(), 1);
        let (pre_slot, stamp) = slots[0];
        assert_eq!(stamp, Some(1), "founding cap is stamped at epoch 1");
        exercise(&runtime, pre_probe, ch.cell, pre_slot).expect("epoch-1 cap exercises at epoch 1");
        let (removed_slot, _) = member_cap_slots(&runtime, removed, ch.cell)[0];

        // THE REMOVE: one turn (one receipt), epoch 1 → 2 on BOTH counters,
        // fresh key committed.
        let pre = ch.status(&runtime).unwrap();
        let (receipt, fan_out2) = ch.remove(&runtime, removed).expect("remove commits");
        let _ = receipt; // ONE TurnReceipt — the remove + rekey + cap-bump turn.
        let post = ch.status(&runtime).unwrap();
        assert_eq!(post.epoch, 2);
        assert_eq!(
            post.delegation_epoch, 2,
            "THE UNIFICATION: one turn stepped the freshness counter too"
        );
        assert_ne!(post.key_commit, pre.key_commit, "rekey rode the remove");
        assert_ne!(post.member_root, pre.member_root);

        // The fan-out excludes the removed member.
        assert_eq!(fan_out2.len(), 3);
        assert!(fan_out2.iter().all(|s| s.member != removed));
        accept_fan_out(&mut members, &fan_out2);

        // FORWARD DARKNESS: epoch-2 ciphertext refuses the removed member's
        // ring (their keys stop at epoch 1); survivors read it.
        let envelope = ch.post(b"post-removal message").unwrap();
        assert_eq!(envelope.epoch, 2);
        let removed_ring = &members[0].1;
        assert!(
            removed_ring.open(&envelope).is_err(),
            "removed member must stay dark at epoch 2"
        );
        assert_eq!(
            members[1].1.open(&envelope).unwrap(),
            b"post-removal message"
        );
        // …and their OLD key really is useless against the new epoch (not
        // just a missing-key refusal): decrypting with the epoch-1 key fails
        // the AEAD.
        let mut forged = envelope.clone();
        forged.epoch = 1; // pretend it is epoch-1 traffic
        assert!(
            removed_ring.open(&forged).is_err(),
            "epoch-1 key + tampered epoch claim must refuse (AAD binds epoch)"
        );

        // CAPABILITY DARKNESS (the unification tooth): the removed member's
        // epoch-1 cap now refuses with CapabilityStale.
        let err = exercise(&runtime, removed, ch.cell, removed_slot).unwrap_err();
        assert!(
            matches!(
                &err,
                SdkError::Turn(TurnError::CapabilityStale {
                    stored_epoch: 1,
                    current_epoch: 2,
                    ..
                })
            ),
            "expected CapabilityStale(1 < 2), got {err:?}"
        );

        // The SURVIVORS' refresh rode the same turn: an epoch-2 cap
        // exercises; a survivor's stale epoch-1 entry refuses identically.
        let (fresh_slot, _) = *member_cap_slots(&runtime, fresh_probe, ch.cell)
            .iter()
            .find(|(_, stamp)| *stamp == Some(2))
            .expect("survivor holds an epoch-2 cap");
        exercise(&runtime, fresh_probe, ch.cell, fresh_slot)
            .expect("survivor's refreshed cap exercises");
        let (stale_slot, _) = *member_cap_slots(&runtime, stale_probe, ch.cell)
            .iter()
            .find(|(_, stamp)| *stamp == Some(1))
            .expect("survivor still carries the stale epoch-1 entry");
        assert!(
            matches!(
                exercise(&runtime, stale_probe, ch.cell, stale_slot).unwrap_err(),
                SdkError::Turn(TurnError::CapabilityStale { .. })
            ),
            "the stale entry refuses for survivors too (refresh = the new grant)"
        );

        // The removed member holds NO epoch-2 cap at all.
        assert!(
            member_cap_slots(&runtime, removed, ch.cell)
                .iter()
                .all(|(_, stamp)| *stamp != Some(2)),
            "removed member was not re-granted"
        );
    }

    // ── the program teeth bite on the real executor ──

    #[test]
    fn executor_rejects_partial_membership_turns() {
        let (mut runtime, members) = setup();
        let (ch, _) = open_channel(&mut runtime, &members);

        // A membership write WITHOUT the epoch step / rekey: the program's
        // unification triple refuses it in-protocol (a "non-member join"
        // forged as a raw turn dies here).
        let mut forged = ch.roster.clone();
        forged.insert(
            CellId::from_bytes([0x77; 32]),
            [0x88; 32], // an interloper's seal pk
        );
        let res = runtime.execute_on(
            ch.cell,
            vec![Effect::SetField {
                cell: ch.cell,
                index: CH_MEMBER_ROOT_SLOT as usize,
                value: roster_root(&forged),
            }],
        );
        assert!(
            matches!(res, Err(SdkError::Turn(_))),
            "membership change without epoch step must refuse: {res:?}"
        );
        let status = ch.status(&runtime).unwrap();
        assert_eq!(status.member_root, roster_root(&ch.roster), "root unmoved");
        assert_eq!(status.epoch, 1);

        // An epoch step that KEEPS the old key commitment: refused (the
        // removal-that-forgets-to-rekey shape).
        let res = runtime.execute_on(
            ch.cell,
            vec![
                Effect::SetField {
                    cell: ch.cell,
                    index: CH_EPOCH_SLOT as usize,
                    value: field_from_u64(2),
                },
                Effect::RevokeDelegation { child: ch.anchor },
            ],
        );
        assert!(matches!(res, Err(SdkError::Turn(_))), "{res:?}");
        assert_eq!(ch.status(&runtime).unwrap().epoch, 1);
        assert_eq!(
            ch.status(&runtime).unwrap().delegation_epoch,
            1,
            "executor atomicity: the refused turn moved NEITHER counter"
        );

        // An epoch rewind: refused.
        let res = runtime.execute_on(
            ch.cell,
            vec![Effect::SetField {
                cell: ch.cell,
                index: CH_EPOCH_SLOT as usize,
                value: field_from_u64(0),
            }],
        );
        assert!(matches!(res, Err(SdkError::Turn(_))), "{res:?}");
    }

    // ── join admits forward-only; rekey is compromise recovery ──

    #[test]
    fn join_grants_forward_only_and_rekey_steps() {
        let (mut runtime, mut members) = setup();
        // Found the group with TWO members; the third joins later.
        let (mut ch, fan_out) = {
            let roster: Roster = members[..2]
                .iter()
                .map(|(id, ring)| (*id, ring.seal_pk()))
                .collect();
            Channel::create(&mut runtime, field_from_u64(0xC0FFEE), roster).expect("create channel")
        };
        accept_fan_out(&mut members, &fan_out);
        let epoch1_envelope = ch.post(b"before the join").unwrap();

        let (late_cell, late_pk) = (members[2].0, members[2].1.seal_pk());
        let (_, fan_out2) = ch.join(&runtime, late_cell, late_pk).expect("join");
        accept_fan_out(&mut members, &fan_out2);

        let status = ch.status(&runtime).unwrap();
        assert_eq!(status.epoch, 2);
        assert_eq!(status.delegation_epoch, 2);

        // The joiner reads epoch-2 traffic…
        let envelope = ch.post(b"after the join").unwrap();
        assert_eq!(members[2].1.open(&envelope).unwrap(), b"after the join");
        // …but NOT the epoch-1 history (keys are forward-only).
        assert!(
            members[2].1.open(&epoch1_envelope).is_err(),
            "a joiner must not read pre-join epochs"
        );
        // A duplicate join refuses.
        assert!(ch.join(&runtime, late_cell, late_pk).is_err());

        // Rekey: membership unchanged, epoch steps, key changes.
        let pre = ch.status(&runtime).unwrap();
        let (_, fan_out3) = ch.rekey(&runtime).expect("rekey");
        assert_eq!(fan_out3.len(), 3);
        let post = ch.status(&runtime).unwrap();
        assert_eq!(post.epoch, 3);
        assert_eq!(post.delegation_epoch, 3);
        assert_eq!(post.member_root, pre.member_root);
        assert_ne!(post.key_commit, pre.key_commit);
    }

    // ── the MLS seam: SenderKeys-through-trait is byte-identical ─────────────

    #[test]
    fn sender_keys_through_trait_is_behaviourally_identical_to_the_free_fanout() {
        // The seam restructure is non-behavioural: routing through the
        // KeySchedule trait's SenderKeys impl produces the SAME fan-out as the
        // historical free function. The seal is a real X25519→HKDF→ChaCha20
        // AEAD with a FRESH ephemeral keypair per copy (PFS), so the raw
        // ciphertext/ephemeral_pk are deliberately randomised and a byte
        // compare is meaningless — equivalence is that each member recovers the
        // IDENTICAL epoch key from either path. We also pin that the free
        // function IS the SenderKeys impl (no second code path can drift).
        let key = [7u8; 32];
        let epoch = 5u64;

        // Three members with REAL seal keypairs (so the fan-out is decryptable).
        let mut rings: Vec<MemberKeyring> = (0u8..3)
            .map(|i| {
                let cell = CellId([i; 32]);
                let mut secret = [0u8; 32];
                secret[0] = i.wrapping_add(1);
                MemberKeyring::new(cell, secret)
            })
            .collect();
        let mut roster = Roster::new();
        for ring in &rings {
            roster.insert(ring.cell, ring.seal_pk());
        }

        let via_free = seal_epoch_key_to_roster(epoch, &key, &roster);
        let via_trait = SenderKeys.seal_epoch_key(epoch, &key, &roster);

        assert_eq!(via_free.len(), 3);
        assert_eq!(via_free.len(), via_trait.len());
        for ((a, b), ring) in via_free.iter().zip(via_trait.iter()).zip(rings.iter_mut()) {
            // Structural fields ARE identical across the seam: same member, same
            // epoch, same destination ordering.
            assert_eq!(a.member, b.member);
            assert_eq!(a.epoch, b.epoch);
            assert_eq!(a.member, ring.cell, "fan-out preserves roster order");
            // Each path's sealed copy decrypts to the SAME epoch key for this
            // member — the real behavioural-equivalence guarantee.
            assert_eq!(ring.accept(a).expect("free copy decrypts"), epoch);
            assert_eq!(
                *ring.epoch_key(epoch).unwrap(),
                key,
                "free path delivers the key"
            );
            assert_eq!(ring.accept(b).expect("trait copy decrypts"), epoch);
            assert_eq!(
                *ring.epoch_key(epoch).unwrap(),
                key,
                "trait path delivers the key"
            );
        }
    }

    #[test]
    #[should_panic(expected = "RFC 9420")]
    fn treekem_stub_is_unimplemented_named_successor() {
        // The named seam is a doer lane, not a wall: TreeKem is present and
        // selectable but refuses loudly until the ratchet tree is wired.
        let roster = Roster::new();
        let _ = TreeKem.seal_epoch_key(1, &[0u8; 32], &roster);
    }
}
