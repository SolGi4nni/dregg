//! Durable custody of the Path of Angels per-slot secret.
//!
//! # Why the curator holds this secret and the node does not mint it
//!
//! The live run seed is `HiddenInstance.runSeedFor ⟨secret, slot, playerKey⟩ ctx`.
//! Every validator that judges a run must derive the SAME seed, or the federation
//! does not merely fail to agree — it agrees on *different answers* and each node
//! believes itself correct. A secret derived per node (from the node signing key,
//! from local entropy, from anything the node owns) guarantees exactly that: a
//! divergent instance per validator, which is strictly worse than a missing one
//! because it settles.
//!
//! So the secret is **curator-held and ceremony-installed**:
//!
//! 1. The curator draws the slot secret off-line.
//! 2. The curator publishes `commit(secret, slot)` in a signed slot opening,
//!    BEFORE the slot opens. (It cannot live in the content bundle: that bundle is
//!    signed once per content epoch and slots open afterwards.)
//! 3. The secret is delivered to the node, which verifies it opens the published
//!    commitment and installs it here.
//!
//! Opening a slot is therefore a curator action requiring the curator key. That is
//! correct rather than inconvenient: opening a slot is an editorial act.
//!
//! # What this module refuses
//!
//! * A slot opening whose Ed25519 signature does not verify against the installed
//!   curator pin — the same pin that gates the POAG1 content epoch and every world
//!   activation.
//! * Any attempt to install a DIFFERENT secret, commitment or curator key for a
//!   slot already installed. An identical retry succeeds (ceremonies get re-run);
//!   substitution never does, for the life of the store.
//! * A slot that does not strictly advance the authority's open slot. Slots are
//!   totally ordered per authority so "the open slot" is a fact about storage
//!   rather than a race between two installs.
//!
//! # What this module does NOT check
//!
//! That `commitment` is the commitment OF `secret` is `HiddenInstance.commit`, a
//! Lean predicate over a Poseidon2-BabyBear sponge. Persist holds no copy of it.
//! The node ceremony verifies that by CALLING Lean before installing, and the judge
//! verifies it a second time on every single run (`Judged.admissionChecks`), so a
//! secret installed here that does not open its commitment cannot settle anything —
//! it can only fail closed.

use ed25519_dalek::{Signature, VerifyingKey};
use redb::{ReadableTable, ReadableTableMetadata, TableDefinition, WriteTransaction};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{PersistentStore, Result, StoreError};

pub(crate) const POA_SIGNAL_SLOT_V1: TableDefinition<&[u8], &[u8]> =
    TableDefinition::new("poa_signal_slot_v1");
pub(crate) const POA_SIGNAL_OPEN_SLOT_V1: TableDefinition<&[u8], u64> =
    TableDefinition::new("poa_signal_open_slot_v1");

/// Schema string covered by the curator's signature.
pub const POA_SLOT_OPENING_STATEMENT_SCHEMA_V1: &str = "POA-SLOT-OPENING-STATEMENT-1";

/// The coordinates a curator signs to open one slot.
///
/// `commitment` is `HiddenInstance.commit secret slot` — a function of the secret
/// and the slot ALONE. It takes no player and no mission, so publishing it tells a
/// reader nothing about any particular run beyond which slot it belongs to. Its
/// binding strength is the sponge capacity, eight lanes, about 248 bits: roughly
/// 2^124 to find a colliding secret. That is the number to quote, not 2^248.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaSlotOpeningStatementV1 {
    schema: String,
    authority_id: [u8; 32],
    mission_id: u64,
    slot: u64,
    commitment: [u8; 32],
}

impl PoaSlotOpeningStatementV1 {
    pub fn new(authority_id: [u8; 32], mission_id: u64, slot: u64, commitment: [u8; 32]) -> Self {
        Self {
            schema: POA_SLOT_OPENING_STATEMENT_SCHEMA_V1.to_owned(),
            authority_id,
            mission_id,
            slot,
            commitment,
        }
    }

    pub const fn authority_id(&self) -> [u8; 32] {
        self.authority_id
    }

    pub const fn mission_id(&self) -> u64 {
        self.mission_id
    }

    pub const fn slot(&self) -> u64 {
        self.slot
    }

    pub const fn commitment(&self) -> [u8; 32] {
        self.commitment
    }

    /// Exact canonical bytes the curator signs: compact, key-ordered JSON.
    ///
    /// Signing anything else — the envelope file, a pretty-printed statement, a
    /// digest of the statement — produces a signature this module refuses.
    pub fn signing_message(&self) -> Result<Vec<u8>> {
        if self.schema != POA_SLOT_OPENING_STATEMENT_SCHEMA_V1 {
            return Err(integrity("PoA slot opening statement has a foreign schema"));
        }
        Ok(format!(
            "{{\"schema\":\"{}\",\"authority_id\":\"{}\",\"mission_id\":{},\"slot\":{},\"commitment\":\"{}\"}}",
            POA_SLOT_OPENING_STATEMENT_SCHEMA_V1,
            hex(&self.authority_id),
            self.mission_id,
            self.slot,
            hex(&self.commitment),
        )
        .into_bytes())
    }
}

/// A slot opening plus the curator signature over its statement.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SignedPoaSlotOpeningEnvelopeV1 {
    statement: PoaSlotOpeningStatementV1,
    curator_key: [u8; 32],
    signature: Vec<u8>,
}

impl SignedPoaSlotOpeningEnvelopeV1 {
    pub fn new(
        statement: PoaSlotOpeningStatementV1,
        curator_key: [u8; 32],
        signature: [u8; 64],
    ) -> Self {
        Self {
            statement,
            curator_key,
            signature: signature.to_vec(),
        }
    }

    pub const fn statement(&self) -> &PoaSlotOpeningStatementV1 {
        &self.statement
    }

    pub const fn curator_key(&self) -> [u8; 32] {
        self.curator_key
    }

    pub fn signature(&self) -> &[u8] {
        &self.signature
    }

    /// Verify against the pin the store already trusts. The envelope's own
    /// `curator_key` is never trusted on its own: a self-consistent envelope
    /// signed by an attacker key is exactly what the pin exists to refuse.
    fn verify_signature(&self, external_curator_key_pin: [u8; 32]) -> Result<()> {
        if self.curator_key != external_curator_key_pin {
            return Err(integrity(
                "PoA slot opening names a curator key that is not the installed pin",
            ));
        }
        if self.signature.len() != 64 {
            return Err(integrity(
                "PoA slot opening signature must contain exactly 64 bytes",
            ));
        }
        let key = VerifyingKey::from_bytes(&self.curator_key)
            .map_err(|_| integrity("PoA slot opening curator key is not a valid Ed25519 key"))?;
        let signature_bytes: [u8; 64] = self
            .signature
            .as_slice()
            .try_into()
            .map_err(|_| integrity("PoA slot opening signature has wrong length"))?;
        key.verify_strict(
            &self.statement.signing_message()?,
            &Signature::from_bytes(&signature_bytes),
        )
        .map_err(|_| integrity("PoA slot opening signature verification failed"))
    }
}

/// One installed slot: the curator's signed opening plus the secret that opens it.
///
/// ⚠ While the slot is LIVE, `secret` must never leave the node. No output wire,
/// descriptor, catalog or authority export renders it, and `Emit` has no function
/// that could. It is handed to the Lean judge — which needs it to re-derive the run
/// seed — and nowhere else.
///
/// ⚑ **The one exception, and it is the point of the commitment.** Once the slot is
/// CLOSED — strictly superseded, so it can settle nothing —
/// [`PersistentStore::load_poa_signal_slot_reveal_v1`] publishes the secret as a
/// [`PoaSlotRevealV1`], which is what the descriptors' `opened_after: "slot-close"`
/// promises and what lets a player check the instance they were judged against was
/// fixed before they played. That accessor holds the closure gate; this type's
/// [`Self::secret`] is still the live value and still must not reach a wire.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaInstalledSlotV1 {
    envelope: SignedPoaSlotOpeningEnvelopeV1,
    secret: [u8; 32],
}

impl PoaInstalledSlotV1 {
    pub const fn envelope(&self) -> &SignedPoaSlotOpeningEnvelopeV1 {
        &self.envelope
    }

    pub const fn slot(&self) -> u64 {
        self.envelope.statement.slot
    }

    pub const fn mission_id(&self) -> u64 {
        self.envelope.statement.mission_id
    }

    pub const fn commitment(&self) -> [u8; 32] {
        self.envelope.statement.commitment
    }

    /// The curator's per-slot secret. Callers must treat this as key material.
    pub const fn secret(&self) -> [u8; 32] {
        self.secret
    }

    /// Raw construction for cross-crate fixtures only.
    ///
    /// ⚠ This bypasses the curator signature AND the Lean commitment check, so a
    /// value built here is NOT evidence that a curator opened anything. It exists
    /// because the alternative — making tests mint curator signatures — would put a
    /// signing path in the node. Nothing outside a test may construct one.
    #[cfg(feature = "test-support")]
    #[doc(hidden)]
    pub fn new_for_test(envelope: SignedPoaSlotOpeningEnvelopeV1, secret: [u8; 32]) -> Self {
        Self { envelope, secret }
    }
}

/// One CLOSED slot, opened: the signed opening players were handed BEFORE they
/// played, plus the secret that opens its commitment.
///
/// ⚠ This is the one type in the crate that is BUILT to carry the secret outward.
/// It is only ever produced by [`PersistentStore::load_poa_signal_slot_reveal_v1`],
/// which produces it only for a slot the store can show is superseded.
///
/// # Why it needs no signature of its own
///
/// The reveal is self-authenticating and that is the point of a commitment. The
/// `envelope` inside it is the curator's original Ed25519 signature over
/// `(authority_id, mission_id, slot, commitment)` — the same bytes published
/// before the slot opened — and the secret either satisfies
/// `HiddenInstance.commit secret slot == commitment` or it does not. A malicious
/// relay can withhold this document or corrupt it, but it cannot forge one: to
/// substitute a different secret it would have to find a second preimage of a
/// curator-signed commitment, which is the sponge capacity (~2^124). So a verifier
/// needs nothing from the node it fetched this from — no TLS trust, no honesty, no
/// second signature — only the curator pin it already had.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaSlotRevealV1 {
    envelope: SignedPoaSlotOpeningEnvelopeV1,
    secret: [u8; 32],
    closed_by_slot: u64,
}

impl PoaSlotRevealV1 {
    pub const fn envelope(&self) -> &SignedPoaSlotOpeningEnvelopeV1 {
        &self.envelope
    }

    pub const fn slot(&self) -> u64 {
        self.envelope.statement.slot
    }

    pub const fn mission_id(&self) -> u64 {
        self.envelope.statement.mission_id
    }

    pub const fn commitment(&self) -> [u8; 32] {
        self.envelope.statement.commitment
    }

    /// The now-published per-slot secret. It stopped being key material when the
    /// slot closed: every run it could answer has already been settled.
    pub const fn secret(&self) -> [u8; 32] {
        self.secret
    }

    /// The open slot that superseded this one — the store's evidence of closure.
    pub const fn closed_by_slot(&self) -> u64 {
        self.closed_by_slot
    }
}

/// What the store will say about a request to open one slot.
///
/// Three answers rather than an `Option`, because "no such slot" and "that slot is
/// still live" are different facts and a client that cannot tell them apart cannot
/// tell a typo from a withheld secret.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PoaSlotRevealStatusV1 {
    /// No slot with these coordinates is installed for this authority.
    Unknown,
    /// The slot is installed but NOT closed. The secret is withheld: it is the
    /// answer to every run currently being played in it.
    StillOpen { open_slot: u64 },
    /// The slot is closed, and this opens it.
    Revealed(PoaSlotRevealV1),
}

/// Outcome of one install attempt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoaSlotInstallStatusV1 {
    /// The slot was not present and is now installed.
    Installed,
    /// An identical opening and secret were already installed. Re-running a
    /// ceremony is not an error.
    AlreadyInstalled,
}

fn slot_key(authority_id: [u8; 32], slot: u64) -> Vec<u8> {
    let mut key = Vec::with_capacity(40);
    key.extend_from_slice(&authority_id);
    key.extend_from_slice(&slot.to_be_bytes());
    key
}

pub(crate) fn initialize_poa_signal_slot_tables_v1_in(write: &WriteTransaction) -> Result<()> {
    let _ = write.open_table(POA_SIGNAL_SLOT_V1)?;
    let _ = write.open_table(POA_SIGNAL_OPEN_SLOT_V1)?;
    Ok(())
}

impl PersistentStore {
    /// Install one curator-signed slot opening together with the secret that
    /// opens it.
    ///
    /// Three refusals, in order: the curator signature must verify against the
    /// installed pin; the secret must actually OPEN the published commitment; and
    /// the slot must strictly advance. The middle one is a Lean call
    /// (`HiddenInstance.commit`) — persist holds no sponge of its own — and it lives
    /// HERE rather than in the operator command so that no other caller can reach
    /// storage around it.
    pub fn install_poa_signal_slot_v1(
        &self,
        envelope: &SignedPoaSlotOpeningEnvelopeV1,
        secret: [u8; 32],
    ) -> Result<PoaSlotInstallStatusV1> {
        let pin = self.load_poa_world_curator_pin_v1()?.ok_or_else(|| {
            integrity(
                "PoA curator pin is not installed; a slot cannot be opened before the curator \
                 key this store trusts is pinned",
            )
        })?;
        envelope.verify_signature(pin)?;
        verify_secret_opens_commitment(
            secret,
            envelope.statement.slot,
            envelope.statement.commitment,
        )?;

        let authority_id = envelope.statement.authority_id;
        let slot = envelope.statement.slot;
        let record = PoaInstalledSlotV1 {
            envelope: envelope.clone(),
            secret,
        };
        let encoded = postcard::to_stdvec(&record)
            .map_err(|error| integrity(format!("cannot encode PoA slot record: {error}")))?;

        let write = self.db.begin_write()?;
        let status = {
            let mut slots = write.open_table(POA_SIGNAL_SLOT_V1)?;
            let key = slot_key(authority_id, slot);
            if let Some(existing) = slots.get(key.as_slice())? {
                let existing: PoaInstalledSlotV1 =
                    postcard::from_bytes(existing.value()).map_err(|error| {
                        integrity(format!("stored PoA slot record is unreadable: {error}"))
                    })?;
                if existing != record {
                    return Err(integrity(
                        "PoA slot is already installed with a different opening or secret; \
                         refusing substitution",
                    ));
                }
                PoaSlotInstallStatusV1::AlreadyInstalled
            } else {
                let mut open = write.open_table(POA_SIGNAL_OPEN_SLOT_V1)?;
                if let Some(current) = open.get(authority_id.as_slice())? {
                    let current = current.value();
                    if slot <= current {
                        return Err(integrity(format!(
                            "PoA slot {slot} does not advance the open slot {current}; slots are \
                             totally ordered per authority"
                        )));
                    }
                }
                slots.insert(key.as_slice(), encoded.as_slice())?;
                open.insert(authority_id.as_slice(), slot)?;
                PoaSlotInstallStatusV1::Installed
            }
        };
        write.commit()?;
        Ok(status)
    }

    /// Insert an installed slot with NO curator signature and NO Lean commitment
    /// check, for cross-crate fixtures only.
    ///
    /// ⚠ This is the storage write with all three refusals removed. It exists
    /// because the alternative — fixtures minting curator signatures — would put a
    /// curator signing path in the node, and because the commitment check needs a
    /// linked archive that some test lanes do not have. Nothing outside a test may
    /// call it, and a slot placed this way is not evidence that a curator opened
    /// anything.
    #[cfg(feature = "test-support")]
    #[doc(hidden)]
    pub fn install_poa_signal_slot_for_test(&self, record: &PoaInstalledSlotV1) -> Result<()> {
        let authority_id = record.envelope.statement.authority_id;
        let slot = record.envelope.statement.slot;
        let encoded = postcard::to_stdvec(record)
            .map_err(|error| integrity(format!("cannot encode PoA slot record: {error}")))?;
        let write = self.db.begin_write()?;
        {
            let mut slots = write.open_table(POA_SIGNAL_SLOT_V1)?;
            let mut open = write.open_table(POA_SIGNAL_OPEN_SLOT_V1)?;
            slots.insert(slot_key(authority_id, slot).as_slice(), encoded.as_slice())?;
            open.insert(authority_id.as_slice(), slot)?;
        }
        write.commit()?;
        Ok(())
    }

    /// Load one installed slot by its coordinates.
    pub fn load_poa_signal_slot_v1(
        &self,
        authority_id: [u8; 32],
        slot: u64,
    ) -> Result<Option<PoaInstalledSlotV1>> {
        let read = self.db.begin_read()?;
        let slots = read.open_table(POA_SIGNAL_SLOT_V1)?;
        let key = slot_key(authority_id, slot);
        let Some(found) = slots.get(key.as_slice())? else {
            return Ok(None);
        };
        postcard::from_bytes(found.value())
            .map(Some)
            .map_err(|error| integrity(format!("stored PoA slot record is unreadable: {error}")))
    }

    /// The authority's currently open slot, if any has been opened.
    ///
    /// A node with no open slot cannot serve a scored run at all. That is the
    /// intended posture: a run played against no committed instance is a run whose
    /// answer nobody promised in advance.
    pub fn load_poa_signal_open_slot_v1(
        &self,
        authority_id: [u8; 32],
    ) -> Result<Option<PoaInstalledSlotV1>> {
        let read = self.db.begin_read()?;
        let open = read.open_table(POA_SIGNAL_OPEN_SLOT_V1)?;
        let Some(slot) = open.get(authority_id.as_slice())? else {
            return Ok(None);
        };
        drop(open);
        self.load_poa_signal_slot_v1(authority_id, slot.value())
    }

    /// **THE SLOT-CLOSE OPENING.** Hand back the secret of a slot that is CLOSED,
    /// and refuse for one that is not.
    ///
    /// This is the read the descriptors' `opened_after: "slot-close"` names, and it
    /// is the only path by which a slot secret is allowed to leave the node. The
    /// gate lives HERE, beside the write that establishes closure, for the same
    /// reason `install_poa_signal_slot_v1` keeps the commitment check in persist:
    /// so that no route, export or command can reach the secret around it.
    ///
    /// # What "closed" means, and why it needs no new record
    ///
    /// `install_poa_signal_slot_v1` refuses a slot that does not STRICTLY advance
    /// the authority's open slot, so slots are totally ordered and
    /// `POA_SIGNAL_OPEN_SLOT_V1` holds the greatest one installed. A slot is
    /// therefore closed exactly when it is strictly less than that pointer —
    /// superseded, its runs no longer settleable. No new signed object, no clock and
    /// no operator assertion is involved: closure is a fact already forced by the
    /// monotone install, which is what makes it checkable rather than announced.
    ///
    /// ⚠ **The consequence, stated rather than hidden:** the CURRENT slot is never
    /// closed, so an authority that stops opening slots never opens its last one.
    /// Withholding is then visible — the publication route keeps reporting that slot
    /// as open — but it is not prevented. Forcing a reveal needs a deadline someone
    /// other than the operator can enforce, and this store has no such clock.
    ///
    /// # Fail-closed
    ///
    /// Every path that is not provably "this slot is strictly below the open
    /// pointer" withholds: a missing pointer, an unreadable record, a slot equal to
    /// or above the pointer. A corrupt store loses the reveal; it does not leak a
    /// live secret.
    pub fn load_poa_signal_slot_reveal_v1(
        &self,
        authority_id: [u8; 32],
        slot: u64,
    ) -> Result<PoaSlotRevealStatusV1> {
        let read = self.db.begin_read()?;
        let open = read.open_table(POA_SIGNAL_OPEN_SLOT_V1)?;
        // No pointer at all ⇒ nothing has ever been opened for this authority, so
        // nothing can be closed. Withhold rather than fall through to the record.
        let Some(open_slot) = open.get(authority_id.as_slice())? else {
            return Ok(PoaSlotRevealStatusV1::Unknown);
        };
        let open_slot = open_slot.value();
        drop(open);
        drop(read);

        let Some(installed) = self.load_poa_signal_slot_v1(authority_id, slot)? else {
            return Ok(PoaSlotRevealStatusV1::Unknown);
        };
        // ⚠ THE REDACTION GATE. `>=` and not `>`: the open slot itself is live, and
        // its secret is the answer to every run currently being played.
        if slot >= open_slot {
            return Ok(PoaSlotRevealStatusV1::StillOpen { open_slot });
        }
        Ok(PoaSlotRevealStatusV1::Revealed(PoaSlotRevealV1 {
            envelope: installed.envelope,
            secret: installed.secret,
            closed_by_slot: open_slot,
        }))
    }

    /// Structural audit: every open-slot pointer resolves, and every stored record
    /// is readable and self-consistent with its key.
    pub fn audit_poa_signal_slots_v1(&self) -> Result<()> {
        let read = self.db.begin_read()?;
        let slots = read.open_table(POA_SIGNAL_SLOT_V1)?;
        for entry in slots.iter()? {
            let (key, value) = entry?;
            let key = key.value();
            if key.len() != 40 {
                return Err(integrity("PoA slot key is not authority_id||slot_be64"));
            }
            let record: PoaInstalledSlotV1 =
                postcard::from_bytes(value.value()).map_err(|error| {
                    integrity(format!("stored PoA slot record is unreadable: {error}"))
                })?;
            let mut authority_id = [0u8; 32];
            authority_id.copy_from_slice(&key[..32]);
            let mut slot_bytes = [0u8; 8];
            slot_bytes.copy_from_slice(&key[32..]);
            if record.envelope.statement.authority_id != authority_id
                || record.envelope.statement.slot != u64::from_be_bytes(slot_bytes)
            {
                return Err(integrity(
                    "stored PoA slot record does not match the coordinates it is filed under",
                ));
            }
        }
        let open = read.open_table(POA_SIGNAL_OPEN_SLOT_V1)?;
        if open.len()? > 0 {
            for entry in open.iter()? {
                let (authority, slot) = entry?;
                let authority = authority.value();
                if authority.len() != 32 {
                    return Err(integrity("PoA open-slot key is not an authority id"));
                }
                let key = {
                    let mut key = authority.to_vec();
                    key.extend_from_slice(&slot.value().to_be_bytes());
                    key
                };
                if slots.get(key.as_slice())?.is_none() {
                    return Err(integrity(
                        "PoA open-slot pointer names a slot that is not installed",
                    ));
                }
            }
        }
        Ok(())
    }
}

/// Ask Lean whether this secret opens this commitment.
///
/// ⚠ The comparison is between two values Lean produced and one the curator
/// published; Rust does no sponge arithmetic. Absent the export the answer is
/// UNAVAILABLE, and an unavailable answer is a refusal — installing a secret whose
/// commitment nobody checked would hand the node an instance the curator never
/// promised, which is the whole thing the commitment exists to prevent.
fn verify_secret_opens_commitment(secret: [u8; 32], slot: u64, commitment: [u8; 32]) -> Result<()> {
    // The derivation wire needs a mission context and a player; the commitment
    // itself is a function of (secret, slot) ALONE, so these are the neutral values
    // `HiddenInstance.commit` provably ignores. Only `commitment` is read back.
    let wire = format!(
        "{{\"format\":\"{}\",\"slot\":{},\"secret\":\"{}\",\"mission_id\":0,\"epoch\":0,\
         \"federation_id\":\"{}\",\"content_session\":\"{}\",\"player_key\":\"{}\"}}",
        dregg_lean_ffi::poa_slot_derive_ffi::SLOT_DERIVE_INPUT_FORMAT,
        slot,
        hex(&secret),
        hex(&[0u8; 32]),
        hex(&[0u8; 32]),
        hex(&[0u8; 32]),
    );
    let reply = dregg_lean_ffi::poa_slot_derive_ffi::derive_poa_slot_instance(&wire)
        .map_err(|error| {
            integrity(format!(
                "cannot verify that the slot secret opens its published commitment: {error}"
            ))
        })?
        .ok_or_else(|| {
            integrity("Lean refused the slot commitment derivation for this secret and slot")
        })?;
    let parsed: serde_json::Value = serde_json::from_str(&reply)
        .map_err(|error| integrity(format!("Lean slot derivation reply is not JSON: {error}")))?;
    let derived = parsed
        .get("commitment")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| integrity("Lean slot derivation reply lacks a commitment"))?;
    if derived != hex(&commitment) {
        return Err(integrity(
            "the slot secret does not open the commitment the curator published; refusing to \
             install an instance nobody committed to",
        ));
    }
    Ok(())
}

/// Digest of one installed slot record, for ceremony reports.
pub fn poa_slot_record_digest(record: &PoaInstalledSlotV1) -> Result<[u8; 32]> {
    let encoded = postcard::to_stdvec(record)
        .map_err(|error| integrity(format!("cannot encode PoA slot record: {error}")))?;
    Ok(sha256(&encoded))
}

fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(char::from_digit(u32::from(byte >> 4), 16).unwrap_or('0'));
        out.push(char::from_digit(u32::from(byte & 0x0f), 16).unwrap_or('0'));
    }
    out
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn integrity(message: impl Into<String>) -> StoreError {
    StoreError::Integrity(message.into())
}

#[cfg(test)]
mod slot_close_tests {
    use super::*;

    /// ⚑ **WHY THESE ARE UNIT TESTS AND SEED STORAGE DIRECTLY.**
    ///
    /// The gate under test — [`PersistentStore::load_poa_signal_slot_reveal_v1`] —
    /// decides whether a slot SECRET leaves the node. It is the highest-stakes
    /// predicate in this file and it involves no cryptography at all: it is a
    /// comparison against the open-slot pointer.
    ///
    /// Reaching it through `install_poa_signal_slot_v1` would drag in
    /// `HiddenInstance.commit` and make the redaction gate untestable whenever the
    /// Lean archive is unavailable — which is precisely when a red suite is most
    /// likely to be waved through. (Measured 2026-08-09: every Lean-calling test in
    /// this crate times out at 180s while the non-Lean tests pass in milliseconds.)
    ///
    /// So these seed the two tables directly, from inside the module that owns
    /// them, and assert only about the gate. That the secret OPENS the commitment
    /// is a different property, checked by the install path and by
    /// `dregg-node poa-verify-slot-reveal`.
    const AUTHORITY: [u8; 32] = [0xa4; 32];
    const OTHER_AUTHORITY: [u8; 32] = [0xb7; 32];
    const CURATOR: [u8; 32] = [0xc0; 32];

    fn secret_for(slot: u64) -> [u8; 32] {
        // Distinct per slot, so a leak names the slot it came from.
        [(slot as u8).wrapping_mul(17).wrapping_add(3); 32]
    }

    fn record_for(authority: [u8; 32], slot: u64) -> PoaInstalledSlotV1 {
        let statement =
            PoaSlotOpeningStatementV1::new(authority, 1, slot, [(slot as u8) ^ 0x5a; 32]);
        PoaInstalledSlotV1 {
            envelope: SignedPoaSlotOpeningEnvelopeV1::new(statement, CURATOR, [0x11; 64]),
            secret: secret_for(slot),
        }
    }

    /// Place a slot row and (optionally) point the authority's open slot at it,
    /// exactly as `install_poa_signal_slot_v1` would, minus every check.
    fn seed(store: &PersistentStore, authority: [u8; 32], slot: u64, make_open: bool) {
        let record = record_for(authority, slot);
        let encoded = postcard::to_stdvec(&record).expect("encode");
        let write = store.db.begin_write().expect("write txn");
        {
            let mut slots = write.open_table(POA_SIGNAL_SLOT_V1).expect("slots table");
            slots
                .insert(slot_key(authority, slot).as_slice(), encoded.as_slice())
                .expect("insert slot");
            if make_open {
                let mut open = write
                    .open_table(POA_SIGNAL_OPEN_SLOT_V1)
                    .expect("open table");
                open.insert(authority.as_slice(), slot)
                    .expect("insert open");
            }
        }
        write.commit().expect("commit");
    }

    /// ⚑ **POLE ONE — a CLOSED slot opens, and carries the secret and its proof of
    /// closure.**
    #[test]
    fn a_superseded_slot_is_revealed_with_its_secret_and_its_closing_slot() {
        let store = PersistentStore::open_in_memory().expect("in-memory store");
        seed(&store, AUTHORITY, 9, false);
        seed(&store, AUTHORITY, 10, true);

        let status = store
            .load_poa_signal_slot_reveal_v1(AUTHORITY, 9)
            .expect("store read");
        let PoaSlotRevealStatusV1::Revealed(reveal) = status else {
            panic!("a superseded slot must open, got {status:?}");
        };
        assert_eq!(reveal.slot(), 9);
        assert_eq!(reveal.secret(), secret_for(9));
        assert_eq!(
            reveal.closed_by_slot(),
            10,
            "the reveal must carry the slot that closed it — the store's evidence of closure"
        );
        assert_eq!(reveal.commitment(), record_for(AUTHORITY, 9).commitment());
        assert_eq!(reveal.envelope().curator_key(), CURATOR);
    }

    /// ⚑ **POLE TWO — the LIVE slot is WITHHELD, and the refusal cannot carry the
    /// secret.**
    ///
    /// This is the whole redaction gate. The live secret is the answer to every run
    /// currently in flight; publishing it would let anyone compute the instance of
    /// a session that has not finished.
    ///
    /// The precondition is asserted before the verdict is read — slot 9 IS present
    /// and IS the open pointer — so the refusal is about closure, not about a
    /// missing row.
    #[test]
    fn the_live_slot_is_withheld_and_no_variant_can_carry_its_secret() {
        let store = PersistentStore::open_in_memory().expect("in-memory store");
        seed(&store, AUTHORITY, 9, true);
        assert!(
            store
                .load_poa_signal_slot_v1(AUTHORITY, 9)
                .expect("store read")
                .is_some(),
            "the precondition is that slot 9 EXISTS; without it the refusal below would \
             be about a missing row"
        );

        let status = store
            .load_poa_signal_slot_reveal_v1(AUTHORITY, 9)
            .expect("store read");
        assert_eq!(
            status,
            PoaSlotRevealStatusV1::StillOpen { open_slot: 9 },
            "the open slot must be withheld"
        );
        // Structural, not a filter: `StillOpen` has no field that could hold a
        // secret, so there is no redaction to forget. Belt and braces anyway —
        // the debug rendering of the refusal must not contain the secret.
        let rendered = format!("{status:?}");
        let leaked = hex(&secret_for(9));
        assert!(
            !rendered.contains(&leaked),
            "the refusal rendered the live secret: {rendered}"
        );
    }

    /// A slot ABOVE the open pointer is withheld too. `install` forbids it, so this
    /// is a corrupted or hand-edited store — and the gate must fail closed on it
    /// rather than treat "not less than" as "greater than".
    #[test]
    fn a_slot_above_the_open_pointer_is_withheld_not_revealed() {
        let store = PersistentStore::open_in_memory().expect("in-memory store");
        seed(&store, AUTHORITY, 4, true);
        seed(&store, AUTHORITY, 9, false); // filed above the pointer, no advance

        let status = store
            .load_poa_signal_slot_reveal_v1(AUTHORITY, 9)
            .expect("store read");
        assert_eq!(status, PoaSlotRevealStatusV1::StillOpen { open_slot: 4 });
    }

    /// ⚑ **FAIL-CLOSED — a slot row with NO open pointer reveals nothing.**
    ///
    /// A corrupt store loses the reveal; it does not leak. If the pointer read were
    /// ever relaxed to "no pointer means everything is closed", every secret in the
    /// table would publish at once.
    #[test]
    fn a_row_with_no_open_pointer_reveals_nothing() {
        let store = PersistentStore::open_in_memory().expect("in-memory store");
        seed(&store, AUTHORITY, 9, false);

        let status = store
            .load_poa_signal_slot_reveal_v1(AUTHORITY, 9)
            .expect("store read");
        assert_eq!(
            status,
            PoaSlotRevealStatusV1::Unknown,
            "with no open pointer nothing is provably closed, so nothing opens"
        );
    }

    /// An uninstalled coordinate is `Unknown`, distinct from a withheld one: a
    /// client must be able to tell a typo from a secret being kept back.
    #[test]
    fn an_uninstalled_slot_is_unknown_rather_than_withheld() {
        let store = PersistentStore::open_in_memory().expect("in-memory store");
        seed(&store, AUTHORITY, 9, false);
        seed(&store, AUTHORITY, 10, true);

        assert_eq!(
            store
                .load_poa_signal_slot_reveal_v1(AUTHORITY, 3)
                .expect("store read"),
            PoaSlotRevealStatusV1::Unknown
        );
        // ...while 9 still opens, or the assertion above would pass for the wrong
        // reason.
        assert!(matches!(
            store
                .load_poa_signal_slot_reveal_v1(AUTHORITY, 9)
                .expect("store read"),
            PoaSlotRevealStatusV1::Revealed(_)
        ));
    }

    /// One authority's pointer must never open another authority's slot.
    #[test]
    fn an_authoritys_pointer_does_not_open_another_authoritys_slot() {
        let store = PersistentStore::open_in_memory().expect("in-memory store");
        // OTHER has advanced well past 9; AUTHORITY has only slot 9, still live.
        seed(&store, OTHER_AUTHORITY, 9, false);
        seed(&store, OTHER_AUTHORITY, 99, true);
        seed(&store, AUTHORITY, 9, true);

        assert_eq!(
            store
                .load_poa_signal_slot_reveal_v1(AUTHORITY, 9)
                .expect("store read"),
            PoaSlotRevealStatusV1::StillOpen { open_slot: 9 },
            "AUTHORITY's live slot must not be opened by OTHER's advanced pointer"
        );
        // ...and OTHER's own slot 9 does open, so the isolation is two-sided.
        assert!(matches!(
            store
                .load_poa_signal_slot_reveal_v1(OTHER_AUTHORITY, 9)
                .expect("store read"),
            PoaSlotRevealStatusV1::Revealed(_)
        ));
    }
}
