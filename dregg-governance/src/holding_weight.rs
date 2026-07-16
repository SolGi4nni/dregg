//! # Proof-of-holding → governance weight, NON-CUSTODIALLY (the missing spine)
//!
//! This is the primitive named missing in `docs/FINDING-chain-participation-census.md`
//! §5.1: *"prove an account I control held ≥ W $DREGG at snapshot S on chain C, into a
//! `VoterId` binding."* It takes a consensus-proven Solana holding
//! ([`dregg_bridge::solana_holdings::ProvenHolding`]) and grants the bound dregg
//! [`VoterId`] vote weight equal to the proven balance — **without the holder moving,
//! locking, escrowing, or wrapping anything.** The tokens stay in the holder's own SPL
//! account; dregg reads a proof over that account and grants weight by proof.
//!
//! ## Why this is the dreggic (non-custodial) shape
//!
//! The lock-and-mirror path (`solana_mirror`) makes a holder surrender custody into a
//! vault to import *spendable* value. That is the WRONG mechanism for *participation*:
//! to vote, no one should have to give up custody. Here the input is a
//! [`ProvenHolding`] — a snapshot proven over the holder's OWN account via dregg's
//! Solana light client (stake-weighted ≥2/3 Ed25519 supermajority on a bank hash +
//! accounts-Merkle inclusion). Granting weight from it moves NO value, holds NO escrow,
//! and requires NO lock. It is purely proof → weight. **If a design needs the holder to
//! lock or transfer to get weight, it is wrong for this lane.**
//!
//! ## Fail-closed (the Nomad-law analog)
//!
//! Weight is granted ONLY when [`ProvenHolding::is_consensus_proven`] is true — i.e. the
//! holding is backed by a real Solana supermajority over a finalized bank hash. A
//! [`LockProofTrust::StructureOnly`](dregg_bridge::solana_trustless::LockProofTrust)
//! holding (a plain-RPC echo) grants ZERO — it is [`GrantError::NotConsensusProven`],
//! never weight. This is the same fail-closed rule the mint gate uses.
//!
//! ## The owner→voter binding
//!
//! A Solana wallet pubkey is an Ed25519 public key, and a dregg [`VoterId`] is likewise
//! an Ed25519 key. The binding is the **simplest sound one**: an Ed25519 signature *by
//! the holding's owner wallet* over a domain-separated message committing to the target
//! [`VoterId`] (see [`binding_message`]). Verifying it proves the owner authorized that
//! `VoterId` to wield the holding's weight — no registry, no trusted third party, self-
//! verifiable from the proof alone. A missing or wrong signature is
//! [`GrantError::UnboundOwner`] and grants nothing (fail closed). The binding is durable
//! (owner→voter, reusable across polls and holdings); per-poll uniqueness is enforced
//! separately by the nullifier below.
//!
//! ## Snapshot + no-double-count
//!
//! The granted weight is the balance proven **as of the finalized snapshot slot**
//! ([`ProvenHolding::slot`]) — a holding proven at slot S grants S-vintage weight, and
//! the [`WeightGrant`] carries that slot so a poll can pin an as-of-S electorate. Within
//! one poll, the same SPL token account must not grant weight twice: the
//! [`HoldingWeightRegistry`] keeps a per-`(poll, token_account)` nullifier set (the
//! consume-once, nullifier-shaped guard). Re-presenting the same account into the same
//! poll is [`GrantError::AlreadyCounted`]. A different poll, or a different token
//! account, is a distinct nullifier and is allowed.

//!
//! ## Cross-chain: the ONE weight binding
//!
//! The same spine now runs for ANY chain via the chain-agnostic
//! [`ProvenForeignHolding`](crate::proven_foreign_holding::ProvenForeignHolding):
//! [`grant_foreign_weight`] is the generic fail-closed core (consensus verdict →
//! owner binding → positive amount → the Lean-proven weight verdict), and the
//! Solana-specific [`grant_weight`] is a thin wrapper over it (`From` + the
//! generic). The registry pins a snapshot **per (poll, chain)** and consumes a
//! per-`(poll, chain+holder+asset)` nullifier — so the same holder on two
//! different chains — or two different NETWORKS of one family, Base vs Ethereum
//! ([`ChainId::Evm`] carries the EIP-155 chain id) — is two DISTINCT facts (both
//! count; a holder legitimately holds on both), while re-presenting one network's
//! holding twice is refused.
//!
//! The owner→voter binding is likewise per-family — the trilogy is complete, so a
//! holder on ANY of the three families binds with their own wallet key:
//!
//! - **Solana**: the Ed25519 [`OwnerBinding`] (unchanged);
//! - **EVM**: `holder` is a left-zero-padded 20-byte keccak address, NOT an Ed25519
//!   key — binds natively with the wallet's secp256k1 key via [`EvmOwnerBinding`]
//!   (EIP-191 `personal_sign` + ECDSA public-key recovery);
//! - **Cosmos**: `holder` is a left-zero-padded 20-byte
//!   `ripemd160(sha256(pubkey))` account address (bech32 is only its display
//!   encoding) — binds natively with the wallet's secp256k1 key via
//!   [`CosmosOwnerBinding`], which CARRIES the 33-byte compressed pubkey (an
//!   address is a hash, so there is no recovery trick: verify under the carried
//!   key, then require the key's derived address == holder).
//!
//! [`grant_foreign_weight`] accepts any form through the [`HolderBinding`]
//! dispatch, which ties each form to the holding's chain/holder SHAPE (Solana
//! stays Ed25519-only; an EVM signature can never bind a Solana or Cosmos
//! holding; a Cosmos binding can never bind a Solana or EVM holding).
//!
//! The ballot domain is `u64` ([`VoteBlock::weight`](crate::VoteBlock::weight)) while a foreign grant is `u128`
//! (EVM-scale): [`foreign_grant_and_cast`](HoldingWeightRegistry::foreign_grant_and_cast)
//! narrows through [`narrow_ballot_weight`] — FAIL-CLOSED, a weight above `u64::MAX` is
//! [`GrantError::WeightOverflow`], never a saturating/truncating cast.

use std::collections::{BTreeMap, HashSet};

use ed25519_dalek::{Signature, VerifyingKey};

use dregg_bridge::solana_holdings::ProvenHolding;

use crate::proven_foreign_holding::{ChainId, ProvenForeignHolding};
use crate::{CastOutcome, HostBallotBox, HostVoteEngine, OptionId, PollId, VoterId};
// The verified executor engine's `tally`/`resolve`/`cast` live on its
// `VoteEngine` trait (the inherent weighted methods ride alongside).
use collective_choice::VoteEngine as _;

/// Domain separator for the owner→voter binding signature. Committing to a domain keeps
/// a signature made for this purpose from being replayable as any other Ed25519 message
/// the owner might sign (and vice-versa).
pub const BIND_DOMAIN: &[u8] = b"dregg-holding-weight-bind-v1";

/// The exact bytes the holding **owner** signs to authorize `voter` to wield the
/// owner's holding weight: `BIND_DOMAIN ‖ owner(32) ‖ voter(32)`. Including the `owner`
/// makes the message self-describing; the signature's validity under `owner`'s key is
/// what actually binds it. The message deliberately does NOT commit to a poll or a
/// specific holding — the binding is a durable owner→voter link, and per-poll,
/// per-account uniqueness is the nullifier's job.
pub fn binding_message(owner: &[u8; 32], voter: &VoterId) -> Vec<u8> {
    let mut m = Vec::with_capacity(BIND_DOMAIN.len() + 64);
    m.extend_from_slice(BIND_DOMAIN);
    m.extend_from_slice(owner);
    m.extend_from_slice(voter);
    m
}

/// A holder's authorization of a dregg [`VoterId`] to wield their holding weight: an
/// Ed25519 signature, made by the Solana **owner** wallet key, over
/// [`binding_message`]`(owner, voter)`. Non-custodial: it is a signature, not a
/// transfer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OwnerBinding {
    /// The dregg voter identity the owner authorizes to carry this weight.
    pub voter: VoterId,
    /// The owner wallet's Ed25519 signature over [`binding_message`]`(owner, voter)`.
    pub sig: [u8; 64],
}

/// Verify that `binding` is a genuine authorization by `owner` (a Solana/Ed25519 wallet
/// pubkey) of `binding.voter`. Returns `false` — fail closed — if `owner` is not a valid
/// Ed25519 point or the signature does not verify (strict, malleability-rejecting) over
/// the domain-separated [`binding_message`].
pub fn verify_binding(owner: &[u8; 32], binding: &OwnerBinding) -> bool {
    let vk = match VerifyingKey::from_bytes(owner) {
        Ok(k) => k,
        Err(_) => return false,
    };
    let sig = Signature::from_bytes(&binding.sig);
    let msg = binding_message(owner, &binding.voter);
    vk.verify_strict(&msg, &sig).is_ok()
}

// ─── The EVM (secp256k1) owner→voter binding ────────────────────────────────────
//
// An EVM holder's `ProvenForeignHolding::holder` is NOT an Ed25519 key — it is the
// 20-byte keccak address, left-zero-padded to 32 bytes ([0..12] = 0, [12..32] =
// address). The Ed25519 [`verify_binding`] can never accept it (the holder cannot
// produce an Ed25519 signature under those bytes), so without this path an EVM
// holder could not bind at all. This is the native secp256k1 binding named as the
// follow-up in [`proven_foreign_holding`](crate::proven_foreign_holding): the holder
// signs with the SAME secp256k1 wallet key that controls the holding, via the
// standard EIP-191 `personal_sign` flow every EVM wallet already exposes.

/// Domain separator for the **EVM** owner→voter binding — the secp256k1 sibling of
/// [`BIND_DOMAIN`], versioned independently. (Exactly 32 ASCII bytes.)
pub const EVM_BIND_DOMAIN: &[u8] = b"dregg-holding-weight-bind-evm-v1";

/// The exact **inner** message an EVM holder signs (via EIP-191 `personal_sign`) to
/// authorize `voter`:
///
/// ```text
/// EVM_BIND_DOMAIN(32) ‖ address(20) ‖ voter(32)      — 84 bytes total
/// ```
///
/// where `address` is the holder's raw 20-byte EVM address. As with
/// [`binding_message`], the message commits to the target [`VoterId`] (no replay to
/// another voter) and to the signing address itself, but deliberately NOT to a poll
/// or holding — the binding is a durable owner→voter link; per-poll uniqueness is
/// the nullifier's job. The wallet then signs the EIP-191 framing of these bytes —
/// see [`eip191_message_hash`] for the exact prehash.
pub fn evm_binding_message(address: &[u8; 20], voter: &VoterId) -> Vec<u8> {
    let mut m = Vec::with_capacity(EVM_BIND_DOMAIN.len() + 20 + 32);
    m.extend_from_slice(EVM_BIND_DOMAIN);
    m.extend_from_slice(address);
    m.extend_from_slice(voter);
    m
}

/// The EIP-191 `personal_sign` prehash of `msg` — the 32 bytes an EVM wallet
/// actually signs:
///
/// ```text
/// keccak256( 0x19 ‖ "Ethereum Signed Message:\n" ‖ ascii_decimal(len(msg)) ‖ msg )
/// ```
///
/// For the 84-byte [`evm_binding_message`] the frame is therefore
/// `"\x19Ethereum Signed Message:\n84" ‖ msg`. Using the standard framing (rather
/// than a bare keccak) means any stock wallet's `personal_sign` produces a valid
/// binding, and — because of the `\x19` lead byte — the signed bytes can never be a
/// valid RLP transaction, so a binding signature can never be replayed as a spend.
pub fn eip191_message_hash(msg: &[u8]) -> [u8; 32] {
    use sha3::{Digest, Keccak256};
    let mut h = Keccak256::new();
    h.update(b"\x19Ethereum Signed Message:\n");
    h.update(msg.len().to_string().as_bytes());
    h.update(msg);
    h.finalize().into()
}

/// The canonical EVM address of a secp256k1 public key:
/// `keccak256(uncompressed_pubkey[1..65])[12..32]` — the last 20 bytes of the keccak
/// of the 64-byte (x ‖ y) point, dropping the SEC1 `0x04` prefix.
pub fn evm_address_of_pubkey(vk: &k256::ecdsa::VerifyingKey) -> [u8; 20] {
    use sha3::{Digest, Keccak256};
    let point = vk.to_encoded_point(false);
    let bytes = point.as_bytes(); // 0x04 ‖ x(32) ‖ y(32)
    debug_assert_eq!(bytes.len(), 65, "uncompressed SEC1 point");
    let digest = Keccak256::digest(&bytes[1..]);
    let mut addr = [0u8; 20];
    addr.copy_from_slice(&digest[12..]);
    addr
}

/// Extract the 20-byte EVM address from a 32-byte `holder` field, FAIL-CLOSED: only
/// a correctly left-zero-padded holder (`holder[0..12] == 0`) is an EVM address per
/// the [`ProvenForeignHolding`] convention. Anything else (e.g. an Ed25519 pubkey
/// registered as the holder identity) is `None` — the EVM binding path refuses it
/// rather than treating 20 arbitrary bytes as an address.
pub fn evm_address_of_holder(holder: &[u8; 32]) -> Option<[u8; 20]> {
    if holder[0..12] != [0u8; 12] {
        return None;
    }
    let mut addr = [0u8; 20];
    addr.copy_from_slice(&holder[12..32]);
    Some(addr)
}

/// An EVM holder's authorization of a dregg [`VoterId`]: a 65-byte secp256k1 ECDSA
/// signature, made by the wallet key whose address IS the holding's `holder`, over
/// the EIP-191 prehash of [`evm_binding_message`]`(address, voter)`. Non-custodial:
/// it is a `personal_sign`, not a transaction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvmOwnerBinding {
    /// The dregg voter identity the owner authorizes to carry this weight.
    pub voter: VoterId,
    /// The 65-byte signature in the wallet wire layout `r(32) ‖ s(32) ‖ v(1)`.
    /// `v` is the recovery id, accepted as `0`/`1` or the Ethereum-conventional
    /// `27`/`28` (normalized by subtracting 27). Any other `v` — including `2`/`3`,
    /// the astronomically-unlikely reduced-x forms no wallet emits — is refused.
    /// `s` must be in the low half of the order (BIP-62 low-S, the same rule
    /// Ethereum enforces since EIP-2); a high-S signature is refused as malleable.
    pub sig: [u8; 65],
}

/// Verify that `binding` is a genuine authorization, by the secp256k1 key whose EVM
/// address is embedded in `holder`, of `binding.voter`. FAIL-CLOSED `false` when:
///
/// - `holder` is not a left-zero-padded EVM address (`holder[0..12] != 0`);
/// - `r`/`s` do not parse as nonzero in-range scalars;
/// - `s` is in the high half of the order (the malleable twin — rejected so a third
///   party cannot mint a "different" binding from an observed one);
/// - `v` is not `0`/`1`/`27`/`28`;
/// - public-key recovery fails, or the recovered key does not re-verify;
/// - the recovered key's address differs from the holder address (the wrong signer,
///   or a signature over a different voter — the prehash commits to `binding.voter`,
///   so a replay for another voter recovers a DIFFERENT key ≠ holder).
///
/// The prehash is [`eip191_message_hash`]`(`[`evm_binding_message`]`(address, binding.voter))`
/// — recomputed here from the claimed holder and voter, never taken from the prover.
pub fn verify_evm_binding(holder: &[u8; 32], binding: &EvmOwnerBinding) -> bool {
    use k256::ecdsa::{RecoveryId, Signature as EvmSignature, VerifyingKey as EvmVerifyingKey};

    // FAIL CLOSED: only a genuinely padded EVM address may take this path.
    let Some(address) = evm_address_of_holder(holder) else {
        return false;
    };
    let Ok(sig) = EvmSignature::from_slice(&binding.sig[..64]) else {
        return false; // r or s zero / out of range
    };
    // Reject the malleable high-S twin (normalize_s returns Some IFF s was high).
    if sig.normalize_s().is_some() {
        return false;
    }
    // v: wallet-conventional 27/28 or raw 0/1. NOTHING else — in particular not the
    // reduced-x recovery ids 2/3 (r ≥ order - never produced by real wallets; the
    // strict set keeps the accepted encoding canonical).
    let v = binding.sig[64];
    let recid_byte = match v {
        0 | 1 => v,
        27 | 28 => v - 27,
        _ => return false,
    };
    let Some(recid) = RecoveryId::from_byte(recid_byte) else {
        return false;
    };
    // Recompute the prehash from the CLAIMED (holder, voter) — the commitment to the
    // voter lives here: a signature minted for voter A, presented with voter B,
    // hashes to a different prehash and recovers a key whose address ≠ holder.
    let prehash = eip191_message_hash(&evm_binding_message(&address, &binding.voter));
    // recover_from_prehash re-verifies the signature under the recovered key before
    // returning it (ecdsa 0.16 `recovery.rs`), so a passing recovery IS a verify.
    let Ok(recovered) = EvmVerifyingKey::recover_from_prehash(&prehash, &sig, recid) else {
        return false;
    };
    evm_address_of_pubkey(&recovered) == address
}

// ─── The Cosmos (secp256k1 / bech32-account) owner→voter binding ────────────────
//
// A Cosmos holder's `ProvenForeignHolding::holder` is the 20-byte Cosmos-SDK
// account address — `ripemd160(sha256(compressed_secp256k1_pubkey))` — left-zero-
// padded to 32 bytes by the cosmos-lightclient edge (`cosmos-lightclient/src/
// bank.rs`, `foreign_holding_fields`: `holder[32 - len..] = address`), the same
// padding convention as EVM. The bech32 string (`cosmos1…`) is only the DISPLAY
// encoding of those 20 bytes; the on-wire holder identity is the raw hash.
//
// Unlike EVM there is no public-key RECOVERY trick that both verifies the
// signature and identifies the signer: the Cosmos convention is that a signature
// travels WITH its 33-byte compressed pubkey. So the binding carries the pubkey,
// the signature verifies under it, and the pubkey is then tied to the proven
// account by requiring its derived address to BE the holder address. Skipping
// (or mis-deriving) that hash equality would let ANY keypair "bind" any Cosmos
// holding — it is the load-bearing check of this path.

/// Domain separator for the **Cosmos** owner→voter binding — the third sibling of
/// [`BIND_DOMAIN`] / [`EVM_BIND_DOMAIN`], versioned independently. (35 ASCII bytes.)
pub const COSMOS_BIND_DOMAIN: &[u8] = b"dregg-holding-weight-bind-cosmos-v1";

/// The exact sign bytes a Cosmos holder signs to authorize `voter`:
///
/// ```text
/// COSMOS_BIND_DOMAIN(35) ‖ address(20) ‖ voter(32)      — 87 bytes total
/// ```
///
/// where `address` is the holder's raw 20-byte account address
/// (`ripemd160(sha256(pubkey))` — see [`cosmos_address_of_pubkey`]). As with the
/// other two families, the message commits to the target [`VoterId`] (no replay to
/// another voter) and to the signing address itself, but deliberately NOT to a poll
/// or holding — the binding is a durable owner→voter link; per-poll uniqueness is
/// the nullifier's job. The ECDSA prehash is the SHA-256 of these bytes — see
/// [`cosmos_binding_prehash`] for the exact digest and an honest statement of
/// which scheme this is.
pub fn cosmos_binding_message(address: &[u8; 20], voter: &VoterId) -> Vec<u8> {
    let mut m = Vec::with_capacity(COSMOS_BIND_DOMAIN.len() + 20 + 32);
    m.extend_from_slice(COSMOS_BIND_DOMAIN);
    m.extend_from_slice(address);
    m.extend_from_slice(voter);
    m
}

/// The 32-byte ECDSA prehash a Cosmos holder actually signs:
///
/// ```text
/// SHA-256( COSMOS_BIND_DOMAIN ‖ address(20) ‖ voter(32) )
/// ```
///
/// ## Which scheme this is (honestly)
///
/// This is a **dregg-specific sign doc, NOT ADR-036 amino-JSON**. It keeps the
/// standard Cosmos secp256k1 digest step — ECDSA over the SHA-256 of the sign
/// bytes — but the sign bytes are dregg's fixed 87-byte domain-separated message
/// rather than an amino-JSON `StdSignDoc`. A stock wallet's `signArbitrary`
/// (ADR-036) output will therefore NOT verify here: ADR-036 wraps the payload in
/// a JSON doc whose `signer` field needs the network's bech32 HRP — a
/// prover-supplied display string this binding deliberately does not carry.
/// Wallet-compatible ADR-036 framing is a relayer/UX-edge follow-up; the SECURITY
/// content — the signature commits to exactly `(address, voter)` under a
/// dregg-only domain, so it can never be replayed as a transaction or for another
/// voter — is the same under either frame.
pub fn cosmos_binding_prehash(address: &[u8; 20], voter: &VoterId) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    Sha256::digest(cosmos_binding_message(address, voter)).into()
}

/// The canonical Cosmos-SDK account address of a secp256k1 public key:
/// `ripemd160(sha256(compressed_pubkey(33)))` — 20 bytes.
///
/// Hashes the canonical compressed SEC1 encoding of the PARSED key — never raw
/// prover-supplied bytes — so the address is a function of the key itself and no
/// alternative encoding of the same point can derive a different address.
pub fn cosmos_address_of_pubkey(vk: &k256::ecdsa::VerifyingKey) -> [u8; 20] {
    use ripemd::Ripemd160;
    use sha2::{Digest, Sha256};
    let point = vk.to_encoded_point(true);
    let bytes = point.as_bytes(); // 0x02/0x03 ‖ x(32)
    debug_assert_eq!(bytes.len(), 33, "compressed SEC1 point");
    let sha = Sha256::digest(bytes);
    let rip = Ripemd160::digest(sha);
    let mut addr = [0u8; 20];
    addr.copy_from_slice(&rip);
    addr
}

/// Extract the 20-byte Cosmos account address from a 32-byte `holder` field,
/// FAIL-CLOSED: only a correctly left-zero-padded holder (`holder[0..12] == 0`) is
/// a 20-byte account address per the cosmos-lightclient edge convention. Anything
/// else — notably a 32-byte module/ICA account (which fills the field and has no
/// single secp256k1 key to bind with anyway) or an Ed25519 pubkey registered as
/// the holder identity — is `None`; the Cosmos binding path refuses it rather than
/// treating 20 arbitrary bytes as an address.
pub fn cosmos_address_of_holder(holder: &[u8; 32]) -> Option<[u8; 20]> {
    if holder[0..12] != [0u8; 12] {
        return None;
    }
    let mut addr = [0u8; 20];
    addr.copy_from_slice(&holder[12..32]);
    Some(addr)
}

/// A Cosmos holder's authorization of a dregg [`VoterId`]: a 64-byte secp256k1
/// ECDSA `(r ‖ s)` signature made by the wallet key whose account address IS the
/// holding's `holder`, over [`cosmos_binding_prehash`]`(address, voter)`, carried
/// together with that wallet's 33-byte compressed pubkey (Cosmos signatures ship
/// the pubkey; there is no recovery id). Non-custodial: it is a signature, not a
/// transaction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CosmosOwnerBinding {
    /// The dregg voter identity the owner authorizes to carry this weight.
    pub voter: VoterId,
    /// The signer's compressed SEC1 public key (`0x02`/`0x03` ‖ x). Prover-supplied
    /// and therefore UNTRUSTED until its derived address matches the holder — see
    /// [`verify_cosmos_binding`].
    pub pubkey: [u8; 33],
    /// The 64-byte `r(32) ‖ s(32)` signature. `s` must be in the low half of the
    /// order (the non-malleable form, as Cosmos-SDK enforces on transactions); a
    /// high-S signature is refused as malleable.
    pub sig: [u8; 64],
}

/// Verify that `binding` is a genuine authorization, by the secp256k1 key whose
/// Cosmos account address is embedded in `holder`, of `binding.voter`. FAIL-CLOSED
/// `false` when:
///
/// - `holder` is not a left-zero-padded 20-byte address (`holder[0..12] != 0`);
/// - the carried pubkey does not parse as a valid compressed SEC1 point (33 bytes
///   ⇒ tag `0x02`/`0x03` with an on-curve x; anything else refuses);
/// - the parsed pubkey's derived address `ripemd160(sha256(pubkey))` differs from
///   the holder address — THE load-bearing check: the pubkey is prover-supplied,
///   and without this hash equality any keypair could "bind" any Cosmos holding;
/// - `r`/`s` do not parse as nonzero in-range scalars;
/// - `s` is in the high half of the order (the malleable twin — rejected so a
///   third party cannot mint a "different" binding from an observed one);
/// - the signature does not verify under the pubkey over the recomputed prehash.
///
/// The prehash is [`cosmos_binding_prehash`]`(address, binding.voter)` — recomputed
/// here from the claimed holder and voter, never taken from the prover — so a
/// signature the owner made for voter A, re-presented for voter B, verifies against
/// a different digest and is refused.
pub fn verify_cosmos_binding(holder: &[u8; 32], binding: &CosmosOwnerBinding) -> bool {
    use k256::ecdsa::signature::hazmat::PrehashVerifier;
    use k256::ecdsa::{Signature as CosmosSignature, VerifyingKey as CosmosVerifyingKey};

    // FAIL CLOSED: only a genuinely padded 20-byte account address takes this path.
    let Some(address) = cosmos_address_of_holder(holder) else {
        return false;
    };
    let Ok(vk) = CosmosVerifyingKey::from_sec1_bytes(&binding.pubkey) else {
        return false; // not a valid compressed point
    };
    // Tie the UNTRUSTED carried pubkey to the PROVEN account: its canonical
    // ripemd160(sha256(·)) address must be the holder address, byte for byte.
    if cosmos_address_of_pubkey(&vk) != address {
        return false;
    }
    let Ok(sig) = CosmosSignature::from_slice(&binding.sig) else {
        return false; // r or s zero / out of range
    };
    // Reject the malleable high-S twin (normalize_s returns Some IFF s was high) —
    // the same rule the EVM path enforces, and the same low-S rule Cosmos-SDK
    // applies to transaction signatures.
    if sig.normalize_s().is_some() {
        return false;
    }
    // Recompute the prehash from the CLAIMED (holder, voter) — the voter
    // commitment lives here.
    let prehash = cosmos_binding_prehash(&address, &binding.voter);
    // k256's verify_prehash itself also refuses high-S outright (defense in depth,
    // same as the EVM path's recover_from_prehash).
    vk.verify_prehash(&prehash, &sig).is_ok()
}

/// The ONE owner→voter authorization interface the chain-agnostic grant path
/// dispatches on: each binding form knows which holdings it may vouch for
/// ([`verifies_for`](Self::verifies_for)) — the dispatch is by the holding's
/// chain/holder SHAPE, never by prover-chosen flags.
///
/// - [`OwnerBinding`] (Ed25519): verifies against `holder` as an Ed25519 pubkey on
///   ANY chain — Solana natively, and the documented interim convention where a
///   non-Solana holder registers an Ed25519 binding key as their 32-byte holder
///   identity at the light-client edge. This is EXACTLY the pre-existing
///   [`verify_binding`] semantics, unchanged.
/// - [`EvmOwnerBinding`] (secp256k1): verifies ONLY for a holding on an EVM-family
///   chain ([`ChainId::Evm`]) whose `holder` is a left-zero-padded EVM address. A
///   Solana or Cosmos holding presented with an EVM binding is refused outright —
///   Solana stays Ed25519-only.
/// - [`CosmosOwnerBinding`] (secp256k1, pubkey-carrying): verifies ONLY for a
///   holding on a Cosmos-SDK chain ([`ChainId::Cosmos`]) whose `holder` is a
///   left-zero-padded 20-byte `ripemd160(sha256(pubkey))` account address. A
///   Solana or EVM holding presented with a Cosmos binding is refused outright.
pub trait HolderBinding {
    /// The dregg voter this binding authorizes.
    fn voter(&self) -> VoterId;
    /// Is this a genuine authorization by `holding.holder` for a holding of
    /// `holding`'s chain shape? FAIL-CLOSED on any mismatch.
    fn verifies_for(&self, holding: &ProvenForeignHolding) -> bool;
}

impl HolderBinding for OwnerBinding {
    fn voter(&self) -> VoterId {
        self.voter
    }
    fn verifies_for(&self, holding: &ProvenForeignHolding) -> bool {
        verify_binding(&holding.holder, self)
    }
}

impl HolderBinding for EvmOwnerBinding {
    fn voter(&self) -> VoterId {
        self.voter
    }
    fn verifies_for(&self, holding: &ProvenForeignHolding) -> bool {
        // Chain-shape dispatch: secp256k1 address recovery vouches ONLY for an
        // EVM-family holding. A Solana/Cosmos holder can never be bound by an EVM
        // signature (fail closed), even if its holder bytes happen to look padded.
        matches!(holding.chain, ChainId::Evm(_)) && verify_evm_binding(&holding.holder, self)
    }
}

impl HolderBinding for CosmosOwnerBinding {
    fn voter(&self) -> VoterId {
        self.voter
    }
    fn verifies_for(&self, holding: &ProvenForeignHolding) -> bool {
        // Chain-shape dispatch: the pubkey-carrying Cosmos binding vouches ONLY for
        // a Cosmos-SDK holding. A Solana/EVM holder can never be bound by it (fail
        // closed) — in particular an EVM holding, whose padded-20-byte holder SHAPE
        // is identical, still refuses here: keccak and ripemd160-sha256 addresses of
        // one key differ, and the chain gate refuses before any hashing anyway.
        matches!(holding.chain, ChainId::Cosmos(_)) && verify_cosmos_binding(&holding.holder, self)
    }
}

/// A runtime-tagged either-form binding, for callers (relayers, wire decoders) that
/// carry both shapes through one channel. Dispatches to the underlying form's
/// [`HolderBinding`] impl — the tag grants no authority; verification still runs
/// against the holding's chain/holder shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VoterBinding {
    /// An Ed25519 [`OwnerBinding`] (Solana native; interim registered-key path).
    Ed25519(OwnerBinding),
    /// A secp256k1 [`EvmOwnerBinding`] (EVM-family address holders).
    Evm(EvmOwnerBinding),
    /// A secp256k1 pubkey-carrying [`CosmosOwnerBinding`] (Cosmos-SDK account
    /// address holders).
    Cosmos(CosmosOwnerBinding),
}

impl HolderBinding for VoterBinding {
    fn voter(&self) -> VoterId {
        match self {
            VoterBinding::Ed25519(b) => b.voter(),
            VoterBinding::Evm(b) => b.voter(),
            VoterBinding::Cosmos(b) => b.voter(),
        }
    }
    fn verifies_for(&self, holding: &ProvenForeignHolding) -> bool {
        match self {
            VoterBinding::Ed25519(b) => b.verifies_for(holding),
            VoterBinding::Evm(b) => b.verifies_for(holding),
            VoterBinding::Cosmos(b) => b.verifies_for(holding),
        }
    }
}

/// The weight granted to a [`VoterId`] from one proven holding, as of the proven
/// snapshot slot. NON-CUSTODIAL: producing this moved no value and locked nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WeightGrant {
    /// The dregg voter the weight is granted to (the bound identity).
    pub voter: VoterId,
    /// The granted weight — equal to the proven balance (atomic units). Weight is the
    /// identity function of the proven amount for this lane; a documented monotone
    /// re-scaling could replace it without changing the fail-closed shape.
    pub weight: u64,
    /// The finalized Solana slot the balance was proven at — the snapshot the weight is
    /// as-of.
    pub slot: u64,
    /// The SPL token account the weight came from — the per-poll nullifier key.
    pub token_account: [u8; 32],
}

/// The weight granted to a [`VoterId`] from one chain-agnostic proven holding, as of
/// the proven per-chain snapshot height. NON-CUSTODIAL: producing this moved no value
/// and locked nothing, on any chain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ForeignWeightGrant {
    /// The dregg voter the weight is granted to (the bound identity).
    pub voter: VoterId,
    /// The granted weight — the Lean verdict's output, equal to the proven balance.
    /// `u128` to carry an EVM-scale balance without truncation.
    pub weight: u128,
    /// The chain the holding was proven on.
    pub chain: ChainId,
    /// The finalized snapshot height (slot / block number / height) the balance was
    /// proven at.
    pub snapshot: u64,
    /// The consume-once nullifier this grant fired
    /// ([`ProvenForeignHolding::nullifier_key`]: chain+holder+asset scoped).
    pub nullifier: [u8; 32],
}

/// Why a weight grant was refused. Every variant grants ZERO weight (fail closed).
///
/// Not `Copy`: [`GrantError::LeanCoreUnavailable`] carries the FFI error string (mirroring
/// `grain-verify`'s `R3Error`), so a stale archive that lacks the verified verdict core surfaces the
/// gap rather than silently reimplementing the decision in Rust.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GrantError {
    /// The holding is not consensus-proven (a [`StructureOnly`](dregg_bridge::solana_trustless::LockProofTrust::StructureOnly)
    /// RPC echo, or any non-`ConsensusVerified` trust). The Nomad-law analog: no
    /// supermajority proof, no weight.
    NotConsensusProven,
    /// The LEAN-PROVEN weight verdict core (`dregg_holding_grant_weight`) is not in the linked
    /// archive — the decision cannot be rendered by the verified object. Carries the FFI error.
    /// (Rebuild `dregg-lean-ffi` so the archive splices `Metatheory.Bridge.ProofOfHoldings`.) There
    /// is NO Rust fallback for the weight DECISION by design: it is the Lean-proven verdict or it is
    /// not made — matching `grain-verify`'s `R3Error::LeanCoreUnavailable`.
    LeanCoreUnavailable(String),
    /// The [`OwnerBinding`] is not a valid signature by the holding's `owner` over the
    /// claimed `voter` — the owner did not authorize this voter.
    UnboundOwner,
    /// The proven balance is zero — a positive proven holding is required to gain
    /// weight.
    ZeroAmount,
    /// This `(poll, token_account)` already granted weight in this poll — the
    /// consume-once nullifier fired (no double-count of the same holding in one poll).
    AlreadyCounted,
    /// The holding was proven at a slot other than the poll's pinned snapshot slot.
    /// A poll fixes ONE finalized snapshot slot; every holding must be proven at
    /// exactly that slot. This closes the move-the-same-tokens attack: proving the
    /// same balance at two different slots (account A at S1, then move A→B and prove
    /// B at S2) would otherwise yield two distinct `token_account` nullifiers and
    /// double the weight. At a single finalized slot the tokens sit in one account.
    WrongSnapshot {
        /// The slot the holding was proven at.
        holding_slot: u64,
        /// The poll's pinned snapshot slot.
        poll_snapshot: u64,
    },
    /// The poll has no pinned snapshot slot — call [`HoldingWeightRegistry::open_snapshot`]
    /// before granting holding-weight into it.
    NoSnapshot,
    /// The poll is not open on the vote engine (no ballot box): no ballot was cast, and
    /// crucially the `(poll, token_account)` nullifier is NOT consumed, so a later
    /// attempt once the poll is open still succeeds.
    PollNotOpen,
    /// The granted foreign weight (a `u128`, sized for EVM-scale balances) does not fit
    /// the ballot domain ([`VoteBlock::weight`](crate::VoteBlock::weight) is `u64`). FAIL-CLOSED: the cast is
    /// REFUSED — never a saturating or truncating narrowing, which would silently
    /// mis-weigh the ballot (truncation could even shrink a whale to near-zero, or
    /// saturation could freeze distinct balances to one value). No ballot is cast and
    /// the nullifier is NOT consumed.
    WeightOverflow {
        /// The verdict weight that exceeds `u64::MAX`.
        weight: u128,
    },
    /// The verified executor engine refused the ballot turn for a reason other
    /// than its one-vote-per-voter rule (which is the in-band
    /// [`CastOutcome::RefusedDoubleVote`]). Carries the engine's refusal.
    /// FAIL-CLOSED: no ballot was cast and the `(poll, holding)` nullifier is
    /// NOT consumed, so a later valid attempt still counts.
    EngineRefused(String),
}

/// FAIL-CLOSED narrowing at the ballot boundary: a [`ForeignWeightGrant::weight`]
/// (`u128`, EVM-scale) becomes a [`VoteBlock::weight`](crate::VoteBlock::weight) (`u64`) only if it fits
/// losslessly; anything above `u64::MAX` is [`GrantError::WeightOverflow`] — NEVER a
/// saturating/truncating cast. Every foreign grant → ballot cast goes through this.
pub fn narrow_ballot_weight(weight: u128) -> Result<u64, GrantError> {
    u64::try_from(weight).map_err(|_| GrantError::WeightOverflow { weight })
}

/// The pure weight-granting primitive: check that `holding` is consensus-proven and that
/// `binding` is a genuine owner→voter authorization, then grant weight equal to the
/// proven balance to `binding.voter`, as-of the proven slot.
///
/// This performs NO dedup — it is the stateless core. Use [`HoldingWeightRegistry`] when
/// you need the per-poll no-double-count nullifier.
///
/// ## The weight VERDICT is the Lean-proven object, not this Rust
///
/// The ed25519 owner→voter binding, the consensus-proof read, and the positive-amount check are
/// fast-Rust PRE-CHECKS — they establish the FACTS. The fail-closed weight VERDICT itself is NOT
/// decided here: the two decision facts (consensus-proven status, the light client's finality
/// verdict) plus the proven amount are marshalled onto a wire and routed to
/// `Metatheory.Bridge.ProofOfHoldings.grantWeightFFI` (the `@[export] dregg_holding_grant_weight`
/// entry, reached via [`dregg_lean_ffi::shadow_holding_grant_weight`]) — the extracted,
/// `#assert_axioms`-clean `grantWeightCore`, PROVED to realize the `grantsWeight` spec by
/// `grantWeightCore_eq_grantsWeight`. The returned weight IS the verified decision's output, not a
/// Rust `holding.amount` literal. A `ConsensusVerified` holding is proven over a FINALIZED bank hash,
/// so finalization is entailed by the consensus proof — `slotFinal` is the same fact on this path
/// (see the `grantWeight` doc in the Lean model).
///
/// Fail-closed order: consensus first (a `StructureOnly` holding is refused before its
/// signature is even examined), then the binding, then a positive-amount check; and if the
/// Lean verdict core is not linked, [`GrantError::LeanCoreUnavailable`] — NEVER a silent Rust
/// reimplementation of the decision.
pub fn grant_weight(
    holding: &ProvenHolding,
    binding: &OwnerBinding,
) -> Result<WeightGrant, GrantError> {
    // The THIN WRAPPER: convert to the chain-agnostic fact and run the ONE generic
    // fail-closed core. All checks (consensus verdict, owner binding, positive amount,
    // the Lean-proven weight verdict) happen in `grant_foreign_weight`.
    let foreign = ProvenForeignHolding::from(holding);
    let grant = grant_foreign_weight(&foreign, binding)?;
    // The Solana amount was a u64, so the verdict (== the amount) fits back losslessly;
    // anything else is a core disagreement — fail closed.
    let weight = u64::try_from(grant.weight).map_err(|_| {
        GrantError::LeanCoreUnavailable(format!(
            "verdict {} overflows the Solana u64 amount domain",
            grant.weight
        ))
    })?;
    Ok(WeightGrant {
        voter: grant.voter,
        weight,
        slot: holding.slot,
        token_account: holding.token_account,
    })
}

/// **The generic, chain-agnostic weight-granting core** — the ONE binding from a proven
/// holding on ANY chain to dregg vote weight, non-custodially. Same fail-closed order
/// as the Solana path always had (it now IS the Solana path — [`grant_weight`] wraps
/// this):
///
/// 1. `consensus_proven` must be `true` — a structure-only RPC echo from any chain is
///    [`GrantError::NotConsensusProven`] and grants ZERO (the Nomad-law analog), before
///    its signature is even examined;
/// 2. `binding` must be a genuine authorization by `holding.holder` of
///    `binding.voter()` (else [`GrantError::UnboundOwner`]) — ANY form of
///    [`HolderBinding`]: an Ed25519 [`OwnerBinding`] (Solana native — the pre-existing
///    path, unchanged), a secp256k1 [`EvmOwnerBinding`] accepted ONLY for an
///    EVM-family holding with a zero-padded EVM-address holder, or a secp256k1
///    pubkey-carrying [`CosmosOwnerBinding`] accepted ONLY for a Cosmos-SDK holding
///    with a zero-padded `ripemd160(sha256(pubkey))` account-address holder
///    (chain-shape dispatch; a Solana holding can never be bound by either
///    secp256k1 form, and the EVM/Cosmos forms can never cross);
/// 3. the proven amount must be positive (else [`GrantError::ZeroAmount`]);
/// 4. the weight VERDICT is rendered by the LEAN-PROVEN `grantWeightCore` over the wire
///    — never a Rust `if`-chain; a missing core is [`GrantError::LeanCoreUnavailable`],
///    NEVER a silent Rust reimplementation.
///
/// Performs NO dedup — the stateless core. Use
/// [`HoldingWeightRegistry::grant_foreign_into_poll`] for the per-poll snapshot pin and
/// the per-`(poll, chain+holder+asset)` nullifier.
pub fn grant_foreign_weight<B: HolderBinding>(
    holding: &ProvenForeignHolding,
    binding: &B,
) -> Result<ForeignWeightGrant, GrantError> {
    // PRE-CHECKS (fast Rust) — establish the facts the verified decision reads.
    if !holding.is_consensus_proven() {
        return Err(GrantError::NotConsensusProven);
    }
    if !binding.verifies_for(holding) {
        return Err(GrantError::UnboundOwner);
    }
    if holding.amount == 0 {
        return Err(GrantError::ZeroAmount);
    }

    // THE VERDICT — the LEAN-PROVEN grantWeightCore over the wire
    // "isConsensusProven finalized amount". A consensus-proven holding is proven over a
    // FINALIZED anchor (bank hash / finalized state_root / Tendermint commit) on every
    // supported chain, so finality is the consensus-proof fact itself on this path.
    // Rust never decides the weight; it marshals to the verified object.
    let consensus = holding.is_consensus_proven();
    let finalized = consensus;
    let wire = format!("{} {} {}", consensus as u8, finalized as u8, holding.amount);
    let out = dregg_lean_ffi::shadow_holding_grant_weight(&wire)
        .map_err(GrantError::LeanCoreUnavailable)?;
    let weight: u128 = out
        .parse()
        .map_err(|_| GrantError::LeanCoreUnavailable(format!("non-numeric verdict: {out:?}")))?;
    if weight == 0 {
        // The verified decision refused (a `0` verdict). With the pre-checks satisfied
        // this is a core disagreement; fail closed rather than fabricate a grant.
        return Err(GrantError::NotConsensusProven);
    }

    Ok(ForeignWeightGrant {
        voter: binding.voter(),
        weight,
        chain: holding.chain,
        snapshot: holding.snapshot,
        nullifier: holding.nullifier_key(),
    })
}

/// A per-poll ledger of which SPL token accounts have already granted weight — the
/// snapshot's consume-once nullifier set. It carries no value and holds no escrow; it
/// only records `(poll, token_account)` pairs so the same holding cannot be counted
/// twice in one poll.
///
/// # The ballot box: the VERIFIED weighted engine is the front door
///
/// A holding-weight ballot is **weighted**: a holder with a proven balance of `W` casts
/// a ballot worth `W`. `collective_choice::CollectiveChoice::cast_weighted` is that
/// ballot as a real executor turn — the option's `Monotonic` tally slot is bumped by
/// exactly `W`, under the engine's one-ballot-per-voter gates (`WriteOnce(VOTE)` +
/// nullifier), with the weight quorum an in-cell `AffineLe` and the genuine-approver
/// floor a `CountGe` witness. [`grant_and_cast`](Self::grant_and_cast) /
/// [`foreign_grant_and_cast`](Self::foreign_grant_and_cast) route through any
/// [`WeightedBallotEngine`]; **the front door is [`VerifiedHoldingBallotBox`]** (the
/// executor engine behind this registry's poll ids). Lean mirror:
/// `Dregg2.Apps.MultisigVote.castVoteW` (weight conservation, one-cast-per-voter under
/// weights, zero-weight/authority refusals — kernel-checked).
///
/// **What is verified**: the *verdict* — the weight decision is rendered by the
/// Lean-proven `grantWeightCore` over the FFI ([`grant_foreign_weight`]), fail-closed
/// with no Rust reimplementation fallback, after fail-closed pre-checks
/// (consensus-proof, owner→voter binding, positive amount) — and now the *tally*: the
/// cast, the monotone board, and the one-vote rule are executor turns on
/// [`VerifiedHoldingBallotBox`]. The snapshot pin and the per-`(poll,
/// chain+holder+asset)` nullifier below are host-side bookkeeping and are honest about
/// it.
///
/// **Demoted residual**: [`HostBallotBox`] also implements [`WeightedBallotEngine`] —
/// kept ONLY as the causal-log derivation aid for out-of-lane consumers
/// (`dregg-interchain-gov`) pending their migration; its one-vote and quorum gates are
/// a `HashSet` and a `>=`. No test or doc in THIS crate points the holding-weight flow
/// at it as a gate.
#[derive(Clone, Debug, Default)]
pub struct HoldingWeightRegistry {
    /// The fired nullifiers: present once a holding's weight has been granted into
    /// that poll. Solana's legacy path stores the raw SPL `token_account`; the generic
    /// cross-chain path stores the domain-separated
    /// [`ProvenForeignHolding::nullifier_key`] (chain+holder+asset digest) — the blake3
    /// derive-key domain keeps the two spaces from colliding.
    spent: HashSet<(PollId, [u8; 32])>,
    /// The finalized SNAPSHOT height each poll pins its holding-weight to, PER CHAIN
    /// (a Solana slot and an EVM block number live on different clocks). Every holding
    /// counted in a poll must be proven at exactly its chain's pinned height (see
    /// [`GrantError::WrongSnapshot`]).
    poll_snapshot: BTreeMap<(PollId, ChainId), u64>,
}

impl HoldingWeightRegistry {
    /// A fresh registry with no granted holdings.
    pub fn new() -> Self {
        HoldingWeightRegistry::default()
    }

    /// Pin `poll`'s **Solana** holding-weight SNAPSHOT to the finalized `slot` — the
    /// legacy single-chain entry, now sugar for
    /// [`open_chain_snapshot`](Self::open_chain_snapshot)`(poll, ChainId::Solana, slot)`.
    /// Every Solana holding counted in `poll` must be proven at exactly this slot — the
    /// defence against double-counting the same tokens by proving them across accounts
    /// at different slots. Call once when the poll's holding-weight window opens.
    pub fn open_snapshot(&mut self, poll: PollId, slot: u64) {
        self.open_chain_snapshot(poll, ChainId::Solana, slot);
    }

    /// Pin `poll`'s holding-weight SNAPSHOT for `chain` to the finalized `height`.
    /// Each chain gets its OWN pin (its own clock); a holding proven at any other
    /// height on that chain is [`GrantError::WrongSnapshot`], and a chain with no pin
    /// refuses outright ([`GrantError::NoSnapshot`] — fail closed).
    pub fn open_chain_snapshot(&mut self, poll: PollId, chain: ChainId, height: u64) {
        self.poll_snapshot.insert((poll, chain), height);
    }

    /// The pinned **Solana** snapshot slot for `poll`, if any.
    pub fn snapshot_of(&self, poll: PollId) -> Option<u64> {
        self.chain_snapshot_of(poll, ChainId::Solana)
    }

    /// The pinned snapshot height for `poll` on `chain`, if any.
    pub fn chain_snapshot_of(&self, poll: PollId, chain: ChainId) -> Option<u64> {
        self.poll_snapshot.get(&(poll, chain)).copied()
    }

    /// Has this Solana `holding` already granted weight in `poll`? (Queries the
    /// unified `(poll, chain+holder+asset)` nullifier — the SAME key the foreign path
    /// uses, so the two registry paths share one consume-once keyspace.)
    pub fn is_spent(&self, poll: PollId, holding: &ProvenHolding) -> bool {
        self.spent
            .contains(&(poll, ProvenForeignHolding::from(holding).nullifier_key()))
    }

    /// How many distinct holdings have granted weight (across all polls)?
    pub fn granted_count(&self) -> usize {
        self.spent.len()
    }

    /// Grant `holding`'s weight to its bound voter **in `poll`**, enforcing the per-poll
    /// no-double-count nullifier. Runs the full fail-closed [`grant_weight`] check
    /// first; only on success does it consume the `(poll, token_account)` nullifier and
    /// return the grant. A holding refused for any [`GrantError`] leaves the nullifier
    /// set unchanged (so a genuinely-later valid proof of the same account can still be
    /// counted). Re-presenting an already-counted account in the same poll is
    /// [`GrantError::AlreadyCounted`].
    pub fn grant_into_poll(
        &mut self,
        poll: PollId,
        holding: &ProvenHolding,
        binding: &OwnerBinding,
    ) -> Result<WeightGrant, GrantError> {
        let grant = self.check_grant(poll, holding, binding)?;
        // ONE nullifier keyspace with the foreign path: a Solana holding fires the
        // SAME (poll, chain+holder+asset) key grant_foreign_into_poll uses, so it can
        // never be counted twice by mixing the two registry paths.
        self.spent
            .insert((poll, ProvenForeignHolding::from(holding).nullifier_key()));
        Ok(grant)
    }

    /// Has this chain-agnostic holding's `(poll, chain+holder+asset)` nullifier
    /// already fired in `poll`?
    pub fn is_foreign_spent(&self, poll: PollId, holding: &ProvenForeignHolding) -> bool {
        self.spent.contains(&(poll, holding.nullifier_key()))
    }

    /// **The cross-chain grant**: grant `holding`'s weight to its bound voter in
    /// `poll`, whatever chain it was proven on, enforcing:
    ///
    /// - the per-`(poll, chain)` SNAPSHOT pin — the holding must be proven at exactly
    ///   the height [`open_chain_snapshot`](Self::open_chain_snapshot) pinned for its
    ///   chain (no pin → [`GrantError::NoSnapshot`], fail closed);
    /// - the full fail-closed [`grant_foreign_weight`] check (consensus verdict →
    ///   owner binding → positive amount → the Lean-proven weight verdict);
    /// - the per-`(poll, chain+holder+asset)` consume-once nullifier — the same
    ///   holder+asset on the same chain counts ONCE per poll
    ///   ([`GrantError::AlreadyCounted`]), while the same holder on a DIFFERENT chain
    ///   is a distinct nullifier and legitimately counts too.
    ///
    /// A holding refused for any [`GrantError`] leaves the nullifier set unchanged, so
    /// a genuinely-later valid proof of the same holding can still be counted.
    pub fn grant_foreign_into_poll<B: HolderBinding>(
        &mut self,
        poll: PollId,
        holding: &ProvenForeignHolding,
        binding: &B,
    ) -> Result<ForeignWeightGrant, GrantError> {
        let grant = self.check_foreign_grant(poll, holding, binding)?;
        self.spent.insert((poll, grant.nullifier));
        Ok(grant)
    }

    /// The pure fail-closed foreign grant check — the per-`(poll, chain)` snapshot pin,
    /// the full [`grant_foreign_weight`] verification, and the unspent-nullifier
    /// confirmation — WITHOUT consuming the nullifier.
    /// [`grant_foreign_into_poll`](Self::grant_foreign_into_poll) consumes on success;
    /// [`foreign_grant_and_cast`](Self::foreign_grant_and_cast) defers the consume until
    /// the engine has accepted the ballot, so a poll-not-open (or weight-overflow)
    /// failure leaves the nullifier available for a later valid attempt.
    fn check_foreign_grant<B: HolderBinding>(
        &self,
        poll: PollId,
        holding: &ProvenForeignHolding,
        binding: &B,
    ) -> Result<ForeignWeightGrant, GrantError> {
        let snapshot = self
            .chain_snapshot_of(poll, holding.chain)
            .ok_or(GrantError::NoSnapshot)?;
        if holding.snapshot != snapshot {
            return Err(GrantError::WrongSnapshot {
                holding_slot: holding.snapshot,
                poll_snapshot: snapshot,
            });
        }
        let grant = grant_foreign_weight(holding, binding)?;
        if self.spent.contains(&(poll, grant.nullifier)) {
            return Err(GrantError::AlreadyCounted);
        }
        Ok(grant)
    }

    /// End-to-end cross-chain convenience — the foreign analog of
    /// [`grant_and_cast`](Self::grant_and_cast): grant `holding`'s weight into `poll`
    /// (snapshot-pinned, dedup-guarded, whatever chain it was proven on) and cast a
    /// ballot for `choice` carrying that weight on the given
    /// [`WeightedBallotEngine`] as the bound voter — the front door is
    /// [`VerifiedHoldingBallotBox`], where the weighted ballot is a real executor
    /// turn.
    ///
    /// **The u128 → u64 NARROWING SEAM, fail-closed**: [`ForeignWeightGrant::weight`]
    /// is a `u128` (sized for EVM-scale balances) but the ballot weight is a `u64`.
    /// The narrowing runs through [`narrow_ballot_weight`] BEFORE the engine sees a
    /// ballot: a weight above `u64::MAX` is [`GrantError::WeightOverflow`] — the cast is
    /// REFUSED, never saturated or truncated, and the nullifier is left unspent (so the
    /// holder is not permanently locked out; e.g. a re-scaled poll could later accept a
    /// re-proof).
    ///
    /// As with [`grant_and_cast`](Self::grant_and_cast), the nullifier is consumed only
    /// after the engine accepts the ballot (any in-band [`CastOutcome`]), so
    /// [`GrantError::PollNotOpen`] and [`GrantError::EngineRefused`] do not burn it;
    /// and the engine's own one-vote-per-voter rule still applies on top
    /// ([`CastOutcome::RefusedDoubleVote`]).
    pub fn foreign_grant_and_cast<B: HolderBinding, E: WeightedBallotEngine>(
        &mut self,
        engine: &mut E,
        poll: PollId,
        choice: OptionId,
        holding: &ProvenForeignHolding,
        binding: &B,
    ) -> Result<CastOutcome, GrantError> {
        // Verify WITHOUT consuming the nullifier first — a downstream refusal
        // (overflow, poll-not-open) must not permanently burn this holding's slot.
        let grant = self.check_foreign_grant(poll, holding, binding)?;
        // FAIL-CLOSED narrowing: u128 verdict → u64 ballot domain, or a typed refusal.
        let weight = narrow_ballot_weight(grant.weight)?;
        // Unknown poll / engine refusal: an `Err` — the nullifier stays untouched.
        let outcome = engine.cast_weighted_ballot(poll, grant.voter, choice, weight)?;
        // The engine accepted the ballot: NOW consume the nullifier.
        self.spent.insert((poll, grant.nullifier));
        Ok(outcome)
    }

    /// The pure fail-closed grant check — runs the full [`grant_weight`] verification,
    /// pins the holding to the poll's snapshot slot, and confirms the
    /// `(poll, token_account)` nullifier is unspent — but does NOT consume the
    /// nullifier. [`grant_into_poll`] consumes on success; [`grant_and_cast`] defers the
    /// consume until the engine has accepted the ballot, so a poll-not-open failure
    /// leaves the nullifier available for a later valid attempt.
    fn check_grant(
        &self,
        poll: PollId,
        holding: &ProvenHolding,
        binding: &OwnerBinding,
    ) -> Result<WeightGrant, GrantError> {
        let snapshot = self
            .chain_snapshot_of(poll, ChainId::Solana)
            .ok_or(GrantError::NoSnapshot)?;
        if holding.slot != snapshot {
            return Err(GrantError::WrongSnapshot {
                holding_slot: holding.slot,
                poll_snapshot: snapshot,
            });
        }
        let grant = grant_weight(holding, binding)?;
        if self
            .spent
            .contains(&(poll, ProvenForeignHolding::from(holding).nullifier_key()))
        {
            return Err(GrantError::AlreadyCounted);
        }
        Ok(grant)
    }

    /// End-to-end convenience: grant `holding`'s weight into `poll` (dedup-guarded) and
    /// cast a ballot for `choice` carrying that weight on the given
    /// [`WeightedBallotEngine`] as the bound voter — the front door is
    /// [`VerifiedHoldingBallotBox`], where the weighted ballot is a real executor turn
    /// (a `Monotonic` tally bump of exactly the granted weight under the executor's
    /// one-ballot-per-voter gates). The engine applies its OWN one-vote-per-voter rule
    /// on top, so a second holding bound to the same voter is refused there
    /// ([`CastOutcome::RefusedDoubleVote`]) even though it is a distinct token-account
    /// nullifier here.
    ///
    /// Note the two guards are complementary: the nullifier stops the *same account*
    /// voting twice; the engine's one-vote rule stops the *same voter* voting twice.
    pub fn grant_and_cast<E: WeightedBallotEngine>(
        &mut self,
        engine: &mut E,
        poll: PollId,
        choice: OptionId,
        holding: &ProvenHolding,
        binding: &OwnerBinding,
    ) -> Result<CastOutcome, GrantError> {
        // Verify WITHOUT consuming the nullifier first — so a poll-not-open failure
        // does not permanently burn this (poll, token_account).
        let grant = self.check_grant(poll, holding, binding)?;
        // Unknown poll / engine refusal: an `Err` — the nullifier stays untouched.
        let outcome = engine.cast_weighted_ballot(poll, grant.voter, choice, grant.weight)?;
        // The engine accepted the ballot: NOW consume the nullifier — the unified
        // (poll, chain+holder+asset) key, so the two registry paths share it.
        self.spent
            .insert((poll, ProvenForeignHolding::from(holding).nullifier_key()));
        Ok(outcome)
    }
}

// ═════════════════════════════════════════════════════════════════════════════
//  The weighted ballot engines — where a granted weight lands.
// ═════════════════════════════════════════════════════════════════════════════

/// The seam between the registry's fail-closed GRANT (snapshot pin, Lean-proven
/// verdict, consume-once nullifier) and the ballot box the granted weight lands
/// in. [`grant_and_cast`](HoldingWeightRegistry::grant_and_cast) /
/// [`foreign_grant_and_cast`](HoldingWeightRegistry::foreign_grant_and_cast)
/// cast through this trait.
///
/// **The front door is [`VerifiedHoldingBallotBox`]** — the verified executor
/// engine (`collective_choice::CollectiveChoice::cast_weighted`): the weighted
/// tally bump, the one-ballot-per-voter rule, and the quorum gates are real
/// executor turns. [`HostBallotBox`] also implements this trait, DEMOTED: a
/// causal-log derivation aid whose gates are a `HashSet` and a `>=`, retained
/// for out-of-lane consumers pending migration — do not point new flows at it.
pub trait WeightedBallotEngine {
    /// Cast a ballot of `weight` for `voter` into `poll`.
    ///
    /// Contract (the registry's nullifier depends on it):
    /// - `Err(`[`GrantError::PollNotOpen`]`)` — the poll is unknown here; the
    ///   caller must NOT consume its nullifier.
    /// - `Err(`[`GrantError::EngineRefused`]`)` — the engine refused the turn
    ///   out-of-band (no ballot recorded); nullifier must stay unconsumed.
    /// - `Ok(outcome)` — the engine adjudicated the ballot in-band
    ///   ([`CastOutcome::Accepted`], or a refusal like
    ///   [`CastOutcome::RefusedDoubleVote`]); the caller consumes the nullifier
    ///   exactly as the pre-weld flow did.
    fn cast_weighted_ballot(
        &mut self,
        poll: PollId,
        voter: VoterId,
        choice: OptionId,
        weight: u64,
    ) -> Result<CastOutcome, GrantError>;
}

/// DEMOTED — the host box as a weighted ballot target: `next_block` + `cast`,
/// the pre-weld flow verbatim. Kept only for out-of-lane consumers
/// (`dregg-interchain-gov`); the holding-weight front door is
/// [`VerifiedHoldingBallotBox`].
impl WeightedBallotEngine for HostBallotBox {
    fn cast_weighted_ballot(
        &mut self,
        poll: PollId,
        voter: VoterId,
        choice: OptionId,
        weight: u64,
    ) -> Result<CastOutcome, GrantError> {
        let block = self
            .next_block(poll, voter, choice, weight)
            .ok_or(GrantError::PollNotOpen)?;
        Ok(self.cast(poll, block))
    }
}

/// **The verified weighted ballot box** — the holding-weight registry's front
/// door onto the verified executor engine
/// ([`collective_choice::CollectiveChoice`]).
///
/// Each poll opened here is a REAL executor poll: the granted weight lands via
/// [`cast_weighted`](collective_choice::CollectiveChoice::cast_weighted) — a
/// `WriteOnce(VOTE)` ballot turn plus a `Monotonic` tally bump of exactly the
/// granted weight — so the one-vote rule is the executor's nullifier +
/// `WriteOnce`, not a `HashSet`, and the weight quorum is the in-cell
/// `AffineLe` with a `CountGe` genuine-approver floor, not a `>=`.
///
/// Eligibility is the registry's fail-closed GRANT (consensus proof →
/// owner→voter binding → the Lean-proven `grantWeightCore` verdict), so the
/// executor poll's electorate is DYNAMIC: the ballot cap is minted to the
/// granted voter at cast time. WrongSnapshot / AlreadyCounted / PollNotOpen
/// semantics are the registry's and are unchanged.
///
/// Supported rules: [`DecisionRule::Plurality`] (total-weight quorum) and
/// [`DecisionRule::Threshold`] (per-option weight gate).
/// [`DecisionRule::Supermajority`] is a closed-electorate HEADCOUNT rule — it
/// has no weighted expression and is refused at open (use the governance face).
pub struct VerifiedHoldingBallotBox {
    engine: collective_choice::CollectiveChoice,
    /// registry poll id (the content-addressed [`PollSpec::id`]) → executor poll.
    polls: BTreeMap<PollId, collective_choice::PollId>,
}

impl VerifiedHoldingBallotBox {
    /// Stand up the verified box (its own embedded executor + operator).
    pub fn new(federation_id: [u8; 32]) -> Self {
        VerifiedHoldingBallotBox {
            engine: collective_choice::CollectiveChoice::new(federation_id),
            polls: BTreeMap::new(),
        }
    }

    /// Open `spec` as a REAL executor poll and return the registry-facing
    /// [`PollId`] (the same content-addressed [`PollSpec::id`] the snapshot pin
    /// and nullifiers key on).
    ///
    /// The weight quorum is `spec.rule`'s: `Plurality { quorum }` gates the
    /// decision-turn on total weight ≥ `quorum`; `Threshold { option, min }`
    /// gates on that option's weight ≥ `min`. `Supermajority` is refused (a
    /// closed-electorate headcount rule — no weighted expression).
    pub fn open_weighted_poll(
        &mut self,
        spec: &crate::PollSpec,
    ) -> Result<PollId, collective_choice::VoteError> {
        let cc_spec = |quorum_m: u64| collective_choice::PollSpec {
            question: spec.question.clone(),
            options: spec.options.clone(),
            // DYNAMIC electorate: eligibility is the registry's verified grant.
            electorate: Vec::new(),
            quorum_m,
        };
        let cc_poll = match spec.rule {
            crate::DecisionRule::Plurality { quorum } => {
                self.engine.open_poll_weighted(cc_spec(quorum))?
            }
            crate::DecisionRule::Threshold { option, min } => self
                .engine
                .open_poll_weighted_gated(cc_spec(min), option.0 as usize)?,
            crate::DecisionRule::Supermajority => {
                return Err(collective_choice::VoteError::BadPollSpec(
                    "Supermajority is a closed-electorate headcount rule; a weighted \
                     holding poll uses Plurality or Threshold"
                        .into(),
                ));
            }
        };
        let id = spec.id();
        self.polls.insert(id, cc_poll);
        Ok(id)
    }

    /// The executor's stored monotone tally (`None` if the poll is unknown here).
    pub fn tally(&self, poll: PollId) -> Option<collective_choice::Tally> {
        let cc_poll = *self.polls.get(&poll)?;
        self.engine.tally(cc_poll).ok()
    }

    /// The light-client recompute over the append-only cast log — when it
    /// agrees with [`tally`](Self::tally) the board is unforged.
    pub fn light_client_tally(&self, poll: PollId) -> Option<collective_choice::Tally> {
        let cc_poll = *self.polls.get(&poll)?;
        self.engine.light_client_tally(cc_poll).ok()
    }

    /// Attempt the decision-turn (the `AffineLe` weight quorum + `CountGe`
    /// genuine-approver floor adjudicate it). `Ok(None)` below quorum.
    pub fn resolve(
        &mut self,
        poll: PollId,
    ) -> Result<Option<collective_choice::Decision>, collective_choice::VoteError> {
        let cc_poll = *self
            .polls
            .get(&poll)
            .ok_or(collective_choice::VoteError::NoSuchPoll)?;
        self.engine.resolve(cc_poll)
    }

    /// The underlying executor engine (read access, for audits).
    pub fn engine(&self) -> &collective_choice::CollectiveChoice {
        &self.engine
    }
}

impl WeightedBallotEngine for VerifiedHoldingBallotBox {
    fn cast_weighted_ballot(
        &mut self,
        poll: PollId,
        voter: VoterId,
        choice: OptionId,
        weight: u64,
    ) -> Result<CastOutcome, GrantError> {
        use collective_choice::VoteError as CcErr;
        // Unknown poll: no executor poll — the caller's nullifier must survive.
        let cc_poll = *self.polls.get(&poll).ok_or(GrantError::PollNotOpen)?;
        // Mint (idempotently) the granted voter's single ballot cap. The poll's
        // electorate is dynamic, so the mint follows the verified grant.
        let cap = match self.engine.issue_ballot(cc_poll, voter) {
            Ok(cap) => cap,
            Err(CcErr::NoSuchPoll) => return Err(GrantError::PollNotOpen),
            Err(e) => return Err(GrantError::EngineRefused(e.to_string())),
        };
        match self
            .engine
            .cast_weighted(cc_poll, &cap, choice.0 as usize, weight)
        {
            Ok(_) => Ok(CastOutcome::Accepted),
            // In-band adjudications — the ballot box judged the ballot; the
            // registry consumes its nullifier exactly as the pre-weld flow did.
            Err(CcErr::DoubleVote) => Ok(CastOutcome::RefusedDoubleVote),
            Err(CcErr::BadOption) => Ok(CastOutcome::RefusedUnknownOption),
            // Out-of-band refusals — no ballot recorded, nullifier must survive.
            Err(CcErr::NoSuchPoll | CcErr::WrongPoll) => Err(GrantError::PollNotOpen),
            Err(e) => Err(GrantError::EngineRefused(e.to_string())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_bridge::solana_trustless::LockProofTrust;
    use ed25519_dalek::{Signer, SigningKey};

    use crate::{DecisionRule, Electorate, PollSpec};

    /// The weight VERDICT is the Lean-proven `grantWeightCore` (`dregg_holding_grant_weight`); there
    /// is NO Rust fallback for the decision (by design). When the extracted core is not in the linked
    /// archive, [`grant_weight`] fail-closes with [`GrantError::LeanCoreUnavailable`], so the positive
    /// grant-path tests can only run once the archive splices `Metatheory.Bridge.ProofOfHoldings`.
    /// This guard skips them (with a note) rather than assert a Rust decision we deliberately do not
    /// have — mirroring `grain-verify`'s R3 test. The PRE-CHECK tests (`NotConsensusProven` /
    /// `UnboundOwner` / `ZeroAmount`) do NOT call it: those errors fire before the Lean verdict.
    fn lean_verdict_core_or_skip() -> bool {
        if dregg_lean_ffi::holding_grant_weight_core_available() {
            return true;
        }
        eprintln!(
            "holding-weight: the Lean-proven verdict core `dregg_holding_grant_weight` is not in \
             the linked archive — rebuild dregg-lean-ffi to splice Metatheory.Bridge.ProofOfHoldings, \
             then re-run. (No Rust fallback for the weight decision by design.)"
        );
        false
    }

    /// A deterministic owner keypair from a seed byte.
    fn owner_key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    /// A consensus-proven holding of `amount`, owned by `owner`, at `slot`.
    fn proven(owner: [u8; 32], token_account: [u8; 32], amount: u64, slot: u64) -> ProvenHolding {
        ProvenHolding {
            token_account,
            owner,
            mint: [7u8; 32],
            amount,
            slot,
            trust: LockProofTrust::ConsensusVerified,
        }
    }

    /// A genuine owner→voter binding: the owner key signs `binding_message(owner, voter)`.
    fn bind(owner: &SigningKey, voter: VoterId) -> OwnerBinding {
        let owner_pk = owner.verifying_key().to_bytes();
        let msg = binding_message(&owner_pk, &voter);
        let sig = owner.sign(&msg).to_bytes();
        OwnerBinding { voter, sig }
    }

    #[test]
    fn holding_consensus_proven_grants_weight_equal_to_amount() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        let owner = owner_key(1);
        let owner_pk = owner.verifying_key().to_bytes();
        let voter: VoterId = [9u8; 32];
        let h = proven(owner_pk, [42u8; 32], 500, 12_345);
        let grant = grant_weight(&h, &bind(&owner, voter)).expect("consensus-proven grants");
        assert_eq!(grant.voter, voter);
        assert_eq!(grant.weight, 500, "weight equals the proven balance N");
        assert_eq!(
            grant.slot, 12_345,
            "weight is as-of the proven snapshot slot"
        );
        assert_eq!(grant.token_account, [42u8; 32]);
    }

    #[test]
    fn holding_structure_only_grants_zero() {
        // REJECT polarity: a StructureOnly (RPC-echo) holding is NOT proof → no weight.
        let owner = owner_key(2);
        let owner_pk = owner.verifying_key().to_bytes();
        let voter: VoterId = [8u8; 32];
        let mut h = proven(owner_pk, [43u8; 32], 1_000_000, 1);
        h.trust = LockProofTrust::StructureOnly; // downgrade to the untrusted rung
        assert!(!h.is_consensus_proven());
        assert_eq!(
            grant_weight(&h, &bind(&owner, voter)),
            Err(GrantError::NotConsensusProven),
            "a StructureOnly holding must grant ZERO, never its (huge) claimed amount",
        );
    }

    #[test]
    fn unbound_owner_is_refused() {
        // REJECT polarity: a binding signed by the WRONG key (not the holding's owner)
        // grants nothing — the owner never authorized this voter.
        let owner = owner_key(3);
        let owner_pk = owner.verifying_key().to_bytes();
        let attacker = owner_key(99); // a different wallet
        let voter: VoterId = [1u8; 32];
        let h = proven(owner_pk, [44u8; 32], 400, 5);
        // Attacker signs the same message but with their own key → invalid under owner.
        let forged = bind(&attacker, voter);
        assert_eq!(
            grant_weight(&h, &forged),
            Err(GrantError::UnboundOwner),
            "a signature not by the holding owner must be refused",
        );
        // A binding over a DIFFERENT voter than the one the owner signed is also refused
        // (the message commits to the voter).
        let real = bind(&owner, voter);
        let swapped = OwnerBinding {
            voter: [2u8; 32],
            sig: real.sig,
        };
        assert_eq!(
            grant_weight(&h, &swapped),
            Err(GrantError::UnboundOwner),
            "reusing a signature for a different voter must be refused",
        );
    }

    #[test]
    fn zero_balance_grants_nothing() {
        // REJECT polarity: a positive proven holding is required.
        let owner = owner_key(4);
        let owner_pk = owner.verifying_key().to_bytes();
        let voter: VoterId = [3u8; 32];
        let h = proven(owner_pk, [45u8; 32], 0, 7);
        assert_eq!(
            grant_weight(&h, &bind(&owner, voter)),
            Err(GrantError::ZeroAmount),
        );
    }

    #[test]
    fn same_token_account_cannot_be_counted_twice_in_a_poll() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        let owner = owner_key(5);
        let owner_pk = owner.verifying_key().to_bytes();
        let voter: VoterId = [4u8; 32];
        let h = proven(owner_pk, [46u8; 32], 250, 9);
        let binding = bind(&owner, voter);
        let poll = PollId([11u8; 32]);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_snapshot(poll, 9); // the poll snapshots at the holding's slot

        // First presentation grants.
        assert_eq!(reg.grant_into_poll(poll, &h, &binding).unwrap().weight, 250);
        // REJECT polarity: the same (poll, token_account) a second time is refused.
        assert_eq!(
            reg.grant_into_poll(poll, &h, &binding),
            Err(GrantError::AlreadyCounted),
            "the same holding must not grant weight twice in one poll",
        );
        assert_eq!(reg.granted_count(), 1, "the nullifier set holds one entry");

        // A DIFFERENT poll is a distinct nullifier → allowed.
        let other_poll = PollId([22u8; 32]);
        reg.open_snapshot(other_poll, 9);
        assert_eq!(
            reg.grant_into_poll(other_poll, &h, &binding)
                .unwrap()
                .weight,
            250,
            "the same account may vote in a different poll",
        );
    }

    #[test]
    fn a_holding_at_the_wrong_snapshot_slot_is_refused() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        // THE MOVE-THE-SAME-TOKENS DEFENSE: a poll pins ONE finalized snapshot slot;
        // proving the same balance at a different slot (having moved it to a fresh
        // account) is refused, so it cannot double-count.
        let owner = owner_key(20);
        let owner_pk = owner.verifying_key().to_bytes();
        let voter: VoterId = [20u8; 32];
        let binding = bind(&owner, voter);
        let poll = PollId([55u8; 32]);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_snapshot(poll, 1000); // the poll's finalized snapshot

        // Account A at the snapshot slot → grants.
        let a = proven(owner_pk, [0xA1u8; 32], 500, 1000);
        assert_eq!(reg.grant_into_poll(poll, &a, &binding).unwrap().weight, 500);

        // The SAME tokens moved to account B and proven at a LATER slot → refused, so
        // the balance cannot be counted twice by moving it.
        let b = proven(owner_pk, [0xB2u8; 32], 500, 1001);
        assert_eq!(
            reg.grant_into_poll(poll, &b, &binding),
            Err(GrantError::WrongSnapshot {
                holding_slot: 1001,
                poll_snapshot: 1000
            }),
        );

        // And a poll with no snapshot opened refuses outright (fail closed).
        let mut bare = HoldingWeightRegistry::new();
        assert_eq!(
            bare.grant_into_poll(poll, &a, &binding),
            Err(GrantError::NoSnapshot)
        );
    }

    #[test]
    fn refused_grant_does_not_spend_the_nullifier() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        // A holding refused (StructureOnly) must NOT consume the nullifier, so a later
        // genuine consensus proof of the same account can still be counted.
        let owner = owner_key(6);
        let owner_pk = owner.verifying_key().to_bytes();
        let voter: VoterId = [5u8; 32];
        let binding = bind(&owner, voter);
        let poll = PollId([33u8; 32]);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_snapshot(poll, 3);

        let mut weak = proven(owner_pk, [47u8; 32], 900, 3);
        weak.trust = LockProofTrust::StructureOnly;
        assert_eq!(
            reg.grant_into_poll(poll, &weak, &binding),
            Err(GrantError::NotConsensusProven),
        );
        assert_eq!(
            reg.granted_count(),
            0,
            "a refused grant spends no nullifier"
        );

        let strong = proven(owner_pk, [47u8; 32], 900, 3);
        assert_eq!(
            reg.grant_into_poll(poll, &strong, &binding).unwrap().weight,
            900
        );
    }

    #[test]
    fn end_to_end_grant_and_cast_into_a_plurality_poll() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        // The weight flows all the way into the real HostBallotBox tally.
        let mut engine = HostBallotBox::new();
        let poll = engine.open_poll(PollSpec {
            question: "ship it?".into(),
            options: vec!["no".into(), "yes".into()],
            electorate: Electorate::Open,
            rule: DecisionRule::Plurality { quorum: 1 },
            enact_on_pass: false,
            nonce: 0,
        });

        let owner = owner_key(7);
        let owner_pk = owner.verifying_key().to_bytes();
        let voter: VoterId = [6u8; 32];
        let h = proven(owner_pk, [48u8; 32], 777, 20);
        let binding = bind(&owner, voter);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_snapshot(poll, 20);

        let outcome = reg
            .grant_and_cast(&mut engine, poll, OptionId(1), &h, &binding)
            .expect("grant succeeds");
        assert_eq!(outcome, CastOutcome::Accepted);

        let tally = engine.tally(poll).unwrap();
        assert_eq!(
            tally.per_option.get(&OptionId(1)).copied().unwrap_or(0),
            777,
            "the proven balance N became N units of vote weight for the bound voter",
        );
        assert_eq!(tally.distinct_voters, 1);

        // A DIFFERENT holder (owner2) bound to the SAME voter is a DISTINCT nullifier
        // (different holder), so it clears the consume-once guard and reaches the
        // engine, whose own one-vote-per-voter rule refuses the second vote. (The same
        // holder re-presenting is caught earlier by the nullifier — see
        // solana_holding_cannot_double_count_across_the_two_registry_paths.)
        let owner2 = owner_key(8);
        let owner2_pk = owner2.verifying_key().to_bytes();
        let binding2 = bind(&owner2, voter);
        let h2 = proven(owner2_pk, [49u8; 32], 111, 20);
        let outcome2 = reg
            .grant_and_cast(&mut engine, poll, OptionId(1), &h2, &binding2)
            .expect("a distinct holder clears the nullifier; the engine then judges the voter");
        assert_eq!(outcome2, CastOutcome::RefusedDoubleVote);
        assert_eq!(
            engine
                .tally(poll)
                .unwrap()
                .per_option
                .get(&OptionId(1))
                .copied()
                .unwrap_or(0),
            777,
            "the double-voter's second holding added no weight",
        );
    }

    // ── the VERIFIED front door: grants land on the executor engine ─────────

    /// The end-to-end flow on the VERIFIED box: the Lean-verdicted weight
    /// becomes a real executor turn — the tally that holds 777 is a `Monotonic`
    /// slot on a poll cell, the double-vote refusal is the executor engine's
    /// nullifier (not a `HashSet`), and the light-client replay agrees with the
    /// stored board.
    #[test]
    fn verified_end_to_end_grant_and_cast_lands_on_the_executor() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        let mut engine = VerifiedHoldingBallotBox::new([9u8; 32]);
        let poll = engine
            .open_weighted_poll(&PollSpec {
                question: "ship it?".into(),
                options: vec!["no".into(), "yes".into()],
                electorate: Electorate::Open,
                rule: DecisionRule::Plurality { quorum: 1 },
                enact_on_pass: false,
                nonce: 0,
            })
            .expect("weighted executor poll opens");

        let owner = owner_key(7);
        let owner_pk = owner.verifying_key().to_bytes();
        let voter: VoterId = [6u8; 32];
        let h = proven(owner_pk, [48u8; 32], 777, 20);
        let binding = bind(&owner, voter);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_snapshot(poll, 20);

        let outcome = reg
            .grant_and_cast(&mut engine, poll, OptionId(1), &h, &binding)
            .expect("grant succeeds");
        assert_eq!(outcome, CastOutcome::Accepted);

        // The proven balance N became N units of vote weight — ON THE EXECUTOR.
        let tally = engine.tally(poll).expect("executor tally");
        assert_eq!(tally.per_option, vec![0, 777]);
        assert_eq!(tally.total, 777);
        // The light-client replay of the cast log agrees with the stored board.
        assert_eq!(engine.light_client_tally(poll).unwrap(), tally);

        // A DIFFERENT holder bound to the SAME voter clears the registry
        // nullifier (distinct holder) and dies at the EXECUTOR's one-vote rule:
        // the voter's single ballot cell is already consumed.
        let owner2 = owner_key(8);
        let owner2_pk = owner2.verifying_key().to_bytes();
        let binding2 = bind(&owner2, voter);
        let h2 = proven(owner2_pk, [49u8; 32], 111, 20);
        let outcome2 = reg
            .grant_and_cast(&mut engine, poll, OptionId(1), &h2, &binding2)
            .expect("a distinct holder clears the nullifier; the executor judges the voter");
        assert_eq!(outcome2, CastOutcome::RefusedDoubleVote);
        assert_eq!(
            engine.tally(poll).unwrap().per_option,
            vec![0, 777],
            "the double-voter's second holding added no weight to the executor board",
        );

        // The weight quorum (Plurality { quorum: 1 } → total weight >= 1)
        // resolves as a real decision-turn.
        let decision = engine
            .resolve(poll)
            .expect("resolve adjudicates")
            .expect("777 >= 1 weight resolves");
        assert_eq!(decision.winner, 1);
        assert_eq!(decision.winner_tally, 777);
    }

    /// Registry semantics are UNCHANGED on the verified box: a holding proven
    /// at the wrong slot is `WrongSnapshot`; re-presenting the same account in
    /// the same poll is `AlreadyCounted`. Neither reaches the executor.
    #[test]
    fn verified_box_keeps_wrong_snapshot_and_already_counted_semantics() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        let mut engine = VerifiedHoldingBallotBox::new([9u8; 32]);
        let poll = engine
            .open_weighted_poll(&PollSpec {
                question: "semantics?".into(),
                options: vec!["no".into(), "yes".into()],
                electorate: Electorate::Open,
                rule: DecisionRule::Plurality { quorum: 1 },
                enact_on_pass: false,
                nonce: 1,
            })
            .unwrap();

        let owner = owner_key(21);
        let owner_pk = owner.verifying_key().to_bytes();
        let voter: VoterId = [21u8; 32];
        let binding = bind(&owner, voter);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_snapshot(poll, 30);

        // WRONG SNAPSHOT: proven at 31, pinned at 30 — refused before any cast.
        let stale = proven(owner_pk, [0xA1u8; 32], 500, 31);
        assert_eq!(
            reg.grant_and_cast(&mut engine, poll, OptionId(1), &stale, &binding),
            Err(GrantError::WrongSnapshot {
                holding_slot: 31,
                poll_snapshot: 30,
            }),
        );
        assert_eq!(engine.tally(poll).unwrap().total, 0);

        // The right slot counts…
        let good = proven(owner_pk, [0xA1u8; 32], 500, 30);
        assert_eq!(
            reg.grant_and_cast(&mut engine, poll, OptionId(1), &good, &binding)
                .unwrap(),
            CastOutcome::Accepted,
        );
        // …and re-presenting the SAME account is the registry's consume-once
        // nullifier, exactly as before.
        assert_eq!(
            reg.grant_and_cast(&mut engine, poll, OptionId(1), &good, &binding),
            Err(GrantError::AlreadyCounted),
        );
        assert_eq!(engine.tally(poll).unwrap().per_option, vec![0, 500]);
    }

    /// MINOR-2 on the verified box: a poll the executor engine has never opened
    /// must NOT consume the `(poll, token_account)` nullifier — the later valid
    /// attempt (once the poll opens) still counts.
    #[test]
    fn verified_box_poll_not_open_does_not_burn_the_nullifier() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        let mut engine = VerifiedHoldingBallotBox::new([9u8; 32]);
        let owner = owner_key(31);
        let owner_pk = owner.verifying_key().to_bytes();
        let voter: VoterId = [31u8; 32];
        let h = proven(owner_pk, [0xC4u8; 32], 640, 42);
        let binding = bind(&owner, voter);
        let mut reg = HoldingWeightRegistry::new();

        let ghost = PollId([0xEDu8; 32]);
        reg.open_snapshot(ghost, 42);
        assert_eq!(
            reg.grant_and_cast(&mut engine, ghost, OptionId(0), &h, &binding),
            Err(GrantError::PollNotOpen),
        );
        assert!(
            !reg.is_spent(ghost, &h),
            "a poll-not-open failure must leave the nullifier available",
        );

        let real = engine
            .open_weighted_poll(&PollSpec {
                question: "later".into(),
                options: vec!["a".into(), "b".into()],
                electorate: Electorate::Open,
                rule: DecisionRule::Plurality { quorum: 1 },
                enact_on_pass: false,
                nonce: 2,
            })
            .unwrap();
        reg.open_snapshot(real, 42);
        assert_eq!(
            reg.grant_and_cast(&mut engine, real, OptionId(0), &h, &binding)
                .unwrap(),
            CastOutcome::Accepted,
        );
        assert_eq!(engine.tally(real).unwrap().per_option, vec![640, 0]);
    }

    /// The weight quorum on the verified box reads WEIGHT, not headcount: one
    /// holding below the quorum leaves the poll pending; a second holding
    /// (different account, different voter) tips the total weight over and the
    /// decision-turn commits.
    #[test]
    fn verified_box_weight_quorum_resolves_on_weight() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        let mut engine = VerifiedHoldingBallotBox::new([9u8; 32]);
        let poll = engine
            .open_weighted_poll(&PollSpec {
                question: "weight quorum?".into(),
                options: vec!["no".into(), "yes".into()],
                electorate: Electorate::Open,
                rule: DecisionRule::Plurality { quorum: 1000 },
                enact_on_pass: false,
                nonce: 3,
            })
            .unwrap();

        let mut reg = HoldingWeightRegistry::new();
        reg.open_snapshot(poll, 50);

        let owner = owner_key(41);
        let voter: VoterId = [41u8; 32];
        let h = proven(owner.verifying_key().to_bytes(), [0xB1u8; 32], 600, 50);
        assert_eq!(
            reg.grant_and_cast(&mut engine, poll, OptionId(1), &h, &bind(&owner, voter))
                .unwrap(),
            CastOutcome::Accepted,
        );
        assert!(
            engine.resolve(poll).unwrap().is_none(),
            "600 < 1000 total weight must stay pending",
        );

        let owner2 = owner_key(42);
        let voter2: VoterId = [42u8; 32];
        let h2 = proven(owner2.verifying_key().to_bytes(), [0xB2u8; 32], 700, 50);
        assert_eq!(
            reg.grant_and_cast(&mut engine, poll, OptionId(1), &h2, &bind(&owner2, voter2))
                .unwrap(),
            CastOutcome::Accepted,
        );
        let decision = engine
            .resolve(poll)
            .unwrap()
            .expect("1300 >= 1000 total weight resolves");
        assert_eq!(decision.winner, 1);
        assert_eq!(decision.winner_tally, 1300);
    }

    #[test]
    fn poll_not_open_on_the_engine_does_not_burn_the_nullifier() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        // MINOR-2: if grant_and_cast targets a poll the engine has no ballot box for,
        // it must NOT consume the (poll, token_account) nullifier — otherwise a correct
        // later attempt (once the poll opens) is permanently DoS'd.
        let mut engine = HostBallotBox::new();
        let owner = owner_key(30);
        let owner_pk = owner.verifying_key().to_bytes();
        let voter: VoterId = [30u8; 32];
        let h = proven(owner_pk, [0xC3u8; 32], 640, 42);
        let binding = bind(&owner, voter);
        let mut reg = HoldingWeightRegistry::new();

        // Target a poll the engine does not know. The registry has a snapshot for it,
        // so we get past check_grant and fail specifically at the engine.
        let ghost = PollId([0xEEu8; 32]);
        reg.open_snapshot(ghost, 42);
        assert_eq!(
            reg.grant_and_cast(&mut engine, ghost, OptionId(0), &h, &binding),
            Err(GrantError::PollNotOpen),
        );
        assert!(
            !reg.is_spent(ghost, &h),
            "a poll-not-open failure must leave the nullifier available",
        );
        assert_eq!(reg.granted_count(), 0);

        // Now the poll opens for real — the SAME account still counts.
        let real = engine.open_poll(PollSpec {
            question: "later".into(),
            options: vec!["a".into(), "b".into()],
            electorate: Electorate::Open,
            rule: DecisionRule::Plurality { quorum: 1 },
            enact_on_pass: false,
            nonce: 1,
        });
        reg.open_snapshot(real, 42);
        assert_eq!(
            reg.grant_and_cast(&mut engine, real, OptionId(0), &h, &binding)
                .unwrap(),
            CastOutcome::Accepted,
        );
    }

    #[test]
    fn solana_holding_cannot_double_count_across_the_two_registry_paths() {
        // The audit's exact probe: the SAME Solana holding must not count twice by
        // mixing grant_into_poll (legacy) and grant_foreign_into_poll (generic). They
        // now share ONE (poll, chain+holder+asset) nullifier keyspace.
        //
        // Positive-path: the first grant must SUCCEED for the double-count probe to
        // mean anything, and a successful grant needs the Lean verdict core linked.
        // Same guard every other positive-path test here carries.
        if !lean_verdict_core_or_skip() {
            return;
        }
        let owner = owner_key(31);
        let owner_pk = owner.verifying_key().to_bytes();
        let voter: VoterId = [31u8; 32];
        let binding = bind(&owner, voter);
        let h = proven(owner_pk, [0xABu8; 32], 500, 9);
        let poll = PollId([0x77u8; 32]);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_snapshot(poll, 9); // the Solana snapshot

        assert_eq!(reg.grant_into_poll(poll, &h, &binding).unwrap().weight, 500);
        assert_eq!(reg.granted_count(), 1);
        // The SAME holding via the foreign path is now AlreadyCounted — NOT a second
        // independent nullifier.
        assert_eq!(
            reg.grant_foreign_into_poll(poll, &ProvenForeignHolding::from(&h), &binding),
            Err(GrantError::AlreadyCounted),
        );
        assert_eq!(
            reg.granted_count(),
            1,
            "one holding = one nullifier, whichever path"
        );
    }

    // ─── The CROSS-CHAIN spine: one weight binding for ANY chain ────────────────

    /// A consensus-proven chain-agnostic holding on `chain`, held by `holder`.
    fn foreign(
        chain: ChainId,
        holder: [u8; 32],
        asset: [u8; 32],
        amount: u128,
        snapshot: u64,
    ) -> ProvenForeignHolding {
        ProvenForeignHolding {
            chain,
            holder,
            asset,
            amount,
            snapshot,
            consensus_proven: true,
        }
    }

    #[test]
    fn a_consensus_proven_holding_on_each_chain_grants_weight_to_its_bound_voter() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        // The SAME generic path grants from Solana, EVM, and Cosmos facts alike.
        let poll = PollId([70u8; 32]);
        let mut reg = HoldingWeightRegistry::new();
        for (i, chain) in [
            ChainId::Solana,
            ChainId::ETHEREUM,
            ChainId::cosmos("cosmoshub-4"),
        ]
        .into_iter()
        .enumerate()
        {
            let owner = owner_key(40 + i as u8);
            let holder = owner.verifying_key().to_bytes();
            let voter: VoterId = [40 + i as u8; 32];
            let snapshot = 1_000 + i as u64; // each chain has its OWN clock
            reg.open_chain_snapshot(poll, chain, snapshot);
            let h = foreign(chain, holder, [0xAAu8; 32], 300 + i as u128, snapshot);
            let grant = reg
                .grant_foreign_into_poll(poll, &h, &bind(&owner, voter))
                .unwrap_or_else(|e| panic!("{chain:?} grant refused: {e:?}"));
            assert_eq!(
                grant.voter, voter,
                "{chain:?}: weight goes to the BOUND voter"
            );
            assert_eq!(
                grant.weight,
                300 + i as u128,
                "{chain:?}: weight = proven balance"
            );
            assert_eq!(grant.chain, chain);
            assert_eq!(grant.snapshot, snapshot);
        }
        assert_eq!(
            reg.granted_count(),
            3,
            "three chains, three distinct nullifiers"
        );
    }

    #[test]
    fn a_structure_only_foreign_holding_grants_zero_on_every_chain() {
        // REJECT polarity, NO Lean core needed (the pre-check fires first): an
        // unproven (RPC-echo) fact from ANY chain grants ZERO — the Nomad-law analog.
        for chain in [
            ChainId::Solana,
            ChainId::ETHEREUM,
            ChainId::cosmos("cosmoshub-4"),
        ] {
            let owner = owner_key(50);
            let holder = owner.verifying_key().to_bytes();
            let voter: VoterId = [50u8; 32];
            let mut h = foreign(chain, holder, [0xBBu8; 32], 1_000_000_000, 5);
            h.consensus_proven = false; // the structure-only rung
            assert_eq!(
                grant_foreign_weight(&h, &bind(&owner, voter)),
                Err(GrantError::NotConsensusProven),
                "{chain:?}: an unproven holding must grant ZERO, never its claimed amount",
            );
        }
    }

    #[test]
    fn foreign_unbound_owner_is_refused() {
        // REJECT polarity, NO Lean core needed: a binding not signed by the holding's
        // holder key grants nothing, on the generic path too.
        let owner = owner_key(51);
        let holder = owner.verifying_key().to_bytes();
        let attacker = owner_key(52);
        let voter: VoterId = [51u8; 32];
        let h = foreign(ChainId::ETHEREUM, holder, [0xCCu8; 32], 700, 9);
        assert_eq!(
            grant_foreign_weight(&h, &bind(&attacker, voter)),
            Err(GrantError::UnboundOwner),
            "a signature not by the holder must be refused",
        );
        // And a signature the owner made for a DIFFERENT voter cannot be re-pointed.
        let real = bind(&owner, voter);
        let swapped = OwnerBinding {
            voter: [99u8; 32],
            sig: real.sig,
        };
        assert_eq!(
            grant_foreign_weight(&h, &swapped),
            Err(GrantError::UnboundOwner),
        );
    }

    #[test]
    fn same_poll_holder_chain_asset_cannot_count_twice() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        let owner = owner_key(53);
        let holder = owner.verifying_key().to_bytes();
        let voter: VoterId = [53u8; 32];
        let binding = bind(&owner, voter);
        let poll = PollId([71u8; 32]);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_chain_snapshot(poll, ChainId::cosmos("cosmoshub-4"), 88);
        let h = foreign(
            ChainId::cosmos("cosmoshub-4"),
            holder,
            [0xDDu8; 32],
            400,
            88,
        );

        assert_eq!(
            reg.grant_foreign_into_poll(poll, &h, &binding)
                .unwrap()
                .weight,
            400
        );
        assert!(reg.is_foreign_spent(poll, &h));
        // REJECT polarity: re-presenting the same (poll, chain+holder+asset) is refused.
        assert_eq!(
            reg.grant_foreign_into_poll(poll, &h, &binding),
            Err(GrantError::AlreadyCounted),
            "the same holding must not grant weight twice in one poll",
        );
        // A DIFFERENT poll is a fresh nullifier.
        let other_poll = PollId([72u8; 32]);
        reg.open_chain_snapshot(other_poll, ChainId::cosmos("cosmoshub-4"), 88);
        assert_eq!(
            reg.grant_foreign_into_poll(other_poll, &h, &binding)
                .unwrap()
                .weight,
            400,
        );
    }

    #[test]
    fn the_same_holder_on_two_different_chains_is_two_distinct_nullifiers() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        // A holder who LEGITIMATELY holds on two chains counts both — the nullifier is
        // chain-scoped, so chain A's grant does not occupy chain B's slot.
        let owner = owner_key(54);
        let holder = owner.verifying_key().to_bytes();
        let voter: VoterId = [54u8; 32];
        let binding = bind(&owner, voter);
        let poll = PollId([73u8; 32]);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_chain_snapshot(poll, ChainId::ETHEREUM, 2_000);
        reg.open_chain_snapshot(poll, ChainId::cosmos("cosmoshub-4"), 3_000);

        let on_evm = foreign(ChainId::ETHEREUM, holder, [0xEEu8; 32], 111, 2_000);
        let on_cosmos = foreign(
            ChainId::cosmos("cosmoshub-4"),
            holder,
            [0xEEu8; 32],
            222,
            3_000,
        );
        let g1 = reg
            .grant_foreign_into_poll(poll, &on_evm, &binding)
            .unwrap();
        let g2 = reg
            .grant_foreign_into_poll(poll, &on_cosmos, &binding)
            .unwrap();
        assert_eq!(g1.weight, 111);
        assert_eq!(g2.weight, 222, "the second chain's holding counts too");
        assert_ne!(
            g1.nullifier, g2.nullifier,
            "chain-scoped: two DISTINCT nullifiers"
        );
        assert_eq!(reg.granted_count(), 2);
        // But the SAME chain again is still refused.
        assert_eq!(
            reg.grant_foreign_into_poll(poll, &on_evm, &binding),
            Err(GrantError::AlreadyCounted),
        );
    }

    #[test]
    fn foreign_snapshot_pin_is_per_chain_and_fail_closed() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        let owner = owner_key(55);
        let holder = owner.verifying_key().to_bytes();
        let voter: VoterId = [55u8; 32];
        let binding = bind(&owner, voter);
        let poll = PollId([74u8; 32]);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_chain_snapshot(poll, ChainId::ETHEREUM, 5_000);

        // Proven at a different height on the pinned chain → refused.
        let stale = foreign(ChainId::ETHEREUM, holder, [0x11u8; 32], 500, 5_001);
        assert_eq!(
            reg.grant_foreign_into_poll(poll, &stale, &binding),
            Err(GrantError::WrongSnapshot {
                holding_slot: 5_001,
                poll_snapshot: 5_000
            }),
        );
        // A chain with NO pin refuses outright — the Evm pin does not leak to Cosmos.
        let unpinned = foreign(
            ChainId::cosmos("cosmoshub-4"),
            holder,
            [0x11u8; 32],
            500,
            5_000,
        );
        assert_eq!(
            reg.grant_foreign_into_poll(poll, &unpinned, &binding),
            Err(GrantError::NoSnapshot),
        );
        // Neither refusal spent a nullifier.
        assert_eq!(reg.granted_count(), 0);
    }

    #[test]
    fn the_solana_from_lights_up_the_generic_path_end_to_end() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        // A REAL bridge ProvenHolding → From → the generic grant: the Solana edge is
        // live through the ONE cross-chain binding, and the thin-wrapper grant_weight
        // agrees with it.
        let owner = owner_key(56);
        let owner_pk = owner.verifying_key().to_bytes();
        let voter: VoterId = [56u8; 32];
        let binding = bind(&owner, voter);
        let h = proven(owner_pk, [0x42u8; 32], 12_345, 6_000);

        let f = ProvenForeignHolding::from(&h);
        let poll = PollId([75u8; 32]);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_chain_snapshot(poll, ChainId::Solana, 6_000);
        let g = reg.grant_foreign_into_poll(poll, &f, &binding).unwrap();
        assert_eq!(g.voter, voter);
        assert_eq!(
            g.weight, 12_345u128,
            "the proven Solana balance became weight"
        );
        assert_eq!(g.chain, ChainId::Solana);
        assert_eq!(g.snapshot, 6_000);

        // The legacy Solana entry is the thin wrapper over the SAME core: same verdict.
        let legacy = grant_weight(&h, &binding).unwrap();
        assert_eq!(legacy.weight as u128, g.weight);
        assert_eq!(legacy.voter, g.voter);
    }

    // ─── The u128 → u64 NARROWING SEAM (fail-closed) + multi-network EVM ────────

    #[test]
    fn narrow_ballot_weight_is_fail_closed_never_truncating() {
        // The pure narrowing (no Lean core involved — this runs ALWAYS):
        // exactly-u64::MAX fits losslessly...
        assert_eq!(
            narrow_ballot_weight(u64::MAX as u128),
            Ok(u64::MAX),
            "u64::MAX itself fits the ballot domain"
        );
        assert_eq!(narrow_ballot_weight(1), Ok(1));
        // REJECT polarity: one past the boundary is a TYPED refusal, not a wrap.
        let over = u64::MAX as u128 + 1;
        assert_eq!(
            narrow_ballot_weight(over),
            Err(GrantError::WeightOverflow { weight: over }),
        );
        // The truncation-attack shape: (1 << 64) + 5 truncates to 5 as a `u64 as` cast
        // — a whale silently shrunk to dust. It must REFUSE instead.
        let would_truncate_to_5 = (1u128 << 64) + 5;
        assert_eq!(
            narrow_ballot_weight(would_truncate_to_5),
            Err(GrantError::WeightOverflow {
                weight: would_truncate_to_5
            }),
            "a weight whose low 64 bits look tiny must refuse, never truncate",
        );
        // And u128::MAX (the saturation-attack shape) likewise refuses.
        assert_eq!(
            narrow_ballot_weight(u128::MAX),
            Err(GrantError::WeightOverflow { weight: u128::MAX }),
        );
    }

    #[test]
    fn an_evm_scale_weight_above_u64_refuses_the_cast_and_spends_nothing() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        // End-to-end REJECT polarity through the REAL engine: a proven EVM balance
        // above u64::MAX clears every grant check (it IS a genuine holding) but the
        // ballot cast REFUSES fail-closed at the narrowing seam — no truncated ballot,
        // no tally movement, no nullifier burned.
        let mut engine = HostBallotBox::new();
        let poll = engine.open_poll(PollSpec {
            question: "whale?".into(),
            options: vec!["no".into(), "yes".into()],
            electorate: Electorate::Open,
            rule: DecisionRule::Plurality { quorum: 1 },
            enact_on_pass: false,
            nonce: 2,
        });
        let owner = owner_key(60);
        let holder = owner.verifying_key().to_bytes();
        let voter: VoterId = [60u8; 32];
        let binding = bind(&owner, voter);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_chain_snapshot(poll, ChainId::ETHEREUM, 9_000);

        let too_big = (1u128 << 64) + 5; // would truncate to 5 — the attack shape
        let whale = foreign(ChainId::ETHEREUM, holder, [0x99u8; 32], too_big, 9_000);

        // The stateless grant itself is fine at u128 (the fact is real)...
        assert_eq!(
            grant_foreign_weight(&whale, &binding).unwrap().weight,
            too_big,
            "the u128 grant carries the full EVM-scale balance untruncated"
        );
        // ...but the CAST refuses at the u64 ballot boundary.
        assert_eq!(
            reg.foreign_grant_and_cast(&mut engine, poll, OptionId(1), &whale, &binding),
            Err(GrantError::WeightOverflow { weight: too_big }),
        );
        // Nothing was tallied — especially not a truncated 5.
        let tally = engine.tally(poll).unwrap();
        assert_eq!(tally.per_option.get(&OptionId(1)).copied().unwrap_or(0), 0);
        assert_eq!(tally.distinct_voters, 0);
        // And the nullifier is NOT spent (the refusal must not lock the holder out).
        assert!(!reg.is_foreign_spent(poll, &whale));
        assert_eq!(reg.granted_count(), 0);
    }

    #[test]
    fn a_normal_foreign_weight_casts_and_tallies() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        // ACCEPT polarity: a normal (fits-u64) foreign holding casts through
        // foreign_grant_and_cast and its full weight reaches the tally.
        let mut engine = HostBallotBox::new();
        let poll = engine.open_poll(PollSpec {
            question: "cross-chain ship it?".into(),
            options: vec!["no".into(), "yes".into()],
            electorate: Electorate::Open,
            rule: DecisionRule::Plurality { quorum: 1 },
            enact_on_pass: false,
            nonce: 3,
        });
        let owner = owner_key(61);
        let holder = owner.verifying_key().to_bytes();
        let voter: VoterId = [61u8; 32];
        let binding = bind(&owner, voter);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_chain_snapshot(poll, ChainId::BASE, 4_400);
        let h = foreign(ChainId::BASE, holder, [0x55u8; 32], 555, 4_400);

        assert_eq!(
            reg.foreign_grant_and_cast(&mut engine, poll, OptionId(1), &h, &binding)
                .unwrap(),
            CastOutcome::Accepted,
        );
        let tally = engine.tally(poll).unwrap();
        assert_eq!(
            tally.per_option.get(&OptionId(1)).copied().unwrap_or(0),
            555,
            "the proven foreign balance became ballot weight"
        );
        assert_eq!(tally.distinct_voters, 1);
        // The nullifier fired: the SAME holding re-presented is AlreadyCounted.
        assert!(reg.is_foreign_spent(poll, &h));
        assert_eq!(
            reg.foreign_grant_and_cast(&mut engine, poll, OptionId(1), &h, &binding),
            Err(GrantError::AlreadyCounted),
        );
    }

    #[test]
    fn the_same_holder_on_base_and_ethereum_is_two_distinct_nullifiers_both_count() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        // MULTI-NETWORK EVM: Base and Ethereum are different consensus domains under
        // ONE family tag — the same holder+asset on both is TWO facts; both count,
        // with two distinct nullifiers and two per-network snapshot pins.
        let owner = owner_key(62);
        let holder = owner.verifying_key().to_bytes();
        let voter: VoterId = [62u8; 32];
        let binding = bind(&owner, voter);
        let poll = PollId([76u8; 32]);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_chain_snapshot(poll, ChainId::ETHEREUM, 21_000_000);
        reg.open_chain_snapshot(poll, ChainId::BASE, 17_000_000);

        let on_eth = foreign(ChainId::ETHEREUM, holder, [0x66u8; 32], 100, 21_000_000);
        let on_base = foreign(ChainId::BASE, holder, [0x66u8; 32], 200, 17_000_000);
        let g1 = reg
            .grant_foreign_into_poll(poll, &on_eth, &binding)
            .unwrap();
        let g2 = reg
            .grant_foreign_into_poll(poll, &on_base, &binding)
            .unwrap();
        assert_eq!(g1.weight, 100);
        assert_eq!(g2.weight, 200, "the Base holding counts too");
        assert_ne!(
            g1.nullifier, g2.nullifier,
            "network-scoped: Base and Ethereum mint DISTINCT nullifiers"
        );
        assert_eq!(reg.granted_count(), 2);
        // REJECT polarity: the SAME network+holder+asset a second time is refused —
        // network multiplicity does not open a same-network double-count.
        assert_eq!(
            reg.grant_foreign_into_poll(poll, &on_eth, &binding),
            Err(GrantError::AlreadyCounted),
        );
        assert_eq!(
            reg.grant_foreign_into_poll(poll, &on_base, &binding),
            Err(GrantError::AlreadyCounted),
        );
        // And one network's pin does not leak to the other: a Base-height proof
        // presented as Ethereum is WrongSnapshot (fail closed).
        let cross = foreign(ChainId::ETHEREUM, holder, [0x67u8; 32], 100, 17_000_000);
        assert_eq!(
            reg.grant_foreign_into_poll(poll, &cross, &binding),
            Err(GrantError::WrongSnapshot {
                holding_slot: 17_000_000,
                poll_snapshot: 21_000_000
            }),
        );
    }

    // ─── The EVM (secp256k1) owner→voter binding ─────────────────────────────────

    use k256::ecdsa::{
        RecoveryId, Signature as EvmSignature, SigningKey as EvmSigningKey,
        VerifyingKey as EvmVerifyingKey,
    };

    /// A deterministic secp256k1 wallet key from a seed byte.
    fn evm_key(seed: u8) -> EvmSigningKey {
        EvmSigningKey::from_slice(&[seed; 32]).expect("a nonzero seed is a valid scalar")
    }

    fn evm_addr(key: &EvmSigningKey) -> [u8; 20] {
        evm_address_of_pubkey(key.verifying_key())
    }

    /// The ProvenForeignHolding holder convention for EVM: 12 zero bytes ‖ address.
    fn padded_holder(address: [u8; 20]) -> [u8; 32] {
        let mut h = [0u8; 32];
        h[12..].copy_from_slice(&address);
        h
    }

    /// A GENUINE EVM binding: the wallet key REALLY signs (RFC-6979 ECDSA, low-S)
    /// the EIP-191 prehash of the binding message for its own address, and the
    /// signature is packed wallet-style as r ‖ s ‖ v with v ∈ {27, 28}.
    fn evm_bind(key: &EvmSigningKey, voter: VoterId) -> EvmOwnerBinding {
        let prehash = eip191_message_hash(&evm_binding_message(&evm_addr(key), &voter));
        let (sig, recid) = key.sign_prehash_recoverable(&prehash).expect("signs");
        let mut bytes = [0u8; 65];
        bytes[..64].copy_from_slice(&sig.to_bytes());
        bytes[64] = recid.to_byte() + 27; // the Ethereum wallet convention
        EvmOwnerBinding { voter, sig: bytes }
    }

    #[test]
    fn evm_binding_message_and_prehash_are_the_documented_bytes() {
        use sha3::{Digest, Keccak256};
        assert_eq!(EVM_BIND_DOMAIN, b"dregg-holding-weight-bind-evm-v1");
        assert_eq!(EVM_BIND_DOMAIN.len(), 32);
        let addr = [0xABu8; 20];
        let voter: VoterId = [0xCDu8; 32];
        let msg = evm_binding_message(&addr, &voter);
        // domain(32) ‖ address(20) ‖ voter(32) — byte for byte.
        assert_eq!(msg.len(), 84);
        assert_eq!(&msg[..32], EVM_BIND_DOMAIN);
        assert_eq!(&msg[32..52], &addr);
        assert_eq!(&msg[52..84], &voter);
        // EIP-191: keccak256(0x19 ‖ "Ethereum Signed Message:\n" ‖ "84" ‖ msg).
        let mut framed = Vec::new();
        framed.extend_from_slice(b"\x19Ethereum Signed Message:\n84");
        framed.extend_from_slice(&msg);
        let expect: [u8; 32] = Keccak256::digest(&framed).into();
        assert_eq!(eip191_message_hash(&msg), expect);
    }

    #[test]
    fn a_genuine_evm_signature_by_the_addresss_key_binds() {
        // ACCEPT polarity, default-run (no Lean core needed): the address's own key
        // signing the EIP-191 binding message verifies...
        let key = evm_key(0x11);
        let voter: VoterId = [0x21u8; 32];
        let holder = padded_holder(evm_addr(&key));
        let binding = evm_bind(&key, voter);
        assert!(
            verify_evm_binding(&holder, &binding),
            "the holder's own wallet key must bind"
        );
        // ...and both wallet-style v (27/28) and raw recovery-id (0/1) encodings work.
        let mut raw_v = binding.clone();
        raw_v.sig[64] -= 27;
        assert!(verify_evm_binding(&holder, &raw_v));

        // The binding stage of grant_foreign_weight PASSES for it: on a zero-amount
        // holding the error is ZeroAmount — i.e. the check fell through the binding
        // gate and hit the next one (this pins the positive binding polarity into the
        // grant path without needing the Lean verdict core).
        let empty = foreign(ChainId::ETHEREUM, holder, [0x0Au8; 32], 0, 7);
        assert_eq!(
            grant_foreign_weight(&empty, &binding),
            Err(GrantError::ZeroAmount),
            "a genuine EVM binding must clear the UnboundOwner gate"
        );
    }

    #[test]
    fn evm_holding_grants_weight_via_the_native_secp256k1_binding() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        // End-to-end ACCEPT: an EVM-address holder — NO Ed25519 key anywhere — binds
        // their proven Base holding to a dregg voter and the weight lands.
        let key = evm_key(0x12);
        let voter: VoterId = [0x22u8; 32];
        let holder = padded_holder(evm_addr(&key));
        let binding = evm_bind(&key, voter);
        let poll = PollId([0x90u8; 32]);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_chain_snapshot(poll, ChainId::BASE, 17_500_000);
        let h = foreign(ChainId::BASE, holder, [0x0Bu8; 32], 1_234, 17_500_000);

        let grant = reg.grant_foreign_into_poll(poll, &h, &binding).unwrap();
        assert_eq!(grant.voter, voter);
        assert_eq!(grant.weight, 1_234);
        assert_eq!(grant.chain, ChainId::BASE);
        // The nullifier fired — the same holding cannot count twice, whichever
        // binding form presents it.
        assert_eq!(
            reg.grant_foreign_into_poll(poll, &h, &binding),
            Err(GrantError::AlreadyCounted),
        );
        // And the runtime-tagged VoterBinding wrapper reaches the same verdict.
        let poll2 = PollId([0x91u8; 32]);
        reg.open_chain_snapshot(poll2, ChainId::BASE, 17_500_000);
        let wrapped = VoterBinding::Evm(binding);
        assert_eq!(
            reg.grant_foreign_into_poll(poll2, &h, &wrapped)
                .unwrap()
                .weight,
            1_234,
        );
    }

    #[test]
    fn an_evm_signature_by_a_different_key_is_refused() {
        // REJECT polarity: the attacker signs the EXACT binding message for the
        // victim's address — recovery yields the ATTACKER's key, whose address is not
        // the holder's, so the binding is refused.
        let victim = evm_key(0x13);
        let attacker = evm_key(0x66);
        let voter: VoterId = [0x23u8; 32];
        let victim_addr = evm_addr(&victim);
        let holder = padded_holder(victim_addr);

        let prehash = eip191_message_hash(&evm_binding_message(&victim_addr, &voter));
        let (sig, recid) = attacker.sign_prehash_recoverable(&prehash).unwrap();
        let mut bytes = [0u8; 65];
        bytes[..64].copy_from_slice(&sig.to_bytes());
        bytes[64] = recid.to_byte() + 27;
        let forged = EvmOwnerBinding { voter, sig: bytes };

        assert!(
            !verify_evm_binding(&holder, &forged),
            "a signature by any key other than the address's must be refused"
        );
        let h = foreign(ChainId::ETHEREUM, holder, [0x0Cu8; 32], 900, 5);
        assert_eq!(
            grant_foreign_weight(&h, &forged),
            Err(GrantError::UnboundOwner),
        );
    }

    #[test]
    fn an_evm_binding_replayed_for_a_different_voter_is_refused() {
        // REJECT polarity: the message commits to the voter. A signature the owner
        // genuinely made for voter A, re-presented claiming voter B, recomputes to a
        // DIFFERENT prehash — recovery then yields some other key ≠ holder.
        let key = evm_key(0x14);
        let voter_a: VoterId = [0xA1u8; 32];
        let voter_b: VoterId = [0xB1u8; 32];
        let holder = padded_holder(evm_addr(&key));
        let genuine = evm_bind(&key, voter_a);
        assert!(verify_evm_binding(&holder, &genuine), "control: A binds");
        let replayed = EvmOwnerBinding {
            voter: voter_b,
            sig: genuine.sig,
        };
        assert!(
            !verify_evm_binding(&holder, &replayed),
            "a binding for voter A must not authorize voter B"
        );
        let h = foreign(ChainId::ETHEREUM, holder, [0x0Du8; 32], 900, 5);
        assert_eq!(
            grant_foreign_weight(&h, &replayed),
            Err(GrantError::UnboundOwner),
        );
    }

    #[test]
    fn a_non_evm_padded_holder_is_refused() {
        // REJECT polarity, fail-closed on SHAPE: holder[0..12] must be zero. Even a
        // GENUINE signature by the key whose address sits in holder[12..32] is refused
        // when the padding bytes are nonzero — those bytes are not an EVM address per
        // the convention, and treating them as one would let a 32-byte identity of
        // some other scheme be "bound" via its low 20 bytes.
        let key = evm_key(0x15);
        let voter: VoterId = [0x25u8; 32];
        let mut holder = padded_holder(evm_addr(&key));
        holder[0] = 1; // corrupt the padding
        assert_eq!(evm_address_of_holder(&holder), None);
        let binding = evm_bind(&key, voter);
        assert!(
            !verify_evm_binding(&holder, &binding),
            "a holder with nonzero padding is NOT an EVM address — refuse"
        );
        let h = foreign(ChainId::ETHEREUM, holder, [0x0Eu8; 32], 900, 5);
        assert_eq!(
            grant_foreign_weight(&h, &binding),
            Err(GrantError::UnboundOwner),
        );
    }

    #[test]
    fn a_malleable_high_s_signature_is_refused() {
        // REJECT polarity: the (r, -s, v^1) twin of a valid signature. This twin
        // WOULD recover to the very same address — we demonstrate that below — so the
        // low-S rule is the ONLY thing standing between one observed binding and a
        // second, distinct-bytes "binding" mintable by any third party.
        let key = evm_key(0x16);
        let voter: VoterId = [0x26u8; 32];
        let addr = evm_addr(&key);
        let holder = padded_holder(addr);
        let genuine = evm_bind(&key, voter);
        assert!(
            verify_evm_binding(&holder, &genuine),
            "control: genuine binds"
        );

        let sig = EvmSignature::from_slice(&genuine.sig[..64]).unwrap();
        let high = EvmSignature::from_scalars(sig.r().to_bytes(), (-*sig.s()).to_bytes())
            .expect("the negated-s twin is a well-formed signature");
        assert!(
            high.normalize_s().is_some(),
            "the twin really is high-S (k256 signing emits low-S, so -s is high)"
        );
        let flipped_v = if genuine.sig[64] == 27 { 28 } else { 27 };

        // The adversarial heart: the twin carries the SAME mathematical authorization
        // — normalizing its s back to the low half (and flipping the parity back)
        // recovers the very same address. So without a low-S rule an observer of one
        // binding could mint a second, distinct-bytes binding for it. The rule is
        // enforced at TWO layers here: our explicit normalize_s refusal in
        // verify_evm_binding, and k256's own verify (which recover_from_prehash calls)
        // refusing any high-S signature outright (k256-0.13 src/ecdsa.rs:203) — the
        // twin does not even recover on this stack.
        let prehash = eip191_message_hash(&evm_binding_message(&addr, &voter));
        let renormalized = high.normalize_s().unwrap();
        let recovered = EvmVerifyingKey::recover_from_prehash(
            &prehash,
            &renormalized,
            RecoveryId::from_byte((flipped_v - 27) ^ 1).unwrap(),
        )
        .expect("the twin's low-S normalization recovers");
        assert_eq!(
            evm_address_of_pubkey(&recovered),
            addr,
            "the twin encodes the SAME authorization under different bytes"
        );
        assert!(
            EvmVerifyingKey::recover_from_prehash(
                &prehash,
                &high,
                RecoveryId::from_byte(flipped_v - 27).unwrap(),
            )
            .is_err(),
            "k256 itself refuses to recover from a high-S signature (defense in depth)"
        );

        let mut forged_sig = [0u8; 65];
        forged_sig[..64].copy_from_slice(&high.to_bytes());
        forged_sig[64] = flipped_v;
        let forged = EvmOwnerBinding {
            voter,
            sig: forged_sig,
        };
        assert!(
            !verify_evm_binding(&holder, &forged),
            "the malleable high-S twin must be refused"
        );
        let h = foreign(ChainId::ETHEREUM, holder, [0x0Fu8; 32], 900, 5);
        assert_eq!(
            grant_foreign_weight(&h, &forged),
            Err(GrantError::UnboundOwner),
        );
    }

    #[test]
    fn an_out_of_range_v_is_refused() {
        // REJECT polarity: only v ∈ {0, 1, 27, 28}. The reduced-x ids (2/3, 29/30)
        // and arbitrary bytes are refused outright — the accepted v set stays tight.
        // (v = 0/1 and 27/28 are two encodings of the same recovery id; nothing in
        // the grant path keys on the binding's bytes, so that duality is harmless.)
        let key = evm_key(0x17);
        let voter: VoterId = [0x27u8; 32];
        let holder = padded_holder(evm_addr(&key));
        let genuine = evm_bind(&key, voter);
        for bad_v in [2u8, 3, 4, 26, 29, 30, 31, 0xFF] {
            let mut tampered = genuine.clone();
            tampered.sig[64] = bad_v;
            assert!(
                !verify_evm_binding(&holder, &tampered),
                "v = {bad_v} must be refused"
            );
        }
    }

    #[test]
    fn an_evm_binding_never_binds_a_solana_or_cosmos_holding() {
        // REJECT polarity, chain-shape dispatch: even a cryptographically-valid EVM
        // binding whose address matches the holder bytes is refused when the holding
        // is not EVM-family — Solana stays Ed25519-only, and the interim Cosmos
        // registered-Ed25519 convention is not silently widened.
        let key = evm_key(0x18);
        let voter: VoterId = [0x28u8; 32];
        let holder = padded_holder(evm_addr(&key));
        let binding = evm_bind(&key, voter);
        // Control: the same (holder, binding) pair IS valid signature-wise.
        assert!(verify_evm_binding(&holder, &binding));
        for chain in [ChainId::Solana, ChainId::cosmos("cosmoshub-4")] {
            let h = foreign(chain, holder, [0x1Au8; 32], 900, 5);
            assert_eq!(
                grant_foreign_weight(&h, &binding),
                Err(GrantError::UnboundOwner),
                "{chain:?}: an EVM signature must not bind a non-EVM holding",
            );
        }
        // And the inverse pairing through the tagged wrapper: an Ed25519 binding on a
        // Solana holding still binds (the pre-existing path, untouched), while the
        // SAME wallet's Ed25519 binding wrapped as Evm is nonsense and refused.
        let ed = owner_key(0x19);
        let ed_holder = ed.verifying_key().to_bytes();
        let ed_binding = bind(&ed, voter);
        let solana = foreign(ChainId::Solana, ed_holder, [0x1Bu8; 32], 0, 5);
        assert_eq!(
            grant_foreign_weight(&solana, &VoterBinding::Ed25519(ed_binding)),
            Err(GrantError::ZeroAmount),
            "Ed25519 on Solana clears the binding gate exactly as before"
        );
    }

    // ─── The Cosmos (secp256k1 / bech32-account) owner→voter binding ────────────

    use k256::ecdsa::signature::hazmat::{PrehashSigner, PrehashVerifier};

    /// A Cosmos wallet key is the same secp256k1 scalar an EVM wallet holds —
    /// `evm_key` doubles as the deterministic Cosmos test key.
    fn cosmos_addr(key: &EvmSigningKey) -> [u8; 20] {
        cosmos_address_of_pubkey(key.verifying_key())
    }

    fn cosmos_pubkey(key: &EvmSigningKey) -> [u8; 33] {
        key.verifying_key()
            .to_encoded_point(true)
            .as_bytes()
            .try_into()
            .expect("compressed SEC1 is 33 bytes")
    }

    /// A GENUINE Cosmos binding: the wallet key REALLY signs (RFC-6979 ECDSA,
    /// low-S) the SHA-256 prehash of the binding message for its OWN account
    /// address, and ships its compressed pubkey alongside — the Cosmos wire shape
    /// (pubkey + 64-byte (r ‖ s), no recovery id).
    fn cosmos_bind(key: &EvmSigningKey, voter: VoterId) -> CosmosOwnerBinding {
        let prehash = cosmos_binding_prehash(&cosmos_addr(key), &voter);
        let sig: EvmSignature = key.sign_prehash(&prehash).expect("signs");
        let mut bytes = [0u8; 64];
        bytes.copy_from_slice(&sig.to_bytes());
        CosmosOwnerBinding {
            voter,
            pubkey: cosmos_pubkey(key),
            sig: bytes,
        }
    }

    #[test]
    fn cosmos_binding_message_and_prehash_are_the_documented_bytes() {
        use sha2::{Digest, Sha256};
        assert_eq!(COSMOS_BIND_DOMAIN, b"dregg-holding-weight-bind-cosmos-v1");
        assert_eq!(COSMOS_BIND_DOMAIN.len(), 35);
        let addr = [0xABu8; 20];
        let voter: VoterId = [0xCDu8; 32];
        let msg = cosmos_binding_message(&addr, &voter);
        // domain(35) ‖ address(20) ‖ voter(32) — byte for byte.
        assert_eq!(msg.len(), 87);
        assert_eq!(&msg[..35], COSMOS_BIND_DOMAIN);
        assert_eq!(&msg[35..55], &addr);
        assert_eq!(&msg[55..87], &voter);
        // The prehash is exactly SHA-256 of those bytes (the dregg-specific sign
        // doc — documented as NOT ADR-036 amino-JSON).
        let expect: [u8; 32] = Sha256::digest(&msg).into();
        assert_eq!(cosmos_binding_prehash(&addr, &voter), expect);
    }

    #[test]
    fn cosmos_address_derivation_matches_the_known_hash160_vector() {
        // ADVERSARIAL GROUND TRUTH for ripemd160(sha256(compressed_pubkey)): the
        // widely-published hash160 vector (the Bitcoin-wiki "technical background"
        // example — Cosmos uses the IDENTICAL construction over the identical
        // curve). If the derivation hashed the wrong encoding (uncompressed, or
        // raw supplied bytes) or composed the digests in the wrong order, this
        // pins it.
        let sk = EvmSigningKey::from_slice(&[
            0x18, 0xE1, 0x4A, 0x7B, 0x6A, 0x30, 0x7F, 0x42, 0x6A, 0x94, 0xF8, 0x11, 0x47, 0x01,
            0xE7, 0xC8, 0xE7, 0x74, 0xE7, 0xF9, 0xA4, 0x7E, 0x2C, 0x20, 0x35, 0xDB, 0x29, 0xA2,
            0x06, 0x32, 0x17, 0x25,
        ])
        .expect("the vector's private scalar");
        assert_eq!(
            cosmos_pubkey(&sk),
            [
                0x02, 0x50, 0x86, 0x3A, 0xD6, 0x4A, 0x87, 0xAE, 0x8A, 0x2F, 0xE8, 0x3C, 0x1A, 0xF1,
                0xA8, 0x40, 0x3C, 0xB5, 0x3F, 0x53, 0xE4, 0x86, 0xD8, 0x51, 0x1D, 0xAD, 0x8A, 0x04,
                0x88, 0x7E, 0x5B, 0x23, 0x52,
            ],
            "the vector's compressed pubkey"
        );
        assert_eq!(
            cosmos_address_of_pubkey(sk.verifying_key()),
            [
                0xF5, 0x4A, 0x58, 0x51, 0xE9, 0x37, 0x2B, 0x87, 0x81, 0x0A, 0x8E, 0x60, 0xCD, 0xD2,
                0xE7, 0xCF, 0xD8, 0x0B, 0x6E, 0x31,
            ],
            "ripemd160(sha256(compressed_pubkey)) — the published hash160"
        );
    }

    #[test]
    fn a_genuine_cosmos_signature_by_the_holders_key_binds() {
        // ACCEPT polarity, default-run (no Lean core needed): the account's own
        // key signing the dregg Cosmos sign doc, shipping its own pubkey, binds.
        let key = evm_key(0x30);
        let voter: VoterId = [0x40u8; 32];
        let holder = padded_holder(cosmos_addr(&key));
        let binding = cosmos_bind(&key, voter);
        assert!(
            verify_cosmos_binding(&holder, &binding),
            "the holder's own wallet key must bind"
        );
        // The binding stage of grant_foreign_weight PASSES for it: on a
        // zero-amount holding the error is ZeroAmount — the check fell through
        // the UnboundOwner gate and hit the next one (positive binding polarity
        // pinned into the grant path without the Lean verdict core).
        let empty = foreign(ChainId::cosmos("cosmoshub-4"), holder, [0x2Au8; 32], 0, 7);
        assert_eq!(
            grant_foreign_weight(&empty, &binding),
            Err(GrantError::ZeroAmount),
            "a genuine Cosmos binding must clear the UnboundOwner gate"
        );
    }

    #[test]
    fn cosmos_holding_grants_weight_via_the_native_secp256k1_binding() {
        if !lean_verdict_core_or_skip() {
            return;
        }
        // End-to-end ACCEPT: a Cosmos account-address holder — NO Ed25519 key
        // anywhere — binds their proven cosmoshub-4 holding to a dregg voter and
        // the weight lands. This closes the trilogy: Solana Ed25519, EVM
        // secp256k1-address, Cosmos secp256k1-address holders all vote natively.
        let key = evm_key(0x31);
        let voter: VoterId = [0x41u8; 32];
        let holder = padded_holder(cosmos_addr(&key));
        let binding = cosmos_bind(&key, voter);
        let chain = ChainId::cosmos("cosmoshub-4");
        let poll = PollId([0xA0u8; 32]);
        let mut reg = HoldingWeightRegistry::new();
        reg.open_chain_snapshot(poll, chain, 21_000_000);
        let h = foreign(chain, holder, [0x2Bu8; 32], 4_321, 21_000_000);

        let grant = reg.grant_foreign_into_poll(poll, &h, &binding).unwrap();
        assert_eq!(grant.voter, voter);
        assert_eq!(grant.weight, 4_321);
        assert_eq!(grant.chain, chain);
        // The nullifier fired — the same holding cannot count twice.
        assert_eq!(
            reg.grant_foreign_into_poll(poll, &h, &binding),
            Err(GrantError::AlreadyCounted),
        );
        // And the runtime-tagged VoterBinding wrapper reaches the same verdict.
        let poll2 = PollId([0xA1u8; 32]);
        reg.open_chain_snapshot(poll2, chain, 21_000_000);
        let wrapped = VoterBinding::Cosmos(binding);
        assert_eq!(
            reg.grant_foreign_into_poll(poll2, &h, &wrapped)
                .unwrap()
                .weight,
            4_321,
        );
    }

    #[test]
    fn a_cosmos_signature_by_a_different_key_is_refused() {
        // REJECT polarity: the attacker signs the EXACT binding message for the
        // victim's address but carries the VICTIM's pubkey — the address check
        // passes, and the signature then fails to verify under that pubkey.
        let victim = evm_key(0x32);
        let attacker = evm_key(0x67);
        let voter: VoterId = [0x42u8; 32];
        let victim_addr = cosmos_addr(&victim);
        let holder = padded_holder(victim_addr);

        let prehash = cosmos_binding_prehash(&victim_addr, &voter);
        let sig: EvmSignature = attacker.sign_prehash(&prehash).unwrap();
        let mut bytes = [0u8; 64];
        bytes.copy_from_slice(&sig.to_bytes());
        let forged = CosmosOwnerBinding {
            voter,
            pubkey: cosmos_pubkey(&victim), // the victim's key did NOT make this sig
            sig: bytes,
        };
        assert!(
            !verify_cosmos_binding(&holder, &forged),
            "a signature by any key other than the address's must be refused"
        );
        let h = foreign(ChainId::cosmos("cosmoshub-4"), holder, [0x2Cu8; 32], 900, 5);
        assert_eq!(
            grant_foreign_weight(&h, &forged),
            Err(GrantError::UnboundOwner),
        );
    }

    #[test]
    fn a_cosmos_pubkey_whose_address_is_not_the_holders_is_refused() {
        // REJECT polarity — THE load-bearing check: the attacker presents a fully
        // SELF-CONSISTENT binding (their own pubkey + a genuine signature under it
        // over the victim-address message), but ripemd160(sha256(their pubkey)) is
        // not the holder address. Without the derived-address equality this would
        // pass — any keypair could bind any Cosmos holding.
        let victim = evm_key(0x33);
        let attacker = evm_key(0x68);
        let voter: VoterId = [0x43u8; 32];
        let victim_addr = cosmos_addr(&victim);
        let holder = padded_holder(victim_addr);

        let prehash = cosmos_binding_prehash(&victim_addr, &voter);
        let sig: EvmSignature = attacker.sign_prehash(&prehash).unwrap();
        let mut bytes = [0u8; 64];
        bytes.copy_from_slice(&sig.to_bytes());
        let forged = CosmosOwnerBinding {
            voter,
            pubkey: cosmos_pubkey(&attacker), // valid sig under THIS key...
            sig: bytes,
        };
        // ...(control: the signature REALLY verifies under the carried pubkey
        // over the victim-address prehash — so the derived-address equality is
        // the ONLY gate standing between this forgery and a grant)...
        assert!(
            attacker
                .verifying_key()
                .verify_prehash(&prehash, &sig)
                .is_ok(),
            "control: the forgery is self-consistent pubkey/sig-wise"
        );
        // ...but its derived address is not the victim's holder — refused.
        assert!(
            !verify_cosmos_binding(&holder, &forged),
            "a pubkey whose derived address is not the holder must be refused"
        );
        let h = foreign(ChainId::cosmos("cosmoshub-4"), holder, [0x2Du8; 32], 900, 5);
        assert_eq!(
            grant_foreign_weight(&h, &forged),
            Err(GrantError::UnboundOwner),
        );
    }

    #[test]
    fn a_cosmos_binding_replayed_for_a_different_voter_is_refused() {
        // REJECT polarity: the sign doc commits to the voter. A signature the
        // owner genuinely made for voter A, re-presented claiming voter B,
        // verifies against a DIFFERENT recomputed prehash and fails.
        let key = evm_key(0x34);
        let voter_a: VoterId = [0xA2u8; 32];
        let voter_b: VoterId = [0xB2u8; 32];
        let holder = padded_holder(cosmos_addr(&key));
        let genuine = cosmos_bind(&key, voter_a);
        assert!(verify_cosmos_binding(&holder, &genuine), "control: A binds");
        let replayed = CosmosOwnerBinding {
            voter: voter_b,
            pubkey: genuine.pubkey,
            sig: genuine.sig,
        };
        assert!(
            !verify_cosmos_binding(&holder, &replayed),
            "a binding for voter A must not authorize voter B"
        );
        let h = foreign(ChainId::cosmos("cosmoshub-4"), holder, [0x2Eu8; 32], 900, 5);
        assert_eq!(
            grant_foreign_weight(&h, &replayed),
            Err(GrantError::UnboundOwner),
        );
    }

    #[test]
    fn a_non_padded_cosmos_holder_is_refused() {
        // REJECT polarity, fail-closed on SHAPE: holder[0..12] must be zero. Even
        // a GENUINE signature by the key whose address sits in holder[12..32] is
        // refused when the padding bytes are nonzero — a 32-byte module/ICA
        // account (or any other identity scheme) must not be "bindable" via its
        // low 20 bytes.
        let key = evm_key(0x35);
        let voter: VoterId = [0x45u8; 32];
        let mut holder = padded_holder(cosmos_addr(&key));
        holder[0] = 1; // corrupt the padding
        assert_eq!(cosmos_address_of_holder(&holder), None);
        let binding = cosmos_bind(&key, voter);
        assert!(
            !verify_cosmos_binding(&holder, &binding),
            "a holder with nonzero padding is NOT a 20-byte account address — refuse"
        );
        let h = foreign(ChainId::cosmos("cosmoshub-4"), holder, [0x2Fu8; 32], 900, 5);
        assert_eq!(
            grant_foreign_weight(&h, &binding),
            Err(GrantError::UnboundOwner),
        );
        // A full 32-byte (module/ICA-shaped) holder likewise refuses.
        assert_eq!(cosmos_address_of_holder(&[0x77u8; 32]), None);
    }

    #[test]
    fn a_cosmos_high_s_signature_is_refused() {
        // REJECT polarity: the (r, -s) malleable twin of a valid signature. The
        // twin carries the SAME mathematical authorization — normalizing its s
        // returns the genuine signature bytes exactly — so without the low-S rule
        // any observer of one binding could mint a second, distinct-bytes
        // "binding". Enforced at TWO layers: our explicit normalize_s refusal in
        // verify_cosmos_binding, and k256's own verify_prehash refusing high-S
        // outright (the same defense-in-depth the EVM path documents).
        let key = evm_key(0x36);
        let voter: VoterId = [0x46u8; 32];
        let addr = cosmos_addr(&key);
        let holder = padded_holder(addr);
        let genuine = cosmos_bind(&key, voter);
        assert!(
            verify_cosmos_binding(&holder, &genuine),
            "control: genuine binds"
        );

        let sig = EvmSignature::from_slice(&genuine.sig).unwrap();
        let high = EvmSignature::from_scalars(sig.r().to_bytes(), (-*sig.s()).to_bytes())
            .expect("the negated-s twin is a well-formed signature");
        assert!(
            high.normalize_s().is_some(),
            "the twin really is high-S (k256 signing emits low-S, so -s is high)"
        );
        // The adversarial heart: the twin IS the same authorization under
        // different bytes — normalizing it back yields the genuine signature.
        assert_eq!(
            high.normalize_s().unwrap().to_bytes(),
            sig.to_bytes(),
            "the high-S twin renormalizes to the genuine signature"
        );
        // Defense in depth: k256's own verifier refuses the high-S form too.
        let prehash = cosmos_binding_prehash(&addr, &voter);
        assert!(
            key.verifying_key().verify_prehash(&prehash, &high).is_err(),
            "k256 itself refuses a high-S signature"
        );

        let mut forged_sig = [0u8; 64];
        forged_sig.copy_from_slice(&high.to_bytes());
        let forged = CosmosOwnerBinding {
            voter,
            pubkey: genuine.pubkey,
            sig: forged_sig,
        };
        assert!(
            !verify_cosmos_binding(&holder, &forged),
            "the malleable high-S twin must be refused"
        );
        let h = foreign(ChainId::cosmos("cosmoshub-4"), holder, [0x3Au8; 32], 900, 5);
        assert_eq!(
            grant_foreign_weight(&h, &forged),
            Err(GrantError::UnboundOwner),
        );
    }

    #[test]
    fn a_malformed_cosmos_pubkey_is_refused() {
        // REJECT polarity: the carried pubkey must be a valid COMPRESSED SEC1
        // point. An uncompressed lead byte (0x04 — 33 bytes is the wrong length
        // for it anyway), an unknown tag, an off-curve/over-p x, or all-zeros must
        // refuse at the parse, never reach the hash-and-verify.
        let key = evm_key(0x37);
        let voter: VoterId = [0x47u8; 32];
        let holder = padded_holder(cosmos_addr(&key));
        let genuine = cosmos_bind(&key, voter);
        for tamper in [0x00u8, 0x04, 0x05, 0xFF] {
            let mut bad = genuine.clone();
            bad.pubkey[0] = tamper;
            assert!(
                !verify_cosmos_binding(&holder, &bad),
                "pubkey tag {tamper:#x} must be refused"
            );
        }
        let mut bad = genuine.clone();
        bad.pubkey = [0u8; 33];
        assert!(!verify_cosmos_binding(&holder, &bad), "zero pubkey refused");
        bad.pubkey = [0xFFu8; 33];
        assert!(
            !verify_cosmos_binding(&holder, &bad),
            "an over-p x coordinate must be refused"
        );
    }

    #[test]
    fn a_cosmos_binding_never_binds_a_solana_or_evm_holding() {
        // REJECT polarity, chain-shape dispatch: even a cryptographically-valid
        // Cosmos binding whose derived address matches the holder bytes is refused
        // when the holding is not Cosmos-family — Solana stays Ed25519-only, and
        // an EVM holding (whose padded-20-byte holder SHAPE is identical) must
        // never be bound by a ripemd160-sha256 address scheme.
        let key = evm_key(0x38);
        let voter: VoterId = [0x48u8; 32];
        let holder = padded_holder(cosmos_addr(&key));
        let binding = cosmos_bind(&key, voter);
        // Control: the same (holder, binding) pair IS valid signature-wise.
        assert!(verify_cosmos_binding(&holder, &binding));
        for chain in [ChainId::Solana, ChainId::ETHEREUM, ChainId::BASE] {
            let h = foreign(chain, holder, [0x3Bu8; 32], 900, 5);
            assert_eq!(
                grant_foreign_weight(&h, &binding),
                Err(GrantError::UnboundOwner),
                "{chain:?}: a Cosmos binding must not bind a non-Cosmos holding",
            );
            // The tagged wrapper reaches the same refusal.
            assert_eq!(
                grant_foreign_weight(&h, &VoterBinding::Cosmos(binding.clone())),
                Err(GrantError::UnboundOwner),
            );
        }
        // And the SAME KEY's addresses genuinely differ per family — the keccak
        // EVM address of this key is NOT its Cosmos account address, so even
        // without the chain gate the cross-family holder bytes would not match.
        assert_ne!(
            evm_address_of_pubkey(key.verifying_key()),
            cosmos_addr(&key),
            "keccak-address ≠ ripemd160-sha256-address for one key"
        );
    }
}
