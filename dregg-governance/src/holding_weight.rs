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

use std::collections::{BTreeMap, HashSet};

use ed25519_dalek::{Signature, VerifyingKey};

use dregg_bridge::solana_holdings::ProvenHolding;

use crate::{CastOutcome, CollectiveChoice, OptionId, PollId, VoteEngine, VoterId};

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

/// Why a weight grant was refused. Every variant grants ZERO weight (fail closed).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GrantError {
    /// The holding is not consensus-proven (a [`StructureOnly`](dregg_bridge::solana_trustless::LockProofTrust::StructureOnly)
    /// RPC echo, or any non-`ConsensusVerified` trust). The Nomad-law analog: no
    /// supermajority proof, no weight.
    NotConsensusProven,
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
}

/// The pure weight-granting primitive: check that `holding` is consensus-proven and that
/// `binding` is a genuine owner→voter authorization, then grant weight equal to the
/// proven balance to `binding.voter`, as-of the proven slot.
///
/// This performs NO dedup — it is the stateless core. Use [`HoldingWeightRegistry`] when
/// you need the per-poll no-double-count nullifier.
///
/// Fail-closed order: consensus first (a `StructureOnly` holding is refused before its
/// signature is even examined), then the binding, then a positive-amount check.
pub fn grant_weight(
    holding: &ProvenHolding,
    binding: &OwnerBinding,
) -> Result<WeightGrant, GrantError> {
    if !holding.is_consensus_proven() {
        return Err(GrantError::NotConsensusProven);
    }
    if !verify_binding(&holding.owner, binding) {
        return Err(GrantError::UnboundOwner);
    }
    if holding.amount == 0 {
        return Err(GrantError::ZeroAmount);
    }
    Ok(WeightGrant {
        voter: binding.voter,
        weight: holding.amount,
        slot: holding.slot,
        token_account: holding.token_account,
    })
}

/// A per-poll ledger of which SPL token accounts have already granted weight — the
/// snapshot's consume-once nullifier set. It carries no value and holds no escrow; it
/// only records `(poll, token_account)` pairs so the same holding cannot be counted
/// twice in one poll.
#[derive(Clone, Debug, Default)]
pub struct HoldingWeightRegistry {
    /// The fired nullifiers: a `(poll, token_account)` is present once its weight has
    /// been granted into that poll.
    spent: HashSet<(PollId, [u8; 32])>,
    /// The finalized SNAPSHOT slot each poll pins its holding-weight to. Every holding
    /// counted in a poll must be proven at exactly this slot (see
    /// [`GrantError::WrongSnapshot`]).
    poll_snapshot: BTreeMap<PollId, u64>,
}

impl HoldingWeightRegistry {
    /// A fresh registry with no granted holdings.
    pub fn new() -> Self {
        HoldingWeightRegistry::default()
    }

    /// Pin `poll`'s holding-weight SNAPSHOT to the finalized `slot`. Every holding
    /// counted in `poll` must be proven at exactly this slot — the defence against
    /// double-counting the same tokens by proving them across accounts at different
    /// slots. Call once when the poll's holding-weight window opens.
    pub fn open_snapshot(&mut self, poll: PollId, slot: u64) {
        self.poll_snapshot.insert(poll, slot);
    }

    /// The pinned snapshot slot for `poll`, if any.
    pub fn snapshot_of(&self, poll: PollId) -> Option<u64> {
        self.poll_snapshot.get(&poll).copied()
    }

    /// Has `token_account` already granted weight in `poll`?
    pub fn is_spent(&self, poll: PollId, token_account: &[u8; 32]) -> bool {
        self.spent.contains(&(poll, *token_account))
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
        self.spent.insert((poll, grant.token_account));
        Ok(grant)
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
            .poll_snapshot
            .get(&poll)
            .copied()
            .ok_or(GrantError::NoSnapshot)?;
        if holding.slot != snapshot {
            return Err(GrantError::WrongSnapshot {
                holding_slot: holding.slot,
                poll_snapshot: snapshot,
            });
        }
        let grant = grant_weight(holding, binding)?;
        if self.spent.contains(&(poll, grant.token_account)) {
            return Err(GrantError::AlreadyCounted);
        }
        Ok(grant)
    }

    /// End-to-end convenience: grant `holding`'s weight into `poll` (dedup-guarded) and
    /// cast a ballot for `choice` carrying that weight into the [`CollectiveChoice`]
    /// engine as the bound voter. The engine applies its OWN one-vote-per-voter rule on
    /// top, so a second holding bound to the same voter is refused there
    /// ([`CastOutcome::RefusedDoubleVote`]) even though it is a distinct token-account
    /// nullifier here.
    ///
    /// Note the two guards are complementary: the nullifier stops the *same account*
    /// voting twice; the engine's voted-set stops the *same voter* voting twice.
    pub fn grant_and_cast(
        &mut self,
        engine: &mut CollectiveChoice,
        poll: PollId,
        choice: OptionId,
        holding: &ProvenHolding,
        binding: &OwnerBinding,
    ) -> Result<CastOutcome, GrantError> {
        // Verify WITHOUT consuming the nullifier first — so a poll-not-open failure
        // does not permanently burn this (poll, token_account).
        let grant = self.check_grant(poll, holding, binding)?;
        let block = engine
            .next_block(poll, grant.voter, choice, grant.weight)
            .ok_or(GrantError::PollNotOpen)?; // unknown poll: no ballot box — nullifier untouched
        // The engine accepted a ballot box: NOW consume the nullifier and cast.
        self.spent.insert((poll, grant.token_account));
        Ok(engine.cast(poll, block))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_bridge::solana_trustless::LockProofTrust;
    use ed25519_dalek::{Signer, SigningKey};

    use crate::{DecisionRule, Electorate, PollSpec};

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
        // The weight flows all the way into the real CollectiveChoice tally.
        let mut engine = CollectiveChoice::new();
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

        // A second holding bound to the SAME voter is refused by the engine's own
        // one-vote-per-voter rule (distinct token-account nullifier here, same voter).
        let h2 = proven(owner_pk, [49u8; 32], 111, 20);
        let outcome2 = reg
            .grant_and_cast(&mut engine, poll, OptionId(1), &h2, &binding)
            .expect("nullifier allows a distinct account; engine then judges the voter");
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

    #[test]
    fn poll_not_open_on_the_engine_does_not_burn_the_nullifier() {
        // MINOR-2: if grant_and_cast targets a poll the engine has no ballot box for,
        // it must NOT consume the (poll, token_account) nullifier — otherwise a correct
        // later attempt (once the poll opens) is permanently DoS'd.
        let mut engine = CollectiveChoice::new();
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
            !reg.is_spent(ghost, &[0xC3u8; 32]),
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
}
