//! The NETWORK-CEREMONY shape: the Pedersen-style DKG ([`crate::dkg`]) and
//! the Raccoon 2-round signing ([`crate::threshold`]) driven as
//! MESSAGE-PASSING protocols over a transport abstraction — each party runs
//! [`run_dkg_ceremony`] / [`run_sign_ceremony`] against a [`Channel`], sends
//! its round message, receives the others', and proceeds. The SAME protocol
//! code runs over the in-memory [`LocalNetwork`] (tests) or a real network
//! transport later; the cryptography is byte-for-byte the in-process
//! reference's (`dkg_deal`/`verify_dkg_share`, `RaccoonSigner`/
//! `RaccoonSignSession`) — this module changes WHO CALLS IT and HOW THE
//! INTERMEDIATE VALUES TRAVEL, not the algebra.
//!
//! # The rounds, as messages
//!
//! DKG (one channel with all `n` members):
//! 1. **Dealing** — every member broadcasts a [`DkgDealingMsg`]: its Feldman
//!    commitments plus its per-recipient shares.
//! 2. **Ack/complaint** — every member Feldman-verifies the shares addressed
//!    to it and broadcasts a [`DkgAckMsg`] (an ack, or a complaint naming the
//!    cheating dealer). Any complaint aborts the ceremony with the accused
//!    dealer named ([`crate::dkg::DkgError::Complaint`]).
//!
//! Signing (one channel with the `t` signers):
//! 1. **Commit** — each signer broadcasts its hash commitment
//!    [`RaccoonCommitMsg`] (`cm_i`, never `w_i`).
//! 2. **Reveal** — each signer broadcasts its [`RaccoonRevealMsg`] (`w_i`),
//!    verified against the frozen commitment set.
//! 3. **Respond** — each signer broadcasts its partial response
//!    [`RaccoonResponseMsg`] (`z_i`); everyone assembles and verifies the
//!    same [`HermineSignature`].
//!
//! # The commit-then-reveal boundary IS the round barrier
//!
//! A party obtains the round-1 commitment set only from
//! [`Channel::recv_round`], and the transport completes a round only when
//! EVERY party's message for it is in. A signer therefore cannot send its
//! reveal until all commitments exist — and cannot inject a second message
//! (a rushed reveal) into the commit round, because the transport pins ONE
//! broadcast per party per round ([`ChannelError::DuplicateSend`]). The
//! `ceremony_commit_reveal_barrier` test pins exactly this.
//!
//! # HONEST boundary — reference transport, message-shaped protocol
//!
//! This module makes the PROTOCOL transport-agnostic (the deployable-shape
//! step): serde-carried round messages, a [`Channel`] seam, per-party
//! drivers. What it does NOT provide: a real network transport, timeouts,
//! retransmission, party authentication/encryption (a deployment encrypts
//! the per-recipient DKG shares — here they ride the broadcast, as in the
//! in-process reference), or Byzantine round-abort recovery (a party that
//! never sends stalls the round; misbehavior is DETECTED and named, not
//! arbitrated). [`LocalNetwork`] is in-memory and synchronous; a real async
//! network transport behind the same [`Channel`] trait is the next
//! engineering layer. Same crate-wide reference boundary as ever
//! (reference PRNG seeds, not constant-time, pre-audit).

use std::sync::{Arc, Condvar, Mutex};

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use crate::dkg::{dkg_deal, verify_dkg_share, DkgError, DkgShareMsg};
use crate::linalg::{Matrix, PolyVec};
use crate::ring::Q;
use crate::threshold::{
    raccoon_challenge, sample_poly, verify_hermine_raccoon, HermineShare, HermineSignature,
    RaccoonCommitMsg, RaccoonError, RaccoonRevealMsg, RaccoonSignSession, RaccoonSigner,
};

// =============================================================================
// The transport abstraction
// =============================================================================

/// Why a transport operation refused.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ChannelError {
    /// The current round is not complete — some party has not broadcast yet
    /// (surfaced by non-blocking receives such as
    /// [`LocalChannel::try_recv_round`]).
    RoundIncomplete,
    /// This party already broadcast in the current round: one message per
    /// party per round — the round-structure tooth that keeps a rushed
    /// second message (e.g. an early reveal) out of the commit round.
    DuplicateSend,
}

/// A synchronous broadcast-round transport, one endpoint per party.
///
/// The contract the ceremonies drive against:
/// * parties are `1..=parties()`, this endpoint is party [`Channel::me`];
/// * [`Channel::broadcast`] sends this party's ONE message for the current
///   round (a second send in the same round is [`ChannelError::DuplicateSend`]);
/// * [`Channel::recv_round`] yields ALL parties' messages for the current
///   round — `(party, bytes)` in ascending party order, self included — and
///   advances this endpoint to the next round. It completes only when every
///   party has broadcast: THE ROUND BARRIER.
///
/// Messages are opaque bytes at this seam (the ceremonies serde-encode their
/// round messages), so a real network transport can implement the same trait
/// without knowing the protocol.
pub trait Channel {
    /// This endpoint's 1-based party index.
    fn me(&self) -> u64;
    /// The number of parties on the channel.
    fn parties(&self) -> u64;
    /// Broadcast this party's message for the current round.
    fn broadcast(&mut self, bytes: Vec<u8>) -> Result<(), ChannelError>;
    /// Receive the complete current round (waiting for it if necessary) and
    /// advance to the next.
    fn recv_round(&mut self) -> Result<Vec<(u64, Vec<u8>)>, ChannelError>;
}

/// The shared state behind a [`LocalNetwork`]: per-round, per-party message
/// slots. `rounds[r][p-1]` is party `p`'s broadcast for round `r`.
struct NetInner {
    n: usize,
    rounds: Vec<Vec<Option<Vec<u8>>>>,
}

impl NetInner {
    fn ensure_round(&mut self, round: usize) {
        while self.rounds.len() <= round {
            self.rounds.push(vec![None; self.n]);
        }
    }

    fn round_complete(&self, round: usize) -> bool {
        self.rounds
            .get(round)
            .is_some_and(|row| row.iter().all(Option::is_some))
    }

    fn collect_round(&self, round: usize) -> Vec<(u64, Vec<u8>)> {
        self.rounds[round]
            .iter()
            .enumerate()
            .map(|(i, m)| (i as u64 + 1, m.clone().expect("round complete")))
            .collect()
    }
}

/// The in-memory reference transport for `n` parties: broadcasts land in
/// shared per-round slots; [`Channel::recv_round`] blocks (condvar) until the
/// round is complete. The bytes really are routed as bytes — each ceremony
/// message crosses a serde encode/decode, so the messages provably survive a
/// byte transport.
pub struct LocalNetwork {
    shared: Arc<(Mutex<NetInner>, Condvar)>,
    n: u64,
}

impl LocalNetwork {
    /// A fresh network of `n ≥ 1` parties.
    pub fn new(n: u64) -> Option<Self> {
        if n == 0 {
            return None;
        }
        Some(Self {
            shared: Arc::new((
                Mutex::new(NetInner {
                    n: n as usize,
                    rounds: Vec::new(),
                }),
                Condvar::new(),
            )),
            n,
        })
    }

    /// One endpoint per party, all starting at round 0. Take them once, at
    /// ceremony start (endpoints share the round history, so a late second
    /// set would replay it).
    pub fn channels(&self) -> Vec<LocalChannel> {
        (1..=self.n)
            .map(|me| LocalChannel {
                shared: Arc::clone(&self.shared),
                me,
                n: self.n,
                round: 0,
            })
            .collect()
    }
}

/// One party's endpoint on a [`LocalNetwork`].
pub struct LocalChannel {
    shared: Arc<(Mutex<NetInner>, Condvar)>,
    me: u64,
    n: u64,
    round: usize,
}

impl LocalChannel {
    /// Non-blocking receive: the complete current round, or
    /// [`ChannelError::RoundIncomplete`] if some party has not broadcast —
    /// the observable form of the round barrier (the blocking
    /// [`Channel::recv_round`] simply waits where this refuses).
    pub fn try_recv_round(&mut self) -> Result<Vec<(u64, Vec<u8>)>, ChannelError> {
        let (lock, _) = &*self.shared;
        let inner = lock.lock().expect("local network lock");
        if !inner.round_complete(self.round) {
            return Err(ChannelError::RoundIncomplete);
        }
        let out = inner.collect_round(self.round);
        self.round += 1;
        Ok(out)
    }
}

impl Channel for LocalChannel {
    fn me(&self) -> u64 {
        self.me
    }

    fn parties(&self) -> u64 {
        self.n
    }

    fn broadcast(&mut self, bytes: Vec<u8>) -> Result<(), ChannelError> {
        let (lock, cvar) = &*self.shared;
        let mut inner = lock.lock().expect("local network lock");
        inner.ensure_round(self.round);
        let slot = &mut inner.rounds[self.round][(self.me - 1) as usize];
        if slot.is_some() {
            return Err(ChannelError::DuplicateSend);
        }
        *slot = Some(bytes);
        cvar.notify_all();
        Ok(())
    }

    fn recv_round(&mut self) -> Result<Vec<(u64, Vec<u8>)>, ChannelError> {
        let (lock, cvar) = &*self.shared;
        let mut inner = lock.lock().expect("local network lock");
        while !inner.round_complete(self.round) {
            inner = cvar.wait(inner).expect("local network lock");
        }
        let out = inner.collect_round(self.round);
        self.round += 1;
        Ok(out)
    }
}

// =============================================================================
// Ceremony errors and messages
// =============================================================================

/// Why a ceremony refused to complete.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CeremonyError {
    /// The transport refused (round violation).
    Channel(ChannelError),
    /// Party `from` sent bytes that do not decode to the round's message
    /// type, or a message whose embedded identity/shape contradicts the
    /// round (wire hygiene).
    BadMessage {
        /// The party whose message was rejected.
        from: u64,
    },
    /// Degenerate ceremony parameters (threshold/committee shape).
    BadParameters,
    /// The DKG protocol refused — including a complaint naming a cheating
    /// dealer ([`DkgError::Complaint`]).
    Dkg(DkgError),
    /// The signing protocol refused — including an equivocating signer named
    /// by [`RaccoonError::Equivocation`].
    Raccoon(RaccoonError),
    /// The assembled signature failed verification (e.g. a sub-threshold
    /// quorum, or a corrupted partial response — round 3 carries no
    /// per-party attribution in this reference).
    InvalidSignature,
}

impl From<ChannelError> for CeremonyError {
    fn from(e: ChannelError) -> Self {
        CeremonyError::Channel(e)
    }
}

/// DKG round-1 broadcast: dealer `i`'s Feldman commitments and its
/// per-recipient shares — the wire form of a [`crate::dkg::DkgDealing`]
/// WITHOUT the dealer-local secret (which never leaves the dealer).
///
/// Reference-transport note: the per-recipient shares ride the broadcast in
/// the clear (as in the in-process reference, and it is what lets tests see
/// tampering); a deployment encrypts each [`DkgShareMsg`] to its recipient.
#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct DkgDealingMsg {
    /// The dealing member's 1-based index.
    pub dealer: u64,
    /// Feldman commitments `Cₖ = A·aₖ`, `k = 0, …, t−1`.
    pub commitments: Vec<PolyVec>,
    /// One share per recipient, `shares[j−1]` addressed to member `j`.
    pub shares: Vec<DkgShareMsg>,
}

/// DKG round-2 broadcast: member `member` either acks the round-1 dealings
/// or complains, naming the first dealer whose share for it failed Feldman
/// verification.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct DkgAckMsg {
    /// The acking/complaining member's 1-based index.
    pub member: u64,
    /// `None` = all shares verified; `Some(dealer)` = a complaint against
    /// that dealer.
    pub complaint: Option<u64>,
}

/// Sign round-3 broadcast: signer `index`'s partial response
/// `z_i = y_i + c·(λ_i·s_i)`.
#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct RaccoonResponseMsg {
    /// The responding signer's 1-based Shamir index.
    pub index: u64,
    /// The partial response `z_i`.
    pub z: PolyVec,
}

/// Public parameters every DKG party agrees on before the ceremony.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DkgCeremonyParams {
    /// Public matrix rows `k`.
    pub rows: usize,
    /// Public matrix columns `ℓ` (the share/module rank).
    pub cols: usize,
    /// The signing threshold `t`.
    pub threshold: u64,
    /// The CRS seed the shared matrix `A` is derived from (a
    /// nothing-up-my-sleeve hash-to-matrix in production).
    pub crs_seed: u64,
}

/// What one party walks away from the DKG with: the public data everyone
/// shares, plus ITS OWN final share — the per-party shape (unlike the
/// in-process [`crate::dkg::HermineDkg`], which holds all `n` shares because
/// it plays all members).
#[derive(Clone)]
pub struct DkgPartyOutput {
    /// The shared public matrix `A` (derived from the CRS seed).
    pub a: Matrix,
    /// The jointly-formed group key `t = Σᵢ Cᵢ,₀`, assembled from broadcasts.
    pub group_key: PolyVec,
    /// The signing threshold `t`.
    pub threshold: u64,
    /// THIS party's final aggregated share `xⱼ = Σᵢ fᵢ(j)`.
    pub share: HermineShare,
}

/// Serde-encode one round message for the wire.
fn encode<T: Serialize>(msg: &T) -> Vec<u8> {
    serde_json::to_vec(msg).expect("ceremony messages serialize infallibly")
}

/// Decode party `from`'s round message, or reject it by name.
fn decode<T: DeserializeOwned>(from: u64, bytes: &[u8]) -> Result<T, CeremonyError> {
    serde_json::from_slice(bytes).map_err(|_| CeremonyError::BadMessage { from })
}

// =============================================================================
// The DKG ceremony, per-party
// =============================================================================

/// Run ONE party's side of the DKG over a transport: deal, broadcast,
/// verify the received dealings, ack-or-complain, aggregate. All `n =
/// channel.parties()` members run this concurrently against the same
/// channel; each returns the shared public data plus its own final share.
///
/// `my_seed` drives only this party's dealing randomness (reference PRNG; a
/// deployment samples locally from a CSPRNG). The protocol and checks are
/// exactly the in-process [`crate::dkg::HermineDkg`]'s — same
/// `dkg_deal`, same Feldman verification, same aggregation — re-driven as
/// messages: a cheating dealer is caught by the recipient's OWN check and
/// the complaint is broadcast, aborting every honest party's ceremony with
/// the dealer named.
pub fn run_dkg_ceremony<C: Channel>(
    channel: &mut C,
    params: &DkgCeremonyParams,
    my_seed: u64,
) -> Result<DkgPartyOutput, CeremonyError> {
    let n = channel.parties();
    let me = channel.me();
    let t = params.threshold;
    if t == 0 || t > n || n >= Q || params.rows == 0 || params.cols == 0 {
        return Err(CeremonyError::BadParameters);
    }

    // The shared CRS: everyone derives the same A from the public seed.
    let mut state = params.crs_seed;
    let a = Matrix::from_fn(params.rows, params.cols, |_, _| sample_poly(&mut state));

    // Round 1 (DEALING): deal my own secret, broadcast commitments + shares.
    let dealing = dkg_deal(&a, me, n, t, my_seed).ok_or(CeremonyError::BadParameters)?;
    channel.broadcast(encode(&DkgDealingMsg {
        dealer: me,
        commitments: dealing.commitments.clone(),
        shares: dealing.shares.clone(),
    }))?;
    let round1 = channel.recv_round()?;

    // Decode + structural wire hygiene: the sender IS the claimed dealer,
    // t commitments, one correctly-addressed share per recipient.
    let mut dealings: Vec<DkgDealingMsg> = Vec::with_capacity(n as usize);
    for (from, bytes) in &round1 {
        let msg: DkgDealingMsg = decode(*from, bytes)?;
        let well_formed = msg.dealer == *from
            && msg.commitments.len() == t as usize
            && msg.shares.len() == n as usize
            && msg
                .shares
                .iter()
                .enumerate()
                .all(|(j, m)| m.recipient == j as u64 + 1);
        if !well_formed {
            return Err(CeremonyError::BadMessage { from: *from });
        }
        dealings.push(msg);
    }

    // Round 2 (ACK/COMPLAINT): Feldman-verify every share addressed to ME;
    // complain about the first cheating dealer, else ack.
    let complaint = dealings
        .iter()
        .find(|d| {
            let share = &d.shares[(me - 1) as usize].share;
            !verify_dkg_share(&a, &d.commitments, me, share)
        })
        .map(|d| d.dealer);
    channel.broadcast(encode(&DkgAckMsg {
        member: me,
        complaint,
    }))?;
    let round2 = channel.recv_round()?;
    for (from, bytes) in &round2 {
        let ack: DkgAckMsg = decode(*from, bytes)?;
        if ack.member != *from {
            return Err(CeremonyError::BadMessage { from: *from });
        }
        if let Some(dealer) = ack.complaint {
            // Detection, not arbitration: the ceremony aborts with the
            // accused dealer named (the in-process reference's shape).
            return Err(CeremonyError::Dkg(DkgError::Complaint {
                accuser: ack.member,
                dealer,
            }));
        }
    }

    // Aggregation: my final share xⱼ = Σᵢ fᵢ(me); group key t = Σᵢ Cᵢ,₀.
    let share = dealings
        .iter()
        .map(|d| d.shares[(me - 1) as usize].share.clone())
        .reduce(|acc, s| acc.add(&s))
        .expect("n ≥ 1 dealings");
    let group_key = dealings
        .iter()
        .map(|d| d.commitments[0].clone())
        .reduce(|acc, c| acc.add(&c))
        .expect("n ≥ 1 dealings");
    Ok(DkgPartyOutput {
        a,
        group_key,
        threshold: t,
        share: HermineShare { index: me, share },
    })
}

// =============================================================================
// The Raccoon signing ceremony, per-party
// =============================================================================

/// Run ONE signer's side of the Raccoon 2-round (commit → reveal, then
/// respond) signing over a transport. The `t` signers each run this
/// concurrently against the same channel; every honest party assembles and
/// returns the SAME verified [`HermineSignature`].
///
/// The commit-then-reveal boundary is enforced by the transport's round
/// barrier: the reveal is only sendable AFTER [`Channel::recv_round`] has
/// yielded the complete commitment round (and a second message cannot enter
/// the commit round — [`ChannelError::DuplicateSend`]). Equivocation between
/// a commitment and its reveal is caught and named by the unchanged
/// [`RaccoonSignSession::combine_reveals`].
///
/// `mask_seed` drives this signer's one-time flooded mask (fresh per
/// ceremony, as ever — the per-signer stream is domain-separated by index).
pub fn run_sign_ceremony<C: Channel>(
    channel: &mut C,
    a: &Matrix,
    group_key: &PolyVec,
    share: &HermineShare,
    mask_seed: u64,
    message: &[u8],
) -> Result<HermineSignature, CeremonyError> {
    // Round 1 (COMMIT): broadcast only the hash commitment cm_i.
    let (local, commit) = RaccoonSigner::round1(a, share.index, mask_seed);
    channel.broadcast(encode(&commit))?;
    let round1 = channel.recv_round()?;
    let commits = round1
        .iter()
        .map(|(from, bytes)| decode::<RaccoonCommitMsg>(*from, bytes))
        .collect::<Result<Vec<_>, _>>()?;
    // Freezing the complete commitment set IS the commit/reveal boundary.
    let session = RaccoonSignSession::new(commits).ok_or(CeremonyError::BadParameters)?;
    let parts = session.parts();

    // Round 2 (REVEAL): only reachable once every commitment is in.
    channel.broadcast(encode(&local.round2_reveal()))?;
    let round2 = channel.recv_round()?;
    let reveals = round2
        .iter()
        .map(|(from, bytes)| decode::<RaccoonRevealMsg>(*from, bytes))
        .collect::<Result<Vec<_>, _>>()?;
    let w = session
        .combine_reveals(&reveals)
        .map_err(CeremonyError::Raccoon)?;
    let c = raccoon_challenge(&w, group_key, message);

    // Round 3 (RESPOND): partial responses, summed by everyone.
    let z_i = local
        .respond(share, &parts, &c)
        .ok_or(CeremonyError::BadParameters)?;
    channel.broadcast(encode(&RaccoonResponseMsg {
        index: share.index,
        z: z_i,
    }))?;
    let round3 = channel.recv_round()?;
    let mut z: Option<PolyVec> = None;
    for ((from, bytes), expected_index) in round3.iter().zip(parts.iter()) {
        let msg: RaccoonResponseMsg = decode(*from, bytes)?;
        // Roster consistency: round-3 senders line up with the frozen
        // commit roster, and shapes agree.
        if msg.index != *expected_index || msg.z.len() != a.cols {
            return Err(CeremonyError::BadMessage { from: *from });
        }
        z = Some(match z {
            None => msg.z,
            Some(acc) => acc.add(&msg.z),
        });
    }
    let z = z.ok_or(CeremonyError::BadParameters)?;

    let sig = HermineSignature { w, c, z };
    // Every party checks what it assembled (a sub-threshold quorum or a
    // corrupted partial fails here; no per-party attribution on round 3 in
    // this reference).
    if !verify_hermine_raccoon(a, group_key, message, &sig) {
        return Err(CeremonyError::InvalidSignature);
    }
    Ok(sig)
}

// =============================================================================
// Tests — the ceremonies over the in-memory transport
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dkg::HermineDkg;
    use crate::threshold::{lagrange_reconstruct, verify_hermine_raccoon};
    use crate::verify;

    const ROWS: usize = 2;
    const COLS: usize = 3;
    const MEMBERS: u64 = 5;
    const THRESHOLD: u64 = 3;
    const SEED: u64 = 0x00de_add0_6001;

    /// Drive one ceremony per party on its own thread (the transport's round
    /// barrier synchronizes them), collecting outputs in party order.
    fn run_parties<T, F>(net: &LocalNetwork, f: F) -> Vec<T>
    where
        T: Send + 'static,
        F: Fn(LocalChannel) -> T + Send + Sync + 'static,
    {
        let f = Arc::new(f);
        let handles: Vec<_> = net
            .channels()
            .into_iter()
            .map(|chan| {
                let f = Arc::clone(&f);
                std::thread::spawn(move || f(chan))
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("party thread"))
            .collect()
    }

    #[test]
    fn dkg_ceremony_over_channel() {
        // n parties run the DKG as a MESSAGE-PASSING protocol over the
        // in-memory transport; their shares reconstruct the group key.
        let params = DkgCeremonyParams {
            rows: ROWS,
            cols: COLS,
            threshold: THRESHOLD,
            crs_seed: SEED,
        };
        // Seed the dealings exactly as the in-process HermineDkg::run does,
        // so the ceremony is a DIFFERENTIAL against it, not just self-green.
        let deal_seed = SEED.wrapping_mul(0x2545f4914f6cdd1d) ^ 0xd6_6001;
        let net = LocalNetwork::new(MEMBERS).unwrap();
        let outputs = run_parties(&net, move |mut chan| {
            run_dkg_ceremony(&mut chan, &params, deal_seed).expect("honest DKG completes")
        });

        // Every party assembled the SAME public data from broadcasts.
        assert_eq!(outputs.len(), MEMBERS as usize);
        for out in &outputs[1..] {
            assert_eq!(out.group_key, outputs[0].group_key);
            assert_eq!(out.a, outputs[0].a);
        }
        // Each party holds ITS OWN share, indexed by its party id.
        for (i, out) in outputs.iter().enumerate() {
            assert_eq!(out.share.index, i as u64 + 1);
        }
        // Differential: byte-identical to the in-process ceremony.
        let reference = HermineDkg::run(ROWS, COLS, MEMBERS, THRESHOLD, SEED).unwrap();
        assert_eq!(outputs[0].group_key, reference.group_key);
        for (out, r) in outputs.iter().zip(reference.shares.iter()) {
            assert_eq!(out.share.share, r.share);
        }
        // The shares are a REAL t-of-n sharing: any t-subset reconstructs a
        // preimage of the group key; sub-threshold subsets do not.
        let a = &outputs[0].a;
        let group_key = &outputs[0].group_key;
        for subset in [[0usize, 1, 2], [0, 2, 4], [2, 3, 4]] {
            let shares: Vec<&HermineShare> = subset.iter().map(|&i| &outputs[i].share).collect();
            assert_eq!(&a.mul_vec(&lagrange_reconstruct(&shares)), group_key);
        }
        for subset in [[0usize, 1], [1, 4], [2, 3]] {
            let shares: Vec<&HermineShare> = subset.iter().map(|&i| &outputs[i].share).collect();
            assert_ne!(&a.mul_vec(&lagrange_reconstruct(&shares)), group_key);
        }
    }

    #[test]
    fn sign_ceremony_over_channel() {
        // t parties run the 2-round (commit → reveal, then respond) signing
        // as a message-passing protocol; everyone assembles the same
        // certificate and the raccoon verifier accepts it. Keys come from a
        // DKG — no dealer anywhere in this signature's history.
        let dkg = HermineDkg::run(ROWS, COLS, MEMBERS, THRESHOLD, SEED).unwrap();
        let message: &[u8] = b"dregg-federation-vote-v1:hermine-ceremony";
        let signer_shares: Vec<HermineShare> = [0usize, 1, 3]
            .iter()
            .map(|&i| dkg.shares[i].clone())
            .collect();
        let (a, group_key) = (dkg.a.clone(), dkg.group_key.clone());

        let net = LocalNetwork::new(THRESHOLD).unwrap();
        let shares = Arc::new(signer_shares);
        let sigs = run_parties(&net, move |mut chan| {
            let share = &shares[(chan.me() - 1) as usize];
            run_sign_ceremony(&mut chan, &a, &group_key, share, 0x4ACC_C4A7, message)
                .expect("honest signing completes")
        });

        // One signature, held identically by every party, and it verifies —
        // both the wrapper and the raw Lean relation.
        assert_eq!(sigs.len(), THRESHOLD as usize);
        for sig in &sigs[1..] {
            assert_eq!(sig, &sigs[0]);
        }
        assert!(verify_hermine_raccoon(
            &dkg.a,
            &dkg.group_key,
            message,
            &sigs[0]
        ));
        assert!(verify(
            &dkg.a,
            &dkg.group_key,
            &sigs[0].w,
            &sigs[0].c,
            &sigs[0].z
        ));

        // Sub-threshold parties running the same ceremony assemble a
        // certificate that FAILS verification — caught in-ceremony.
        let sub_shares: Vec<HermineShare> = dkg.shares[0..2].to_vec();
        let (a, group_key) = (dkg.a.clone(), dkg.group_key.clone());
        let net = LocalNetwork::new(2).unwrap();
        let sub_shares = Arc::new(sub_shares);
        let results = run_parties(&net, move |mut chan| {
            let share = &sub_shares[(chan.me() - 1) as usize];
            run_sign_ceremony(&mut chan, &a, &group_key, share, 0x4ACC_FFFF, message)
        });
        for r in results {
            assert_eq!(r.unwrap_err(), CeremonyError::InvalidSignature);
        }
    }

    #[test]
    fn ceremony_commit_reveal_barrier() {
        // THE round-structure tooth: a party cannot reveal before every
        // commitment is in. Driven single-threaded against the transport so
        // the refusals are observable.
        let d = crate::threshold::HermineTestDealer::deal(ROWS, COLS, MEMBERS, THRESHOLD, SEED)
            .unwrap();
        let net = LocalNetwork::new(3).unwrap();
        let mut chans = net.channels();

        // Each signer forms its round-1 state; parties 1 and 2 commit.
        let (locals, commits): (Vec<RaccoonSigner>, Vec<RaccoonCommitMsg>) = d.shares[0..3]
            .iter()
            .map(|s| RaccoonSigner::round1(&d.a, s.index, 0x0BA4_41E4))
            .unzip();
        chans[0].broadcast(encode(&commits[0])).unwrap();
        chans[1].broadcast(encode(&commits[1])).unwrap();

        // Party 1 cannot obtain the commitment set — the round is
        // incomplete (party 3 has not committed), so the ceremony cannot
        // reach its reveal step.
        assert_eq!(
            chans[0].try_recv_round().unwrap_err(),
            ChannelError::RoundIncomplete
        );
        // Nor can it rush its reveal INTO the commit round: one message per
        // party per round.
        assert_eq!(
            chans[0]
                .broadcast(encode(&locals[0].round2_reveal()))
                .unwrap_err(),
            ChannelError::DuplicateSend
        );

        // Party 3 commits; the barrier opens; only NOW is the reveal
        // sendable — with every party's contribution already bound to its
        // hash commitment.
        chans[2].broadcast(encode(&commits[2])).unwrap();
        let round1 = chans[0].try_recv_round().unwrap();
        assert_eq!(round1.len(), 3);
        let decoded: Vec<RaccoonCommitMsg> = round1
            .iter()
            .map(|(from, bytes)| decode(*from, bytes).unwrap())
            .collect();
        assert_eq!(decoded, commits);
        chans[0]
            .broadcast(encode(&locals[0].round2_reveal()))
            .unwrap();
    }
}
