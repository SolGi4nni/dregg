//! DISTRIBUTED NO-SINGLE-VIEWER CEREMONY — a runnable demonstrator.
//!
//! This stands up `N` isolated custody party-actors, runs the REAL
//! [`DistributedDkg`] ceremony across them to a collective public key, encrypts
//! a batch of private bilateral obligations under that key, NETS them
//! HOMOMORPHICALLY (nobody sees an obligation), and reveals ONLY the net vector
//! through a `t`-of-`N` threshold decrypt. Then it shows the malice tooth: a
//! dealer that lies to one recipient is refused, BY that recipient, with an
//! attributed error.
//!
//! Everything here is the production API in
//! [`fhegg_fhe::threshold::distributed`] and [`fhegg_fhe::threshold::quorum`];
//! this file invents no cryptography. It runs the parties as isolated structs in
//! one process (the `tests/distributed_threshold_committee.rs` integration test
//! is the same ceremony across separate OS processes over real TCP — this
//! demonstrator trades that process boundary for a readable, measurable
//! single-binary run, and keeps the OWNERSHIP boundary the process test proves).
//!
//! # Why no single actor can view another's secret (structural, not asserted)
//!
//! Each [`PartyActor`] owns exactly three secret things — its own transport
//! `identity` (Ed25519 seed + ML-KEM-768 decapsulation key), its own Ed25519
//! `signing_key`, and, after setup, its own `custody` (one Shamir row of the
//! collective secret). There is NO field, method, or accessor anywhere in this
//! file that hands one actor another actor's `identity`, `signing_key`, or
//! `custody`. Peers exchange ONLY `Vec<u8>` wire messages (sealed dealings,
//! sealed cross-evaluations, signed decrypt shares). The message bus routes
//! bytes by index; it never aliases two actors' secret state at once. The
//! `DistributedDkg` each actor holds is derived from the PUBLIC roster and
//! carries no secret — every method that touches a secret takes THIS actor's own
//! `&identity` as an argument. The collective secret `s = Σ_d s_d` is never
//! materialized in any variable, in this file or in the library.
//!
//! Run it:
//! ```text
//! cargo run --example distributed_ceremony_demo --features verified-pq-runtime-tests
//! ```

use std::time::{Duration, Instant};

use dregg_pq::hybrid_kem::{
    install_verified_mlkem_decaps_core, install_verified_mlkem_encaps_core,
    install_verified_mlkem_keygen_core, MlKemDecapsCoreInstall, MlKemEncapsCoreInstall,
    MlKemKeygenCoreInstall,
};
use dregg_pq::{
    install_verified_mldsa_keygen_core_real, install_verified_mldsa_sign_core_real,
    install_verified_mldsa_verify_core, ml_kem768_keygen, MlDsaKeygenCoreRealInstall,
    MlDsaSignCoreRealInstall, MlDsaVerifyCoreInstall,
};
use ed25519_dalek::SigningKey;
use fhe::bfv::{Encoding, Plaintext};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};
use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::convex_step::{center, encode_signed, signed_add, SignedCt};
use fhegg_fhe::mpc_party::transport::{EqualityTransportRoster, NativePqTransportIdentity};
use fhegg_fhe::threshold::distributed::{
    AcceptedDealing, DistributedCommitteeError, DistributedCustody, DistributedDkg,
};
use fhegg_fhe::threshold::quorum::{
    AuthenticatedQuorumCombiner, AuthenticatedQuorumRoster, QuorumError, QuorumKeygenSession,
    QuorumOpeningSession,
};
use fhegg_fhe::threshold::{BfvParams, CollectivePublicKey, MIN_SMUDGE_BITS};
use rand::rngs::{OsRng, StdRng};
use rand::{Rng, RngCore, SeedableRng};

// ── committee shape ──────────────────────────────────────────────────────────
const N_PARTIES: usize = 4;
const THRESHOLD: usize = 3;

// ── the house-blind clearing round ───────────────────────────────────────────
/// Members of the multilateral clearing ring. Each becomes one SIMD slot of the
/// net-position ciphertext, so ONE decrypt reveals every member's net at once.
const N_MEMBERS: usize = 128;
/// How many other members each member owes (sparse, realistic).
const OBLIGATIONS_PER_MEMBER: usize = 8;
/// Max gross amount of one bilateral obligation.
const MAX_AMOUNT: i64 = 50;

/// The clearing-ring sizing. Defaults reproduce the pinned constants above; each
/// can be overridden at runtime (env var) so ONE release build can be swept
/// across member counts and obligation densities without recompiling. Every
/// field feeds the SAME real ceremony — nothing here weakens the crypto.
#[derive(Clone, Copy)]
struct RingConfig {
    /// Members in the clearing ring (= SIMD slots used). `FHEGG_N_MEMBERS`.
    n_members: usize,
    /// How many other members each member owes. `FHEGG_OBLIGATIONS`.
    obligations_per_member: usize,
    /// Max gross amount of one bilateral obligation. `FHEGG_MAX_AMOUNT`.
    max_amount: i64,
}

impl RingConfig {
    fn from_env() -> Self {
        fn env_usize(key: &str, default: usize) -> usize {
            std::env::var(key)
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(default)
        }
        fn env_i64(key: &str, default: i64) -> i64 {
            std::env::var(key)
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(default)
        }
        Self {
            n_members: env_usize("FHEGG_N_MEMBERS", N_MEMBERS),
            obligations_per_member: env_usize("FHEGG_OBLIGATIONS", OBLIGATIONS_PER_MEMBER),
            max_amount: env_i64("FHEGG_MAX_AMOUNT", MAX_AMOUNT),
        }
    }

    /// A conservative signed-window cap for one member's obligation vector
    /// (row-sum bound: at most this member's total gross owing). Kept well inside
    /// the centered window `(t-1)/2` even after summing all members of them.
    fn member_gross_cap(&self) -> i64 {
        (self.obligations_per_member as i64) * self.max_amount
    }
}

// ─────────────────────────────────────────────────────────────────────────────
//  A single custody party. Owns ONLY its own secret state.
//
//  The actor lives in its OWN module with PRIVATE fields, so the structural
//  no-single-viewer guarantee is enforced by Rust's privacy, not by convention:
//  code outside this module (the orchestrator, the clearing house, `main`)
//  CANNOT NAME `identity`, `signing_key`, or `custody`. It can only call the
//  public methods below, each of which touches exactly one party's own secrets
//  and returns `Vec<u8>` wire messages (or public values). There is no method
//  that returns a secret, and no method that takes a second party's secret.
// ─────────────────────────────────────────────────────────────────────────────

mod party {
    use super::*;

    /// This party's post-setup custody. `state.party` is a `QuorumParty` holding
    /// exactly one Shamir row — there is no accessor from it to the collective
    /// secret. `auth_roster` is PUBLIC (the enrolled Ed25519 verification keys).
    struct CustodyState {
        state: DistributedCustody,
        auth_roster: AuthenticatedQuorumRoster,
    }

    /// One custody party-actor. The three secret-bearing fields (`identity`,
    /// `signing_key`, `custody`) are PRIVATE to this module — no other actor and
    /// no orchestrator variable can read them. Peers receive only the `Vec<u8>`
    /// values the public methods return.
    pub struct PartyActor {
        index: usize,
        /// SECRET: Ed25519 seed + ML-KEM-768 keypair. Never leaves this struct.
        identity: NativePqTransportIdentity,
        /// SECRET: the Ed25519 key this party signs its decrypt shares with.
        signing_key: SigningKey,
        /// PUBLIC: derived from the enrolled roster; carries no secret.
        dkg: DistributedDkg,
        /// PUBLIC: the enrolled Ed25519 verification keys, in party order.
        party_keys: Vec<[u8; 32]>,
        /// This party's own verified dealings (its row from each dealer).
        accepted: Vec<AcceptedDealing>,
        /// This party's custody share, after `finish`.
        custody: Option<CustodyState>,
    }

    impl PartyActor {
        /// Build one actor. It MOVES IN its own secret identity + signing key;
        /// the `dkg` and `party_keys` are public roster data.
        pub fn new(
            index: usize,
            identity: NativePqTransportIdentity,
            signing_key: SigningKey,
            dkg: DistributedDkg,
            party_keys: Vec<[u8; 32]>,
        ) -> Self {
            Self {
                index,
                identity,
                signing_key,
                dkg,
                party_keys,
                accepted: Vec::new(),
                custody: None,
            }
        }

        pub fn index(&self) -> usize {
            self.index
        }

        /// The PUBLIC keygen session (no secret), for the relying party's opening.
        pub fn session(&self) -> QuorumKeygenSession {
            self.dkg.session().clone()
        }

        /// Put this party's accepted dealings in canonical dealer order, which
        /// phase-2 cross-evaluation requires on both the sending and checking side.
        pub fn canonicalize_accepted(&mut self) {
            self.accepted.sort_by_key(AcceptedDealing::dealer);
        }

        /// PHASE 1 (dealer side): deal, self-verify, keep own row, emit one sealed
        /// message per peer. Returns `(recipient, sealed_bytes)` — bytes only.
        pub fn deal(&mut self) -> Result<Vec<(usize, Vec<u8>)>, DistributedCommitteeError> {
            let dealing = self.dkg.deal(&self.identity, self.index)?;
            let (own, sealed) = dealing.own();
            self.accepted.push(own);
            Ok(sealed)
        }

        /// HOSTILE (debug builds only): deal honestly to everyone EXCEPT `victim`,
        /// whose row is corrupted after the public commitment is fixed.
        #[cfg(debug_assertions)]
        pub fn deal_hostile(
            &mut self,
            victim: usize,
        ) -> Result<Vec<(usize, Vec<u8>)>, DistributedCommitteeError> {
            let dealing =
                self.dkg
                    .deal_with_hostile_row_corruption(&self.identity, self.index, victim)?;
            let (own, sealed) = dealing.own();
            self.accepted.push(own);
            Ok(sealed)
        }

        /// PHASE 1 (recipient side): authenticate, open, and VERIFY a dealer's
        /// sealed row against its public commitment. A lie lands here as an `Err`.
        pub fn accept(
            &mut self,
            dealer: usize,
            sealed: &[u8],
        ) -> Result<(), DistributedCommitteeError> {
            let accepted = self
                .dkg
                .accept_dealing(&self.identity, self.index, dealer, sealed)?;
            self.accepted.push(accepted);
            Ok(())
        }

        /// PHASE 2 (sender side): this party's cross-evaluation of every dealer's
        /// row at each peer's point, sealed per peer.
        pub fn cross_messages(&self) -> Result<Vec<(usize, Vec<u8>)>, DistributedCommitteeError> {
            let mut out = Vec::new();
            for peer in 0..N_PARTIES {
                if peer == self.index {
                    continue;
                }
                let message = self.dkg.cross_evaluation_message(&self.accepted, peer)?;
                let sealed = self.dkg.seal(
                    &self.identity,
                    self.index,
                    peer,
                    fhegg_fhe::threshold::distributed::SEQUENCE_CROSS_EVALUATION,
                    &message,
                )?;
                out.push((peer, sealed));
            }
            Ok(out)
        }

        /// PHASE 2 (receiver side): check a peer's sealed cross-evaluation against
        /// this party's own rows. Disagreement is a refusal.
        pub fn check_cross(
            &self,
            peer: usize,
            sealed: &[u8],
        ) -> Result<(), DistributedCommitteeError> {
            let message = self.dkg.open(
                &self.identity,
                peer,
                self.index,
                fhegg_fhe::threshold::distributed::SEQUENCE_CROSS_EVALUATION,
                sealed,
            )?;
            self.dkg
                .check_cross_evaluation_message(&self.accepted, peer, &message)
        }

        /// PHASE 3: aggregate the collective public key and assemble this party's
        /// custody row. Consumes `accepted`.
        pub fn finish(&mut self) -> Result<(), DistributedCommitteeError> {
            self.accepted.sort_by_key(AcceptedDealing::dealer);
            let accepted = std::mem::take(&mut self.accepted);
            let state = self.dkg.finish(self.index, accepted)?;
            let auth_roster =
                AuthenticatedQuorumRoster::new(self.dkg.session().clone(), self.party_keys.clone())
                    .expect("custody roster from the public enrolled keys");
            self.custody = Some(CustodyState { state, auth_roster });
            Ok(())
        }

        /// OPENING: produce this party's SIGNED partial-decrypt share for one
        /// ciphertext, from its own custody row only. Returns the framed wire bytes.
        pub fn signed_partial_decrypt(
            &mut self,
            opening: &QuorumOpeningSession,
            ct: &LeanCiphertext,
            params: &BfvParams,
        ) -> Result<Vec<u8>, QuorumError> {
            let signing_key = self.signing_key.clone();
            let custody = self.custody.as_mut().expect("custody after setup");
            let share =
                custody
                    .state
                    .party
                    .partial_decrypt(opening, ct, MIN_SMUDGE_BITS, params)?;
            let signed = custody.auth_roster.sign_share(share, &signing_key)?;
            Ok(signed.to_wire_bytes())
        }

        /// The PUBLIC collective key this party aggregated (no secret).
        pub fn collective_public_key(&self) -> &CollectivePublicKey {
            &self
                .custody
                .as_ref()
                .expect("custody after setup")
                .state
                .collective
        }

        /// The PUBLIC setup digest every honest party computes identically.
        pub fn setup_digest(&self) -> [u8; 32] {
            self.custody
                .as_ref()
                .expect("custody after setup")
                .state
                .setup_digest
        }
    }
}

use party::PartyActor;

// ─────────────────────────────────────────────────────────────────────────────
//  Verified-PQ runtime — install the audited Lean cores, or fail closed.
// ─────────────────────────────────────────────────────────────────────────────

/// Install the Lean-verified ML-DSA + ML-KEM cores. `DREGG_ALLOW_UNAUDITED_PQ`
/// is never set: if the audited cores are absent, `dregg-pq` aborts rather than
/// answer with unaudited crypto, and that abort is the correct outcome.
fn install_verified_pq_cores() -> Result<(), String> {
    if std::env::var_os("DREGG_ALLOW_UNAUDITED_PQ").is_some() {
        return Err("refusing to run under DREGG_ALLOW_UNAUDITED_PQ".into());
    }
    macro_rules! require {
        ($call:expr, $ok:pat, $what:literal) => {
            if !matches!($call, $ok) {
                return Err(format!("the verified {} core did not install", $what));
            }
        };
    }
    require!(
        install_verified_mldsa_keygen_core_real(
            dregg_lean_ffi::mldsa_keygen_real_core_available,
            |wire| dregg_lean_ffi::shadow_mldsa_keygen_real(wire).ok(),
        ),
        MlDsaKeygenCoreRealInstall::Installed | MlDsaKeygenCoreRealInstall::AlreadyInstalled,
        "ML-DSA keygen"
    );
    require!(
        install_verified_mldsa_sign_core_real(
            dregg_lean_ffi::fips204_sign_real_core_available,
            |wire| dregg_lean_ffi::shadow_fips204_sign_real(wire).ok(),
        ),
        MlDsaSignCoreRealInstall::Installed | MlDsaSignCoreRealInstall::AlreadyInstalled,
        "ML-DSA sign"
    );
    require!(
        install_verified_mldsa_verify_core(
            dregg_lean_ffi::fips204_verify_real_core_available,
            |wire| dregg_lean_ffi::shadow_fips204_verify_real(wire).ok(),
        ),
        MlDsaVerifyCoreInstall::Installed | MlDsaVerifyCoreInstall::AlreadyInstalled,
        "ML-DSA verify"
    );
    require!(
        install_verified_mlkem_keygen_core(
            dregg_lean_ffi::mlkem_keygen_real_core_available,
            |wire| dregg_lean_ffi::shadow_mlkem_keygen_real(wire).ok(),
        ),
        MlKemKeygenCoreInstall::Installed | MlKemKeygenCoreInstall::AlreadyInstalled,
        "ML-KEM keygen"
    );
    require!(
        install_verified_mlkem_encaps_core(
            dregg_lean_ffi::mlkem_encaps_real_core_available,
            |wire| dregg_lean_ffi::shadow_mlkem_encaps_real(wire).ok(),
        ),
        MlKemEncapsCoreInstall::Installed | MlKemEncapsCoreInstall::AlreadyInstalled,
        "ML-KEM encaps"
    );
    require!(
        install_verified_mlkem_decaps_core(
            dregg_lean_ffi::mlkem_decaps_real_core_available,
            |wire| dregg_lean_ffi::shadow_mlkem_decaps_real(wire).ok(),
        ),
        MlKemDecapsCoreInstall::Installed | MlKemDecapsCoreInstall::AlreadyInstalled,
        "ML-KEM decaps"
    );
    Ok(())
}

/// Fresh native-PQ transport identity (Ed25519 seed + ML-KEM-768 keypair).
fn fresh_identity() -> (NativePqTransportIdentity, SigningKey) {
    let mut seed = [0u8; 32];
    OsRng.try_fill_bytes(&mut seed).expect("OS entropy");
    let signing_key = SigningKey::from_bytes(&seed);
    let (ek, dk) = ml_kem768_keygen();
    let identity = NativePqTransportIdentity::from_material(signing_key.clone(), ek, dk)
        .expect("native-PQ identity material");
    (identity, signing_key)
}

/// Build `N_PARTIES` custody actors plus the clearing house (relying party).
/// Each actor MOVES IN its own secret identity + signing key; the orchestrator
/// keeps only the public roster.
fn stand_up_committee(
    params: &BfvParams,
) -> (Vec<PartyActor>, NativePqTransportIdentity, Vec<[u8; 32]>) {
    let secrets: Vec<(NativePqTransportIdentity, SigningKey)> =
        (0..N_PARTIES).map(|_| fresh_identity()).collect();
    let (house_identity, _house_signing) = fresh_identity();

    let public_roster: Vec<_> = secrets
        .iter()
        .map(|(identity, _)| identity.public_identity())
        .collect();
    let party_keys: Vec<[u8; 32]> = public_roster.iter().map(|id| id.ed25519()).collect();
    let roster = EqualityTransportRoster::new_native_post_quantum(
        public_roster,
        house_identity.public_identity(),
    )
    .expect("native-PQ roster");
    let dkg = DistributedDkg::new(roster, THRESHOLD, params.clone()).expect("dkg parameters");

    let actors = secrets
        .into_iter()
        .enumerate()
        .map(|(index, (identity, signing_key))| {
            PartyActor::new(
                index,
                identity,
                signing_key,
                dkg.clone(),
                party_keys.clone(),
            )
        })
        .collect();
    (actors, house_identity, party_keys)
}

/// Run the honest DKG ceremony across `actors` to custody + a collective key.
fn run_dkg(actors: &mut [PartyActor]) -> Result<(), DistributedCommitteeError> {
    // PHASE 1: everyone deals; route sealed rows to recipients.
    let mut dealt: Vec<(usize, usize, Vec<u8>)> = Vec::new(); // (dealer, recipient, bytes)
    for actor in actors.iter_mut() {
        let dealer = actor.index();
        for (recipient, bytes) in actor.deal()? {
            dealt.push((dealer, recipient, bytes));
        }
    }
    for (dealer, recipient, bytes) in dealt {
        actors[recipient].accept(dealer, &bytes)?;
    }

    // Canonical dealer order, on every party, BEFORE cross-evaluation: the
    // sender's evaluation vector and the receiver's own rows must align dealer
    // for dealer (this is what the party binary sorts before sending cross).
    for actor in actors.iter_mut() {
        actor.canonicalize_accepted();
    }

    // PHASE 2: everyone cross-evaluates; route + check.
    let mut cross: Vec<(usize, usize, Vec<u8>)> = Vec::new(); // (sender, recipient, bytes)
    for actor in actors.iter() {
        let sender = actor.index();
        for (recipient, bytes) in actor.cross_messages()? {
            cross.push((sender, recipient, bytes));
        }
    }
    for (sender, recipient, bytes) in cross {
        actors[recipient].check_cross(sender, &bytes)?;
    }

    // PHASE 3: everyone finishes.
    for actor in actors.iter_mut() {
        actor.finish()?;
    }
    Ok(())
}

// ─────────────────────────────────────────────────────────────────────────────
//  The house-blind clearing computation.
// ─────────────────────────────────────────────────────────────────────────────

/// A private bilateral obligation book: `g[i][j]` = gross amount member `i`
/// owes member `j` (diagonal 0). Deterministic, so the run is reproducible.
struct ObligationBook {
    g: Vec<Vec<i64>>,
    n_members: usize,
    nonzero: usize,
    gross: i64,
}

fn build_obligation_book(cfg: &RingConfig) -> ObligationBook {
    let n = cfg.n_members;
    let mut rng = StdRng::seed_from_u64(0x0b11_6a70_c1ea_1234);
    let mut g = vec![vec![0i64; n]; n];
    let mut nonzero = 0usize;
    let mut gross = 0i64;
    for (i, row) in g.iter_mut().enumerate() {
        for _ in 0..cfg.obligations_per_member {
            let j = rng.gen_range(0..n);
            if j == i {
                continue;
            }
            let amount = rng.gen_range(1..=cfg.max_amount);
            if row[j] == 0 {
                nonzero += 1;
            }
            row[j] += amount;
            gross += amount;
        }
    }
    ObligationBook {
        g,
        n_members: n,
        nonzero,
        gross,
    }
}

/// Member `i`'s contribution vector to the global net: `+g[i][j]` credited to
/// each creditor `j`, and `-Σ_j g[i][j]` debited to `i`. Sums to zero over
/// slots, so the netted total conserves.
fn member_contribution(book: &ObligationBook, i: usize) -> Vec<i64> {
    let n = book.n_members;
    let mut v = vec![0i64; n];
    let mut owing = 0i64;
    for j in 0..n {
        v[j] += book.g[i][j];
        owing += book.g[i][j];
    }
    v[i] -= owing;
    v
}

/// Cleartext reference net vector (what the encrypted clearing must reproduce).
fn reference_nets(book: &ObligationBook) -> Vec<i64> {
    let n = book.n_members;
    let mut nets = vec![0i64; n];
    for i in 0..n {
        for j in 0..n {
            nets[j] += book.g[i][j]; // j is owed
            nets[i] -= book.g[i][j]; // i owes
        }
    }
    nets
}

/// Encrypt one member's contribution vector under the collective key, wrapped as
/// a signed ciphertext with a conservative window.
fn encrypt_contribution(
    pk: &CollectivePublicKey,
    params: &BfvParams,
    values: &[i64],
    t: u64,
    member_gross_cap: i64,
) -> SignedCt {
    let mut slots = vec![0u64; params.degree()];
    for (slot, &v) in slots.iter_mut().zip(values) {
        *slot = encode_signed(v, t);
    }
    let pt = Plaintext::try_encode(&slots, Encoding::simd(), params.arc()).expect("simd encode");
    let ct = pk
        .pk
        .try_encrypt(&pt, &mut rand_09::rng())
        .expect("collective-key encrypt");
    let lean =
        LeanCiphertext::from_fhe_bytes(&ct.to_bytes(), params.moduli(), params.degree(), t - 1)
            .expect("lean ciphertext");
    SignedCt::new(lean, -member_gross_cap, member_gross_cap, t).expect("signed window")
}

// ─────────────────────────────────────────────────────────────────────────────

fn main() {
    println!("── DISTRIBUTED NO-SINGLE-VIEWER CEREMONY DEMONSTRATOR ──\n");

    if let Err(why) = install_verified_pq_cores() {
        eprintln!("BLOCKER: verified-PQ runtime unavailable: {why}");
        eprintln!("(the audited Lean cores must be installed; the project refuses the unaudited fallback)");
        std::process::exit(1);
    }
    println!("verified-PQ cores installed (ML-DSA-65 + ML-KEM-768, audited Lean cores)\n");

    let params = BfvParams::fold_set();
    let t = params.plaintext_modulus();
    let window_half = (t - 1) / 2;

    let cfg = RingConfig::from_env();
    let member_gross_cap = cfg.member_gross_cap();

    // ── SCENARIO A: honest ceremony + house-blind clearing ───────────────────
    let (mut actors, _house, party_keys) = stand_up_committee(&params);
    println!(
        "committee: N={N_PARTIES} custody parties, t={THRESHOLD}-of-{N_PARTIES} opening threshold"
    );
    println!(
        "BFV: degree {} ({} SIMD slots), plaintext modulus {t}, centered window +/-{window_half}",
        params.degree(),
        params.degree()
    );
    println!(
        "ring config: M={} members, {} obligations/member, max amount {} \
         (per-member window cap +/-{member_gross_cap})",
        cfg.n_members, cfg.obligations_per_member, cfg.max_amount
    );

    let keygen_start = Instant::now();
    run_dkg(&mut actors).expect("the honest distributed DKG completes");
    let keygen_ms = keygen_start.elapsed().as_secs_f64() * 1e3;

    // Every party independently agreed on the same public setup and key.
    let digest0 = actors[0].setup_digest();
    assert!(
        actors.iter().all(|a| a.setup_digest() == digest0),
        "parties finished on different setups"
    );
    let pk0 = actors[0].collective_public_key().pk.to_bytes();
    assert!(
        actors
            .iter()
            .all(|a| a.collective_public_key().pk.to_bytes() == pk0),
        "parties disagree on the collective public key"
    );
    println!(
        "DKG DONE in {keygen_ms:.1} ms — collective key agreed by all {N_PARTIES} parties, setup digest {}",
        hex8(&digest0)
    );
    println!("  (the collective secret s = Σ s_d was never assembled in any variable)\n");

    // (a) DEMO-ONLY reference: build the private book and the O(M^2) cleartext
    //     net. This is the check the demo asserts against — the REAL system never
    //     computes it (no party may see the plaintext books). Timed apart so it is
    //     never charged to the operator.
    let ref_start = Instant::now();
    let book = build_obligation_book(&cfg);
    let reference = reference_nets(&book);
    let ref_ms = ref_start.elapsed().as_secs_f64() * 1e3;
    assert_eq!(
        reference.iter().sum::<i64>(),
        0,
        "cleartext netting must conserve"
    );
    let window_use: i64 = (cfg.n_members as i64) * member_gross_cap;
    assert!(
        window_use < window_half as i64,
        "batch would exceed the signed window ({window_use} >= {window_half})"
    );
    println!(
        "clearing ring: M={} members, {} private bilateral obligations ({} total gross), \
         net packed into {} SIMD slots",
        cfg.n_members, book.nonzero, book.gross, cfg.n_members
    );
    println!(
        "  (a) reference (DEMO-ONLY cleartext O(M^2) check, NOT in the real system): {ref_ms:.1} ms"
    );

    // Clear it house-blind. Two costs, timed apart:
    //   (b) per-member ENCRYPTION — one member builds its own contribution vector,
    //       SIMD-encodes it, and encrypts under the collective key. In the real
    //       system each member's OWN client does exactly ONE of these, all in
    //       parallel; the operator does none of them. We sum the M of them here in
    //       one process only for accounting, and also report the per-client cost.
    //   (c) the homomorphic FOLD — the share-less clearing house's M-1 `signed_add`s
    //       over the members' ciphertexts. THIS is the operator's per-clearing cost.
    let collective = actors[0].collective_public_key().clone();
    let mut enc_dur = Duration::ZERO; // (b) per-client (summed over M clients)
    let mut fold_dur = Duration::ZERO; // (c) operator
    let mut netted: Option<SignedCt> = None;
    for i in 0..cfg.n_members {
        let enc_t = Instant::now();
        let contribution = member_contribution(&book, i);
        let ct = encrypt_contribution(&collective, &params, &contribution, t, member_gross_cap);
        enc_dur += enc_t.elapsed();

        let fold_t = Instant::now();
        netted = Some(match netted.take() {
            None => ct,
            Some(acc) => signed_add(&acc, &ct, t).expect("homomorphic net add"),
        });
        fold_dur += fold_t.elapsed();
    }
    let net_ct = netted.expect("at least one member");
    let enc_ms = enc_dur.as_secs_f64() * 1e3;
    let fold_ms = fold_dur.as_secs_f64() * 1e3;
    let enc_per_client_ms = enc_ms / (cfg.n_members as f64);
    println!(
        "  (b) encryption (PER-CLIENT, parallel; operator does NONE): {enc_ms:.1} ms summed over \
         {} clients = {enc_per_client_ms:.2} ms each",
        cfg.n_members
    );
    println!(
        "  (c) homomorphic FOLD (the OPERATOR's per-clearing cost, {} `signed_add`s by the \
         share-less house): {fold_ms:.1} ms",
        cfg.n_members.saturating_sub(1)
    );

    // ── DISTRIBUTED DECRYPT: a t-subset each produces one signed share. ───────
    let quorum: Vec<usize> = (0..THRESHOLD).collect(); // canonical, increasing
    let mut nonce = [0u8; 32];
    OsRng.try_fill_bytes(&mut nonce).expect("OS entropy");
    let opening = QuorumOpeningSession::new(actors[0].session(), nonce, quorum.clone())
        .expect("t-party opening");
    let lean_net = net_ct.ciphertext().clone();

    let decrypt_start = Instant::now();
    let mut framed: Vec<Vec<u8>> = Vec::with_capacity(quorum.len());
    for &party in &quorum {
        let share = actors[party]
            .signed_partial_decrypt(&opening, &lean_net, &params)
            .expect("a custody party signs its own partial decrypt");
        framed.push(share);
    }
    // The clearing house holds NO share; it verifies t signed shares and combines.
    let quorum_roster = AuthenticatedQuorumRoster::new(actors[0].session(), party_keys.clone())
        .expect("public custody roster");
    let opened = AuthenticatedQuorumCombiner::new(quorum_roster)
        .combine_framed(&opening, &lean_net, &framed, &params)
        .expect("t signed shares reveal the net vector");
    let decrypt_ms = decrypt_start.elapsed().as_secs_f64() * 1e3;

    // Center-decode and check against the cleartext reference + conservation.
    let revealed: Vec<i64> = (0..cfg.n_members).map(|k| center(opened[k], t)).collect();
    assert_eq!(
        revealed, reference,
        "the house-blind clearing did not reproduce the cleartext nets"
    );
    assert_eq!(
        revealed.iter().sum::<i64>(),
        0,
        "revealed nets do not conserve"
    );
    println!(
        "  decrypt: threshold decrypt ({THRESHOLD} signed shares) + combine (over the ONE net \
         ciphertext, independent of M) in {decrypt_ms:.1} ms — revealed ONLY the {}-slot net vector",
        cfg.n_members
    );

    let (creditor, &max_net) = revealed.iter().enumerate().max_by_key(|(_, &v)| v).unwrap();
    let (debtor, &min_net) = revealed.iter().enumerate().min_by_key(|(_, &v)| v).unwrap();
    println!(
        "  sample nets: member {creditor} is owed net {max_net}; member {debtor} owes net {}; Σ nets = 0",
        -min_net
    );

    println!(
        "\n★ N={N_PARTIES} custody parties, t={THRESHOLD}: {} orders across M={} members \
         cleared HOUSE-BLIND. OPERATOR per-clearing cost = fold {fold_ms:.1} ms + decrypt {decrypt_ms:.1} ms \
         (keygen {keygen_ms:.0} ms is ONE-TIME; encryption is per-client-parallel; the reference is demo-only). \
         Nobody saw an order.",
        book.nonzero, cfg.n_members
    );
    // Machine-readable line for the scale sweep (all values observed, release build).
    println!(
        "SCALE members={} obligations={} max_amount={} nonzero={} gross={} \
         ref_ms={ref_ms:.3} enc_ms={enc_ms:.3} enc_per_client_ms={enc_per_client_ms:.4} \
         fold_ms={fold_ms:.3} decrypt_ms={decrypt_ms:.3} keygen_ms={keygen_ms:.3}",
        cfg.n_members, cfg.obligations_per_member, cfg.max_amount, book.nonzero, book.gross
    );
    println!();

    // ── SCENARIO B: malice is caught and attributed. ─────────────────────────
    run_malice_scenario(&params);
}

/// A fresh committee where dealer 0 lies to recipient 1. The recipient must
/// refuse with an ATTRIBUTED error, and the committee must not come up.
fn run_malice_scenario(params: &BfvParams) {
    println!("── SCENARIO B: a dealer that lies to one recipient ──");
    #[cfg(not(debug_assertions))]
    {
        let _ = params;
        println!("(skipped: the hostile dealer entry point is compiled out of release builds)");
        return;
    }
    #[cfg(debug_assertions)]
    {
        const HOSTILE_DEALER: usize = 0;
        const VICTIM: usize = 1;
        let (mut actors, _house, _party_keys) = stand_up_committee(params);

        // Everyone deals; dealer 0 corrupts the row it seals to victim 1.
        let mut dealt: Vec<(usize, usize, Vec<u8>)> = Vec::new();
        for actor in actors.iter_mut() {
            let dealer = actor.index();
            let sealed = if dealer == HOSTILE_DEALER {
                actor.deal_hostile(VICTIM).expect("hostile deal")
            } else {
                actor.deal().expect("honest deal")
            };
            for (recipient, bytes) in sealed {
                dealt.push((dealer, recipient, bytes));
            }
        }

        // Route rows; the victim's acceptance of dealer 0 must refuse.
        let mut victim_refusal: Option<DistributedCommitteeError> = None;
        for (dealer, recipient, bytes) in dealt {
            match actors[recipient].accept(dealer, &bytes) {
                Ok(()) => {}
                Err(error) => {
                    println!("party {recipient} REFUSED the dealing from party {dealer}: {error}");
                    if recipient == VICTIM && dealer == HOSTILE_DEALER {
                        victim_refusal = Some(error);
                    }
                }
            }
        }

        let refusal = victim_refusal.expect("the victim must refuse the corrupted row");
        match refusal {
            DistributedCommitteeError::Quorum(QuorumError::VssCommitmentMismatch {
                dealer,
                recipient,
            }) => {
                assert_eq!(dealer, HOSTILE_DEALER);
                assert_eq!(recipient, VICTIM);
                println!(
                    "✔ malice ATTRIBUTED: VssCommitmentMismatch {{ dealer: {dealer}, recipient: {recipient} }} \
                     — the committee does not come up, and the liar is named.\n"
                );
            }
            other => panic!("expected an attributed commitment-mismatch refusal, got {other}"),
        }
    }
}

fn hex8(bytes: &[u8]) -> String {
    bytes.iter().take(8).map(|b| format!("{b:02x}")).collect()
}
