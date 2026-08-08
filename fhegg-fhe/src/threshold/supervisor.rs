//! **WHERE A DISTRIBUTED COMMITTEE'S PROCESS LIFECYCLE LIVES.**
//!
//! [`super::relying_party::DistributedCommitteeClient`] can drive the whole
//! authenticated committee — key agreement, the verified commit round, the
//! relinearization ceremony, certificate-checked opening — and it has been able to
//! since the endorsement seam closed. The production callers still ran the old
//! in-process committee anyway, and the reason was never cryptographic. It was
//! that a distributed committee is `n` PROCESSES to enrol, spawn, wait on, name a
//! failure of, and shut down, and both market ceremonies are synchronous functions
//! that return a ready committee. Nobody had anywhere to put the process
//! supervision, and putting it inside a market offering would have been putting it
//! in the wrong place.
//!
//! This module is that place, and its address is the argument for it: process
//! supervision of committee parties belongs in the crate that OWNS the party
//! binary and the wire protocol, not in a consumer. A market, an offering or a
//! node then holds a [`LiveCommittee`] it did not spawn and cannot corrupt, and
//! contains no supervisor of its own.
//!
//! # The two postures, and which one is production
//!
//! * [`CommitteeSupervisor::attach`] — **the production posture.** The `n` party
//!   processes are already running, operated independently (ideally on separate
//!   hosts under separate authority, which is the entire point of the committee).
//!   This caller enrols itself at the relying-party slot, waits for the committee
//!   to reach custody, and drives it. It spawns nothing and can kill nothing.
//! * [`CommitteeSupervisor::spawn_local`] — **the single-host posture**, for
//!   development, for tests, and for a deployment that has honestly decided one
//!   host is enough. It forks the `n` party processes itself and owns their
//!   lifetimes. Say out loud what it costs: `n` processes under ONE operator on
//!   ONE host is a weaker adversary model than `n` independently-operated hosts,
//!   because the operator can read every process's memory. What survives is
//!   everything the protocol enforces — sealed authenticated transport, the
//!   endorsement binding proof, certificate-checked openings, and the fact that no
//!   single process ever holds more than one custody share. What does not survive
//!   is an adversary who owns the host.
//!
//! Both return the SAME [`LiveCommittee`]; the only difference is whether the
//! children are ours to kill.
//!
//! # What this does NOT do
//!
//! It does not restart a dead party, re-share to a replacement, or survive the
//! relying party's own restart. A party that dies has ended this committee's life,
//! and [`LiveCommittee`] says so by refusing rather than by degrading. Proactive
//! re-sharing and committee rotation are real work and they are not here.

use std::collections::BTreeMap;
use std::fs;
use std::io::{BufRead, BufReader};
use std::net::SocketAddr;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use ed25519_dalek::SigningKey;
use fhe::bfv::{Ciphertext, Encoding, Plaintext, RelinearizationKey};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};
use rand::rngs::OsRng;
use rand::RngCore;

use crate::bfv_mul::{BoundedCiphertext, MulEngine};
use crate::mpc_party::transport::{EqualityTransportRoster, NativePqTransportIdentity};
use crate::threshold::distributed::{decode_enrollment, encode_enrollment, DistributedDkg};
use crate::threshold::quorum::VerifiedDkgTranscript;
use crate::threshold::relying_party::{DistributedCommitteeClient, RelyingPartyError, WireCost};
use crate::threshold::{BfvParams, CollectivePublicKey};

/// How many trailing stderr lines a supervised party keeps for its epitaph.
///
/// A dead party's REASON is the whole value of capturing stderr at all: the
/// difference between "party 1 exited with status 2" and
/// "`VssCommitmentMismatch { dealer: 0, recipient: 1 }`" is the difference between
/// an operator paging someone and an operator knowing which party lied.
const STDERR_TAIL_LINES: usize = 64;

/// Why a committee could not be stood up, driven, or opened.
#[derive(Debug)]
pub enum SupervisorError {
    /// The spec itself cannot describe a committee.
    Spec(String),
    /// A rendezvous directory could not be created, written or read.
    Rendezvous(String),
    /// A party process could not be launched, or did not announce itself.
    Launch(String),
    /// **A party process DIED**, with the reason it named. `refusal` is the last
    /// line it wrote containing a refusal — the actual cause, not the exit status.
    PartyDied {
        party: usize,
        status: String,
        refusal: Option<String>,
        stderr_tail: Vec<String>,
    },
    /// The committee did not reach custody before the deadline, with what each
    /// party had reached by then.
    SetupTimeout {
        waited: Duration,
        ready: Vec<usize>,
        missing: Vec<usize>,
    },
    /// The relying-party half refused: transport, disagreement, a quorum or
    /// certificate refusal, or a relinearization refusal.
    Committee(RelyingPartyError),
    /// An opening roster cannot open: too few parties named, or a party named
    /// twice or out of range.
    Roster(String),
    /// A plaintext could not be encoded or encrypted to the collective key.
    Encoding(String),
}

impl std::fmt::Display for SupervisorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Spec(why) => write!(f, "the committee spec was refused: {why}"),
            Self::Rendezvous(why) => write!(f, "the committee rendezvous failed: {why}"),
            Self::Launch(why) => write!(f, "a committee party could not be launched: {why}"),
            Self::PartyDied {
                party,
                status,
                refusal,
                ..
            } => match refusal {
                Some(refusal) => write!(
                    f,
                    "committee party {party} died ({status}) REFUSING: {refusal}"
                ),
                None => write!(
                    f,
                    "committee party {party} died ({status}) and named no refusal"
                ),
            },
            Self::SetupTimeout {
                waited,
                ready,
                missing,
            } => write!(
                f,
                "the committee did not reach custody in {waited:?}: parties {ready:?} reached it, \
                 parties {missing:?} did not"
            ),
            Self::Committee(error) => write!(f, "{error}"),
            Self::Roster(why) => write!(f, "the opening roster was refused: {why}"),
            Self::Encoding(why) => write!(f, "a plaintext could not be prepared: {why}"),
        }
    }
}

impl std::error::Error for SupervisorError {}

impl From<RelyingPartyError> for SupervisorError {
    fn from(error: RelyingPartyError) -> Self {
        Self::Committee(error)
    }
}

impl From<crate::threshold::distributed::DistributedCommitteeError> for SupervisorError {
    fn from(error: crate::threshold::distributed::DistributedCommitteeError) -> Self {
        Self::Committee(RelyingPartyError::Committee(error))
    }
}

type Result<T> = std::result::Result<T, SupervisorError>;

/// The full parameter set of one committee's lifecycle.
#[derive(Clone)]
pub struct CommitteeSpec {
    /// The shared rendezvous directory: public identities and listen addresses
    /// ONLY. It is the equivalent of DNS plus a public key directory, and no
    /// protocol message ever passes through it. Every party's secret lives `0600`
    /// under its own `secret/` entry and is read by nobody else.
    pub session_dir: PathBuf,
    /// Roster size.
    pub n_parties: usize,
    /// Opening threshold. `t` live parties open; `n - t` may be offline.
    pub threshold: usize,
    /// The BFV parameter set. Must be the one the party binaries were built to
    /// use — they derive it themselves and a disagreement surfaces as a refusal,
    /// not as a wrong answer.
    pub params: BfvParams,
    /// How long the committee has to reach custody before the wait is a failure.
    pub setup_timeout: Duration,
    /// Per-request socket timeout for this caller.
    pub io_timeout: Duration,
}

impl CommitteeSpec {
    /// A spec over a fresh, uniquely-named rendezvous directory under the system
    /// temporary directory.
    pub fn ephemeral(label: &str, n_parties: usize, threshold: usize, params: BfvParams) -> Self {
        let mut session_dir = std::env::temp_dir();
        session_dir.push(format!(
            "fhegg-committee-{label}-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or_default()
        ));
        Self {
            session_dir,
            n_parties,
            threshold,
            params,
            setup_timeout: Duration::from_secs(900),
            io_timeout: Duration::from_secs(300),
        }
    }

    fn check(&self) -> Result<()> {
        if self.n_parties < 2 {
            return Err(SupervisorError::Spec(format!(
                "a committee with no-single-viewer content needs at least 2 parties, got {}",
                self.n_parties
            )));
        }
        if self.threshold < 2 {
            return Err(SupervisorError::Spec(format!(
                "an opening threshold of {} lets ONE party open unilaterally, which is the \
                 property the committee exists to deny",
                self.threshold
            )));
        }
        if self.threshold > self.n_parties {
            return Err(SupervisorError::Spec(format!(
                "a {}-of-{} committee can never open",
                self.threshold, self.n_parties
            )));
        }
        Ok(())
    }

    fn enroll_dir(&self) -> PathBuf {
        self.session_dir.join("enroll")
    }

    fn ready_path(&self, party: usize) -> PathBuf {
        self.session_dir
            .join("ready")
            .join(format!("{party}.ready"))
    }

    fn address_path(&self, party: usize) -> PathBuf {
        self.session_dir.join("addr").join(format!("{party}.addr"))
    }

    fn public_path(&self, slot: usize) -> PathBuf {
        self.enroll_dir().join(format!("{slot}.pub"))
    }
}

/// How to launch one party process, when this caller is the one launching them.
#[derive(Debug, Clone)]
pub struct PartyLaunch {
    /// The `threshold-committee-party` binary. It is built by `fhegg-fhe` under
    /// `--features verified-pq-runtime-tests`, and a test reaches it through
    /// `env!("CARGO_BIN_EXE_threshold-committee-party")`.
    pub binary: PathBuf,
    /// Extra environment for every child, e.g. the debug-only
    /// `FHEGG_COMMITTEE_TAMPER_ROW` adversary. Applied per party index; a party
    /// with no entry gets none.
    pub per_party_env: BTreeMap<usize, Vec<(String, String)>>,
    /// Inherit the child's stderr to this process's stderr as well as capturing
    /// it. Off by default: the capture is what the epitaph is built from, and a
    /// running committee is chatty.
    pub echo_stderr: bool,
}

impl PartyLaunch {
    pub fn new(binary: impl Into<PathBuf>) -> Self {
        Self {
            binary: binary.into(),
            per_party_env: BTreeMap::new(),
            echo_stderr: false,
        }
    }

    /// Give one party extra environment. Used to arm the debug-only lying-dealer
    /// adversary at a named party.
    pub fn with_party_env(mut self, party: usize, key: &str, value: &str) -> Self {
        self.per_party_env
            .entry(party)
            .or_default()
            .push((key.to_string(), value.to_string()));
        self
    }
}

/// One party process this supervisor owns, plus everything needed to say what
/// happened to it.
struct SupervisedParty {
    party: usize,
    child: Child,
    /// The pid the party reported for ITSELF on stdout. Compared against the pid
    /// the OS gave us, it is the evidence these are processes and not threads
    /// with a story.
    reported_pid: u32,
    address: SocketAddr,
    stderr: Arc<Mutex<Vec<String>>>,
}

impl SupervisedParty {
    fn stderr_tail(&self) -> Vec<String> {
        self.stderr
            .lock()
            .map(|lines| lines.clone())
            .unwrap_or_default()
    }

    /// The last line this party wrote that names a refusal. The party binary
    /// prints its refusals with `REFUSED`, and its fatal exit path prints
    /// `threshold-committee-party: <error>`; both are cause, not status.
    fn refusal(&self) -> Option<String> {
        self.stderr_tail()
            .iter()
            .rev()
            .find(|line| line.contains("REFUSED") || line.contains("threshold-committee-party:"))
            .cloned()
    }

    fn died(&mut self) -> Option<SupervisorError> {
        let status = self.child.try_wait().ok().flatten()?;
        Some(SupervisorError::PartyDied {
            party: self.party,
            status: status.to_string(),
            refusal: self.refusal(),
            stderr_tail: self.stderr_tail(),
        })
    }
}

impl Drop for SupervisedParty {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Wall-clock for every phase of standing a committee up.
///
/// These are MEASUREMENTS of one run on one machine, not a model. Read them as
/// "what it cost here", and re-measure anywhere the answer matters.
#[derive(Debug, Clone, Copy, Default)]
pub struct CommitteePhases {
    /// Generating and publishing this caller's relying-party identity.
    pub enroll: Duration,
    /// Forking the party processes and reading their announcements. Zero when
    /// attached to already-running parties.
    pub spawn: Duration,
    /// The DISTRIBUTED KEY GENERATION: every party deals, delivers one sealed row
    /// per peer, verifies the dealings addressed to it, cross-evaluates, and
    /// aggregates its custody. Measured as the wait for the last `ready` file, so
    /// it includes the parties' own lattice work.
    pub dkg: Duration,
    /// Asking every party for its independently-aggregated collective public key
    /// and refusing unless all `n` agree.
    pub key_agreement: Duration,
    /// The verified commit round plus the finalize round: every party's
    /// aggregate-row commitment and its binding proof collected and checked, then
    /// the assembled set pushed back so each party reaches certificate-capable
    /// custody.
    pub commit_round: Duration,
}

impl CommitteePhases {
    /// Everything above, summed: the wall-clock from "no committee" to "a
    /// committee that can be asked to open something".
    pub fn total(&self) -> Duration {
        self.enroll + self.spawn + self.dkg + self.key_agreement + self.commit_round
    }
}

/// Stands committees up. It holds no state; the state is the [`LiveCommittee`].
pub struct CommitteeSupervisor;

impl CommitteeSupervisor {
    /// **THE PRODUCTION POSTURE.** The `n` party processes are already running
    /// under their own operators. Enrol at the relying-party slot, wait for the
    /// committee to reach custody, and drive it. Nothing is spawned; nothing can
    /// be killed.
    pub fn attach(spec: CommitteeSpec) -> Result<LiveCommittee> {
        Self::stand_up(spec, Vec::new(), Duration::ZERO)
    }

    /// **THE SINGLE-HOST POSTURE.** Fork the `n` party processes and own their
    /// lifetimes. Read [`CommitteeSupervisor`]'s module docs for exactly which
    /// part of the claim one host costs you.
    pub fn spawn_local(spec: CommitteeSpec, launch: &PartyLaunch) -> Result<LiveCommittee> {
        spec.check()?;
        prepare_rendezvous(&spec)?;
        let started = Instant::now();
        let mut parties = Vec::with_capacity(spec.n_parties);
        for party in 0..spec.n_parties {
            parties.push(spawn_party(&spec, launch, party)?);
        }
        assert_separate_processes(&parties)?;
        let spawn = started.elapsed();
        Self::stand_up(spec, parties, spawn)
    }

    fn stand_up(
        spec: CommitteeSpec,
        mut parties: Vec<SupervisedParty>,
        spawn: Duration,
    ) -> Result<LiveCommittee> {
        spec.check()?;
        prepare_rendezvous(&spec)?;

        // ── ENROL. The parties cannot derive the roster — and therefore cannot
        // derive the session or the CRP seed — until EVERY slot including the
        // relying party's is published. So this must land before the wait.
        let started = Instant::now();
        let identity = enroll_relying_party(&spec)?;
        let enroll = started.elapsed();

        // ── DKG. Wait for custody, failing THE MOMENT a party dies rather than
        // at the deadline: without that, a two-second refusal is indistinguishable
        // from a slow ceremony until the timeout, and the reason stays buried in a
        // child's stderr. That is the difference this supervisor exists to make.
        let started = Instant::now();
        wait_for_custody(&spec, &mut parties)?;
        let dkg = started.elapsed();

        let addresses = read_addresses(&spec, &parties)?;
        let client = build_client(&spec, identity, addresses)?;

        let started = Instant::now();
        let collective = client.collective_public_key()?;
        let key_agreement = started.elapsed();

        let started = Instant::now();
        let transcript = client.verified_transcript(&collective)?;
        let commit_round = started.elapsed();

        Ok(LiveCommittee {
            client,
            collective,
            transcript,
            spec,
            parties,
            phases: CommitteePhases {
                enroll,
                spawn,
                dkg,
                key_agreement,
                commit_round,
            },
            relin: OnceLock::new(),
        })
    }
}

/// **A COMMITTEE THAT IS UP.** It holds no share and never learns one; it holds a
/// client, the collective key every party independently agreed, and the verified
/// transcript every decrypt-share certificate anchors to.
///
/// A consumer — a market offering, a node's clearing surface — holds one of these
/// and contains no process supervision of its own. That is the whole point.
pub struct LiveCommittee {
    client: DistributedCommitteeClient,
    collective: CollectivePublicKey,
    transcript: VerifiedDkgTranscript,
    spec: CommitteeSpec,
    /// Empty when attached: an attached committee's processes are not ours.
    parties: Vec<SupervisedParty>,
    phases: CommitteePhases,
    relin: OnceLock<RelinearizationKey>,
}

impl LiveCommittee {
    /// The measured wall-clock of standing this committee up, phase by phase.
    pub fn phases(&self) -> CommitteePhases {
        self.phases
    }

    /// What this caller has spent on the wire so far. Difference two of these to
    /// price any operation exactly.
    pub fn wire_cost(&self) -> WireCost {
        self.client.wire_cost()
    }

    /// The pids of the party processes THIS supervisor spawned. Empty when
    /// attached — an attached committee is deliberately unable to name, and
    /// therefore unable to kill, someone else's processes.
    pub fn party_pids(&self) -> Vec<u32> {
        self.parties.iter().map(|p| p.reported_pid).collect()
    }

    pub fn n_parties(&self) -> usize {
        self.spec.n_parties
    }

    /// The opening threshold: `t` live parties open, `n - t` may be offline.
    ///
    /// A caller migrating off an `n`-of-`n` in-process committee must read this
    /// rather than assume: `t`-of-`n` is a WEAKER reconstruction requirement, and
    /// it is a deliberate availability trade, not a detail to match silently.
    pub fn threshold(&self) -> usize {
        self.spec.threshold
    }

    pub fn params(&self) -> &BfvParams {
        &self.spec.params
    }

    pub fn plaintext_modulus(&self) -> u64 {
        self.spec.params.plaintext_modulus()
    }

    /// The collective public key. Encrypting to it needs no secret and no quorum.
    pub fn collective(&self) -> &CollectivePublicKey {
        &self.collective
    }

    /// A short public fingerprint of the collective key everything is encrypted to.
    pub fn collective_key_digest(&self) -> [u8; 32] {
        *blake3::hash(&self.collective.pk.to_bytes()).as_bytes()
    }

    /// The verified transcript every decrypt-share certificate is checked against.
    pub fn transcript(&self) -> &VerifiedDkgTranscript {
        &self.transcript
    }

    pub fn client(&self) -> &DistributedCommitteeClient {
        &self.client
    }

    /// The lowest-indexed `t` parties, which is the roster a caller with no
    /// liveness information of its own should use.
    pub fn default_roster(&self) -> Vec<usize> {
        (0..self.spec.threshold).collect()
    }

    /// Encrypt one value into SIMD slot 0 under the collective key. No secret and
    /// no quorum is involved: anyone holding the public key can do this, including
    /// a trader in its own process.
    pub fn encrypt(&self, value: u64) -> Result<Ciphertext> {
        let pt = self.plaintext(value)?;
        self.collective
            .pk
            .try_encrypt(&pt, &mut rand_09::rng())
            .map_err(|e| SupervisorError::Encoding(format!("collective encrypt: {e}")))
    }

    /// A bare SIMD plaintext, for the plaintext-multiply weights a linear path uses.
    pub fn plaintext(&self, value: u64) -> Result<Plaintext> {
        Plaintext::try_encode(&[value], Encoding::simd(), self.spec.params.arc())
            .map_err(|e| SupervisorError::Encoding(format!("encode: {e}")))
    }

    /// **OPEN, ACROSS PROCESSES, CERTIFICATE-CHECKED.** `roster` names the live
    /// parties; each produces a certificate-carrying signed share in its OWN
    /// process, and the verified combiner refuses any share whose certificate is
    /// missing or does not verify against [`Self::transcript`].
    ///
    /// A roster shorter than `t` is refused HERE, before a byte moves, and the
    /// refusal says how short it was — a caller must not learn that its committee
    /// is unavailable from a combiner arity error three round-trips later.
    pub fn open_slots(
        &self,
        ciphertext_bytes: &[u8],
        plain_bound: u64,
        roster: &[usize],
        nonce: [u8; 32],
    ) -> Result<Vec<u64>> {
        self.check_roster(roster)?;
        Ok(self.client.open_verified(
            &self.transcript,
            ciphertext_bytes,
            plain_bound,
            roster,
            nonce,
        )?)
    }

    /// [`Self::open_slots`] over the default `t`-party roster, returning SIMD slot 0.
    pub fn open(&self, ciphertext: &Ciphertext, plain_bound: u64, nonce: [u8; 32]) -> Result<u64> {
        let roster = self.default_roster();
        let slots = self.open_slots(&ciphertext.to_bytes(), plain_bound, &roster, nonce)?;
        slots
            .first()
            .copied()
            .ok_or_else(|| SupervisorError::Roster("the opening returned no slots".to_string()))
    }

    /// [`Self::open`] for a bound-carrying ciphertext.
    pub fn open_bounded(&self, ciphertext: &BoundedCiphertext, nonce: [u8; 32]) -> Result<u64> {
        self.open(&ciphertext.ct, ciphertext.plain_bound, nonce)
    }

    /// **THE DISTRIBUTED RELINEARIZATION KEY**, run once and cached.
    ///
    /// `n`-of-`n` over the DEALERS, not `t`-of-`n`: relin runs on
    /// `s = sum_d s_d` because the Lagrange custody rows provably cannot carry it.
    /// Every party must be live for this call, which is a STRICTER liveness
    /// requirement than opening — say so where a caller can act on it rather than
    /// discovering it as a timeout.
    ///
    /// The key returned has passed its acceptance gate: fresh random `ct x ct`
    /// products decrypted through this committee's real `t`-of-`n` certified
    /// opening.
    pub fn relin_key(
        &self,
        public_entropy: [u8; 32],
        timeout: Duration,
        trials: usize,
    ) -> Result<&RelinearizationKey> {
        if let Some(key) = self.relin.get() {
            return Ok(key);
        }
        let roster = self.default_roster();
        let key = self.client.relin_key(
            &self.collective,
            &self.transcript,
            public_entropy,
            timeout,
            trials,
            &roster,
        )?;
        let _ = self.relin.set(key);
        self.relin
            .get()
            .ok_or_else(|| SupervisorError::Roster("the relin cache did not accept a key".into()))
    }

    /// The wrap-guarded `ct x ct` multiply engine over the distributed relin key.
    pub fn mul_engine(
        &self,
        public_entropy: [u8; 32],
        timeout: Duration,
        trials: usize,
    ) -> Result<MulEngine> {
        let key = self.relin_key(public_entropy, timeout, trials)?;
        MulEngine::new(key, self.spec.params.arc())
            .map_err(|e| SupervisorError::Roster(format!("the multiply engine refused: {e:?}")))
    }

    /// Refuse an unopenable roster before anything is sent.
    fn check_roster(&self, roster: &[usize]) -> Result<()> {
        if roster.len() < self.spec.threshold {
            return Err(SupervisorError::Roster(format!(
                "{} live parties named, below the {}-of-{} opening threshold — nothing was sent",
                roster.len(),
                self.spec.threshold,
                self.spec.n_parties
            )));
        }
        let mut seen = roster.to_vec();
        seen.sort_unstable();
        seen.dedup();
        if seen.len() != roster.len() {
            return Err(SupervisorError::Roster(
                "an opening roster named the same party twice".to_string(),
            ));
        }
        // The opening session takes the roster in INCREASING order — the Lagrange
        // coefficients are computed against that order, so an out-of-order roster
        // is a wrong opening rather than an invalid one. Refuse it by name here
        // instead of letting it become a garbage plaintext downstream.
        if seen.as_slice() != roster {
            return Err(SupervisorError::Roster(format!(
                "an opening roster must name parties in increasing order; got {roster:?}"
            )));
        }
        if let Some(&out) = roster.iter().find(|&&p| p >= self.spec.n_parties) {
            return Err(SupervisorError::Roster(format!(
                "party {out} is not on a {}-party committee",
                self.spec.n_parties
            )));
        }
        Ok(())
    }

    /// Release this committee. Consuming, because a released committee is not a
    /// committee.
    ///
    /// **WHAT IT DOES DEPENDS ON WHO OWNS THE PARTIES, and it must.** A caller that
    /// spawned them sends the shutdown frame, waits for them to exit, and removes
    /// the rendezvous directory it created. A caller that ATTACHED to parties
    /// running under someone else's authority does none of that — it drops its own
    /// client and leaves. `KIND_SHUTDOWN` ends a party process, so an attached
    /// caller "shutting down" would be terminating a committee it does not operate
    /// and deleting an operator's directory, on the strength of holding an address
    /// list. The module header promises an attached caller can kill nothing; this
    /// is where that promise is either kept or quietly broken.
    pub fn shutdown(mut self) {
        if self.parties.is_empty() {
            return;
        }
        for party in 0..self.spec.n_parties {
            self.client.shutdown(party);
        }
        // The party answers the shutdown frame and then exits, so a short grace
        // beats a kill; `Drop` on each `SupervisedParty` is the backstop.
        let deadline = Instant::now() + Duration::from_secs(10);
        for party in &mut self.parties {
            while Instant::now() < deadline {
                match party.child.try_wait() {
                    Ok(Some(_)) | Err(_) => break,
                    Ok(None) => std::thread::sleep(Duration::from_millis(50)),
                }
            }
        }
        let _ = fs::remove_dir_all(&self.spec.session_dir);
    }
}

// ─── the lifecycle steps, each one thing ─────────────────────────────────────

fn prepare_rendezvous(spec: &CommitteeSpec) -> Result<()> {
    fs::create_dir_all(spec.enroll_dir())
        .map_err(|e| SupervisorError::Rendezvous(format!("{:?}: {e}", spec.enroll_dir())))
}

/// Enrol THIS process at the relying-party slot, roster index `n`.
///
/// Refuses if the Lean-verified PQ cores are not installed. That is a CHECK, not a
/// docblock: without them `dregg-pq` aborts the process at the first ML-DSA
/// operation, and a bare SIGABRT several seconds into a ceremony is the worst
/// possible way to learn that the archive is missing.
fn enroll_relying_party(spec: &CommitteeSpec) -> Result<NativePqTransportIdentity> {
    let missing = missing_verified_pq_cores();
    if !missing.is_empty() {
        return Err(SupervisorError::Launch(format!(
            "the Lean-verified PQ cores are not installed in this process ({}). Every committee \
             message is a dual-signed hybrid-PQ envelope, so dregg-pq would abort this process at \
             the first ML-DSA operation rather than answer from the unaudited fallback. Install \
             them before standing a committee up.",
            missing.join(", ")
        )));
    }

    let mut seed = [0u8; 32];
    OsRng.try_fill_bytes(&mut seed).map_err(|e| {
        SupervisorError::Launch(format!("no OS entropy for the relying party: {e}"))
    })?;
    let (encapsulation_key, decapsulation_key) = dregg_pq::ml_kem768_keygen();
    let identity = NativePqTransportIdentity::from_material(
        SigningKey::from_bytes(&seed),
        encapsulation_key,
        decapsulation_key,
    )
    .map_err(|e| SupervisorError::Launch(format!("relying-party identity: {e}")))?;

    let path = spec.public_path(spec.n_parties);
    let temporary = path.with_extension("tmp");
    fs::write(&temporary, encode_enrollment(&identity.public_identity()))
        .and_then(|()| fs::rename(&temporary, &path))
        .map_err(|e| SupervisorError::Rendezvous(format!("publish {path:?}: {e}")))?;
    Ok(identity)
}

/// Which verified PQ directions this process is missing, by name.
fn missing_verified_pq_cores() -> Vec<&'static str> {
    let mut missing = Vec::new();
    if !dregg_pq::lean_verify_core_real_installed() {
        missing.push("ml-dsa verify");
    }
    if !dregg_pq::lean_sign_core_real_installed() {
        missing.push("ml-dsa sign");
    }
    if !dregg_pq::lean_keygen_core_real_installed() {
        missing.push("ml-dsa keygen");
    }
    if !dregg_pq::hybrid_kem::mlkem_keygen_real_core_installed() {
        missing.push("ml-kem keygen");
    }
    if !dregg_pq::hybrid_kem::mlkem_encaps_real_core_installed() {
        missing.push("ml-kem encaps");
    }
    if !dregg_pq::hybrid_kem::mlkem_decaps_real_core_installed() {
        missing.push("ml-kem decaps");
    }
    missing
}

fn spawn_party(
    spec: &CommitteeSpec,
    launch: &PartyLaunch,
    party: usize,
) -> Result<SupervisedParty> {
    let mut command = Command::new(&launch.binary);
    command
        .args([
            "serve",
            spec.session_dir
                .to_str()
                .ok_or_else(|| SupervisorError::Spec("the session dir is not utf-8".into()))?,
            &party.to_string(),
            &spec.n_parties.to_string(),
            &spec.threshold.to_string(),
        ])
        // NEVER inherited: a party that reaches dregg-pq's unaudited fallback must
        // abort, and an opt-in leaking in from the supervisor's environment would
        // silently turn the audited transport into an unaudited one.
        .env_remove("DREGG_ALLOW_UNAUDITED_PQ")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    for (key, value) in launch.per_party_env.get(&party).into_iter().flatten() {
        command.env(key, value);
    }
    let mut child = command.spawn().map_err(|e| {
        SupervisorError::Launch(format!("{:?} for party {party}: {e}", launch.binary))
    })?;

    // Drain stderr on its own thread. Two reasons, both load-bearing: a child
    // whose stderr pipe fills BLOCKS forever, and the captured tail is the only
    // place a refusal's CAUSE exists.
    let stderr = Arc::new(Mutex::new(Vec::new()));
    if let Some(pipe) = child.stderr.take() {
        let sink = Arc::clone(&stderr);
        let echo = launch.echo_stderr;
        std::thread::spawn(move || {
            for line in BufReader::new(pipe)
                .lines()
                .map_while(std::result::Result::ok)
            {
                if echo {
                    eprintln!("party {party}: {line}");
                }
                if let Ok(mut lines) = sink.lock() {
                    if lines.len() == STDERR_TAIL_LINES {
                        lines.remove(0);
                    }
                    lines.push(line);
                }
            }
        });
    }

    // The first stdout line is the party's own `getpid()` and listen address.
    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| SupervisorError::Launch(format!("party {party} has no stdout")))?;
    let mut line = String::new();
    BufReader::new(stdout)
        .read_line(&mut line)
        .map_err(|e| SupervisorError::Launch(format!("party {party} announcement: {e}")))?;
    let fields = line.split_whitespace().collect::<Vec<_>>();
    if fields.first().copied() != Some("party") || fields.len() < 6 {
        let tail = stderr.lock().map(|l| l.join(" | ")).unwrap_or_default();
        return Err(SupervisorError::Launch(format!(
            "party {party} did not announce itself (stdout {line:?}); stderr: {tail}"
        )));
    }
    let reported_pid = fields[3]
        .parse::<u32>()
        .map_err(|_| SupervisorError::Launch(format!("party {party} pid field: {line:?}")))?;
    let address = fields
        .last()
        .expect("checked length")
        .parse::<SocketAddr>()
        .map_err(|_| SupervisorError::Launch(format!("party {party} address field: {line:?}")))?;

    Ok(SupervisedParty {
        party,
        child,
        reported_pid,
        address,
        stderr,
    })
}

/// Assert the spawned parties really are separate processes.
///
/// It costs three comparisons and it is the difference between a distributed
/// committee and a story about one.
fn assert_separate_processes(parties: &[SupervisedParty]) -> Result<()> {
    let mut seen = std::collections::BTreeSet::new();
    for party in parties {
        if party.child.id() != party.reported_pid {
            return Err(SupervisorError::Launch(format!(
                "party {} reported pid {} but the OS gave the parent {}",
                party.party,
                party.reported_pid,
                party.child.id()
            )));
        }
        if party.reported_pid == std::process::id() {
            return Err(SupervisorError::Launch(format!(
                "party {} is running inside the relying party's process",
                party.party
            )));
        }
        if !seen.insert(party.reported_pid) {
            return Err(SupervisorError::Launch(format!(
                "party {} shares a process with another party",
                party.party
            )));
        }
    }
    Ok(())
}

/// Wait for every party to reach custody, FAILING THE MOMENT ONE DIES.
fn wait_for_custody(spec: &CommitteeSpec, parties: &mut [SupervisedParty]) -> Result<()> {
    let started = Instant::now();
    let deadline = started + spec.setup_timeout;
    loop {
        let ready = (0..spec.n_parties)
            .filter(|&party| spec.ready_path(party).exists())
            .collect::<Vec<_>>();
        if ready.len() == spec.n_parties {
            return check_one_setup(spec);
        }
        for party in parties.iter_mut() {
            if let Some(death) = party.died() {
                return Err(death);
            }
        }
        if Instant::now() >= deadline {
            let missing = (0..spec.n_parties)
                .filter(|party| !ready.contains(party))
                .collect::<Vec<_>>();
            return Err(SupervisorError::SetupTimeout {
                waited: started.elapsed(),
                ready,
                missing,
            });
        }
        std::thread::sleep(Duration::from_millis(50));
    }
}

/// Every party independently derived a setup digest from the messages it verified
/// ITSELF. If two disagree, they are not one committee, and combining across them
/// would be combining across two.
fn check_one_setup(spec: &CommitteeSpec) -> Result<()> {
    let mut first: Option<Vec<u8>> = None;
    for party in 0..spec.n_parties {
        let path = spec.ready_path(party);
        let digest = fs::read(&path)
            .map_err(|e| SupervisorError::Rendezvous(format!("setup digest {path:?}: {e}")))?;
        match &first {
            None => first = Some(digest),
            Some(expected) if expected != &digest => {
                return Err(SupervisorError::Rendezvous(format!(
                    "party {party} finished on a DIFFERENT setup than party 0 — these are two \
                     committees, not one"
                )));
            }
            Some(_) => {}
        }
    }
    Ok(())
}

/// Read every party's listen address from the RENDEZVOUS, in both postures.
///
/// One path deliberately, not two. `spawn_local` has each child's announced address
/// in hand and could have used it directly — but then `attach`'s disk read would be
/// a second shape exercised by nothing, and two shapes that agree today are two
/// shapes that disagree later. So both read the rendezvous, and where the announced
/// address IS available it is used as a cross-check: the address a party published
/// must be the address it told us it bound, or the rendezvous is not describing this
/// committee.
fn read_addresses(spec: &CommitteeSpec, parties: &[SupervisedParty]) -> Result<Vec<SocketAddr>> {
    let mut addresses = Vec::with_capacity(spec.n_parties);
    for party in 0..spec.n_parties {
        let path = spec.address_path(party);
        let text = fs::read_to_string(&path)
            .map_err(|e| SupervisorError::Rendezvous(format!("address {path:?}: {e}")))?;
        let address = text
            .trim()
            .parse::<SocketAddr>()
            .map_err(|e| SupervisorError::Rendezvous(format!("address {path:?}: {e}")))?;
        if let Some(supervised) = parties.iter().find(|p| p.party == party) {
            if supervised.address != address {
                return Err(SupervisorError::Rendezvous(format!(
                    "party {party} announced {} but the rendezvous publishes {address} — the \
                     directory is not describing this committee",
                    supervised.address
                )));
            }
        }
        addresses.push(address);
    }
    Ok(addresses)
}

fn build_client(
    spec: &CommitteeSpec,
    identity: NativePqTransportIdentity,
    addresses: Vec<SocketAddr>,
) -> Result<DistributedCommitteeClient> {
    let mut identities = Vec::with_capacity(spec.n_parties);
    for party in 0..spec.n_parties {
        let path = spec.public_path(party);
        let bytes = fs::read(&path)
            .map_err(|e| SupervisorError::Rendezvous(format!("enrollment {path:?}: {e}")))?;
        identities.push(
            decode_enrollment(&bytes)
                .map_err(|e| SupervisorError::Rendezvous(format!("enrollment {path:?}: {e}")))?,
        );
    }
    let party_keys = identities.iter().map(|i| i.ed25519()).collect::<Vec<_>>();
    let roster = EqualityTransportRoster::new_native_post_quantum(
        std::mem::take(&mut identities),
        identity.public_identity(),
    )
    .map_err(|e| SupervisorError::Rendezvous(format!("native-PQ roster: {e}")))?;
    let dkg = DistributedDkg::new(roster, spec.threshold, spec.params.clone())?;
    Ok(
        DistributedCommitteeClient::new(identity, dkg, addresses, party_keys)?
            .with_io_timeout(spec.io_timeout),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spec() -> CommitteeSpec {
        CommitteeSpec::ephemeral("unit", 3, 2, BfvParams::fold_set())
    }

    /// The spec refuses shapes that cannot carry the property the committee exists
    /// for, and it refuses them BEFORE a process is forked.
    #[test]
    fn a_spec_that_cannot_carry_the_property_is_refused_before_anything_is_spawned() {
        let mut one_party = spec();
        one_party.n_parties = 1;
        assert!(matches!(one_party.check(), Err(SupervisorError::Spec(_))));

        // A 1-of-n committee lets a SINGLE party open unilaterally. That is not a
        // weaker committee, it is the absence of one.
        let mut unilateral = spec();
        unilateral.threshold = 1;
        assert!(matches!(unilateral.check(), Err(SupervisorError::Spec(_))));

        let mut unopenable = spec();
        unopenable.threshold = 4;
        assert!(matches!(unopenable.check(), Err(SupervisorError::Spec(_))));

        assert!(spec().check().is_ok());
    }

    /// Wire cost differences are what price a phase, so the arithmetic has to
    /// saturate rather than wrap when snapshots are taken out of order.
    #[test]
    fn wire_cost_differences_saturate() {
        let early = WireCost {
            round_trips: 3,
            bytes_out: 100,
            bytes_in: 900,
        };
        let late = WireCost {
            round_trips: 11,
            bytes_out: 400,
            bytes_in: 1_100,
        };
        assert_eq!(
            late.since(early),
            WireCost {
                round_trips: 8,
                bytes_out: 300,
                bytes_in: 200
            }
        );
        assert_eq!(early.since(late), WireCost::default());
    }
}
