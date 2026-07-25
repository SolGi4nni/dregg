//! # THE ORACLE PIT — a confidential prediction market whose subject is the daily Descent.
//!
//! Public odds, private positions. Everyone sees the line; nobody sees who is holding what.
//! The market's SUBJECT is one specific run of the Lean-native Descent
//! ([`dreggnet_offerings::native_descent`]), named by `(deploy seed, run day-seed)` — the
//! beacon-derived provenance root that is unpredictable until the day is revealed. The market
//! settles on the run's REPLAY-DERIVED terminal state, never on an asserted result.
//!
//! ## Where the settlement authority actually comes from
//!
//! A prediction market is only as honest as its oracle. This one does not have an oracle
//! committee voting on "did the run get crowned"; it has an **exact re-execution**:
//!
//! 1. The pit is opened on a [`PitSubject`]. The subject's digest is written into the pit cell's
//!    `SELLER` register at birth, which the sealed-auction program holds `WriteOnce` FOR LIFE —
//!    so a live pit cannot be re-pointed at a different run.
//! 2. A settler hands the pit a [`NativeDescentRecord`] (the run's portable record). The pit
//!    refuses it unless `record.seed` and `record.day_seed` are EXACTLY the subject's. This check
//!    is load-bearing: replay redeploys on the record's OWN `day_seed`, so without it a settler
//!    could hand over a genuine run from a different day.
//! 3. The record is replayed through [`NativeDescentOffering::resume_record`]. That path
//!    redeploys a fresh `Descent` on the record's day-seed and re-executes every command through
//!    the real executor carrying the Lean-emitted `dungeonProgram` teeth, recomputing each turn's
//!    `turn_hash` and `receipt_hash`, the post-state, and the journal root, and RE-MINTING the
//!    banked relic notes. A spliced move, a substituted player, a re-pointed day, or a hand-edited
//!    completion breaks it.
//!
//!    Off-process reproducibility is real and not incidental: `WorldCell::from_compiled` derives
//!    the world's owner key as `blake3::derive_key("spween-dregg-world-owner-v1", scene_id ‖ seed)`,
//!    so the same `(scene id, seed)` yields the same cell id and the same turn hashes on anyone's
//!    machine. That is what makes the settlement checkable by a third party rather than only by us.
//!
//!    STATED AT ITS ACTUAL RESOLUTION: `replay_record` also compares `executor_signature`, but
//!    `Descent::deploy_on_day` never calls `set_executor_signing_key` (only the durable-restore
//!    path does), so at these deployment settings that field is `None` on both sides and the
//!    comparison is inert. The replay's real teeth are the recomputed hashes, the post-state
//!    equality, and the journal-root chain — which is a strong gate, but it is a REPRODUCIBILITY
//!    gate, not a signature check. Nothing here proves a record came from a blessed host; it
//!    proves the record is a real, self-consistent execution of that day's world.
//! 4. The outcome is read off the **replayed session** ([`read_verified_run`]), never off the
//!    submitted record's own `completion` field.
//! 5. The verdict digest [`pit_verdict`] — binding the subject, the replayed journal root, the
//!    terminal `flee` receipt hash, and the resolved boolean — is frozen into the pit cell's
//!    `WINNER` register by a real `resolve` turn. `WriteOnce` + `StrictMonotonic(PHASE)` mean the
//!    verdict cannot be re-announced.
//!
//! Every step of that is checkable by a third party holding the same record: re-run
//! [`read_verified_run`], recompute [`pit_verdict`], and compare it against the frozen on-ledger
//! register. Nothing here asks you to trust the pit's own bookkeeping.
//!
//! ## Where the confidentiality actually comes from
//!
//! A position is `(side, stake)`. The pit's own state holds neither:
//!
//! * the **stake** rides as a BFV ciphertext under an **n-of-n collective public key**
//!   ([`fhegg_fhe::threshold`]) — a real multiparty keygen where every party contributes to a
//!   public key nobody holds the secret for;
//! * the **side** is hidden because every position contributes to BOTH side aggregates: the
//!   backed side gets `Enc(stake)`, the other gets `Enc(0)`, and BFV encryption is randomized, so
//!   the two ciphertexts are indistinguishable;
//! * the **holder binding** is a hiding commitment `blake3_derive_key(subject, side, stake, nonce,
//!   holder)` frozen into the pit cell's `WriteOnce` commit board. The pit stores only that
//!   32-byte digest. A claim recomputes the digest from the CLAIMANT's own identity, so a
//!   position that was never taken has no matching frozen slot and cannot claim, and one holder's
//!   opening does not let another holder claim it.
//!
//! The **odds** are the marginal prices of the quadratic cost function
//! `c(q_yes, q_no) = A·q_yes² + B·q_yes·q_no + C·q_no²`:
//! `p_yes = ∂c/∂q_yes = 2A·q_yes + B·q_no`, `p_no = ∂c/∂q_no = B·q_yes + 2C·q_no`. Those are
//! LINEAR, so the pit computes them under the collective key with public-scalar multiplies and
//! homomorphic adds, then opens them by a **full-quorum threshold decrypt**. The **pool** is the
//! cost function itself, which needs a real ct×ct multiply, so it runs on the n-of-n multiparty
//! **relinearization** ceremony and is likewise only ever opened by the full quorum.
//!
//! ### What that does and does not buy (read this before quoting the module)
//!
//! * Opening BOTH marginals determines both aggregates exactly (the 2×2 system is invertible when
//!   `4AC ≠ B²`). That is **by design** — the aggregate IS the line a prediction market publishes.
//!   What stays hidden is the per-trader decomposition of that aggregate.
//! * `combine` refusing an `n−1` share set is an explicit quorum check inside `combine`, not a
//!   proof. The cryptographic no-single-viewer property rests on the smudging discipline
//!   (`MIN_SMUDGE_BITS`) that the partial decryptions carry; the `is_err()` only shows the API
//!   fails closed.
//! * The committee's parties run **in one process** here. Each holds its own independent secret
//!   and `combine` needs all of them, so the threshold property is real; the co-location is a
//!   deployment property. The transport-separated form is [`fhegg_fhe::mpc_party`].
//! * [`HostedWallets`] is a NAMED SEAM. A hosted offering has to serve the player's own private
//!   projection, so this session keeps the openings it handed out. That store is the ONE place
//!   plaintext positions exist, it is structurally separate from [`OraclePitBook`], and no pricing
//!   or settlement path can reach it — [`OraclePitBook::quote`],
//!   [`OraclePitBook::settle_on_verified_run`], and [`read_verified_run`] all take the book (or
//!   nothing) and never the wallets. In a real deployment the wallet lives on the player's device
//!   and the pit is house-blind outright.
//! * Value does not move here. The pit computes obligations (`pool`, `payout_per_share`, a
//!   claimant's payout) and stops. Escrow and transfer are the [`crate::MarketOffering`] /
//!   `dregg_intent::verified_settle` seam; a public escrow leg would leak position size and needs
//!   the confidential-amount path (`crate::fhegg_atomic_asset`).

use std::collections::BTreeMap;
use std::time::Duration;

use deos_view::{MenuItem, ViewNode};
use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, Effect, EmbeddedExecutor, Event,
    TurnReceipt, field_from_u64, symbol,
};
use dregg_cell::{CellMode, FactoryCreationParams};
use dreggnet_offerings::native_descent::{
    CommittedSeed, NativeDescentOffering, NativeDescentRecord,
};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};
use fhe::bfv::{Ciphertext, Encoding, Plaintext};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};
use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::bfv_mul::{BoundedCiphertext, MulEngine};
use fhegg_fhe::threshold::relin::{RelinKeySession, generate_relinearization_key};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, MIN_SMUDGE_BITS,
    ThresholdParty, combine,
};
use starbridge_sealed_auction::{
    AUCTION_FACTORY_VK, COMMIT_BASE, COMMIT_CAPACITY, HIGH_BID_SLOT, PHASE_COMMIT, PHASE_RESOLVED,
    PHASE_REVEAL, PHASE_SLOT, SELLER_SLOT, WINNER_SLOT, auction_child_program_vk,
    auction_factory_descriptor, close_commit_effects, commit_slot, field_to_u64,
};

/// Stable host/catalog key for the Oracle Pit offering.
pub const ORACLE_PIT_OFFERING_KEY: &str = "oracle-pit";

/// The affordance verb that takes a private position backing YES. `arg` is the stake in shares.
pub const TURN_BACK_YES: &str = "pit-back-yes";
/// The affordance verb that takes a private position backing NO. `arg` is the stake in shares.
pub const TURN_BACK_NO: &str = "pit-back-no";
/// The affordance verb that opens a held position against a settled pit. Carries the opening in
/// [`Action::text`] (see [`PositionOpening::encode`]); `arg` is unused.
pub const TURN_CLAIM: &str = "pit-claim";

/// Largest stake one position may carry, in shares. Small because the whole quadratic must stay
/// under the BFV plaintext modulus (`t = 1_032_193`) or the wrap guard fails the settlement
/// closed rather than opening a silently-wrong pool.
pub const MAX_POSITION_STAKE: u64 = 32;

/// How many positions one pit cell's `WriteOnce` commit board holds. The board is the cell's
/// field slots after the four reserved registers, so this is a real substrate bound, not a policy.
pub const MAX_PIT_POSITIONS: usize = COMMIT_CAPACITY;

const SUBJECT_DOMAIN: &str = "dreggnet-market/oracle-pit/subject/v1";
const POSITION_DOMAIN: &str = "dreggnet-market/oracle-pit/position/v1";
const VERDICT_DOMAIN: &str = "dreggnet-market/oracle-pit/verdict/v1";

/// The threshold committee's public entropy for the relinearization ceremony's CRP. Public by
/// construction — the ceremony binds it together with the keygen session and collective key.
const RELIN_PUBLIC_ENTROPY: [u8; 32] = *b"dreggnet-market-oracle-pit-relin";

// =============================================================================
// The subject: WHICH run, and WHAT question about it.
// =============================================================================

/// A binary question about a Descent run, resolvable from the run's replay-derived terminal state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DescentQuestion {
    /// Did the run bank the Crown of the Deep (relic 0)? The headline daily line.
    Crowned,
    /// Did the run bank at all — reach a terminal `flee` before the light died?
    Banked,
    /// Did the run reach at least this floor? Depth never decreases, so the terminal depth is the
    /// deepest depth.
    DepthAtLeast(u64),
    /// Did the run bank at least this many relics?
    RelicsBankedAtLeast(u64),
}

impl DescentQuestion {
    /// The question's stable wire code, hashed into the subject digest.
    fn code(&self) -> (u8, u64) {
        match self {
            DescentQuestion::Crowned => (1, 0),
            DescentQuestion::Banked => (2, 0),
            DescentQuestion::DepthAtLeast(d) => (3, *d),
            DescentQuestion::RelicsBankedAtLeast(k) => (4, *k),
        }
    }

    /// Resolve the question against a reading of a re-executed run. Pure: no market state, no
    /// clock, no committee.
    pub fn resolve(&self, reading: &PitOracleReading) -> bool {
        match self {
            DescentQuestion::Crowned => reading.crowned,
            DescentQuestion::Banked => reading.banked,
            DescentQuestion::DepthAtLeast(d) => reading.depth >= *d,
            DescentQuestion::RelicsBankedAtLeast(k) => reading.banked_relics >= *k,
        }
    }

    /// The human line a surface paints.
    pub fn headline(&self) -> String {
        match self {
            DescentQuestion::Crowned => "Will today's Descent be CROWNED?".to_string(),
            DescentQuestion::Banked => {
                "Will today's Descent BANK before the light dies?".to_string()
            }
            DescentQuestion::DepthAtLeast(d) => format!("Will today's Descent reach floor {d}?"),
            DescentQuestion::RelicsBankedAtLeast(k) => {
                format!("Will today's Descent bank {k} relics or more?")
            }
        }
    }
}

/// **What the pit is a market ON.** A run of the Lean-native Descent plus one binary question
/// about it. The subject's digest is frozen into the pit cell at birth.
///
/// # ⚠ RUN DESIGNATION — the load-bearing limitation of this module
///
/// `(seed, day_seed)` identifies **the day's WORLD, not a run of it.** The world is fixed by the
/// beacon; the MOVES are not. Every player who descends that day — and the same player descending
/// twice — produces a *different, equally genuine* [`NativeDescentRecord`], and every one of them
/// re-executes cleanly. So an unpinned pit does not settle on "today's run"; it settles on
/// **whichever verified terminal run of that day's world reaches it first**, which hands the
/// outcome to whoever settles rather than to the dungeon.
///
/// This is not hypothetical: a crowned run and a timid one on the same day both pass
/// [`read_verified_run`] for the same unpinned subject. The re-execution gate is doing its job —
/// it refuses FORGED runs — but "genuine" is weaker than "the one this market is about".
///
/// [`on_player`](Self::on_player) narrows it to one player and closes cross-player substitution.
/// It does not close same-player substitution. **Fully closing this needs a designator outside
/// this module**: the day's canonical run has to be named by something the settler does not
/// control — the daily leaderboard's admitted entry, or a run-identity commitment published
/// before the board freezes — and the subject must pin THAT. Until a deployment supplies one, the
/// pit is sound only where a single designated run exists by construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PitSubject {
    /// The run's normalized deploy seed — the world identity a replay redeploys on.
    pub seed: u8,
    /// The run's committed day-seed: the beacon-derived provenance root. Derive it from a verified
    /// daily beacon with
    /// [`native_descent_run_day_seed`](dreggnet_offerings::native_descent::native_descent_run_day_seed).
    pub day_seed: CommittedSeed,
    /// **The designated player, when the deployment pins one.** See the RUN-DESIGNATION note on
    /// [`PitSubject`]: `(seed, day_seed)` fixes the WORLD, not the run, so a pit that does not pin
    /// a player will accept any verified terminal run of that day's world. `None` is the unpinned
    /// form and is only sound when something outside this module designates the run.
    pub player: Option<String>,
    /// The binary question the pit prices.
    pub question: DescentQuestion,
}

impl PitSubject {
    /// A subject over `(seed, day_seed)` asking `question`, with NO designated player.
    ///
    /// Read the RUN-DESIGNATION note on [`PitSubject`] before deploying this form: it settles on
    /// whichever verified terminal run of that day's world is submitted first.
    pub fn new(seed: u8, day_seed: CommittedSeed, question: DescentQuestion) -> Self {
        PitSubject {
            seed,
            day_seed,
            player: None,
            question,
        }
    }

    /// A subject pinned to ONE player's run of that day's world. [`read_verified_run`] then refuses
    /// a record whose replay-derived actor is anyone else, which closes cross-player substitution.
    /// It does NOT close same-player substitution — one player can still play the day twice and
    /// submit whichever record they prefer.
    pub fn on_player(mut self, player: &DreggIdentity) -> Self {
        self.player = Some(player.as_str().to_string());
        self
    }

    /// The 32-byte subject digest — the pit's identity. Frozen into the pit cell's `WriteOnce`
    /// `SELLER` register at birth, so a live pit cannot be re-pointed at another run or question.
    pub fn digest(&self) -> [u8; 32] {
        let (code, arg) = self.question.code();
        let mut h = blake3::Hasher::new_derive_key(SUBJECT_DOMAIN);
        h.update(&[self.seed]);
        h.update(self.day_seed.as_bytes());
        match &self.player {
            None => h.update(&[0u8]),
            Some(player) => {
                h.update(&[1u8]);
                h.update(&(player.len() as u64).to_be_bytes());
                h.update(player.as_bytes())
            }
        };
        h.update(&[code]);
        h.update(&arg.to_be_bytes());
        *h.finalize().as_bytes()
    }
}

// =============================================================================
// The oracle: a run's terminal state, read by exact re-execution.
// =============================================================================

/// How a run ENDED, as the re-execution found it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PitRunTerminal {
    /// The run reached a terminal `flee` — the pack banked.
    Banked,
    /// The run stranded: no affordance is legal any more (the light died) and it never banked.
    /// Permadeath by exhaustion; nothing was banked and nothing minted.
    Died,
}

/// **A reading of one re-executed run.** Every field comes from the REPLAYED session, not from the
/// submitted record's own summary. Re-derivable by anyone holding the same record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PitOracleReading {
    /// How the run ended.
    pub terminal: PitRunTerminal,
    /// Whether the run banked at all (`terminal == Banked`).
    pub banked: bool,
    /// Whether the Crown of the Deep (relic 0) was among the banked relics.
    pub crowned: bool,
    /// How many relics banked.
    pub banked_relics: u64,
    /// The deepest floor reached (depth never decreases, so this is the terminal depth).
    pub depth: u64,
    /// How many committed moves the run took.
    pub moves: usize,
    /// The replayed journal root — the run's identity after re-execution.
    pub run_root: [u8; 32],
    /// The terminal `flee` executor receipt hash, when the run banked. `None` for a stranded run.
    pub settlement_receipt_hash: Option<[u8; 32]>,
}

/// Why the pit refused to settle. Every variant leaves the market exactly as it was.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PitRefusal {
    /// The record names a different deploy seed than the subject.
    WrongRun { want: u8, got: u8 },
    /// The record names a different day-seed than the subject. Load-bearing: replay redeploys on
    /// the record's own day-seed, so without this a genuine run from another day would replay
    /// cleanly and settle the wrong market.
    WrongDay,
    /// The subject pins a player and the record's replay-derived actor is someone else. Only
    /// raised by a subject built with [`PitSubject::on_player`].
    WrongPlayer,
    /// Exact re-execution refused the record (a spliced move, a substituted player, a hand-edited
    /// completion, a re-pointed provenance root). Carries the replay's own break reason.
    ReplayFailed(String),
    /// The record is a PREFIX of a live run: it neither banked nor stranded, so the run has not
    /// finished. A live run cannot be settled by submitting the part of it you like.
    RunNotTerminal,
    /// The pit's position board is still open. Positions must be frozen before the oracle is
    /// consulted.
    StillOpen,
    /// The pit already settled; its verdict is frozen on-ledger.
    AlreadySettled,
    /// The threshold committee could not open a value (see the inner reason).
    Committee(String),
    /// The homomorphic pricing refused rather than return a wrapped value.
    Pricing(String),
    /// The executor refused the settlement turn.
    Executor(String),
    /// Nobody took a position, so there is nothing to settle.
    NoPositions,
}

impl std::fmt::Display for PitRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PitRefusal::WrongRun { want, got } => write!(
                f,
                "this pit is a market on run seed {want}; the record is run seed {got}"
            ),
            PitRefusal::WrongDay => write!(
                f,
                "the record's day-seed is not this pit's subject day-seed — a run from another day \
                 replays cleanly and would settle the wrong market"
            ),
            PitRefusal::WrongPlayer => write!(
                f,
                "this pit is pinned to one player's run and the record was played by someone else"
            ),
            PitRefusal::ReplayFailed(why) => {
                write!(f, "the run record did not re-execute: {why}")
            }
            PitRefusal::RunNotTerminal => write!(
                f,
                "the run has not finished — it neither banked nor stranded, so this record is a \
                 prefix of a live run"
            ),
            PitRefusal::StillOpen => write!(
                f,
                "the position board is still open — freeze it before consulting the oracle"
            ),
            PitRefusal::AlreadySettled => {
                write!(f, "this pit already settled; its verdict is frozen")
            }
            PitRefusal::Committee(why) => write!(f, "the threshold committee refused: {why}"),
            PitRefusal::Pricing(why) => write!(f, "the pit refused to price: {why}"),
            PitRefusal::Executor(why) => write!(f, "the executor refused: {why}"),
            PitRefusal::NoPositions => write!(f, "no positions were taken — nothing to settle"),
        }
    }
}

impl std::error::Error for PitRefusal {}

/// **THE SETTLEMENT SOURCE.** Re-execute `record` and read the run's terminal state off the
/// replay. Takes only the subject and the record: no market state, no committee, no wallet — so an
/// auditor can run exactly this and get exactly the pit's own reading.
///
/// The `seed` / `day_seed` equality checks come FIRST and are not decoration: the replay redeploys
/// on `record.day_seed`, so an unchecked record from a different day would re-execute perfectly
/// and settle the wrong market.
pub fn read_verified_run(
    subject: &PitSubject,
    record: &NativeDescentRecord,
) -> Result<PitOracleReading, PitRefusal> {
    if record.seed != subject.seed {
        return Err(PitRefusal::WrongRun {
            want: subject.seed,
            got: record.seed,
        });
    }
    if record.day_seed != subject.day_seed {
        return Err(PitRefusal::WrongDay);
    }

    // Exact re-execution: a fresh Descent redeployed on the record's day-seed, every command
    // re-run through the real executor carrying the Lean-emitted dungeonProgram teeth, every
    // receipt hash / executor signature / post-state / journal root recomputed, and the banked
    // relic notes re-minted. The offering owns this gate; the pit never re-implements it.
    let offering = NativeDescentOffering::on_run_day_seed(record.day_seed);
    let replayed = offering
        .resume_record(record)
        .map_err(|error| PitRefusal::ReplayFailed(error.to_string()))?;

    // A pinned pit checks the actor the REPLAY bound (the offering binds it on the first admitted
    // turn and refuses any later substitution), never the record's asserted `actor` field.
    if let Some(pinned) = &subject.player {
        let played_by = replayed.actor().map(|actor| actor.as_str().to_string());
        if played_by.as_deref() != Some(pinned.as_str()) {
            return Err(PitRefusal::WrongPlayer);
        }
    }

    let depth = replayed
        .checkpoint()
        .map(|checkpoint| checkpoint.state.depth)
        .unwrap_or(0);
    let moves = replayed.events().len();
    let run_root = replayed.root();

    // The completion is the REPLAY's own derived completion (`replay_record` rebuilds it from the
    // committed custody and refuses a record whose stated completion differs), so reading it here
    // is reading the re-execution, not the submission.
    if let Some(completion) = replayed.completion() {
        return Ok(PitOracleReading {
            terminal: PitRunTerminal::Banked,
            banked: true,
            crowned: completion.crowned,
            banked_relics: completion.banked_relics.len() as u64,
            depth,
            moves,
            run_root,
            settlement_receipt_hash: Some(completion.settlement_receipt_hash),
        });
    }

    // No terminal bank. The run is FINISHED only if it can no longer move — the light died with
    // the pack still in hand. Asking the offering for the affordances of the replayed state is the
    // only honest way to know that without re-deriving the game's own breath arithmetic here.
    let stranded = offering
        .actions(&replayed)
        .iter()
        .all(|affordance| !affordance.enabled);
    if !stranded {
        return Err(PitRefusal::RunNotTerminal);
    }
    Ok(PitOracleReading {
        terminal: PitRunTerminal::Died,
        banked: false,
        crowned: false,
        banked_relics: 0,
        depth,
        moves,
        run_root,
        settlement_receipt_hash: None,
    })
}

/// **The pit's verdict digest** — the 32 bytes frozen into the pit cell's `WriteOnce` `WINNER`
/// register at settlement. It binds the subject, the replayed run's journal root, the terminal
/// receipt hash, the whole reading, and the resolved boolean, so an auditor holding the run record
/// recomputes it independently and compares it against the on-ledger register.
pub fn pit_verdict(subject: &PitSubject, reading: &PitOracleReading, outcome: bool) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(VERDICT_DOMAIN);
    h.update(&subject.digest());
    h.update(&reading.run_root);
    h.update(&reading.settlement_receipt_hash.unwrap_or([0; 32]));
    h.update(&[
        u8::from(reading.banked),
        u8::from(reading.crowned),
        u8::from(outcome),
    ]);
    h.update(&reading.banked_relics.to_be_bytes());
    h.update(&reading.depth.to_be_bytes());
    *h.finalize().as_bytes()
}

// =============================================================================
// Positions, openings, and the cost matrix.
// =============================================================================

/// Which side of the line a position backs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PitSide {
    /// The question resolves TRUE.
    Yes,
    /// The question resolves FALSE.
    No,
}

impl PitSide {
    fn code(self) -> u8 {
        match self {
            PitSide::Yes => 1,
            PitSide::No => 2,
        }
    }

    fn from_code(code: u8) -> Option<Self> {
        match code {
            1 => Some(PitSide::Yes),
            2 => Some(PitSide::No),
            _ => None,
        }
    }

    /// The side the settled outcome pays.
    pub fn winning(outcome: bool) -> Self {
        if outcome { PitSide::Yes } else { PitSide::No }
    }

    /// The human label.
    pub fn label(self) -> &'static str {
        match self {
            PitSide::Yes => "YES",
            PitSide::No => "NO",
        }
    }
}

/// **A position's opening** — the secret `(side, stake, nonce)` whose commitment is frozen on the
/// pit's board, plus the public slot/commitment it landed at. This is the ONLY object that reveals
/// a position, and holding it is what lets its owner claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PositionOpening {
    /// The side backed.
    pub side: PitSide,
    /// The stake in shares.
    pub stake: u64,
    /// The blinding nonce.
    pub nonce: u64,
    /// The `WriteOnce` commit-board slot the commitment froze into.
    pub slot: usize,
    /// The frozen commitment digest.
    pub commitment: [u8; 32],
}

impl PositionOpening {
    /// The canonical claim payload a holder puts in [`Action::text`]: `side:stake:nonce`.
    pub fn encode(&self) -> String {
        format!("{}:{}:{}", self.side.code(), self.stake, self.nonce)
    }

    /// Parse a claim payload. Deliberately strict — a malformed opening is not a near-miss.
    pub fn decode(text: &str) -> Option<(PitSide, u64, u64)> {
        let mut parts = text.trim().split(':');
        let side = PitSide::from_code(parts.next()?.parse::<u8>().ok()?)?;
        let stake = parts.next()?.parse::<u64>().ok()?;
        let nonce = parts.next()?.parse::<u64>().ok()?;
        if parts.next().is_some() {
            return None;
        }
        Some((side, stake, nonce))
    }
}

/// The hiding, binding commitment a position freezes onto the board. The HOLDER is inside the
/// preimage, so a claim recomputed from a different claimant's identity does not match any frozen
/// slot — one person's opening never claims another person's position.
pub fn position_commitment(
    subject: &PitSubject,
    side: PitSide,
    stake: u64,
    nonce: u64,
    holder: &DreggIdentity,
) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(POSITION_DOMAIN);
    h.update(&subject.digest());
    h.update(&[side.code()]);
    h.update(&stake.to_be_bytes());
    h.update(&nonce.to_be_bytes());
    h.update(&(holder.as_str().len() as u64).to_be_bytes());
    h.update(holder.as_str().as_bytes());
    *h.finalize().as_bytes()
}

/// **The pit's public cost matrix** `c(q_yes, q_no) = A·q_yes² + B·q_yes·q_no + C·q_no²`.
///
/// `B` is the cross term. At `B = 0` the quoted line is exactly pari-mutuel
/// (`p_yes / (p_yes + p_no) = q_yes / (q_yes + q_no)`); a positive `B` couples the two sides so the
/// book never quotes a certainty — the implied probability is confined to
/// `[B/(2A+B), 2A/(2A+B)]` at the extremes. That is a market-maker property, deliberately public.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PitCostMatrix {
    /// The `q_yes²` weight. Must be non-zero.
    pub a: u64,
    /// The `q_yes·q_no` cross weight.
    pub b: u64,
    /// The `q_no²` weight. Must be non-zero.
    pub c: u64,
}

impl PitCostMatrix {
    /// The unit quadratic `q_yes² + q_yes·q_no + q_no²` — the form
    /// `metatheory/Market/OraclePitQuadratic` prices.
    pub const fn unit() -> Self {
        PitCostMatrix { a: 1, b: 1, c: 1 }
    }

    /// A cost matrix, refused if it is degenerate or if its worst-case pool would exceed the BFV
    /// plaintext modulus at the pit's declared position bounds (the wrap guard, checked at
    /// construction so the pit cannot open a silently-wrapped pool later).
    pub fn new(a: u64, b: u64, c: u64, positions: usize, t: u64) -> Result<Self, PitRefusal> {
        if a == 0 || c == 0 {
            return Err(PitRefusal::Pricing(
                "a degenerate cost matrix (A or C = 0) quotes no line on that side".to_string(),
            ));
        }
        let matrix = PitCostMatrix { a, b, c };
        let bound = (positions as u128) * (MAX_POSITION_STAKE as u128);
        let worst = (a as u128 + b as u128 + c as u128) * bound * bound;
        if worst >= t as u128 {
            return Err(PitRefusal::Pricing(format!(
                "cost matrix ({a},{b},{c}) over {positions} positions could reach {worst} \
                 >= plaintext modulus {t} — the pit would wrap"
            )));
        }
        Ok(matrix)
    }

    /// The plaintext cost function, for the payout arithmetic and as the oracle every homomorphic
    /// pool opening is checked against in tests.
    pub fn cost(&self, q_yes: u64, q_no: u64) -> u128 {
        (self.a as u128) * (q_yes as u128) * (q_yes as u128)
            + (self.b as u128) * (q_yes as u128) * (q_no as u128)
            + (self.c as u128) * (q_no as u128) * (q_no as u128)
    }
}

// =============================================================================
// The threshold committee.
// =============================================================================

/// **The pit's n-of-n threshold committee.** A real multiparty BFV keygen: every party contributes
/// to a collective public key whose secret exists nowhere, and every opening needs every party's
/// partial decryption. Positions are encrypted to `collective`; prices and the pool are opened only
/// by [`combine`] over all `n` shares.
///
/// The parties run in one process here — each still holds its own independent secret and `combine`
/// still needs all of them, so the threshold property is real; only the transport is co-located.
pub struct PitCommittee {
    params: BfvParams,
    keygen: KeygenSession,
    collective: CollectivePublicKey,
    parties: Vec<ThresholdParty>,
}

impl PitCommittee {
    /// Run the n-of-n collective keygen ceremony for `n` parties.
    pub fn ceremony(n: usize) -> Result<Self, PitRefusal> {
        let params = BfvParams::fold_set();
        let keygen =
            KeygenSession::random(n).map_err(|e| PitRefusal::Committee(format!("{e:?}")))?;
        let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
        let mut parties = Vec::with_capacity(n);
        for index in 0..n {
            let (party, contribution) = ThresholdParty::join(&keygen, index, &params)
                .map_err(|e| PitRefusal::Committee(format!("{e:?}")))?;
            coordinator
                .accept(contribution)
                .map_err(|e| PitRefusal::Committee(format!("{e:?}")))?;
            parties.push(party);
        }
        let collective = coordinator
            .finish()
            .map_err(|e| PitRefusal::Committee(format!("{e:?}")))?;
        Ok(PitCommittee {
            params,
            keygen,
            collective,
            parties,
        })
    }

    /// How many parties must agree to open anything.
    pub fn quorum(&self) -> usize {
        self.parties.len()
    }

    /// The BFV plaintext modulus the wrap guards are checked against.
    pub fn plaintext_modulus(&self) -> u64 {
        self.params.plaintext_modulus()
    }

    fn encrypt(&self, value: u64) -> Result<Ciphertext, PitRefusal> {
        let pt = Plaintext::try_encode(&[value], Encoding::simd(), self.params.arc())
            .map_err(|e| PitRefusal::Committee(format!("encode: {e}")))?;
        let mut rng = rand_09::rng();
        self.collective
            .pk
            .try_encrypt(&pt, &mut rng)
            .map_err(|e| PitRefusal::Committee(format!("collective encrypt: {e}")))
    }

    fn weight(&self, w: u64) -> Result<Plaintext, PitRefusal> {
        Plaintext::try_encode(&[w], Encoding::simd(), self.params.arc())
            .map_err(|e| PitRefusal::Committee(format!("weight encode: {e}")))
    }

    /// Open one ciphertext by a FULL-quorum threshold decrypt. Every party partial-decrypts with
    /// the smudging floor; `combine` refuses anything short of the whole roster.
    fn open(&self, ct: &Ciphertext, plain_bound: u64) -> Result<u64, PitRefusal> {
        let lean = LeanCiphertext::from_fhe_bytes(
            &ct.to_bytes(),
            self.params.moduli(),
            self.params.degree(),
            plain_bound,
        )
        .map_err(|e| PitRefusal::Committee(format!("Lean boundary: {e:?}")))?;
        let mut shares = Vec::with_capacity(self.parties.len());
        for party in &self.parties {
            shares.push(
                party
                    .partial_decrypt(&lean, MIN_SMUDGE_BITS)
                    .map_err(|e| PitRefusal::Committee(format!("partial decrypt: {e:?}")))?,
            );
        }
        let opened = combine(&shares, &self.params)
            .map_err(|e| PitRefusal::Committee(format!("combine: {e:?}")))?;
        opened
            .first()
            .copied()
            .ok_or_else(|| PitRefusal::Committee("combine returned no slots".to_string()))
    }

    /// Run the n-of-n multiparty relinearization ceremony and build the ct×ct multiply engine the
    /// quadratic pool needs. Kept off the position/quote path, which is linear and needs no relin.
    fn mul_engine(&self) -> Result<MulEngine, PitRefusal> {
        let session = RelinKeySession::from_public_entropy(
            &self.keygen,
            &self.collective,
            RELIN_PUBLIC_ENTROPY,
            Duration::from_secs(90),
        )
        .map_err(|e| PitRefusal::Committee(format!("relin session: {e:?}")))?;
        let relin =
            generate_relinearization_key(&session, &self.params, &self.collective, &self.parties)
                .map_err(|e| PitRefusal::Committee(format!("relin ceremony: {e:?}")))?;
        MulEngine::new(&relin, self.params.arc())
            .map_err(|e| PitRefusal::Pricing(format!("mul engine: {e:?}")))
    }
}

// =============================================================================
// The book: on-ledger commitments + encrypted aggregates. House-blind.
// =============================================================================

/// One position as the PIT sees it. There is no side here and no stake — only the frozen
/// commitment and the pair of ciphertexts, exactly one of which encrypts a zero.
struct PitEntry {
    slot: usize,
    commitment: [u8; 32],
    enc_yes: Ciphertext,
    enc_no: Ciphertext,
    claimed: bool,
}

/// A published line: the marginal prices opened by the full committee, and the implied
/// probabilities they normalize to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PitQuote {
    /// `∂c/∂q_yes = 2A·q_yes + B·q_no`, opened by full quorum.
    pub price_yes: u64,
    /// `∂c/∂q_no = B·q_yes + 2C·q_no`, opened by full quorum.
    pub price_no: u64,
    /// The implied probability of YES in basis points (`price_yes / (price_yes + price_no)`).
    pub implied_yes_bps: u32,
    /// The implied probability of NO in basis points.
    pub implied_no_bps: u32,
    /// How many positions were on the board when the line was published.
    pub positions: usize,
}

/// What one settled claim pays and why.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PitPayout {
    /// The board slot claimed.
    pub slot: usize,
    /// The side the claimed position backed.
    pub side: PitSide,
    /// The claimed position's stake.
    pub stake: u64,
    /// The payout in pool units (`0` for a losing position).
    pub amount: u64,
}

/// The pit's settled state: the verdict, its oracle reading, and the pool arithmetic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PitSettlement {
    /// The question's resolved value.
    pub outcome: bool,
    /// The re-execution the outcome was read off.
    pub reading: PitOracleReading,
    /// The cost-function pool, opened by full quorum from the ct×ct quadratic.
    pub pool: u64,
    /// The winning side's aggregate shares, opened by full quorum.
    pub winning_shares: u64,
    /// The losing side's aggregate shares, opened by full quorum.
    pub losing_shares: u64,
    /// `pool / winning_shares`, FLOORED. Integer division leaves dust in the pit, so the claims
    /// always sum to at most [`pool`](Self::pool) and never over it. `0` when nobody backed the
    /// winning side — the whole pool is then unclaimable and stays with the pit.
    pub payout_per_share: u64,
    /// The digest frozen into the pit cell's `WINNER` register.
    pub verdict: [u8; 32],
}

/// **THE PIT'S BOOK** — the house-blind market object: an on-ledger `WriteOnce` commit board of
/// position commitments, the two encrypted side aggregates, the committee, and the published line.
/// It holds no plaintext position and no holder identity.
pub struct OraclePitBook {
    subject: PitSubject,
    matrix: PitCostMatrix,
    committee: PitCommittee,
    cclerk: AppCipherclerk,
    executor: EmbeddedExecutor,
    cell: CellId,
    entries: Vec<PitEntry>,
    open: bool,
    last_quote: Option<PitQuote>,
    settlement: Option<PitSettlement>,
    receipts: Vec<TurnReceipt>,
}

impl OraclePitBook {
    /// Birth the pit cell and freeze the subject onto it.
    fn deploy(
        subject: PitSubject,
        matrix: PitCostMatrix,
        committee: PitCommittee,
        seed: u64,
    ) -> Result<Self, OfferingError> {
        let federation =
            *blake3::hash(format!("dreggnet-market oracle-pit fed seed={seed}").as_bytes())
                .as_bytes();
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), federation);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        executor.deploy_factory(auction_factory_descriptor());
        let owner = cclerk.public_key().0;
        let token = subject.digest();
        let params = FactoryCreationParams {
            mode: CellMode::Sovereign,
            program_vk: Some(auction_child_program_vk()),
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: owner,
        };
        executor.with_ledger_mut(|ledger| {
            if let Some(agent) = ledger.get_mut(&cclerk.cell_id()) {
                agent.state.set_balance(1_000_000_000);
            }
        });
        let birth = cclerk.create_from_factory(AUCTION_FACTORY_VK, owner, token, params);
        let receipt = executor.submit_turn(&birth).map_err(|error| {
            OfferingError::Deploy(format!("the pit cell failed to come alive: {error}"))
        })?;
        let cell = CellId::derive_raw(&owner, &token);
        // Freeze the SUBJECT into the WriteOnce SELLER register: the pit cannot be re-pointed at
        // another run or another question for the rest of its life. PHASE starts at COMMIT (0).
        executor.with_ledger_mut(|ledger| {
            if let Some(agent) = ledger.get_mut(&cclerk.cell_id()) {
                agent.capabilities.grant(cell, AuthRequired::Signature);
            }
            if let Some(pit) = ledger.get_mut(&cell) {
                pit.state.set_field(SELLER_SLOT, subject.digest());
            }
        });
        Ok(OraclePitBook {
            subject,
            matrix,
            committee,
            cclerk,
            executor,
            cell,
            entries: Vec::new(),
            open: true,
            last_quote: None,
            settlement: None,
            receipts: vec![receipt],
        })
    }

    /// What this pit is a market on.
    pub fn subject(&self) -> &PitSubject {
        &self.subject
    }

    /// The public cost matrix.
    pub fn matrix(&self) -> PitCostMatrix {
        self.matrix
    }

    /// The pit cell — the on-ledger handle carrying the frozen subject and the position board.
    pub fn cell(&self) -> CellId {
        self.cell
    }

    /// How many positions are on the board.
    pub fn positions(&self) -> usize {
        self.entries.len()
    }

    /// Whether the board still admits positions.
    pub fn is_open(&self) -> bool {
        self.open
    }

    /// The settled state, once the oracle has been consulted.
    pub fn settlement(&self) -> Option<&PitSettlement> {
        self.settlement.as_ref()
    }

    /// The last published line.
    pub fn last_quote(&self) -> Option<PitQuote> {
        self.last_quote
    }

    /// The committed receipt chain (birth + each position + the freeze + the settlement + claims).
    pub fn receipts(&self) -> &[TurnReceipt] {
        &self.receipts
    }

    /// The on-ledger `PHASE` register — the real freeze state, read off the ledger rather than off
    /// this struct's own bool.
    pub fn onledger_phase(&self) -> Option<u64> {
        let state = self.executor.cell_state(self.cell)?;
        Some(field_to_u64(&state.fields[PHASE_SLOT]))
    }

    /// **Take a private position.** The stake is encrypted to the collective key on the backed side
    /// and a fresh encryption of ZERO goes to the other, so the pit cannot tell which side moved.
    /// The `(side, stake, nonce, holder)` commitment freezes into the next `WriteOnce` board slot
    /// by a real executor turn.
    ///
    /// Returns the opening. The pit does not keep it — the caller must.
    pub fn take_position(
        &mut self,
        side: PitSide,
        stake: u64,
        nonce: u64,
        holder: &DreggIdentity,
    ) -> Result<(PositionOpening, TurnReceipt), PitRefusal> {
        if !self.open {
            return Err(PitRefusal::StillOpen);
        }
        if stake == 0 || stake > MAX_POSITION_STAKE {
            return Err(PitRefusal::Pricing(format!(
                "a position stakes 1..={MAX_POSITION_STAKE} shares"
            )));
        }
        if self.entries.len() >= MAX_PIT_POSITIONS {
            return Err(PitRefusal::Pricing(format!(
                "the pit cell's WriteOnce board holds {MAX_PIT_POSITIONS} positions and is full"
            )));
        }
        let (yes_amount, no_amount) = match side {
            PitSide::Yes => (stake, 0),
            PitSide::No => (0, stake),
        };
        let enc_yes = self.committee.encrypt(yes_amount)?;
        let enc_no = self.committee.encrypt(no_amount)?;
        let commitment = position_commitment(&self.subject, side, stake, nonce, holder);
        let slot = commit_slot(self.entries.len());

        let effects = vec![
            Effect::SetField {
                cell: self.cell,
                index: slot as u64,
                value: commitment,
            },
            Effect::EmitEvent {
                cell: self.cell,
                event: Event::new(symbol("oracle-pit-position"), vec![commitment]),
            },
        ];
        let action = self.cclerk.make_action(self.cell, "commit_bid", effects);
        let receipt = self
            .executor
            .submit_action(&self.cclerk, action)
            .map_err(|error| PitRefusal::Executor(error.to_string()))?;

        self.entries.push(PitEntry {
            slot,
            commitment,
            enc_yes,
            enc_no,
            claimed: false,
        });
        self.receipts.push(receipt.clone());
        Ok((
            PositionOpening {
                side,
                stake,
                nonce,
                slot,
                commitment,
            },
            receipt,
        ))
    }

    /// Try to overwrite an already-frozen board slot with a different commitment. This exists so a
    /// caller can DRIVE the executor's `WriteOnce` refusal rather than assert it: a committed
    /// position cannot be rewritten after the run's outcome starts to look bad.
    pub fn attempt_overwrite(
        &self,
        slot: usize,
        replacement: [u8; 32],
    ) -> Result<TurnReceipt, String> {
        let effects = vec![Effect::SetField {
            cell: self.cell,
            index: slot as u64,
            value: replacement,
        }];
        let action = self.cclerk.make_action(self.cell, "commit_bid", effects);
        self.executor
            .submit_action(&self.cclerk, action)
            .map_err(|error| error.to_string())
    }

    /// The two encrypted side aggregates: homomorphic sums over every position's ciphertext pair.
    /// Each position contributed to BOTH, so nothing about which side moved is visible here.
    fn aggregates(&self) -> Result<(Ciphertext, Ciphertext, u64), PitRefusal> {
        let mut iter = self.entries.iter();
        let first = iter.next().ok_or(PitRefusal::NoPositions)?;
        let mut agg_yes = first.enc_yes.clone();
        let mut agg_no = first.enc_no.clone();
        for entry in iter {
            agg_yes = &agg_yes + &entry.enc_yes;
            agg_no = &agg_no + &entry.enc_no;
        }
        // The public per-side bound the wrap guards use. It is derived from the position COUNT
        // (public) and the declared stake ceiling (public) — never from anyone's actual stake.
        let bound = (self.entries.len() as u64) * MAX_POSITION_STAKE;
        Ok((agg_yes, agg_no, bound))
    }

    /// **Publish the line.** Compute both marginal prices under the collective key (public-scalar
    /// multiplies + homomorphic adds — linear, so no relinearization) and open them by a
    /// full-quorum threshold decrypt. Positions never leave the ciphertext domain.
    ///
    /// This is a READ of the market, not a move: it commits no turn and mints no receipt.
    pub fn quote(&mut self) -> Result<PitQuote, PitRefusal> {
        let (agg_yes, agg_no, bound) = self.aggregates()?;
        let PitCostMatrix { a, b, c } = self.matrix;

        let price_yes_ct = &(&agg_yes * &self.committee.weight(2 * a)?)
            + &(&agg_no * &self.committee.weight(b)?);
        let price_no_ct = &(&agg_yes * &self.committee.weight(b)?)
            + &(&agg_no * &self.committee.weight(2 * c)?);
        let yes_bound = (2 * a + b) * bound;
        let no_bound = (b + 2 * c) * bound;
        let t = self.committee.plaintext_modulus();
        if yes_bound >= t || no_bound >= t {
            return Err(PitRefusal::Pricing(format!(
                "the quoted line's bound would exceed the plaintext modulus {t}"
            )));
        }

        let price_yes = self.committee.open(&price_yes_ct, yes_bound)?;
        let price_no = self.committee.open(&price_no_ct, no_bound)?;
        let total = price_yes as u128 + price_no as u128;
        let (implied_yes_bps, implied_no_bps) = if total == 0 {
            (5_000, 5_000)
        } else {
            let yes = ((price_yes as u128 * 10_000) / total) as u32;
            (yes, 10_000u32.saturating_sub(yes))
        };
        let quote = PitQuote {
            price_yes,
            price_no,
            implied_yes_bps,
            implied_no_bps,
            positions: self.entries.len(),
        };
        self.last_quote = Some(quote);
        Ok(quote)
    }

    /// **Freeze the board.** A real `close_commit` turn advances the pit cell's `PHASE` from
    /// `COMMIT` to `REVEAL` under the executor's `StrictMonotonic(PHASE)` constraint. Positions
    /// must be frozen BEFORE the oracle is consulted, or the market would be settling a question
    /// whose answer is already on the table.
    pub fn freeze(&mut self) -> Result<TurnReceipt, PitRefusal> {
        if !self.open {
            return Err(PitRefusal::StillOpen);
        }
        let action =
            self.cclerk
                .make_action(self.cell, "close_commit", close_commit_effects(self.cell));
        let receipt = self
            .executor
            .submit_action(&self.cclerk, action)
            .map_err(|error| PitRefusal::Executor(error.to_string()))?;
        self.open = false;
        self.receipts.push(receipt.clone());
        Ok(receipt)
    }

    /// **Settle on the verified run.** Re-executes `record` through the Descent offering's exact
    /// replay gate ([`read_verified_run`]), resolves the subject's question against the REPLAYED
    /// terminal state, opens the quadratic pool and the two side aggregates by full quorum, and
    /// freezes the verdict digest into the pit cell's `WriteOnce` `WINNER` register with a real
    /// `resolve` turn.
    ///
    /// Note the argument list: a subject and a record. This method cannot see any holder's opening
    /// even in principle — settlement is house-blind by construction, not by discipline.
    pub fn settle_on_verified_run(
        &mut self,
        record: &NativeDescentRecord,
    ) -> Result<PitSettlement, PitRefusal> {
        if self.settlement.is_some() {
            return Err(PitRefusal::AlreadySettled);
        }
        if self.open {
            return Err(PitRefusal::StillOpen);
        }
        let reading = read_verified_run(&self.subject, record)?;
        let outcome = self.subject.question.resolve(&reading);

        let (agg_yes, agg_no, bound) = self.aggregates()?;
        let PitCostMatrix { a, b, c } = self.matrix;

        // The POOL is the quadratic cost function itself: three ct×ct multiplies under the
        // collective key, which need the n-of-n multiparty relinearization ceremony.
        let engine = self.committee.mul_engine()?;
        let by = BoundedCiphertext::new(agg_yes.clone(), bound);
        let bn = BoundedCiphertext::new(agg_no.clone(), bound);
        let p_yy = engine
            .multiply(&by, &by)
            .map_err(|e| PitRefusal::Pricing(format!("{e:?}")))?;
        let p_yn = engine
            .multiply(&by, &bn)
            .map_err(|e| PitRefusal::Pricing(format!("{e:?}")))?;
        let p_nn = engine
            .multiply(&bn, &bn)
            .map_err(|e| PitRefusal::Pricing(format!("{e:?}")))?;

        let mut pool_ct: Option<Ciphertext> = None;
        let mut pool_bound: u128 = 0;
        for (weight, product) in [(a, &p_yy), (b, &p_yn), (c, &p_nn)] {
            if weight == 0 {
                continue;
            }
            let term = if weight == 1 {
                product.ct.clone()
            } else {
                &product.ct * &self.committee.weight(weight)?
            };
            pool_bound += (weight as u128) * (product.plain_bound as u128);
            pool_ct = Some(match pool_ct {
                None => term,
                Some(acc) => &acc + &term,
            });
        }
        let pool_ct = pool_ct.ok_or_else(|| {
            PitRefusal::Pricing("a wholly-zero cost matrix prices nothing".to_string())
        })?;
        let t = self.committee.plaintext_modulus();
        if pool_bound >= t as u128 {
            return Err(PitRefusal::Pricing(format!(
                "the pool's bound {pool_bound} would wrap the plaintext modulus {t} — refusing \
                 rather than opening a wrong pool"
            )));
        }
        let pool = self.committee.open(&pool_ct, pool_bound as u64)?;

        // The winning side's aggregate is what the pool divides among, so settling opens both.
        // On a pit that published a line this discloses nothing new — the two marginals already
        // determine both aggregates. On a pit that never quoted, this IS the first disclosure of
        // the aggregates; it is still only the totals, never the per-holder decomposition.
        let scaled_yes = &agg_yes * &self.committee.weight(1)?;
        let scaled_no = &agg_no * &self.committee.weight(1)?;
        let q_yes = self.committee.open(&scaled_yes, bound)?;
        let q_no = self.committee.open(&scaled_no, bound)?;
        let (winning_shares, losing_shares) = if outcome {
            (q_yes, q_no)
        } else {
            (q_no, q_yes)
        };
        let payout_per_share = if winning_shares == 0 {
            0
        } else {
            pool / winning_shares
        };

        let verdict = pit_verdict(&self.subject, &reading, outcome);
        let effects = vec![
            Effect::SetField {
                cell: self.cell,
                index: PHASE_SLOT as u64,
                value: field_from_u64(PHASE_RESOLVED),
            },
            Effect::SetField {
                cell: self.cell,
                index: WINNER_SLOT as u64,
                value: verdict,
            },
            Effect::SetField {
                cell: self.cell,
                index: HIGH_BID_SLOT as u64,
                value: field_from_u64(payout_per_share),
            },
            Effect::EmitEvent {
                cell: self.cell,
                event: Event::new(symbol("oracle-pit-settled"), vec![verdict]),
            },
        ];
        let action = self.cclerk.make_action(self.cell, "resolve", effects);
        let receipt = self
            .executor
            .submit_action(&self.cclerk, action)
            .map_err(|error| PitRefusal::Executor(error.to_string()))?;
        self.receipts.push(receipt);

        let settlement = PitSettlement {
            outcome,
            reading,
            pool,
            winning_shares,
            losing_shares,
            payout_per_share,
            verdict,
        };
        self.settlement = Some(settlement.clone());
        Ok(settlement)
    }

    /// **Claim a settled position.** The claimant supplies their own opening; the commitment is
    /// recomputed from `(subject, side, stake, nonce, CLAIMANT)` and must match a commitment that
    /// is FROZEN ON THE LEDGER at its slot. A position that was never taken has no such slot; a
    /// position taken by someone else recomputes to a different digest.
    pub fn claim(
        &mut self,
        side: PitSide,
        stake: u64,
        nonce: u64,
        claimant: &DreggIdentity,
    ) -> Result<(PitPayout, TurnReceipt), PitRefusal> {
        let settlement = self.settlement.clone().ok_or_else(|| {
            PitRefusal::Pricing("this pit has not settled — nothing to claim yet".to_string())
        })?;
        let commitment = position_commitment(&self.subject, side, stake, nonce, claimant);

        let state = self.executor.cell_state(self.cell).ok_or_else(|| {
            PitRefusal::Executor("the pit cell is missing from the ledger".to_string())
        })?;
        // Find the first UNCLAIMED entry carrying this commitment. Matching on commitment alone
        // would strand a second, legitimately-taken position whenever a caller reuses a nonce for
        // the same (side, stake, holder): both stakes are folded into the aggregate and both
        // occupy their own board slot, so both must be claimable exactly once.
        // Scanned rather than collected on purpose: a `Vec` of borrows into `self.entries` has a
        // `Drop` impl, so its borrow would stay live to end of scope and collide with the
        // `claimed` write below.
        let mut unclaimed: Option<usize> = None;
        let mut any_match = false;
        for (index, entry) in self.entries.iter().enumerate() {
            if entry.commitment != commitment {
                continue;
            }
            any_match = true;
            if !entry.claimed {
                unclaimed = Some(index);
                break;
            }
        }
        if !any_match {
            return Err(PitRefusal::Pricing(
                "no such position on the frozen board — an untaken position cannot claim"
                    .to_string(),
            ));
        }
        let index = unclaimed
            .ok_or_else(|| PitRefusal::Pricing("this position was already claimed".to_string()))?;
        let slot = self.entries[index].slot;
        if state.fields[slot] != commitment {
            return Err(PitRefusal::Executor(
                "the on-ledger board no longer carries this position's frozen commitment"
                    .to_string(),
            ));
        }

        let winning = PitSide::winning(settlement.outcome);
        let amount = if side == winning {
            stake.saturating_mul(settlement.payout_per_share)
        } else {
            0
        };
        let effects = vec![Effect::EmitEvent {
            cell: self.cell,
            event: Event::new(
                symbol("oracle-pit-claim"),
                vec![commitment, field_from_u64(amount)],
            ),
        }];
        let action = self.cclerk.make_action(self.cell, "reveal_bid", effects);
        let receipt = self
            .executor
            .submit_action(&self.cclerk, action)
            .map_err(|error| PitRefusal::Executor(error.to_string()))?;
        self.entries[index].claimed = true;
        self.receipts.push(receipt.clone());
        Ok((
            PitPayout {
                slot,
                side,
                stake,
                amount,
            },
            receipt,
        ))
    }

    /// Re-verify the pit against the ledger: the subject is still the one frozen at birth, the
    /// board is exactly the recorded commitments, and (once settled) the on-ledger verdict register
    /// recomputes from the stored oracle reading.
    pub fn reverify(&self) -> VerifyReport {
        let turns = self.receipts.len();
        let Some(state) = self.executor.cell_state(self.cell) else {
            return VerifyReport::broken(turns, "the pit cell is missing from the ledger");
        };
        if state.fields[SELLER_SLOT] != self.subject.digest() {
            return VerifyReport::broken(
                turns,
                "the on-ledger subject register differs from this pit's subject",
            );
        }
        for slot in COMMIT_BASE..COMMIT_BASE + COMMIT_CAPACITY {
            let expected = self
                .entries
                .iter()
                .find(|entry| entry.slot == slot)
                .map(|entry| entry.commitment)
                .unwrap_or([0; 32]);
            if state.fields[slot] != expected {
                return VerifyReport::broken(
                    turns,
                    format!("the on-ledger position board differs at slot {slot}"),
                );
            }
        }
        match &self.settlement {
            None => {
                let phase = if self.open {
                    PHASE_COMMIT
                } else {
                    PHASE_REVEAL
                };
                if state.fields[PHASE_SLOT] != field_from_u64(phase) {
                    return VerifyReport::broken(turns, "the on-ledger phase differs from the pit");
                }
                VerifyReport::ok(turns)
            }
            Some(settlement) => {
                if state.fields[PHASE_SLOT] != field_from_u64(PHASE_RESOLVED) {
                    return VerifyReport::broken(turns, "a settled pit is not on-ledger RESOLVED");
                }
                let recomputed =
                    pit_verdict(&self.subject, &settlement.reading, settlement.outcome);
                if recomputed != settlement.verdict {
                    return VerifyReport::broken(
                        turns,
                        "the settlement verdict does not recompute from its own oracle reading",
                    );
                }
                if state.fields[WINNER_SLOT] != recomputed {
                    return VerifyReport::broken(
                        turns,
                        "the on-ledger verdict register differs from the recomputed verdict",
                    );
                }
                if state.fields[HIGH_BID_SLOT] != field_from_u64(settlement.payout_per_share) {
                    return VerifyReport::broken(
                        turns,
                        "the on-ledger payout register differs from the settled payout",
                    );
                }
                VerifyReport::ok(turns)
            }
        }
    }
}

// =============================================================================
// The hosted-wallet seam.
// =============================================================================

/// **A NAMED SEAM.** A hosted offering must serve each player their own private projection, which
/// means someone on the server side has to remember the openings it handed out. This is that
/// store, and it is the ONLY place plaintext positions exist in this module.
///
/// It is structurally separated from [`OraclePitBook`]: the pricing path
/// ([`OraclePitBook::quote`]), the settlement path
/// ([`OraclePitBook::settle_on_verified_run`]), and the oracle ([`read_verified_run`]) take the
/// book or nothing, so no line and no verdict can be a function of what is stored here. In a real
/// deployment the wallet lives on the player's device and the pit is house-blind outright; a
/// device-held wallet drops in by simply never populating this map.
#[derive(Default)]
pub struct HostedWallets {
    by_holder: BTreeMap<String, Vec<PositionOpening>>,
}

impl HostedWallets {
    /// An empty wallet store.
    pub fn new() -> Self {
        Self::default()
    }

    /// Record an opening for its holder.
    pub fn record(&mut self, holder: &DreggIdentity, opening: PositionOpening) {
        self.by_holder
            .entry(holder.as_str().to_string())
            .or_default()
            .push(opening);
    }

    /// A holder's openings.
    pub fn openings(&self, holder: &DreggIdentity) -> &[PositionOpening] {
        self.by_holder
            .get(holder.as_str())
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// How many holders this store knows.
    pub fn holders(&self) -> usize {
        self.by_holder.len()
    }
}

// =============================================================================
// The Offering.
// =============================================================================

/// A live Oracle Pit session: the house-blind book plus the hosted-wallet seam.
pub struct OraclePitSession {
    /// The pit's book — commitments, ciphertexts, committee, on-ledger cell. House-blind.
    pub book: OraclePitBook,
    /// The hosted-wallet seam (see [`HostedWallets`]).
    pub wallets: HostedWallets,
    next_nonce: u64,
}

impl OraclePitSession {
    /// Take a position and record its opening in the hosted wallet in one step — the shape a
    /// frontend uses, where the server is also acting as the player's wallet.
    pub fn back(
        &mut self,
        side: PitSide,
        stake: u64,
        holder: &DreggIdentity,
    ) -> Result<(PositionOpening, TurnReceipt), PitRefusal> {
        let nonce = self.next_nonce;
        self.next_nonce += 1;
        let (opening, receipt) = self.book.take_position(side, stake, nonce, holder)?;
        self.wallets.record(holder, opening);
        Ok((opening, receipt))
    }

    /// A holder's projected payout at the settled line, from their hosted openings.
    pub fn projected_payout(&self, holder: &DreggIdentity) -> u64 {
        let Some(settlement) = self.book.settlement() else {
            return 0;
        };
        let winning = PitSide::winning(settlement.outcome);
        self.wallets
            .openings(holder)
            .iter()
            .filter(|opening| opening.side == winning)
            .map(|opening| opening.stake.saturating_mul(settlement.payout_per_share))
            .sum()
    }
}

/// **THE ORACLE PIT OFFERING.** Mounted once with a subject, a cost matrix, and a committee size;
/// each [`Offering::open`] births a fresh pit cell and runs a fresh n-of-n keygen ceremony.
///
/// Its [`hidden_information`](Offering::hidden_information) is `true`: the per-viewer projection
/// shows a holder their OWN positions, so a frontend must never paint `render_for` onto a shared
/// Discord/Telegram surface. Use [`dreggnet_offerings::audience::project`], whose `Shared` branch
/// cannot even name a viewer.
pub struct OraclePitOffering {
    subject: PitSubject,
    matrix: PitCostMatrix,
    parties: usize,
}

impl OraclePitOffering {
    /// The offering's stable host/catalog key.
    pub const KEY: &'static str = ORACLE_PIT_OFFERING_KEY;

    /// A pit on `subject` priced by `matrix`, opened under an `parties`-of-`parties` committee.
    /// The cost matrix is checked against the plaintext modulus at the board's full capacity, so a
    /// pit that could ever wrap is refused here rather than opening a wrong pool later.
    pub fn new(
        subject: PitSubject,
        matrix: PitCostMatrix,
        parties: usize,
    ) -> Result<Self, PitRefusal> {
        if parties < 2 {
            return Err(PitRefusal::Committee(
                "a no-single-viewer committee needs at least two parties".to_string(),
            ));
        }
        let t = BfvParams::fold_set().plaintext_modulus();
        PitCostMatrix::new(matrix.a, matrix.b, matrix.c, MAX_PIT_POSITIONS, t)?;
        Ok(OraclePitOffering {
            subject,
            matrix,
            parties,
        })
    }

    /// The subject this offering opens pits on.
    pub fn subject(&self) -> &PitSubject {
        &self.subject
    }
}

impl Offering for OraclePitOffering {
    type Session = OraclePitSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        let seed = cfg.seed.unwrap_or(1);
        let committee = PitCommittee::ceremony(self.parties)
            .map_err(|error| OfferingError::Deploy(error.to_string()))?;
        let book = OraclePitBook::deploy(self.subject.clone(), self.matrix, committee, seed)?;
        Ok(OraclePitSession {
            book,
            wallets: HostedWallets::new(),
            next_nonce: 1,
        })
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        let open = session.book.is_open();
        let settled = session.book.settlement().is_some();
        vec![
            Action::new("Back YES (private position)", TURN_BACK_YES, 1, open),
            Action::new("Back NO (private position)", TURN_BACK_NO, 1, open),
            Action::new("Claim a settled position", TURN_CLAIM, 0, settled).taking_text(),
        ]
    }

    fn actions_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Vec<Action> {
        let settled = session.book.settlement().is_some();
        let holds = !session.wallets.openings(viewer).is_empty();
        let mut actions = self.actions(session);
        // The claim affordance is a per-viewer capability: only a holder can open a position.
        if let Some(claim) = actions.iter_mut().find(|action| action.turn == TURN_CLAIM) {
            claim.enabled = settled && holds;
        }
        actions
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        match input.turn.as_str() {
            TURN_BACK_YES | TURN_BACK_NO => {
                if input.arg <= 0 {
                    return Outcome::Refused("a position stakes at least one share".to_string());
                }
                let side = if input.turn == TURN_BACK_YES {
                    PitSide::Yes
                } else {
                    PitSide::No
                };
                match session.back(side, input.arg as u64, &actor) {
                    Ok((_, receipt)) => Outcome::Landed {
                        receipt,
                        ended: false,
                    },
                    Err(refusal) => Outcome::Refused(refusal.to_string()),
                }
            }
            TURN_CLAIM => {
                let Some(text) = input.text.as_deref() else {
                    return Outcome::Refused(
                        "a claim carries its opening (side:stake:nonce) in the affordance text"
                            .to_string(),
                    );
                };
                let Some((side, stake, nonce)) = PositionOpening::decode(text) else {
                    return Outcome::Refused(
                        "malformed position opening — expected side:stake:nonce".to_string(),
                    );
                };
                match session.book.claim(side, stake, nonce, &actor) {
                    Ok((_, receipt)) => Outcome::Landed {
                        receipt,
                        ended: false,
                    },
                    Err(refusal) => Outcome::Refused(refusal.to_string()),
                }
            }
            other => Outcome::Refused(format!("unknown Oracle Pit affordance: {other}")),
        }
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        session.book.reverify()
    }

    /// The SHARED surface: the line, the pool, the verdict. No side, no stake, no holder.
    fn render(&self, session: &Self::Session) -> Surface {
        let book = &session.book;
        let mut children = vec![
            ViewNode::Text(book.subject.question.headline()),
            ViewNode::Text(format!(
                "subject: run seed {} on day-seed {}",
                book.subject.seed,
                hex16(book.subject.day_seed.as_bytes())
            )),
            ViewNode::Text(format!(
                "cost matrix: {}·q_yes² + {}·q_yes·q_no + {}·q_no²",
                book.matrix.a, book.matrix.b, book.matrix.c
            )),
            ViewNode::Text(format!(
                "{} private position{} on the frozen board · {}-of-{} committee",
                book.positions(),
                if book.positions() == 1 { "" } else { "s" },
                book.committee.quorum(),
                book.committee.quorum()
            )),
        ];
        match book.last_quote() {
            Some(quote) => children.push(ViewNode::Text(format!(
                "THE LINE — YES {}.{:02}% / NO {}.{:02}% (marginal prices {} / {}, opened by full quorum)",
                quote.implied_yes_bps / 100,
                quote.implied_yes_bps % 100,
                quote.implied_no_bps / 100,
                quote.implied_no_bps % 100,
                quote.price_yes,
                quote.price_no,
            ))),
            None => children.push(ViewNode::Text(
                "no line published yet — the committee has not opened the marginals".to_string(),
            )),
        }
        match book.settlement() {
            Some(settlement) => {
                children.push(ViewNode::Text(format!(
                    "SETTLED {} — the run {} at floor {} with {} relic{} banked ({} moves)",
                    if settlement.outcome { "YES" } else { "NO" },
                    match settlement.reading.terminal {
                        PitRunTerminal::Banked =>
                            if settlement.reading.crowned {
                                "was CROWNED"
                            } else {
                                "banked"
                            },
                        PitRunTerminal::Died => "died in the dark",
                    },
                    settlement.reading.depth,
                    settlement.reading.banked_relics,
                    if settlement.reading.banked_relics == 1 {
                        ""
                    } else {
                        "s"
                    },
                    settlement.reading.moves,
                )));
                children.push(ViewNode::Text(format!(
                    "pool {} · {} winning shares · {} per share · verdict {}",
                    settlement.pool,
                    settlement.winning_shares,
                    settlement.payout_per_share,
                    hex16(&settlement.verdict),
                )));
                children.push(ViewNode::Text(format!(
                    "the verdict is checkable: re-execute the run record on day-seed {} and \
                     recompute pit_verdict against journal root {}",
                    hex16(book.subject.day_seed.as_bytes()),
                    hex16(&settlement.reading.run_root),
                )));
            }
            None if book.is_open() => children.push(ViewNode::Text(
                "the board is OPEN — positions are being taken".to_string(),
            )),
            None => children.push(ViewNode::Text(
                "the board is FROZEN — waiting on the run's verified record".to_string(),
            )),
        }
        Surface(ViewNode::Section {
            title: "The Oracle Pit".to_string(),
            tag: "accent".to_string(),
            children,
        })
    }

    /// The PRIVATE per-viewer projection: everything the shared surface shows, plus this viewer's
    /// OWN positions. Never paint this on a shared surface — see
    /// [`hidden_information`](Offering::hidden_information).
    fn render_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Surface {
        let public = self.render(session);
        let openings = session.wallets.openings(viewer);
        let mut rows: Vec<ViewNode> = Vec::new();
        if openings.is_empty() {
            rows.push(ViewNode::Text(
                "you hold no position in this pit".to_string(),
            ));
        } else {
            for opening in openings {
                rows.push(ViewNode::Text(format!(
                    "YOUR POSITION: {} · {} share{} · slot {} · commitment {}",
                    opening.side.label(),
                    opening.stake,
                    if opening.stake == 1 { "" } else { "s" },
                    opening.slot,
                    hex16(&opening.commitment),
                )));
                rows.push(ViewNode::Menu {
                    items: vec![MenuItem {
                        label: format!("Claim this position (opening {})", opening.encode()),
                        turn: TURN_CLAIM.to_string(),
                        arg: opening.slot as i64,
                        enabled: session.book.settlement().is_some(),
                    }],
                });
            }
            if session.book.settlement().is_some() {
                rows.push(ViewNode::Text(format!(
                    "your projected payout: {}",
                    session.projected_payout(viewer)
                )));
            }
        }
        Surface(ViewNode::Section {
            title: "The Oracle Pit — your book".to_string(),
            tag: "accent".to_string(),
            children: std::iter::once(public.0).chain(rows).collect(),
        })
    }

    /// `true` — [`render_for`](Offering::render_for) reveals the viewer's own side and stake, which
    /// is exactly what the market hides from everyone else.
    fn hidden_information(&self) -> bool {
        true
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

fn hex16(bytes: &[u8; 32]) -> String {
    bytes[..8].iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn subject(question: DescentQuestion) -> PitSubject {
        PitSubject::new(7, CommittedSeed::from_bytes([0x5a; 32]), question)
    }

    /// The subject digest binds every component: a different seed, day, or question is a different
    /// pit identity (and therefore a different frozen on-ledger register).
    #[test]
    fn subject_digest_separates_run_day_and_question() {
        let base = subject(DescentQuestion::Crowned);
        let other_question = subject(DescentQuestion::Banked);
        let other_day = PitSubject::new(
            7,
            CommittedSeed::from_bytes([0x5b; 32]),
            DescentQuestion::Crowned,
        );
        let other_seed = PitSubject::new(
            8,
            CommittedSeed::from_bytes([0x5a; 32]),
            DescentQuestion::Crowned,
        );
        assert_ne!(base.digest(), other_question.digest());
        assert_ne!(base.digest(), other_day.digest());
        assert_ne!(base.digest(), other_seed.digest());
        assert_ne!(
            DescentQuestion::DepthAtLeast(3),
            DescentQuestion::DepthAtLeast(4)
        );
    }

    /// A position commitment binds the HOLDER, so recomputing it as a different claimant yields a
    /// different digest — one player's opening cannot claim another player's frozen slot.
    #[test]
    fn position_commitment_binds_the_holder_and_the_opening() {
        let s = subject(DescentQuestion::Crowned);
        let alice = DreggIdentity("alice".to_string());
        let bob = DreggIdentity("bob".to_string());
        let mine = position_commitment(&s, PitSide::Yes, 4, 1, &alice);
        assert_ne!(mine, position_commitment(&s, PitSide::Yes, 4, 1, &bob));
        assert_ne!(mine, position_commitment(&s, PitSide::No, 4, 1, &alice));
        assert_ne!(mine, position_commitment(&s, PitSide::Yes, 5, 1, &alice));
        assert_ne!(mine, position_commitment(&s, PitSide::Yes, 4, 2, &alice));
    }

    /// The opening round-trips through its claim wire, and a malformed one is refused outright.
    #[test]
    fn opening_wire_round_trips_and_refuses_garbage() {
        let opening = PositionOpening {
            side: PitSide::No,
            stake: 12,
            nonce: 9,
            slot: 5,
            commitment: [0; 32],
        };
        assert_eq!(
            PositionOpening::decode(&opening.encode()),
            Some((PitSide::No, 12, 9))
        );
        assert_eq!(PositionOpening::decode("1:2"), None);
        assert_eq!(PositionOpening::decode("1:2:3:4"), None);
        assert_eq!(PositionOpening::decode("9:2:3"), None);
        assert_eq!(PositionOpening::decode(""), None);
    }

    /// The wrap guard is a construction-time refusal, not a runtime surprise: a cost matrix whose
    /// worst-case pool could reach the plaintext modulus never becomes an offering.
    #[test]
    fn a_wrapping_cost_matrix_is_refused_at_construction() {
        let t = BfvParams::fold_set().plaintext_modulus();
        assert!(PitCostMatrix::new(1, 1, 1, MAX_PIT_POSITIONS, t).is_ok());
        assert!(matches!(
            PitCostMatrix::new(1_000, 1_000, 1_000, MAX_PIT_POSITIONS, t),
            Err(PitRefusal::Pricing(_))
        ));
        assert!(matches!(
            PitCostMatrix::new(0, 1, 1, MAX_PIT_POSITIONS, t),
            Err(PitRefusal::Pricing(_))
        ));
        assert!(matches!(
            OraclePitOffering::new(subject(DescentQuestion::Crowned), PitCostMatrix::unit(), 1),
            Err(PitRefusal::Committee(_))
        ));
    }

    /// The question resolver is pure and reads only the replay-derived reading.
    #[test]
    fn questions_resolve_off_the_reading() {
        let banked = PitOracleReading {
            terminal: PitRunTerminal::Banked,
            banked: true,
            crowned: true,
            banked_relics: 4,
            depth: 4,
            moves: 18,
            run_root: [1; 32],
            settlement_receipt_hash: Some([2; 32]),
        };
        let died = PitOracleReading {
            terminal: PitRunTerminal::Died,
            banked: false,
            crowned: false,
            banked_relics: 0,
            depth: 2,
            moves: 9,
            run_root: [3; 32],
            settlement_receipt_hash: None,
        };
        assert!(DescentQuestion::Crowned.resolve(&banked));
        assert!(!DescentQuestion::Crowned.resolve(&died));
        assert!(DescentQuestion::Banked.resolve(&banked));
        assert!(!DescentQuestion::Banked.resolve(&died));
        assert!(DescentQuestion::DepthAtLeast(4).resolve(&banked));
        assert!(!DescentQuestion::DepthAtLeast(4).resolve(&died));
        assert!(DescentQuestion::DepthAtLeast(2).resolve(&died));
        assert!(DescentQuestion::RelicsBankedAtLeast(4).resolve(&banked));
        assert!(!DescentQuestion::RelicsBankedAtLeast(1).resolve(&died));
    }

    /// The verdict digest is a function of the WHOLE reading: a different run root, a different
    /// terminal receipt, or a flipped outcome is a different frozen register.
    #[test]
    fn the_verdict_digest_binds_the_replayed_run() {
        let s = subject(DescentQuestion::Crowned);
        let reading = PitOracleReading {
            terminal: PitRunTerminal::Banked,
            banked: true,
            crowned: true,
            banked_relics: 4,
            depth: 4,
            moves: 18,
            run_root: [1; 32],
            settlement_receipt_hash: Some([2; 32]),
        };
        let base = pit_verdict(&s, &reading, true);
        assert_ne!(base, pit_verdict(&s, &reading, false));
        let mut other_root = reading.clone();
        other_root.run_root = [9; 32];
        assert_ne!(base, pit_verdict(&s, &other_root, true));
        let mut other_receipt = reading.clone();
        other_receipt.settlement_receipt_hash = Some([9; 32]);
        assert_ne!(base, pit_verdict(&s, &other_receipt, true));
        assert_ne!(
            base,
            pit_verdict(&subject(DescentQuestion::Banked), &reading, true)
        );
    }
}
