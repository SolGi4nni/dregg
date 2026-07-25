//! THE DARK POOL a player can actually stand in front of and swap on.
//!
//! [`dark_amm_game`](crate::dark_amm_game) and [`dark_amm_collective`](crate::dark_amm_collective)
//! already carry an encrypted constant-product table, but neither is *playable*: both return an
//! empty [`Offering::actions`] set and refuse every [`Offering::advance`], so the only way in is to
//! hand-build a multi-megabyte BFV ciphertext bundle out of band and upload it through
//! `invoke_binary_operation`. There is no button, no seat, no purse, no per-player projection.
//!
//! This module is the player-facing one. The pool is a **blind relic vendor**:
//!
//! * its two reserves — `x` = $DREGG held, `y` = relic notes held — live ONLY as BFV ciphertexts
//!   under an **n-of-n collective key** produced by the frozen
//!   [`fhegg_fhe::threshold`] ceremony, so no single custodian (and no `n-1` coalition) holds the
//!   decryption key;
//! * a swap's fairness is decided by ONE wrap-guarded homomorphic `ct×ct` multiply of the
//!   *candidate* post-swap reserves, whose product is opened by a **full-quorum threshold
//!   decrypt** and compared to the public invariant `k`. That opened bit is the ONLY fairness
//!   authority in the path — nothing in this module compares plaintext reserves to decide whether
//!   a swap is fair;
//! * the value actually moves: the relic is a real [`dreggnet_asset`] note crossed through
//!   [`dreggnet_trade`]'s owner-gated sealed escrow against a real `$DREGG` purse, and each
//!   accepted swap commits a real executor turn on the pool's journal cell (a
//!   `StrictMonotonic` sequence, so a replayed swap is a real refusal) — that turn's
//!   [`TurnReceipt`] is the [`Outcome::Landed`] receipt.
//!
//! # What is hidden, precisely — read this before believing the word "dark"
//!
//! HIDDEN from the host process, from every frontend, and from the shared surface:
//! the reserve pair `(x, y)` and every quoted price, because the house
//! ([`DarkPool`] with [`DarkPool::strip_lp_view`] applied) holds ciphertexts + the public
//! relinearization key + the public `k`, and the secret key exists only as `n` shares.
//!
//! DISCLOSED, not hidden:
//! * **`k = x·y` is public by construction.** It is the invariant the opened product is compared
//!   against. Publishing `k` publishes the *product* of the reserves, never the split.
//! * **A filled taker can solve for the reserves.** From `x·y = k` and
//!   `(x+dx)(y-dy) = k` with their own `(dx, dy)` in hand, the two equations determine `(x, y)`
//!   exactly. So this construction hides the book from OBSERVERS and from the HOST, not from a
//!   counterparty who actually fills. That is why [`hidden_information`](Offering::hidden_information)
//!   is `true` and the fill price is painted only by
//!   [`render_for`](Offering::render_for): putting one price on a shared Discord/Telegram card
//!   hands every reader the reserves.
//! * **The LP quoting role sees plaintext.** [`Quoter`] holds the plaintext reserves and is the
//!   only thing that can name an exact price. It is a *separate role from the house* (the house
//!   cannot quote and cannot decrypt), but in this build both live in one process. A deployment
//!   that wants the quote hidden from the host has to move [`Quoter`] to the LP and let takers
//!   propose their own `(dx, dy)` — which this module already supports through
//!   [`TURN_PROPOSE`], where no quoter is consulted at all.
//! * **The custody ledger re-reveals the aggregate.** [`dreggnet_trade`]'s `$DREGG` purses and
//!   note lineages are plaintext. Anyone reading the settlement layer can add up what the pool
//!   holds. The FHE hides the book at DECISION time (no host front-running, no depth leak on the
//!   public card); it does not shield the custody balances, and nothing in this repository does.
//! * **Amount bounds are declarations, not range proofs**, and the `mod t` forgery residual named
//!   in [`fhegg_fhe::dark_amm`] applies here unchanged.
//! * **`quote_exact` is exact-only.** This construction admits a swap only when the post-swap
//!   product is EXACTLY `k` — there is no fee and no rounding slack, because BFV gives cheap
//!   equality and not cheap comparison. Sizes with no exact quote are refused, which is a real
//!   limitation of the invariant, not a policy.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::{Arc, Mutex, MutexGuard};

use deos_view::ViewNode;
use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellProgram, Effect, EmbeddedExecutor,
    StateConstraint, TransitionCase, TransitionGuard, TurnReceipt, field_from_u64, symbol,
};
use dregg_cell::Cell;
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};
use dreggnet_trade::{AssetId, TradeError, TradeWorld};
use fhegg_fhe::bfv_mul::BoundedCiphertext;
use fhegg_fhe::dark_amm::{AppliedSwap, DarkAmmError, DarkPool};
use rand_09::SeedableRng;
use rand_09::rngs::StdRng;

use crate::threshold_committee::{
    CommitteeCeremony, CommitteeError, PartySeeding, RelinSchedule, ThresholdCommittee,
};

/// Stable catalog key. Deliberately NOT `dark-pool`: that key belongs to
/// [`crate::dark_amm_game::DARK_AMM_OFFERING_KEY`], the upload-only table, and admitting one
/// never implies the other was mounted.
pub const DARK_POOL_VENDOR_KEY: &str = "dark-pool-vendor";

/// Take a seat: derive the actor's purse and credit the devnet faucet once.
pub const TURN_JOIN: &str = "pool/join";
/// Swap at the pool's own exact quote. `arg` = relics out (this vendor crosses one per swap).
pub const TURN_SWAP: &str = "pool/swap";
/// Propose your OWN price. `arg` = the `$DREGG` you offer for one relic. No quoter is consulted:
/// the homomorphic invariant alone accepts or refuses it.
pub const TURN_PROPOSE: &str = "pool/propose";

/// The method the journal turn presents. Every other method default-denies.
pub const POOL_SWAP_METHOD: &str = "dark-pool/swap";

const JOURNAL_FEDERATION: [u8; 32] = [0xD4; 32];
const SEQUENCE_SLOT: u8 = 0;
const DIGEST_SLOT: u8 = 1;

/// The devnet faucet credit a fresh seat receives, in `$DREGG`. A faucet, said out loud: it is a
/// credit from nowhere so a player can be stood up in a test/devnet. It is not a claim that the
/// player earned this value.
pub const SEAT_FAUCET_DREGG: u64 = 100_000;

/// The pool's `$DREGG` label in [`TradeWorld`].
const POOL_LABEL: &str = "dark-pool-vendor/house";

/// The exact security account every frontend paints beside this table.
pub const DARK_POOL_DISCLOSURE: &str = "Blind relic vendor: the pool's reserves (DREGG held, relics held) exist only as BFV ciphertexts under an n-of-n collective key, and a swap is admitted only when one homomorphic ct-by-ct product of the candidate post-swap reserves opens — under a FULL threshold quorum — to the public invariant k. No single custodian and no n-1 coalition holds the decryption key. Disclosed and NOT hidden: k is public by construction (it is the product of the reserves, never the split); a taker who fills can solve x and y from their own fill and k, so a fill price is a per-viewer release and never belongs on a shared surface; the liquidity-provider quoting role holds plaintext reserves in this build (takers can bypass it entirely with a self-priced proposal, which no quoter sees); the DREGG purses and note lineages in the settlement layer are plaintext, so aggregate custody is readable even though the decision-time book is not; amount bounds are caller declarations, not range proofs.";

/// Why the pool refused, or could not be stood up.
#[derive(Debug, Clone)]
pub enum DarkPoolError {
    /// The n-of-n key ceremony failed.
    Ceremony(String),
    /// The encrypted pool could not be initialised at these reserves/caps.
    Pool(String),
    /// A threshold decrypt could not be assembled or combined.
    Opening(String),
    /// The homomorphic invariant opened to something other than the public `k`: the proposal
    /// would have moved value out of the pool. Carries NO opened number — a refused proposal's
    /// raw product stays inside the host process.
    UnfairSwap,
    /// This size has no EXACT quote at the current reserves (the invariant admits only a post-swap
    /// product of exactly `k`).
    NoExactQuote { relics: u64 },
    /// The vendor has no relic left to cross (or the requested count would empty it, which the
    /// invariant prices at infinity).
    VaultEmpty,
    /// The owner gate / purse / sealed escrow refused the value cross.
    Trade(String),
    /// The journal turn was refused by the real executor (a replayed or out-of-order sequence).
    Journal(String),
    /// The actor has not taken a seat.
    NoSeat,
    /// The actor already holds a seat at this pool.
    AlreadySeated,
    /// The pool is quarantined after a partially-applied swap.
    Quarantined(String),
}

impl std::fmt::Display for DarkPoolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ceremony(why) => write!(f, "the n-of-n key ceremony failed: {why}"),
            Self::Pool(why) => write!(f, "the encrypted pool refused its genesis: {why}"),
            Self::Opening(why) => write!(f, "the threshold opening failed: {why}"),
            Self::UnfairSwap => write!(
                f,
                "the homomorphic constant-product check refused this swap: the candidate reserves \
                 do not open to the public invariant"
            ),
            Self::NoExactQuote { relics } => write!(
                f,
                "no exact quote exists for {relics} relic(s) at the current reserves"
            ),
            Self::VaultEmpty => write!(f, "the vendor has no relic to cross"),
            Self::Trade(why) => write!(f, "the owned-asset cross was refused: {why}"),
            Self::Journal(why) => write!(f, "the pool journal turn was refused: {why}"),
            Self::NoSeat => write!(f, "take a seat at the pool before swapping"),
            Self::AlreadySeated => write!(f, "you already hold a seat at this pool"),
            Self::Quarantined(why) => write!(f, "the pool is quarantined: {why}"),
        }
    }
}

impl std::error::Error for DarkPoolError {}

impl From<TradeError> for DarkPoolError {
    fn from(value: TradeError) -> Self {
        Self::Trade(value.to_string())
    }
}

impl From<CommitteeError> for DarkPoolError {
    fn from(value: CommitteeError) -> Self {
        match value {
            CommitteeError::Opening(why) => DarkPoolError::Opening(why),
            other => DarkPoolError::Ceremony(other.to_string()),
        }
    }
}

// ---------------------------------------------------------------------------
// n-of-n custody
// ---------------------------------------------------------------------------

/// The `n` parties that jointly hold the pool's BFV secret key.
///
/// This is [`ThresholdCommittee`] — the one committee object this crate has, shared with
/// [`crate::oracle_pit`]. The alias is kept because "custody" is the word the pool's own
/// vocabulary uses for it, not because the pool has a committee of its own.
///
/// The only secret-dependent object that leaves a party is a `DecryptShare`, and
/// [`ThresholdCommittee::combine_shares`] reconstructs a plaintext only from a complete,
/// distinct, ciphertext-matching, adequately-smudged share set. `shares` and `combine_shares`
/// are public because they are exactly what a distributed deployment ships over the wire — and
/// because an adversarial test needs to be able to try a short or forged coalition against the
/// real combiner. Read `combine_shares`'s doc for which of its refusals is structural and which
/// is cryptographic; they are not the same claim.
pub type DarkPoolCustody = ThresholdCommittee;

/// blake3 derive-key domain for the pool's public CRP seed.
const CRP_DOMAIN: &str = "dregg-dark-pool-crp-v1";
/// blake3 derive-key domain for each custodian's per-party root.
const PARTY_DOMAIN: &str = "dregg-dark-pool-party-custody-v1";

/// Run the pool's n-of-n ceremony from one 32-byte custody root.
///
/// Determinism is from `root` alone, so a pool is reproducible for audit. **Said plainly, because
/// it is the pool's real custody posture:** deriving all `n` party roots from one value inside
/// one process is a shared dealer. Whoever holds `root` holds every share and can decrypt the
/// book unilaterally — the n-of-n property of a pool stood up this way is worth exactly the
/// secrecy of `root`. A deployment MUST replace this with per-party roots kept outside the
/// coordinator process (see `ThresholdParty::join_seeded`'s custody note). Standing this up in
/// one process is a SIMULATED ceremony: the parties are real and independently keyed, but nothing
/// here proves they ran on separate machines.
///
/// The relinearization key is generated eagerly: the house needs a multiply-capable key to
/// encrypt its genesis reserves, and the cost belongs to pool genesis either way.
fn pool_ceremony(n_parties: usize, root: [u8; 32]) -> Result<DarkPoolCustody, DarkPoolError> {
    Ok(CommitteeCeremony {
        n_parties,
        seeding: PartySeeding::FromRoot {
            root,
            crp_domain: CRP_DOMAIN,
            party_domain: PARTY_DOMAIN,
        },
        relin_entropy: blake3::derive_key("dregg-dark-pool-relin-entropy-v1", &root),
        relin_timeout: std::time::Duration::from_secs(300),
        relin_schedule: RelinSchedule::AtGenesis,
    }
    .run()?)
}

// ---------------------------------------------------------------------------
// the LP quoting role (plaintext) — deliberately NOT the house
// ---------------------------------------------------------------------------

/// The liquidity provider's plaintext tracking view: the only object in this module that can name
/// an exact price. It is NOT consulted on the [`TURN_PROPOSE`] path, and the house never reads it.
#[derive(Debug, Clone, Copy)]
struct Quoter {
    x: u64,
    y: u64,
    k: u64,
}

impl Quoter {
    fn new(x: u64, y: u64) -> Self {
        Quoter { x, y, k: x * y }
    }

    /// The EXACT `$DREGG` price of `relics` out: `dx = x·dy / (y − dy)`, defined only when it is a
    /// whole number, because the invariant admits a post-swap product of exactly `k` and nothing
    /// else. `None` at `dy >= y` — draining the pool is priced at infinity.
    fn exact_price(&self, relics: u64) -> Option<u64> {
        if relics == 0 || relics >= self.y {
            return None;
        }
        let denominator = (self.y - relics) as u128;
        let numerator = (self.x as u128) * (relics as u128);
        if numerator % denominator != 0 {
            return None;
        }
        u64::try_from(numerator / denominator).ok()
    }

    fn apply(&mut self, price: u64, relics: u64) {
        self.x += price;
        self.y -= relics;
    }
}

// ---------------------------------------------------------------------------
// the journal cell — where the real committed turn lives
// ---------------------------------------------------------------------------

/// One sovereign ledger holding the pool's journal cell. Each accepted swap is a real
/// owner-signed turn whose only tooth is `StrictMonotonic(sequence)`, so a replayed or
/// out-of-order swap is a genuine executor refusal rather than app bookkeeping.
struct Journal {
    cclerk: AppCipherclerk,
    exec: EmbeddedExecutor,
    cell: CellId,
    sequence: u64,
}

fn journal_program() -> CellProgram {
    CellProgram::Cases(vec![TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(POOL_SWAP_METHOD),
        },
        constraints: vec![StateConstraint::StrictMonotonic {
            index: SEQUENCE_SLOT,
        }],
    }])
}

impl Journal {
    fn new(seed: u64) -> Self {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), JOURNAL_FEDERATION);
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        let owner = cclerk.public_key().0;
        let token =
            *blake3::hash(format!("dark-pool-vendor journal seed={seed}").as_bytes()).as_bytes();
        let cell = CellId::derive_raw(&owner, &token);
        let agent = cclerk.cell_id();
        exec.with_ledger_mut(|ledger| {
            if ledger.get(&cell).is_none() {
                let _ = ledger.insert_cell(Cell::new(owner, token));
            }
            if let Some(agent_cell) = ledger.get_mut(&agent) {
                agent_cell.capabilities.grant(cell, AuthRequired::Signature);
            }
        });
        exec.install_program(cell, journal_program());
        Journal {
            cclerk,
            exec,
            cell,
            sequence: 0,
        }
    }

    /// Commit ONE real turn recording the swap. `sequence` must strictly increase or the executor
    /// refuses it.
    fn record(&mut self, sequence: u64, digest: [u8; 32]) -> Result<TurnReceipt, DarkPoolError> {
        let effects = vec![
            Effect::SetField {
                cell: self.cell,
                index: SEQUENCE_SLOT as u64,
                value: field_from_u64(sequence),
            },
            Effect::SetField {
                cell: self.cell,
                index: DIGEST_SLOT as u64,
                value: digest,
            },
        ];
        let action = self
            .cclerk
            .make_action(self.cell, POOL_SWAP_METHOD, effects);
        let receipt = self
            .exec
            .submit_action(&self.cclerk, action)
            .map_err(|e| DarkPoolError::Journal(e.to_string()))?;
        self.sequence = sequence;
        Ok(receipt)
    }
}

// ---------------------------------------------------------------------------
// receipts and cards
// ---------------------------------------------------------------------------

/// ONE player's fill. Its `price` is a **per-viewer release**: publishing it beside the public `k`
/// hands the reader both reserves. It never appears in [`Offering::render`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PoolFill {
    /// The pool-wide swap sequence this fill landed at.
    pub sequence: u64,
    /// Relic notes received.
    pub relics: u64,
    /// `$DREGG` paid. PRIVATE — see the type doc.
    pub price: u64,
    /// The relic note that crossed (its lineage is extended, never restarted).
    pub asset: AssetId,
    /// The committed journal turn.
    pub turn_hash: [u8; 32],
    /// Whether the taker named their own price ([`TURN_PROPOSE`]) instead of taking the quote.
    pub self_priced: bool,
}

/// The viewer-blind public record of one accepted swap. Deliberately carries NO amount: not the
/// price, not the reserves, not the relic count.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PublicSwapCard {
    /// The pool-wide swap sequence.
    pub sequence: u64,
    /// A short, stable fingerprint of the taker — not their identity string.
    pub taker_fingerprint: String,
    /// The committed journal turn.
    pub turn_hash: [u8; 32],
    /// How many full-quorum threshold openings this swap consumed (one: the invariant).
    pub quorum_openings: u64,
}

// ---------------------------------------------------------------------------
// the pool core
// ---------------------------------------------------------------------------

struct PoolCore {
    custody: DarkPoolCustody,
    /// The BLIND house: ciphertexts, public relin key, public `k`. `strip_lp_view` has been
    /// applied, so it holds no plaintext reserve and it cannot quote.
    house: DarkPool,
    /// The LP role. Separate from the house on purpose.
    quoter: Quoter,
    world: TradeWorld,
    vault: VecDeque<AssetId>,
    journal: Journal,
    seated: BTreeSet<String>,
    fills: BTreeMap<String, Vec<PoolFill>>,
    public: Vec<PublicSwapCard>,
    seat_turns: u64,
    quorum_openings: u64,
    refusals: u64,
    quarantine: Option<String>,
}

/// Genesis reserves. `2520 = lcm(1..10)`, so the whole one-relic-at-a-time ladder down to the last
/// relic has an exact integer quote at every step — the invariant admits nothing else.
const GENESIS_DREGG: u64 = 2_520;
const GENESIS_RELICS: u64 = 11;
const GENESIS_CAP_DREGG: u64 = 4_096;
const GENESIS_CAP_RELICS: u64 = 16;

impl PoolCore {
    fn stand_up(root: [u8; 32], seed: u64, n_custodians: usize) -> Result<Self, DarkPoolError> {
        let custody = pool_ceremony(n_custodians, root)?;

        // The reserves are encrypted to the COLLECTIVE key here and never decrypted again except
        // by a full quorum.
        let mut rng = StdRng::from_seed(root);
        let mut house = DarkPool::init(
            custody.params().arc(),
            &custody.collective().pk,
            custody.relin_key()?,
            GENESIS_DREGG,
            GENESIS_RELICS,
            GENESIS_CAP_DREGG,
            GENESIS_CAP_RELICS,
            &mut rng,
        )
        .map_err(|e: DarkAmmError| DarkPoolError::Pool(e.to_string()))?;
        // The house is blind from here on: it can verify a candidate, never quote, never read a
        // reserve.
        house.strip_lp_view();

        let mut world = TradeWorld::new();
        let mut vault = VecDeque::new();
        for index in 0..GENESIS_RELICS {
            let mint_seed = format!("dark-pool-vendor/relic/{seed}/{index}");
            vault.push_back(world.mint(POOL_LABEL, mint_seed.as_bytes()));
        }
        // The pool is FULLY BACKED at genesis: its real `$DREGG` custody equals the encrypted
        // reserve `x`, and its relic vault equals the encrypted reserve `y`. That correspondence
        // is checked every `verify` — and it is also, said plainly, the exact reason a
        // ledger-watcher can reconstruct the book the FHE hides at decision time.
        world.fund_dregg(POOL_LABEL, GENESIS_DREGG);

        Ok(PoolCore {
            custody,
            house,
            quoter: Quoter::new(GENESIS_DREGG, GENESIS_RELICS),
            world,
            vault,
            journal: Journal::new(seed),
            seated: BTreeSet::new(),
            fills: BTreeMap::new(),
            public: Vec::new(),
            seat_turns: 0,
            quorum_openings: 0,
            refusals: 0,
            quarantine: None,
        })
    }

    /// Take a seat: ONE real committed journal turn, then the devnet faucet credit. A second
    /// seat is refused and commits nothing (anti-ghost: a refusal never leaves a purse behind).
    fn seat(&mut self, actor: &DreggIdentity) -> Result<TurnReceipt, DarkPoolError> {
        if let Some(why) = &self.quarantine {
            return Err(DarkPoolError::Quarantined(why.clone()));
        }
        if self.seated.contains(actor.as_str()) {
            return Err(DarkPoolError::AlreadySeated);
        }
        let sequence = self.journal.sequence + 1;
        let mut digest = blake3::Hasher::new_derive_key("dregg-dark-pool-seat-v1");
        digest.update(&sequence.to_le_bytes());
        digest.update(actor.as_str().as_bytes());
        let receipt = self
            .journal
            .record(sequence, *digest.finalize().as_bytes())?;
        self.seated.insert(actor.as_str().to_string());
        self.world.fund_dregg(actor.as_str(), SEAT_FAUCET_DREGG);
        self.seat_turns += 1;
        Ok(receipt)
    }

    /// THE SWAP. `offered_price` is `Some` on the self-priced [`TURN_PROPOSE`] path, in which case
    /// the quoter is never consulted.
    fn swap(
        &mut self,
        actor: &DreggIdentity,
        relics: u64,
        offered_price: Option<u64>,
    ) -> Result<(TurnReceipt, PoolFill), DarkPoolError> {
        if let Some(why) = &self.quarantine {
            return Err(DarkPoolError::Quarantined(why.clone()));
        }
        if !self.seated.contains(actor.as_str()) {
            return Err(DarkPoolError::NoSeat);
        }
        if relics != 1 {
            return Err(DarkPoolError::NoExactQuote { relics });
        }
        let self_priced = offered_price.is_some();
        let price = match offered_price {
            Some(price) => price,
            None => self
                .quoter
                .exact_price(relics)
                .ok_or(DarkPoolError::NoExactQuote { relics })?,
        };
        let Some(&asset) = self.vault.front() else {
            return Err(DarkPoolError::VaultEmpty);
        };

        // ── the fairness gate: ONE homomorphic ct×ct multiply of the CANDIDATE post-swap
        // reserves, opened by a FULL threshold quorum, compared to the public k. Nothing else in
        // this function decides fairness; in particular the quoter is not re-consulted, and no
        // plaintext reserve is read.
        let candidate: AppliedSwap =
            self.house
                .try_swap_proposed(price, relics)
                .map_err(|e| match e {
                    DarkAmmError::ZeroAmount => DarkPoolError::NoExactQuote { relics },
                    other => DarkPoolError::Pool(other.to_string()),
                })?;
        let opened = self.custody.open_bounded(&candidate.invariant)?;
        self.quorum_openings += 1;
        if candidate.check_invariant(opened).is_err() {
            // Refused. The raw product stays inside this process; it is not in the error.
            self.refusals += 1;
            return Err(DarkPoolError::UnfairSwap);
        }

        // ── the value cross. Owner-gated + sealed-escrow atomic: the relic enters custody only
        // under the pool's own signature, and a taker who cannot pay gets the seller made whole.
        // This runs BEFORE the encrypted state advances, so a purse shortfall leaves the pool
        // exactly where it was.
        let mut listing = self.world.list(POOL_LABEL, asset, price)?;
        self.world.buy(&mut listing, actor.as_str())?;
        self.vault.pop_front();

        // ── the encrypted state advances. `commit` re-checks the opened invariant, so this cannot
        // install a candidate the quorum refused.
        self.house
            .commit(&candidate, opened)
            .map_err(|e| DarkPoolError::Pool(e.to_string()))?;
        self.quoter.apply(price, relics);

        let sequence = self.public.len() as u64 + 1;
        let mut digest = blake3::Hasher::new_derive_key("dregg-dark-pool-swap-v1");
        digest.update(&sequence.to_le_bytes());
        digest.update(actor.as_str().as_bytes());
        digest.update(&asset.bytes());
        digest.update(&self.custody.collective_key_digest());
        let digest = *digest.finalize().as_bytes();
        let receipt = match self.journal.record(self.journal.sequence + 1, digest) {
            Ok(receipt) => receipt,
            Err(error) => {
                // The value already crossed and the ciphertexts already advanced. Never report a
                // committed move as a clean refusal a client might retry.
                self.quarantine = Some(format!(
                    "swap {sequence} crossed value but its journal turn was refused: {error}"
                ));
                return Err(DarkPoolError::Quarantined(
                    self.quarantine.clone().expect("just set"),
                ));
            }
        };

        let fill = PoolFill {
            sequence,
            relics,
            price,
            asset,
            turn_hash: receipt.turn_hash,
            self_priced,
        };
        self.fills
            .entry(actor.as_str().to_string())
            .or_default()
            .push(fill.clone());
        self.public.push(PublicSwapCard {
            sequence,
            taker_fingerprint: fingerprint(actor.as_str()),
            turn_hash: receipt.turn_hash,
            quorum_openings: 1,
        });
        Ok((receipt, fill))
    }

    /// Open the CURRENT encrypted reserves under a full quorum and check they still track the LP
    /// view. This is an audit capability (it needs every custodian) and it publishes nothing: the
    /// opened values are compared here and dropped.
    fn audit_reserves(&self) -> Result<bool, DarkPoolError> {
        let state = self.house.reserve_cts();
        let x = self.custody.open_bounded(&state.ct_x)?;
        let y = self.custody.open_bounded(&state.ct_y)?;
        Ok(x == self.quoter.x && y == self.quoter.y)
    }
}

fn fingerprint(actor: &str) -> String {
    let digest = blake3::hash(actor.as_bytes());
    hex8(&digest.as_bytes()[..4])
}

fn hex8(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

// ---------------------------------------------------------------------------
// the offering
// ---------------------------------------------------------------------------

/// The mounted Dark Pool. One pool, many sessions: the encrypted book, the custody roster, the
/// relic vault and the purses are pool-level state, so opening a second surface does NOT re-run
/// the key ceremony (see [`DarkPoolOffering::mount`] for why that matters).
#[derive(Clone)]
pub struct DarkPoolOffering {
    core: Arc<Mutex<PoolCore>>,
    custodians: usize,
}

impl DarkPoolOffering {
    /// Stand up the pool from a `u64` seed: run the n-of-n ceremony ONCE, encrypt the genesis
    /// reserves to the collective key, and mint the relic vault.
    ///
    /// **This is the expensive call.** The keygen + relinearization ceremony at the degree-4096
    /// `fold_set` parameters is a fraction of a second per custodian, so it belongs to POOL
    /// GENESIS (a deployment event), never to a player opening a session. [`Offering::open`] is
    /// deliberately cheap and attaches to the already-ceremonied pool.
    ///
    /// **The custody root of a pool mounted this way carries at most 64 bits, and `seed` is a
    /// caller-chosen parameter.** Every custodian's secret share is derived from it, so anyone
    /// who learns `(seed, custodians)` reconstructs the whole committee and decrypts the book
    /// alone — the n-of-n property is worth exactly the secrecy of that `u64`. This is the
    /// REPRODUCIBLE path: it exists so a test or an audit can replay a pool byte-for-byte. A
    /// deployment that means the threshold claim uses
    /// [`mount_with_custody_root`](Self::mount_with_custody_root) with 32 bytes of real entropy —
    /// and even then, read [`pool_ceremony`]: one process holding all `n` roots is a simulated
    /// ceremony, not a distributed one.
    pub fn mount(seed: u64, custodians: usize) -> Result<Self, DarkPoolError> {
        let mut material = Vec::with_capacity(16);
        material.extend_from_slice(&seed.to_le_bytes());
        material.extend_from_slice(&(custodians as u64).to_le_bytes());
        let root = blake3::derive_key("dregg-dark-pool-genesis-v1", &material);
        Self::stand_up(root, seed, custodians)
    }

    /// Stand up the pool from a full 32-byte custody root. Same ceremony as [`mount`](Self::mount)
    /// without the 64-bit ceiling on the root; `seed` still names the vault/journal identity, so
    /// two pools on the same seed and different roots are the same market under different keys.
    pub fn mount_with_custody_root(
        root: [u8; 32],
        seed: u64,
        custodians: usize,
    ) -> Result<Self, DarkPoolError> {
        Self::stand_up(root, seed, custodians)
    }

    fn stand_up(root: [u8; 32], seed: u64, custodians: usize) -> Result<Self, DarkPoolError> {
        // The roster floor is enforced by the ceremony itself
        // ([`crate::threshold_committee::MIN_COMMITTEE_PARTIES`]); this branch only names it in
        // the pool's own vocabulary before paying for a keygen that would refuse anyway.
        if custodians < 2 {
            return Err(DarkPoolError::Ceremony(
                "an n-of-n dark pool needs at least two custodians".to_string(),
            ));
        }
        Ok(Self {
            core: Arc::new(Mutex::new(PoolCore::stand_up(root, seed, custodians)?)),
            custodians,
        })
    }

    /// How many custodians hold the key (all of them must agree to open anything).
    pub fn custodians(&self) -> usize {
        self.custodians
    }

    fn lock(&self) -> Result<MutexGuard<'_, PoolCore>, DarkPoolError> {
        self.core
            .lock()
            .map_err(|_| DarkPoolError::Quarantined("the pool lock is poisoned".to_string()))
    }

    /// A player's own fills — the per-viewer release. NOT for a shared surface.
    pub fn fills_for(&self, viewer: &DreggIdentity) -> Vec<PoolFill> {
        self.lock()
            .ok()
            .and_then(|core| core.fills.get(viewer.as_str()).cloned())
            .unwrap_or_default()
    }

    /// A player's `$DREGG` purse.
    pub fn purse_of(&self, viewer: &DreggIdentity) -> i64 {
        self.lock()
            .map(|mut core| core.world.dregg_balance(viewer.as_str()))
            .unwrap_or(0)
    }

    /// The viewer-blind public record.
    pub fn public_cards(&self) -> Vec<PublicSwapCard> {
        self.lock()
            .map(|core| core.public.clone())
            .unwrap_or_default()
    }

    /// The pool's own custody handle, for a deployment that drives the parties itself (and for an
    /// adversarial test that wants to try a short or forged coalition against the real combiner).
    pub fn with_custody<R>(
        &self,
        f: impl FnOnce(&DarkPoolCustody) -> R,
    ) -> Result<R, DarkPoolError> {
        Ok(f(&self.lock()?.custody))
    }

    /// The current encrypted invariant ciphertext for the CANDIDATE `(price, relics)` — the exact
    /// object the fairness gate opens. Exposed so a custody deployment (or a test) can drive the
    /// quorum itself.
    pub fn candidate_invariant(
        &self,
        price: u64,
        relics: u64,
    ) -> Result<BoundedCiphertext, DarkPoolError> {
        let core = self.lock()?;
        core.house
            .try_swap_proposed(price, relics)
            .map(|candidate| candidate.invariant)
            .map_err(|e| DarkPoolError::Pool(e.to_string()))
    }

    /// The public invariant `k`. Public by construction; it is the product of the reserves and
    /// never their split.
    pub fn public_invariant(&self) -> u64 {
        self.lock().map(|core| core.house.k).unwrap_or(0)
    }
}

/// One surface's view of the mounted pool. It carries no pool state of its own: opening a second
/// surface attaches to the SAME encrypted book, which is what a pool is.
pub struct DarkPoolSession {
    core: Arc<Mutex<PoolCore>>,
}

impl DarkPoolSession {
    fn lock(&self) -> Result<MutexGuard<'_, PoolCore>, DarkPoolError> {
        self.core
            .lock()
            .map_err(|_| DarkPoolError::Quarantined("the pool lock is poisoned".to_string()))
    }
}

fn parse_proposal(input: &Action) -> Result<u64, String> {
    if input.arg <= 0 {
        return Err("a self-priced proposal must offer a positive amount of $DREGG".to_string());
    }
    u64::try_from(input.arg).map_err(|_| "the offered amount does not fit a $DREGG value".into())
}

impl Offering for DarkPoolOffering {
    type Session = DarkPoolSession;

    fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        // Cheap on purpose: the ceremony already happened at `mount`.
        Ok(DarkPoolSession {
            core: Arc::clone(&self.core),
        })
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        let Ok(core) = session.lock() else {
            return Vec::new();
        };
        if core.quarantine.is_some() {
            return Vec::new();
        }
        // NOTE: no affordance is gated on the reserves. Dimming "the sizes that have an exact
        // quote right now" would paint the book onto the surface the encryption exists to keep
        // blind; a size with no exact quote is refused at `advance` instead.
        vec![
            Action::new("Take a seat at the dark pool", TURN_JOIN, 0, true),
            Action::new("Swap for one relic at the pool's quote", TURN_SWAP, 1, true),
            Action::new("Name your own price for one relic", TURN_PROPOSE, 0, true).taking_text(),
        ]
    }

    fn actions_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Vec<Action> {
        let Ok(core) = session.lock() else {
            return Vec::new();
        };
        if core.quarantine.is_some() {
            return Vec::new();
        }
        let seated = core.seated.contains(viewer.as_str());
        vec![
            Action::new("Take a seat at the dark pool", TURN_JOIN, 0, !seated),
            Action::new(
                "Swap for one relic at the pool's quote",
                TURN_SWAP,
                1,
                seated,
            ),
            Action::new("Name your own price for one relic", TURN_PROPOSE, 0, seated).taking_text(),
        ]
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        let mut core = match session.lock() {
            Ok(core) => core,
            Err(error) => return Outcome::Refused(error.to_string()),
        };
        match input.turn.as_str() {
            TURN_JOIN => match core.seat(&actor) {
                Ok(receipt) => Outcome::Landed {
                    receipt,
                    ended: false,
                },
                Err(error) => Outcome::Refused(error.to_string()),
            },
            TURN_SWAP => {
                let relics = u64::try_from(input.arg.max(0)).unwrap_or(0);
                match core.swap(&actor, relics, None) {
                    Ok((receipt, _)) => Outcome::Landed {
                        receipt,
                        ended: false,
                    },
                    Err(error) => Outcome::Refused(error.to_string()),
                }
            }
            TURN_PROPOSE => match parse_proposal(&input) {
                Ok(price) => match core.swap(&actor, 1, Some(price)) {
                    Ok((receipt, _)) => Outcome::Landed {
                        receipt,
                        ended: false,
                    },
                    Err(error) => Outcome::Refused(error.to_string()),
                },
                Err(why) => Outcome::Refused(why),
            },
            other => Outcome::Refused(format!("unknown dark-pool affordance: {other}")),
        }
    }

    /// Re-verify the pool WITHOUT trusting its own bookkeeping:
    ///
    /// 1. re-derive the reserve trajectory from the recorded fills alone and check the
    ///    constant product holds at every step — a plaintext re-check of exactly what the
    ///    homomorphic gate decided;
    /// 2. open the CURRENT encrypted reserves under a full quorum and confirm the ciphertext
    ///    state actually tracks that trajectory (the cross-check that makes step 1 non-vacuous:
    ///    without it the fills could be fiction);
    /// 3. check every journal turn committed with a strictly increasing sequence and a real hash;
    /// 4. re-verify every crossed relic's provenance lineage.
    fn verify(&self, session: &Self::Session) -> VerifyReport {
        let Ok(mut core) = session.lock() else {
            return VerifyReport::broken(0, "the pool lock is poisoned");
        };
        if let Some(why) = &core.quarantine {
            return VerifyReport::broken(core.public.len(), why.clone());
        }
        let turns = core.public.len();

        // (1) the invariant trajectory, re-derived from the fills.
        let mut replay = Quoter::new(GENESIS_DREGG, GENESIS_RELICS);
        let mut ordered: Vec<&PoolFill> = core.fills.values().flatten().collect();
        ordered.sort_by_key(|fill| fill.sequence);
        for (index, fill) in ordered.iter().enumerate() {
            if fill.sequence != (index as u64) + 1 {
                return VerifyReport::broken(turns, "the recorded fill sequence has a gap");
            }
            if fill.relics >= replay.y {
                return VerifyReport::broken(turns, "a recorded fill would have drained the pool");
            }
            replay.apply(fill.price, fill.relics);
            if replay.x * replay.y != replay.k {
                return VerifyReport::broken(
                    turns,
                    format!(
                        "swap {} broke the constant product on replay",
                        fill.sequence
                    ),
                );
            }
        }

        // (2) the ENCRYPTED state must agree — opened under the full quorum, never published.
        match core.audit_reserves() {
            Ok(true) => {}
            Ok(false) => {
                return VerifyReport::broken(
                    turns,
                    "the encrypted reserves do not open to the replayed trajectory",
                );
            }
            Err(error) => return VerifyReport::broken(turns, error.to_string()),
        }

        // (3) the journal chain: every seat and every swap is one real committed turn, and the
        // cell's StrictMonotonic sequence must account for exactly all of them.
        for (index, card) in core.public.iter().enumerate() {
            if card.sequence != (index as u64) + 1 {
                return VerifyReport::broken(turns, "the public swap sequence is not contiguous");
            }
            if card.turn_hash == [0u8; 32] {
                return VerifyReport::broken(turns, "a public swap card carries no committed turn");
            }
        }
        if core.journal.sequence != core.seat_turns + turns as u64 {
            return VerifyReport::broken(
                turns,
                "the journal cell's committed sequence does not account for every seat and swap",
            );
        }

        // (4) every crossed relic's lineage.
        for fill in &ordered {
            let provenance = core.world.verify_provenance(fill.asset);
            if !provenance.verified {
                return VerifyReport::broken(
                    turns,
                    format!(
                        "the relic crossed at swap {} broke provenance: {}",
                        fill.sequence,
                        provenance.reasons.join("; ")
                    ),
                );
            }
        }

        // (5) FULL BACKING: the real custody must equal the encrypted reserves. The pool is not
        // allowed to price against liquidity it does not hold.
        let custody_dregg = core.world.dregg_balance(POOL_LABEL);
        let custody_relics = core.vault.len() as u64;
        if custody_dregg != core.quoter.x as i64 || custody_relics != core.quoter.y {
            return VerifyReport::broken(
                turns,
                format!(
                    "the pool is not fully backed: custody holds {custody_dregg} $DREGG and \
                     {custody_relics} relic(s) against reserves of {} and {}",
                    core.quoter.x, core.quoter.y
                ),
            );
        }

        let mut report = VerifyReport::ok(turns);
        report.detail = format!(
            "{turns} dark-pool swap(s) re-verified: constant product re-derived from the fills, \
             the encrypted reserves re-opened under all {} custodians and matched, {} full-quorum \
             opening(s) consumed, every crossed relic's lineage intact, and the pool is fully \
             backed by real custody",
            core.custody.n_parties(),
            core.quorum_openings
        );
        report
    }

    /// The VIEWER-BLIND card. Carries no reserve, no price, no relic count, no purse — exactly
    /// what may sit in a Discord channel or on a projector.
    fn render(&self, session: &Self::Session) -> Surface {
        let Ok(core) = session.lock() else {
            return Surface(ViewNode::Section {
                title: "The Dark Pool — unavailable".to_string(),
                tag: "bad".to_string(),
                children: vec![ViewNode::Text("the pool lock is poisoned".to_string())],
            });
        };
        if let Some(why) = &core.quarantine {
            return Surface(ViewNode::Section {
                title: "The Dark Pool — quarantined".to_string(),
                tag: "bad".to_string(),
                children: vec![ViewNode::Text(why.clone())],
            });
        }
        Surface(ViewNode::Section {
            title: "The Dark Pool — blind relic vendor".to_string(),
            tag: "accent".to_string(),
            children: vec![
                ViewNode::Section {
                    title: "Public book".to_string(),
                    tag: "genuine".to_string(),
                    children: vec![
                        ViewNode::Text(format!(
                            "{} swap(s) filled · {} refused by the invariant · {} full-quorum opening(s)",
                            core.public.len(),
                            core.refusals,
                            core.quorum_openings
                        )),
                        ViewNode::Text(format!(
                            "public invariant k={} · collective key {} · {}-of-{} custody",
                            core.house.k,
                            hex8(&core.custody.collective_key_digest()[..4]),
                            core.custody.n_parties(),
                            core.custody.n_parties()
                        )),
                        ViewNode::Text(
                            "Absent from this surface: the reserve split, every fill price, every \
                             taker's purse and holdings. A price beside a public k determines the \
                             book, so a fill is shown only to the taker who made it."
                                .to_string(),
                        ),
                    ],
                },
                ViewNode::Section {
                    title: "Boundary".to_string(),
                    tag: "muted".to_string(),
                    children: vec![ViewNode::Text(DARK_POOL_DISCLOSURE.to_string())],
                },
            ],
        })
    }

    /// The PER-VIEWER projection: this viewer's purse, their relics and their fill prices, plus
    /// the public card. Safe only on a single-reader surface — see
    /// [`hidden_information`](Offering::hidden_information).
    fn render_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Surface {
        let public = self.render(session);
        let Ok(mut core) = session.lock() else {
            return public;
        };
        if core.quarantine.is_some() {
            return public;
        }
        let seated = core.seated.contains(viewer.as_str());
        let purse = core.world.dregg_balance(viewer.as_str());
        let fills = core.fills.get(viewer.as_str()).cloned().unwrap_or_default();
        let mut children = vec![ViewNode::Text(if seated {
            format!(
                "Your purse: {purse} $DREGG · {} relic(s) taken",
                fills.len()
            )
        } else {
            "You have no seat at this pool yet.".to_string()
        })];
        for fill in &fills {
            children.push(ViewNode::Text(format!(
                "swap #{} · {} relic for {} $DREGG{} · turn {}",
                fill.sequence,
                fill.relics,
                fill.price,
                if fill.self_priced {
                    " (your own price)"
                } else {
                    " (pool quote)"
                },
                hex8(&fill.turn_hash[..4])
            )));
        }
        children.push(ViewNode::Text(
            "Your fill prices are yours alone: published beside the public k they would reveal \
             the pool's whole book."
                .to_string(),
        ));
        Surface(ViewNode::Section {
            title: "The Dark Pool — your position".to_string(),
            tag: "accent".to_string(),
            children: vec![
                ViewNode::Section {
                    title: "Private".to_string(),
                    tag: "genuine".to_string(),
                    children,
                },
                public.0,
            ],
        })
    }

    /// `true`. [`render_for`](Offering::render_for) carries the viewer's own fill PRICES, and a
    /// price beside the public `k` determines both reserves — so a frontend must never copy this
    /// projection onto a shared surface.
    fn hidden_information(&self) -> bool {
        true
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_exact_quote_ladder_walks_the_pool_down_to_its_last_relic() {
        // The genesis reserves are chosen so the invariant — which admits ONLY a post-swap
        // product of exactly k — has an integer price at every rung. This is plaintext
        // arithmetic about the quoter, not a claim about the crypto.
        let mut q = Quoter::new(GENESIS_DREGG, GENESIS_RELICS);
        let mut rungs = 0;
        while let Some(price) = q.exact_price(1) {
            q.apply(price, 1);
            assert_eq!(q.x * q.y, q.k, "the ladder left the constant product");
            rungs += 1;
        }
        assert_eq!(rungs, GENESIS_RELICS - 1, "the ladder stopped early");
        assert_eq!(q.y, 1, "the last relic must be unbuyable (infinite price)");
        assert_eq!(q.exact_price(1), None);
    }

    #[test]
    fn a_self_priced_proposal_below_the_quote_is_not_an_exact_quote() {
        let q = Quoter::new(GENESIS_DREGG, GENESIS_RELICS);
        let fair = q.exact_price(1).expect("genesis quote");
        assert_eq!(fair, 252);
        // (2520 + 100)(11 - 1) = 26200 != 27720; the homomorphic gate is what actually refuses
        // it at runtime, this only pins the arithmetic the gate is deciding.
        assert_ne!((GENESIS_DREGG + 100) * (GENESIS_RELICS - 1), q.k);
    }
}
