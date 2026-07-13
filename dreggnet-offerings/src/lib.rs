//! # DreggNet Cloud — the frontend-agnostic Offering/Session core.
//!
//! The dungeon (`discord-bot/fiction.rs`) is **offering #0** — the first instance of a
//! general pattern: a **confined, verifiable, paid, per-session thing** hosted on the real
//! dregg substrate. This crate extracts that pattern into a reusable [`Offering`] trait and a
//! [`Frontend`] abstraction, so Telegram / WeChat / web frontends and hosted-Hermes / grain
//! offerings plug into ONE core. See `docs/DREGGNET-CLOUD-OFFERINGS.md` (the design).
//!
//! ## The shape every offering shares (proved end-to-end by the dungeon)
//! 1. **A per-session confined thing** — a channel/thread/chat hosts one live session.
//! 2. **A confined intelligence/app** — the dungeon's jailed narrator; elsewhere a hosted
//!    Hermes agent or a Sandstorm grain.
//! 3. **Real verifiable turns** — each input is a real executor turn → a [`TurnReceipt`];
//!    [`Offering::verify`] re-checks the whole chain (the executor is the source of truth — a
//!    jailbroken narration cannot change the world).
//! 4. **Payment-gated** — a paid action debits a run-credit ([`RunCost`]); empty → free tier.
//! 5. **Optionally collective** — write-once ballots + quorum when a crowd drives one session
//!    (the ballot lives one layer up, in the orchestrator/frontend; the core resolves the
//!    *typed [`Action`]* the crowd picked, on the substrate).
//!
//! ## The abstraction
//! An [`Offering`] is `open` / [`actions`](Offering::actions) / [`advance`](Offering::advance)
//! / [`verify`](Offering::verify) / [`render`](Offering::render) / [`price`](Offering::price).
//! Its `render` returns a **deos affordance [`Surface`]** (a [`deos_view::ViewNode`]); its
//! [`Action`]s are **cap-gated affordances** (the `{turn, arg}` shape a `ViewNode` button
//! fires); an [`advance`](Offering::advance) is **one real turn** whose [`Outcome`] is
//! `Landed(TurnReceipt)` or `Refused(reason)` — the same anti-ghost shape the dungeon uses.
//!
//! ## Frontends — Discord is #0; Telegram, WeChat, web are the SAME offerings, different surfaces
//! The offering/session/payment/verify CORE is frontend-agnostic (this crate carries **no**
//! serenity/Discord dependency). A [`Frontend`] is an **affordance-renderer**: it derives a
//! per-platform [`DreggIdentity`], `present`s an offering's [`Surface`] + [`Action`]s, and
//! `collect`s a platform event back into a typed `(SessionId, Action, DreggIdentity)`. The
//! core resolves that action on the substrate; the executor stays the sole referee on every
//! surface. [`mock::MockFrontend`] is the reference renderer the tests drive.

pub mod dungeon;
pub mod mock;

use dregg_app_framework::TurnReceipt;

/// A **deos affordance surface** — the frontend-agnostic, gpui-free serializable view-tree an
/// offering's [`render`](Offering::render) produces. It IS a [`deos_view::ViewNode`] (the doc's
/// mandate: reuse the deos surface, do not reinvent it). Every frontend is a *renderer of this
/// tree* — the native cockpit paints it to gpui widgets, `deos-view`'s `web`/`discord`
/// renderers paint it to HTML / a Discord embed, and [`mock::MockFrontend`] presents it in a
/// test. A newtype (not a bare alias) so it can carry surface-level helpers and read as a
/// first-class Offering concept.
#[derive(Debug, Clone)]
pub struct Surface(pub deos_view::ViewNode);

impl Surface {
    /// The underlying deos view-tree (for a renderer to walk).
    pub fn view(&self) -> &deos_view::ViewNode {
        &self.0
    }
}

/// A **cap-gated affordance** — one candidate move on an offering's surface. It is the deos
/// `{turn, arg}` affordance shape (exactly what a [`deos_view::ViewNode::Button`] /
/// [`deos_view::MenuItem`] fires), so an [`Action`] round-trips through a rendered [`Surface`]:
/// `render` paints an action into a button/menu-row carrying `(turn, arg)`; a [`Frontend`]
/// collects a press of `(turn, arg)` back into the same [`Action`].
///
/// `enabled` is the **cap tooth shown, not hidden**: a currently-ineligible affordance is
/// rendered dimmed (a `!enabled` menu row) rather than removed — but it is only a *decoration*.
/// The executor is the sole referee: firing a `!enabled` (or forged) action still lands as a
/// real [`Outcome::Refused`] on the substrate (the anti-ghost tooth).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Action {
    /// The human label (the button/menu-row text). E.g. `"Press on into the plundered hall"`.
    pub label: String,
    /// The affordance verb — its identity within the surface (the deos analogue of htmx's
    /// `hx-post` path). The dungeon uses `"choose"`; a Hermes offering might use `"prompt"`.
    pub turn: String,
    /// The affordance argument — for the dungeon, the scene choice index within the current
    /// passage (the index [`spween_dregg::WorldCell::apply_choice`] checks the gate case
    /// against). Carried as `i64` to match the deos `ViewNode` `{turn, arg}` wire shape.
    pub arg: i64,
    /// Whether the affordance is currently eligible (its scene/cap condition holds). A
    /// decoration for the surface (`false` → shown dimmed); the executor still refuses an
    /// ineligible move on `advance`.
    pub enabled: bool,
    /// An **optional first-class free-text payload** the affordance carries alongside its
    /// `{turn, arg}`. A `{turn, arg: i64}` names an *index* move (a scene choice, a cell to
    /// delete); a **text-shaped** move — a document EDIT's inserted prose, a hosted-Hermes
    /// PROMPT, a title's new value — needs a *string*, and this is where it rides.
    ///
    /// `None` is the text-free affordance (a fixed-index button/menu-row), and it is the
    /// **default** every existing affordance already is: this field is additive and invisible to
    /// them — an `Action` with `text: None` presents, collects, and encodes exactly as before.
    /// A text-bearing affordance sets it with [`Action::with_text`].
    ///
    /// This is the real payload the two WORKAROUNDS approximated and can now retire (as
    /// follow-ups): dreggnet-doc rode an edit's text on [`Action::label`] (the label doubling as
    /// the content), and the discord-bot minted a separate `askt`/`subt` modal wire to carry the
    /// string beside the button. With a first-class `text`, the payload is part of the actuation
    /// itself — a [`Frontend`] present/collect and the deos affordance codec round-trip it
    /// losslessly, no label-riding and no side channel.
    pub text: Option<String>,
}

impl Action {
    /// A convenience constructor for a **text-free** affordance (`text: None`) — the fixed
    /// `{turn, arg}` button/menu-row every existing offering builds. Attach a free-text payload
    /// with [`Action::with_text`].
    pub fn new(label: impl Into<String>, turn: impl Into<String>, arg: i64, enabled: bool) -> Self {
        Action {
            label: label.into(),
            turn: turn.into(),
            arg,
            enabled,
            text: None,
        }
    }

    /// **Attach a free-text payload** to this affordance (builder-style) — a document edit's
    /// prose, a Hermes prompt, a title's value. The `{label, turn, arg, enabled}` are unchanged;
    /// only [`Action::text`] is set, so the affordance now carries its string as a first-class
    /// part of the actuation rather than on the label or a side channel.
    ///
    /// ```
    /// # use dreggnet_offerings::Action;
    /// let a = Action::new("…continue the document", "insert", 3, true)
    ///     .with_text("the dragon's hoard glittered in the torchlight");
    /// assert_eq!(a.text.as_deref(), Some("the dragon's hoard glittered in the torchlight"));
    /// assert_eq!(a.arg, 3); // the {turn, arg} shape is untouched
    /// ```
    pub fn with_text(mut self, text: impl Into<String>) -> Self {
        self.text = Some(text.into());
        self
    }
}

/// The outcome of an [`advance`](Offering::advance) — the same anti-ghost shape the dungeon
/// uses. A legal move commits **one real verified turn** (a [`TurnReceipt`] chained on the
/// session's receipt chain); an illegal one is a real executor refusal — **nothing commits, no
/// receipt** (the anti-ghost tooth). The confined intelligence never decides this: the
/// executor resolves the typed [`Action`] on the substrate, not any prose.
#[derive(Debug, Clone)]
pub enum Outcome {
    /// The move landed as one verified, committed turn — a real [`TurnReceipt`].
    Landed {
        /// The committed turn's receipt (a genuine `turn_hash`, chained pre/post state).
        receipt: TurnReceipt,
        /// Whether this move ended the session (the offering reached a terminal state).
        ended: bool,
    },
    /// The real executor REFUSED the move (an installed gate bit): nothing committed, no
    /// receipt. Carries the executor's own reason.
    Refused(String),
}

impl Outcome {
    /// Did this move land a real receipt?
    pub fn landed(&self) -> bool {
        matches!(self, Outcome::Landed { .. })
    }
}

/// What a paid action costs, in **run-credits**. One credit maps to one
/// `dregg_pay::CreditLedger::debit` (priced at `PayConfig::price_per_run` atomic `$DREGG`, or a
/// flat USDC amount — the dual-asset model). `credits == 0` is the **free tier** (no debit).
///
/// The *substrate turn itself is free and verifiable* on every offering; a `RunCost > 0` prices
/// the offering's **confined intelligence** (the dungeon's Bedrock narration, a hosted-Hermes
/// agent call). The frontend/orchestrator debits the credit against the actor's balance before
/// serving the paid render; the core stays payment-model-agnostic (it names the cost, it does
/// not hold the ledger).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RunCost {
    /// Run-credits debited when this action fires (`0` → free tier).
    pub credits: u64,
}

impl RunCost {
    /// The free tier — no credit debited.
    pub const fn free() -> Self {
        RunCost { credits: 0 }
    }

    /// A paid action costing `credits` run-credits.
    pub const fn credits(credits: u64) -> Self {
        RunCost { credits }
    }

    /// Whether this cost debits anything (i.e. is a paid-tier action).
    pub fn is_paid(&self) -> bool {
        self.credits > 0
    }
}

/// The result of [`Offering::verify`] — an offering's own proof that its session's committed
/// chain is honest. For a substrate-backed offering this is the outcome of re-verifying the
/// whole receipt chain **by replay** (re-driving a fresh, identically-seeded confined state
/// through the recorded inputs and confirming it reproduces exactly the committed state chain).
/// A forged / reordered / ineligible input breaks replay.
#[derive(Debug, Clone)]
pub struct VerifyReport {
    /// Whether the session's committed chain re-verifies.
    pub verified: bool,
    /// The number of real verified turns checked (genesis + committed steps).
    pub turns: usize,
    /// A human account — `"re-verified by replay"` on success, or the replay break on failure.
    pub detail: String,
}

impl VerifyReport {
    /// A passing report over `turns` verified turns.
    pub fn ok(turns: usize) -> Self {
        VerifyReport {
            verified: true,
            turns,
            detail: "re-verified by replay".to_string(),
        }
    }

    /// A failing report carrying the break reason.
    pub fn broken(turns: usize, detail: impl Into<String>) -> Self {
        VerifyReport {
            verified: false,
            turns,
            detail: detail.into(),
        }
    }
}

/// Configuration for opening a session. Offering-agnostic; an offering reads the fields it
/// needs (the dungeon uses `seed` for a deterministic, replay-verifiable world identity).
#[derive(Debug, Clone, Default)]
pub struct SessionConfig {
    /// A deterministic session seed — the offering re-derives an identically-seeded confined
    /// state from it when verifying by replay. `None` → the offering's default.
    pub seed: Option<u64>,
}

impl SessionConfig {
    /// A config pinning a deterministic seed.
    pub fn with_seed(seed: u64) -> Self {
        SessionConfig { seed: Some(seed) }
    }
}

/// An error opening an offering session (the confined thing refused to deploy).
#[derive(Debug, Clone)]
pub enum OfferingError {
    /// The confined substrate refused to deploy (carries the reason).
    Deploy(String),
}

impl std::fmt::Display for OfferingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OfferingError::Deploy(why) => write!(f, "offering deploy failed: {why}"),
        }
    }
}

impl std::error::Error for OfferingError {}

/// A **frontend-agnostic dregg identity** — the actor an [`Action`] is attributed to. It is a
/// derived cryptographic identity (an Ed25519 public key hex), NOT a platform nickname: a
/// [`Frontend`] derives it per-platform (Discord from the user's `UserCipherclerk`, Telegram
/// from the Telegram user id, …), and the SAME actor across platforms resolves to the SAME
/// identity iff the derivation inputs match. The core treats it opaquely.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DreggIdentity(pub String);

impl DreggIdentity {
    /// The public-key hex (or other opaque handle) this identity wraps.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// **A single option's vote count** in a [`Tally`] — how many of the electorate picked the
/// affordance carrying `arg`. `arg` is exactly an [`Action::arg`] (the choice index), so a tally
/// row lines up with the ballot options a frontend rendered.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VoteCount {
    /// The [`Action::arg`] this count is for (the choice index the option carries).
    pub arg: i64,
    /// How many voters picked it.
    pub votes: u32,
}

impl VoteCount {
    /// `votes` votes for the option carrying `arg`.
    pub fn new(arg: i64, votes: u32) -> Self {
        VoteCount { arg, votes }
    }
}

/// **The crowd's ballot outcome** — the per-option vote distribution and the winning `arg` that
/// was carried onto the substrate. A [`CollectiveDecision`] pairs this with the electorate + the
/// carrier, so an offering records "the party split THIS way, option X won" as first-class receipt
/// metadata beside the single world-signed turn (the substrate still admits exactly one typed
/// [`Action`]; the tally is the provenance of *which* one the crowd picked).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tally {
    /// The per-option vote counts (the ballot distribution).
    pub counts: Vec<VoteCount>,
    /// The winning option's [`Action::arg`] — the choice actually carried onto the substrate.
    pub winner: i64,
}

impl Tally {
    /// A tally with an explicitly-named winner (the frontend already resolved the ballot).
    pub fn new(counts: Vec<VoteCount>, winner: i64) -> Self {
        Tally { counts, winner }
    }

    /// A **plurality** tally: the option with the most votes wins; a tie breaks to the
    /// first-listed option (the ballot's own order). `None` if there are no counts — the natural
    /// constructor for a crowd ballot the frontend hands over.
    pub fn plurality(counts: Vec<VoteCount>) -> Option<Self> {
        let mut best: Option<&VoteCount> = None;
        for c in &counts {
            // strictly-greater keeps the FIRST maximum on a tie (stable to ballot order)
            if best.map_or(true, |b| c.votes > b.votes) {
                best = Some(c);
            }
        }
        let winner = best?.arg;
        Some(Tally { counts, winner })
    }

    /// Total votes cast across all options.
    pub fn total_votes(&self) -> u32 {
        self.counts.iter().map(|c| c.votes).sum()
    }

    /// Votes for the winning option (`0` if the winner is not among the counts).
    pub fn winning_votes(&self) -> u32 {
        self.counts
            .iter()
            .find(|c| c.arg == self.winner)
            .map(|c| c.votes)
            .unwrap_or(0)
    }
}

/// **A first-class collective decision** — the crowd turn the single-actor
/// [`advance`](Offering::advance) cannot express. Where `advance` attributes ONE `actor`, a
/// plurality/quorum turn has an *electorate* (everyone who voted), a *carrier* (the identity the
/// winning move is attributed to — the mover of record), and a [`Tally`] (how the crowd split).
/// An offering records all three beside the one world-signed substrate turn, so the receipt says
/// **"the PARTY (these voters) decided X, carried by Y"** rather than a nameless `party` constant
/// — closing the gap the /dungeon refactor flagged, where `party_actor()` erased who carried the
/// decision. Optional: [`advance`](Offering::advance) still records a single actor; a collective
/// turn is [`advance_collective`](Offering::advance_collective), whose default resolves the move
/// as `advance` attributed to the `carrier`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CollectiveDecision {
    /// Everyone who took part in the ballot (the crowd of record).
    pub electorate: Vec<DreggIdentity>,
    /// The identity the winning move is attributed to — the mover of record. The default
    /// [`advance_collective`](Offering::advance_collective) resolves the turn as this actor, so
    /// the single-actor `actor_of_step` and the collective record agree on who carried it.
    pub carrier: DreggIdentity,
    /// How the crowd split, and which option won (carried onto the substrate).
    pub tally: Tally,
}

impl CollectiveDecision {
    /// A collective decision over `electorate`, carried by `carrier`, with outcome `tally`.
    pub fn new(electorate: Vec<DreggIdentity>, carrier: DreggIdentity, tally: Tally) -> Self {
        CollectiveDecision {
            electorate,
            carrier,
            tally,
        }
    }

    /// How many identities took part in the decision.
    pub fn electorate_size(&self) -> usize {
        self.electorate.len()
    }

    /// Whether `who` was part of the electorate that made this decision.
    pub fn voted(&self, who: &DreggIdentity) -> bool {
        self.electorate.contains(who)
    }
}

/// A session's identity within a [`Frontend`] — the surface slot a session is presented in (a
/// Discord channel/thread id, a Telegram chat id, a web session token). Opaque to the core.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SessionId(pub String);

impl SessionId {
    /// Wrap a raw session key.
    pub fn new(id: impl Into<String>) -> Self {
        SessionId(id.into())
    }
}

/// **An offering** — a confined, verifiable, paid, per-session thing hosted on the real dregg
/// substrate. Every offering (dungeon #0, hosted-Hermes, a grain) implements this ONE trait;
/// every [`Frontend`] drives it through the SAME six methods.
///
/// The load-bearing invariant: [`advance`](Offering::advance) resolves the typed [`Action`] on
/// the substrate — the executor is the sole referee, never the confined intelligence. A legal
/// move lands a real [`TurnReceipt`]; an illegal one is a real refusal that commits nothing.
pub trait Offering {
    /// The live confined session state (a `WorldCell` playthrough, a Hermes jail, a grain).
    /// Carries a real verifiable state chain.
    type Session;

    /// Open a fresh session (deploy the confined thing, run its genesis turn). The seed in
    /// `cfg` pins a deterministic, replay-verifiable identity.
    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError>;

    /// The candidate moves available in the session's current state — the cap-gated affordances
    /// a frontend renders as buttons/menu-rows (a ballot's options when a crowd drives one).
    fn actions(&self, session: &Self::Session) -> Vec<Action>;

    /// **Advance the session by one real turn.** Resolves `input` on the substrate as ONE
    /// cap-bounded turn attributed to `actor`: a legal move lands a real [`TurnReceipt`]
    /// ([`Outcome::Landed`]); an illegal/ineligible/forged move is a real executor refusal
    /// ([`Outcome::Refused`]) that commits nothing (anti-ghost).
    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome;

    /// **Advance by one real turn carrying a first-class [`CollectiveDecision`]** — the
    /// plurality/crowd analogue of [`advance`](Offering::advance). Where `advance` attributes a
    /// turn to ONE actor, this carries the whole electorate + the [`Tally`] + the carrier, so the
    /// offering records "the PARTY decided X, carried by Y" rather than a nameless constant.
    ///
    /// **Default relationship (optional, non-breaking):** resolves the move on the substrate
    /// exactly as [`advance`](Offering::advance) attributed to the decision's `carrier` — the
    /// single-actor path is the floor, so every offering gets a working `advance_collective` for
    /// free and the two stay in agreement on the mover. An offering that wants a *receipt* of the
    /// crowd decision (persist the electorate + tally beside the committed turn) overrides this
    /// (see [`dungeon::DungeonOffering`]); a refused move records nothing either way (anti-ghost).
    fn advance_collective(
        &self,
        session: &mut Self::Session,
        input: Action,
        decision: CollectiveDecision,
    ) -> Outcome {
        self.advance(session, input, decision.carrier)
    }

    /// Re-verify the session's committed chain (by replay / the offering's own proof).
    fn verify(&self, session: &Self::Session) -> VerifyReport;

    /// Render the session's current state as a **deos affordance [`Surface`]** — room/prose/
    /// state plus the [`actions`](Offering::actions) as cap-gated affordances.
    fn render(&self, session: &Self::Session) -> Surface;

    /// What a paid action costs (run-credits). The free tier is [`RunCost::free`].
    fn price(&self, input: &Action) -> RunCost;
}

/// **The frontend-facing tamper-verify seam.** An [`Offering`]'s [`verify`](Offering::verify)
/// re-checks a session the offering *itself* holds — but a frontend often holds only a
/// *transmitted* record (a serialized playthrough) that may have been **forged in transit**, and
/// cannot reach the offering's private world identity (the dungeon's `seed`/`scene`) to check it.
/// Before this seam the tamper tooth (forged-choice-fails-replay) was reachable only *inside* the
/// offering crate, so a frontend could not express "a forged record fails". This trait is that
/// seam: export a session's authentic record, and re-verify a (possibly forged) record against the
/// offering's own world identity — the frontend never touches substrate internals, yet a
/// forged/reordered/ineligible record fails while a legal one passes (non-vacuous).
///
/// It is **additive** to [`Offering`] — a separate extension trait, so no existing `Offering` impl
/// changes — and reusable by any record-backed offering. [`dungeon::DungeonOffering`] implements it
/// over the substrate playthrough (full replay + chain-linkage re-verification).
pub trait RecordVerify {
    /// The offering's live session — the authoritative world identity lives here, privately (the
    /// frontend holds it opaquely and passes it to bind a record to its authentic identity).
    type Session;
    /// The **public, transmissible** record a frontend holds — what it serializes, sends over a
    /// wire, and might receive tampered. For the dungeon this is the substrate playthrough.
    type Record;

    /// Export the session's authentic record — what a frontend transmits / persists / re-checks.
    fn export_record(&self, session: &Self::Session) -> Self::Record;

    /// **Re-verify a (possibly forged) `record`** against this offering's authentic world identity
    /// (bound through `session`, whose internals stay private to the offering). Returns a
    /// [`VerifyReport`]: a legal record re-verifies; a forged / reordered / ineligible / spliced
    /// one fails. The frontend-side tamper check, expressible without substrate internals.
    fn verify_record(&self, session: &Self::Session, record: &Self::Record) -> VerifyReport;
}

/// **A frontend** — an affordance-renderer over the ONE offering core. Discord is #0 (built);
/// Telegram / WeChat / web are more `Frontend` impls mapping the SAME [`Surface`] / [`Action`]s
/// onto inline keyboards / OA-menus / a web DOM. A frontend NEVER trusts a confined
/// intelligence and NEVER re-implements the offering logic: it derives identity, presents the
/// surface, collects a typed action, and hands it to the core.
///
/// This trait is generic over the platform's user + event types (a Discord `ComponentInteraction`,
/// a Telegram `CallbackQuery`, a web POST). The core stays agnostic to them.
pub trait Frontend {
    /// The platform's user handle (a Discord user id, a Telegram user id, a web session user).
    type PlatformUser;
    /// A platform interaction event (a button press, a slash command, a callback query).
    type PlatformEvent;

    /// Derive `user`'s frontend-agnostic [`DreggIdentity`] (per-platform: Discord from the
    /// derived Ed25519 key, Telegram from the user id, …). The SAME actor → the SAME identity.
    fn identity(&self, user: Self::PlatformUser) -> DreggIdentity;

    /// Open a surface slot for `session` (spin a thread/group/chat). Called by the orchestrator
    /// after [`Offering::open`], before the first [`present`](Frontend::present).
    fn spin_session(&mut self, session: SessionId);

    /// Present an offering's [`Surface`] + its [`Action`]s in `session`'s surface slot (paint
    /// the room + the action controls). Idempotent per render — a re-present replaces.
    fn present(&mut self, session: &SessionId, surface: &Surface, actions: &[Action]);

    /// Collect a platform event into a typed `(SessionId, Action, DreggIdentity)` — a press of
    /// a rendered affordance mapped back to the offering [`Action`] the core resolves. `None`
    /// if the event is not an affordance the frontend presented.
    fn collect(&self, ev: Self::PlatformEvent) -> Option<(SessionId, Action, DreggIdentity)>;

    /// Tear a session's surface down (archive the thread/chat on completion).
    fn teardown(&mut self, session: &SessionId);
}
