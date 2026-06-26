//! # Sealed-submission art gallery (Starbridge usecase app)
//!
//! Artists submit work to a juried gallery. To keep the jury honest and stop
//! artists copying or front-running each other's entries, submissions are
//! *sealed*: during a SUBMISSION phase each artist COMMITS a hash binding
//! `(artist, piece, nonce)`; the curator then CLOSES submissions; artists
//! REVEAL their pieces; and the curator CURATES — picks the featured piece for
//! display. Because the commit is a hash, no artist can peek at, copy, or
//! resubmit on top of another's entry before the reveal, and — once committed —
//! a sealed submission is FROZEN, so a piece cannot be quietly swapped out from
//! under the curator after the open call closes.
//!
//! This is the executable surface of a commit-reveal curation lifecycle (the
//! same shape the sealed-auction app proves for awards). It composes — in one
//! cell's slot-caveat program — the guarantees:
//!
//! | Guarantee                            | How this cell enforces it |
//! |--------------------------------------|---------------------------|
//! | a committed submission opens to EXACTLY its piece | the seal binds `(artist, piece, nonce)` under collision-resistance — a swapped piece hashes to a different seal, not in the board |
//! | no reveal before the call closes     | the REVEAL phase gate (`PHASE` lifecycle) |
//! | a non-submitted artist cannot be featured | only committed (then revealed) pieces enter the revealed set |
//! | a committed submission cannot be swapped | each commit slot is `WriteOnce` — an EXECUTOR REFUSAL (the anti-tamper tooth) |
//! | the call only advances              | `Monotonic(PHASE)` floor + `StrictMonotonic(PHASE)` advance |
//!
//! ## The sealed submission
//!
//! `seal(sub) = BLAKE3_derive_key("dregg-gallery submission v1", artist || piece || nonce)`.
//! Binding (a commitment opens to exactly its piece) and hiding (the nonce blinds
//! the piece digest). Collision-resistance is the assumption the binding rests on.
//!
//! ## The commit phase is ON-LEDGER (the deos floor)
//!
//! A gallery is a **factory-born sovereign cell** ([`gallery_factory_descriptor`])
//! whose installed [`CellProgram`] ([`gallery_cell_program`]) IS the curation
//! policy, re-checked by the verified executor on every turn that touches it:
//!
//!   * [`PHASE_SLOT`] — the lifecycle phase code (`SUBMISSION=0 -> REVEAL=1 ->
//!     CURATED=2`). `Monotonic` floor (every method) + `StrictMonotonic` (scoped to
//!     the phase-advancing methods `close_submissions` / `curate`) — the call only
//!     ADVANCES, never rewinds, never re-fires.
//!   * `SUBMIT_BASE + i` — the i-th artist's sealed submission. Each `WriteOnce` — a
//!     sealed piece is FROZEN the instant it is committed (the anti-tamper tooth, an
//!     EXECUTOR REFUSAL). The [`Submission::seal`] digest is the value written.
//!   * [`CURATOR_SLOT`] — the curating party (`WriteOnce`, bound at seed).
//!     [`FEATURED_SLOT`] / [`FEATURED_HASH_SLOT`] — written at curate (`WriteOnce` —
//!     the featured choice freezes once announced).
//!
//! The in-process [`Gallery`] / [`Submission`] commit-reveal state machine below is
//! the executable witness of the commit-reveal CRYPTO; the on-ledger cell is the
//! deos floor that makes "you cannot swap a committed submission" a real executor
//! refusal.

use std::collections::{BTreeMap, HashSet};

use dregg_app_framework::CellId as DeosCellId;
use dregg_app_framework::{
    AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellAffordance, CellMode, CellProgram,
    ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect, EmbeddedExecutor, Event,
    FactoryDescriptor, FieldElement, FireExecuteError, GatedAffordance, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt,
    canonical_program_vk, field_from_bytes, field_from_u64, hex_encode_32, symbol,
};

/// The deos-view CARD: the app's UI as a renderer-independent `deos.ui.*` view-tree.
pub mod card;
/// The CELLS-AS-SERVICE-OBJECTS face: a typed `InterfaceDescriptor` + `invoke()`
/// method dispatch over the gallery lifecycle.
pub mod service;

/// An artist/piece id, restricted to the low byte the in-process model indexes by.
pub type ArtistId = u8;

/// A 32-byte sealed commitment.
pub type Seal = [u8; 32];

// ---------------------------------------------------------------------------
// The sealed submission and its commitment
// ---------------------------------------------------------------------------

/// A sealed submission: the artist, the `piece` digest (a content-addressed hash
/// of the artwork), and a private `nonce` that blinds the commitment. `piece` and
/// `nonce` are secret until reveal; only [`Submission::seal`] is public during the
/// submission phase.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Submission {
    /// The artist placing the submission.
    pub artist: ArtistId,
    /// The piece digest — a content hash of the artwork (the thing displayed).
    pub piece: u64,
    /// The blinding nonce — secret; gives the commitment hiding.
    pub nonce: u64,
}

impl Submission {
    /// Construct a submission.
    pub fn new(artist: ArtistId, piece: u64, nonce: u64) -> Self {
        Self {
            artist,
            piece,
            nonce,
        }
    }

    /// The sealed commitment — `BLAKE3(artist || piece || nonce)`. Binding (opens to
    /// exactly its piece) and hiding (the nonce blinds the piece).
    pub fn seal(&self) -> Seal {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-gallery submission v1");
        hasher.update(&[self.artist]);
        hasher.update(&self.piece.to_le_bytes());
        hasher.update(&self.nonce.to_le_bytes());
        *hasher.finalize().as_bytes()
    }
}

// ---------------------------------------------------------------------------
// The gallery phase + state machine
// ---------------------------------------------------------------------------

/// The gallery phase. Reveals bind only in `Reveal`; curation fires only in
/// `Reveal`; `Curated` is terminal. The `Submission -> Reveal -> Curated` ordering
/// is the curation phase gate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    /// Collecting sealed submissions; reveals are rejected.
    Submission,
    /// Submission phase closed; reveals accepted, curation may fire.
    Reveal,
    /// The featured piece has been chosen; terminal.
    Curated,
}

/// Errors from the gallery curation protocol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GalleryError {
    /// A submission was attempted outside the submission phase (no late entries).
    NotSubmissionPhase,
    /// A reveal/curate was attempted while still submitting (no reveal before close).
    NotRevealPhase,
    /// The gallery is already curated (terminal).
    AlreadyCurated,
    /// The revealed piece's seal is not among the committed seals — a non-submitted
    /// artist, or a swap whose changed piece no longer matches its commitment.
    NotSubmitted,
    /// No valid reveals were collected, so there is nothing to feature.
    NothingToFeature,
}

impl std::fmt::Display for GalleryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotSubmissionPhase => {
                write!(f, "submission attempted outside the submission phase")
            }
            Self::NotRevealPhase => write!(f, "reveal/curate attempted before submissions closed"),
            Self::AlreadyCurated => write!(f, "the gallery is already curated"),
            Self::NotSubmitted => write!(
                f,
                "the revealed piece was not among the committed submissions"
            ),
            Self::NothingToFeature => write!(f, "no valid reveals collected; nothing to feature"),
        }
    }
}

impl std::error::Error for GalleryError {}

/// A sealed-submission gallery. The public coordination state: who curates
/// (`curator`), the collected sealed `submissions`, the `phase`, and the
/// `revealed` pieces (gathered in the reveal phase). The secret `(piece, nonce)` of
/// an unrevealed submission is NOT here — only its seal.
#[derive(Clone, Debug)]
pub struct Gallery {
    /// The curating party (picks the featured piece).
    pub curator: ArtistId,
    /// The sealed commitments collected during the submission phase (a set —
    /// membership is the only query, so a `HashSet` makes the reveal-time check O(1)).
    pub submissions: HashSet<Seal>,
    /// The current phase.
    pub phase: Phase,
    /// The validly-revealed submissions, keyed by seal so a seal reveals at most once.
    revealed: BTreeMap<Seal, Submission>,
}

impl Gallery {
    /// Open a fresh gallery in the submission phase.
    pub fn new(curator: ArtistId) -> Self {
        Self {
            curator,
            submissions: HashSet::new(),
            phase: Phase::Submission,
            revealed: BTreeMap::new(),
        }
    }

    /// **Submission phase** — append a sealed commitment. Legal ONLY in the
    /// submission phase (no late entries after the call closes).
    pub fn submit(&mut self, seal: Seal) -> Result<(), GalleryError> {
        if self.phase != Phase::Submission {
            return Err(GalleryError::NotSubmissionPhase);
        }
        self.submissions.insert(seal);
        Ok(())
    }

    /// Close the submission phase, opening reveals (`Submission -> Reveal`).
    pub fn close_submissions(&mut self) {
        if self.phase == Phase::Submission {
            self.phase = Phase::Reveal;
        }
    }

    /// Whether a submission's reveal would be valid: the gallery is in the reveal
    /// phase AND the submission's seal is among the committed seals (the two teeth:
    /// phase gate + membership gate).
    pub fn valid_reveal(&self, sub: &Submission) -> bool {
        self.phase == Phase::Reveal && self.submissions.contains(&sub.seal())
    }

    /// **Reveal phase** — open a submission. Accepted iff [`Gallery::valid_reveal`]
    /// holds. A non-submitted artist (or a swapper whose changed piece no longer
    /// matches its seal) is rejected with [`GalleryError::NotSubmitted`]. On success
    /// the piece joins the revealed set.
    pub fn reveal(&mut self, sub: Submission) -> Result<(), GalleryError> {
        match self.phase {
            Phase::Submission => return Err(GalleryError::NotRevealPhase),
            Phase::Curated => return Err(GalleryError::AlreadyCurated),
            Phase::Reveal => {}
        }
        let seal = sub.seal();
        if !self.submissions.contains(&seal) {
            return Err(GalleryError::NotSubmitted);
        }
        self.revealed.insert(seal, sub);
        Ok(())
    }

    /// The featured piece among the validly-revealed submissions — here the piece
    /// with the maximal `piece` digest (a deterministic, jury-free default; a real
    /// deployment would score on merit). `None` if no valid reveals were collected.
    pub fn featured(&self) -> Option<Submission> {
        self.revealed.values().copied().max_by_key(|s| s.piece)
    }

    /// **Curate** — pick the featured piece (top revealed) and mark the gallery
    /// `Curated`. Fails if submissions have not closed (`NotRevealPhase`) or no valid
    /// reveals were collected (`NothingToFeature`). The featured piece is provably
    /// among the submitted (then revealed) parties.
    pub fn curate(&mut self) -> Result<Submission, GalleryError> {
        if self.phase != Phase::Reveal {
            return Err(GalleryError::NotRevealPhase);
        }
        let featured = self.featured().ok_or(GalleryError::NothingToFeature)?;
        self.phase = Phase::Curated;
        Ok(featured)
    }
}

// =============================================================================
// THE ON-LEDGER FLOOR — the gallery as a factory-born sovereign cell.
// =============================================================================
//
// The original submission board would be an in-process `BTreeMap<Seal>` — the
// anti-tamper tooth living in a Rust membership check. Here the gallery is a
// factory-born cell whose installed `CellProgram` IS the curation policy,
// re-checked by the verified executor on EVERY touching turn — so "you cannot
// swap a committed submission" becomes an EXECUTOR REFUSAL (`WriteOnce`), and
// "the call only advances" becomes an EXECUTOR REFUSAL (`StrictMonotonic`).

/// Slot 0 — `PHASE`. The curation lifecycle phase code (`SUBMISSION=0 -> REVEAL=1
/// -> CURATED=2`). `Monotonic` floor + `StrictMonotonic` advance on
/// `close_submissions` / `curate` — the call only advances, never rewinds, never
/// re-fires.
pub const PHASE_SLOT: usize = 0;

/// Slot 1 — `CURATOR`. The curating party's identity scalar. `WriteOnce` — bound at
/// seed, frozen for the life of the gallery.
pub const CURATOR_SLOT: usize = 1;

/// Slot 2 — `FEATURED`. The featured artist's identity scalar, written at curate.
/// `WriteOnce` — the choice freezes once announced.
pub const FEATURED_SLOT: usize = 2;

/// Slot 3 — `FEATURED_HASH`. The featured piece's seal, written at curate.
/// `WriteOnce` — the choice freezes once announced.
pub const FEATURED_HASH_SLOT: usize = 3;

/// The first submission-board slot. Artist `i`'s sealed submission lives at
/// `SUBMIT_BASE + i`, each carrying a `WriteOnce` caveat — a committed sealed
/// submission is FROZEN forever (the anti-tamper tooth: you cannot swap a committed
/// piece). The [`Submission::seal`] digest is the value written.
pub const SUBMIT_BASE: usize = 4;

/// How many sealed-submission slots fit on a single gallery cell.
pub const SUBMIT_CAPACITY: usize = dregg_cell::state::STATE_SLOTS - SUBMIT_BASE;

/// The slot index of artist `i`'s sealed submission.
pub fn submit_slot(i: usize) -> usize {
    SUBMIT_BASE + i
}

/// `PHASE` codes — strictly increasing, so the curation lifecycle is one-way.
pub const PHASE_SUBMISSION: u64 = 0;
pub const PHASE_REVEAL: u64 = 1;
pub const PHASE_CURATED: u64 = 2;

/// Factory VK we publish for the gallery factory.
pub const GALLERY_FACTORY_VK: [u8; 32] = *b"starbridge-gallery-curate-factry";

/// The perpetual gallery invariants (the `Always` case) — also flattened into the
/// descriptor's `state_constraints` for constructor transparency. These hold on
/// EVERY touching turn, in EVERY phase:
///
///   * the **anti-tamper** board: each submission slot is `WriteOnce` — a sealed
///     piece is frozen the instant it is committed (swapping a committed submission
///     is REFUSED, the headline tooth);
///   * `CURATOR` / `FEATURED` / `FEATURED_HASH` are `WriteOnce` — the curator is
///     bound once at seed; the featured choice freezes once announced;
///   * the **anti-rollback** phase floor: `Monotonic(PHASE)` — the phase may never
///     REWIND on ANY method, so the lifecycle is one-way even on the factory-born
///     cell. This is the NON-strict floor: a method that legitimately leaves PHASE
///     unchanged (every `submit` during SUBMISSION) still passes. The strictly-
///     increasing advance is the phase-advancing methods' extra clause
///     (`StrictMonotonic(PHASE)` in the `close_submissions` / `curate` cases of
///     [`gallery_cell_program`]).
fn gallery_invariants() -> Vec<StateConstraint> {
    let mut cs = Vec::with_capacity(4 + SUBMIT_CAPACITY);
    cs.push(StateConstraint::WriteOnce {
        index: CURATOR_SLOT as u8,
    });
    cs.push(StateConstraint::WriteOnce {
        index: FEATURED_SLOT as u8,
    });
    cs.push(StateConstraint::WriteOnce {
        index: FEATURED_HASH_SLOT as u8,
    });
    // the anti-rollback phase floor — the phase may never rewind (non-strict, so a
    // PHASE-unchanged submit still passes). The strict no-advance bite lives in the
    // phase-advancing method cases.
    cs.push(StateConstraint::Monotonic {
        index: PHASE_SLOT as u8,
    });
    // the anti-tamper submission board — every submission slot is write-once.
    for i in 0..SUBMIT_CAPACITY {
        cs.push(StateConstraint::WriteOnce {
            index: submit_slot(i) as u8,
        });
    }
    cs
}

/// The `CellProgram` installed on every gallery cell — a method-dispatched `Cases`
/// program whose `Always` case carries the perpetual invariants ([`gallery_invariants`]:
/// the `WriteOnce` submission board + result registers) and whose phase-advancing
/// cases bind the `StrictMonotonic(PHASE)` lifecycle tooth:
///
///   * **`Always`**: the anti-tamper board (`WriteOnce(SUBMIT_BASE + i)`) + the
///     result registers (`WriteOnce(CURATOR/FEATURED/FEATURED_HASH)`) — every turn.
///   * **`submit`**: no extra clause — a submit writes a fresh submission slot, which
///     the `Always` `WriteOnce` governs (a re-submit to a taken slot is REFUSED). The
///     phase is NOT advanced (many artists submit in SUBMISSION).
///   * **`close_submissions`**: `StrictMonotonic(PHASE)` — advance SUBMISSION ->
///     REVEAL (a rewind or no-advance is REFUSED).
///   * **`reveal`**: no extra clause — a reveal in the REVEAL phase records its piece;
///     the phase is not advanced.
///   * **`curate`**: `StrictMonotonic(PHASE)` — advance REVEAL -> CURATED, writing
///     `FEATURED` / `FEATURED_HASH` (frozen by the `Always` `WriteOnce`).
///
/// The program is method-dispatching, so an unknown method is default-denied
/// (`NoTransitionCaseMatched`).
pub fn gallery_cell_program() -> CellProgram {
    CellProgram::Cases(vec![
        // ── invariants: every transition, every method ──────────────────
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: gallery_invariants(),
        },
        // ── submit: write a fresh submission slot (Always WriteOnce governs it) ─
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("submit"),
            },
            constraints: vec![],
        },
        // ── close_submissions: advance SUBMISSION -> REVEAL (StrictMonotonic) ─
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("close_submissions"),
            },
            constraints: vec![StateConstraint::StrictMonotonic {
                index: PHASE_SLOT as u8,
            }],
        },
        // ── reveal: record a revealed piece (no phase change) ────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("reveal"),
            },
            constraints: vec![],
        },
        // ── curate: advance REVEAL -> CURATED (StrictMonotonic) ──────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("curate"),
            },
            constraints: vec![StateConstraint::StrictMonotonic {
                index: PHASE_SLOT as u8,
            }],
        },
    ])
}

/// The descriptor's flat `state_constraints` — exactly the predicate the executor
/// installs as the born cell's `CellProgram` and re-checks **unconditionally** on
/// every turn. These are the `Always`-true invariants only — the `WriteOnce`
/// submission board + result registers (the anti-tamper tooth) + the `Monotonic`
/// floor. The phase-scoped `StrictMonotonic(PHASE)` lives in the
/// `close_submissions` / `curate` cases of [`gallery_cell_program`].
fn gallery_state_constraints() -> Vec<StateConstraint> {
    gallery_invariants()
}

/// Canonical child-program VK for gallery cells.
pub fn gallery_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&gallery_cell_program())
}

/// Build the gallery-cell [`FactoryDescriptor`]. The cell is born empty; the seed
/// turn binds `CURATOR` and sets `PHASE = SUBMISSION`; artists then commit sealed
/// submissions into the `WriteOnce` board, the curator closes submissions, artists
/// reveal, and the curator curates — every step gated by the curation policy
/// installed here FOR LIFE.
pub fn gallery_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: GALLERY_FACTORY_VK,
        child_program_vk: Some(gallery_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(gallery_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: gallery_state_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(1_000_000),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![gallery_factory_descriptor()]
}

// =============================================================================
// The deos-native surface — the GALLERY as a composed `DeosApp`.
// =============================================================================
//
// The lifecycle operations are ONE [`DeosApp`] ([`gallery_app`] below); the framework
// wires the rest — per-viewer projection, web-of-cells publish (the GALLERY cell IS a
// `dregg://` sturdyref), per-viewer rehydration, the generated
// `<dregg-affordance-surface>` component, and the manifest.
//
// **The seam is closed** — a TWO-TEMPO fire (mirror sealed-auction / escrow-market).
// The state-mutating operations (`submit`, `close_submissions`, `reveal`, `curate`)
// are [`GatedAffordance`]s carrying a live-state PHASE PRECONDITION; the FULL gallery
// program ([`gallery_cell_program`]: the `WriteOnce` submission board + the
// `Monotonic`/`StrictMonotonic(PHASE)` lifecycle) is INSTALLED on the seeded gallery
// cell ([`seed_gallery`]) and RE-ENFORCED by the executor on every touching turn:
//
//   1. the deos PRECONDITION gate (the cap-gate `is_attenuation` AND the live-state
//      PHASE precondition `CellProgram::evaluate`) decides the button's verdict IN-BAND
//      — nothing submitted on a miss (anti-ghost; the htmx reactivity rides this);
//   2. [`fire_submit`] / [`fire_close_submissions`] / [`fire_reveal`] / [`fire_curate`]
//      submit the FULL multi-effect turn (built from the cell's LIVE state), and the
//      executor RE-ENFORCES the installed program — so SWAPPING a committed submission
//      (`WriteOnce`) and a PHASE that rewinds / does-not-advance (`StrictMonotonic`) are
//      REAL executor refusals in the SUBMISSION path (see `tests/deos_seam.rs`).

/// The gallery rights tiers, ON THE REAL ATTENUATION LATTICE:
///
///   - a VISITOR (the public / an auditor browsing the gallery) holds
///     [`AuthRequired::Signature`] — the narrow read tier: `view_gallery` and nothing
///     else;
///   - an ARTIST (a creator entering work) holds [`AuthRequired::Either`] — it can
///     `submit` (seal a piece) and `reveal` (open it) AND view;
///   - the CURATOR (the party running the call) holds [`AuthRequired::None`]/root — it
///     can `close_submissions` (close the call) and `curate` (feature a piece) on top
///     of everything an artist can do.
///
/// So `Signature ⊂ Either ⊂ None` IS the visitor ⊂ artist ⊂ curator ladder.
pub const VISITOR_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The artist rights tier (sig-or-proof — submit + reveal + view). See [`VISITOR_RIGHTS`].
pub const ARTIST_RIGHTS: AuthRequired = AuthRequired::Either;
/// The curator rights tier (root — close + curate + all). See [`VISITOR_RIGHTS`].
pub const CURATOR_RIGHTS: AuthRequired = AuthRequired::None;

/// The **life-of-cell gallery program** the executor re-enforces on every touching
/// turn — the canonical method-dispatched [`gallery_cell_program`]. This is the SAME
/// program a factory-born gallery cell carries FOR LIFE (the one
/// `tests/factory_birth.rs` proves bites on the executor); installed by
/// [`seed_gallery`] so the gated fires re-enforce it.
pub fn gallery_program() -> CellProgram {
    gallery_cell_program()
}

/// A live-state precondition: the gallery is in `phase`. A real [`CellProgram`] read
/// against the cell's current state, so a button is DARK in the wrong phase and LIT
/// in the right one (the htmx tooth).
fn phase_precondition(phase: u64) -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: PHASE_SLOT as u8,
        value: field_from_u64(phase),
    }])
}

/// The `submit` precondition — the gallery is in SUBMISSION (`PHASE == SUBMISSION`).
pub fn submit_precondition() -> CellProgram {
    phase_precondition(PHASE_SUBMISSION)
}

/// The `reveal` precondition — the gallery is in REVEAL (`PHASE == REVEAL`).
pub fn reveal_precondition() -> CellProgram {
    phase_precondition(PHASE_REVEAL)
}

/// The curator's `close_submissions` precondition — the gallery is in SUBMISSION.
pub fn close_submissions_precondition() -> CellProgram {
    phase_precondition(PHASE_SUBMISSION)
}

/// The curator's `curate` precondition — the gallery is in REVEAL.
pub fn curate_precondition() -> CellProgram {
    phase_precondition(PHASE_REVEAL)
}

/// **The GALLERY as a composed [`DeosApp`]** — the whole interaction surface, on the
/// deos bones. The gallery cell is the agent's OWN cell (`cipherclerk.cell_id()`) so
/// fires execute against the seeded embedded ledger.
///
/// Five operations on the GALLERY cell, on the visitor ⊂ artist ⊂ curator rights
/// ladder:
///
///   - `view_gallery` — a cap-only affordance (a VISITOR browses): `Signature`, an
///     `EmitEvent`;
///   - `submit` — a [`GatedAffordance`] (an ARTIST seals a piece): `Either`, a
///     SUBMISSION precondition; the real fire ([`fire_submit`]) writes the next free
///     `WriteOnce` submission slot (read from live state), re-enforced by the executor
///     (swapping a committed submission is REFUSED — the anti-tamper tooth);
///   - `close_submissions` — a [`GatedAffordance`] (the CURATOR closes the call):
///     `None`, a SUBMISSION precondition; advances `PHASE -> REVEAL` (`StrictMonotonic`);
///   - `reveal` — a [`GatedAffordance`] (an ARTIST opens its piece): `Either`, a REVEAL
///     precondition; records the revealed piece;
///   - `curate` — a [`GatedAffordance`] (the CURATOR features a piece): `None`, a
///     REVEAL precondition; advances `PHASE -> CURATED` and writes `FEATURED` /
///     `FEATURED_HASH`.
///
/// The gallery cell is published into the web-of-cells at the visitor tier and is
/// discoverable under `gallery` / `art`.
///
/// Seed the cell's program + SUBMISSION state with [`seed_gallery`] so the gated
/// fires have a live state and the executor re-enforces the program.
pub fn gallery_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let cell = cipherclerk.cell_id();

    // `view_gallery` — a visitor browses. Cap-only.
    let view = CellAffordance::new(
        "view_gallery",
        VISITOR_RIGHTS,
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("gallery-read"), vec![]),
        },
    );
    // `submit` — an ARTIST seals a piece. The decisive effect is a representative
    // submission-slot write; gated on the SUBMISSION precondition. The actual fire
    // ([`fire_submit`]) writes the next free submission slot (read from live state),
    // re-enforced by the `WriteOnce` board (swapping a committed submission is REFUSED).
    let submit = GatedAffordance::new(
        CellAffordance::new(
            "submit",
            ARTIST_RIGHTS,
            Effect::SetField {
                cell,
                index: submit_slot(0),
                value: field_from_u64(0),
            },
        ),
        submit_precondition(),
    );
    // `close_submissions` — the CURATOR closes the call. The decisive effect advances
    // PHASE -> REVEAL; gated on the SUBMISSION precondition. The executor re-enforces
    // `StrictMonotonic(PHASE)` (a rewind / no-advance is refused).
    let close = GatedAffordance::new(
        CellAffordance::new(
            "close_submissions",
            CURATOR_RIGHTS,
            Effect::SetField {
                cell,
                index: PHASE_SLOT,
                value: field_from_u64(PHASE_REVEAL),
            },
        ),
        close_submissions_precondition(),
    );
    // `reveal` — an ARTIST opens its piece. The decisive effect emits the revealed
    // piece; gated on the REVEAL precondition.
    let reveal = GatedAffordance::new(
        CellAffordance::new(
            "reveal",
            ARTIST_RIGHTS,
            Effect::EmitEvent {
                cell,
                event: Event::new(symbol("gallery-reveal"), vec![]),
            },
        ),
        reveal_precondition(),
    );
    // `curate` — the CURATOR features a piece. The decisive effect advances PHASE ->
    // CURATED; gated on the REVEAL precondition. The executor re-enforces
    // `StrictMonotonic(PHASE)` + the `WriteOnce(FEATURED/FEATURED_HASH)` registers.
    let curate = GatedAffordance::new(
        CellAffordance::new(
            "curate",
            CURATOR_RIGHTS,
            Effect::SetField {
                cell,
                index: PHASE_SLOT,
                value: field_from_u64(PHASE_CURATED),
            },
        ),
        curate_precondition(),
    );

    DeosApp::builder("gallery", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["gallery".into(), "art".into()])
        .cell(
            DeosCell::new(cell, "gallery")
                .affordance(view)
                .gated(submit)
                .gated(close)
                .gated(reveal)
                .gated(curate)
                .publish(VISITOR_RIGHTS),
        )
        .build()
}

/// **Seed the GALLERY cell** so the gated fires have live state + the program bites:
/// install the full [`gallery_program`] on the seeded gallery cell (so the executor
/// re-enforces it on every touching turn), then bind the genesis state directly into
/// the embedded ledger — bind `CURATOR` (`WriteOnce`, frozen after) and set
/// `PHASE = SUBMISSION` (submission slots empty).
///
/// After seeding, the gallery is in SUBMISSION with a bound curator — a real `(old,
/// new)` baseline against which `submit` writes the board. Returns the seeded curator
/// scalar.
pub fn seed_gallery(executor: &EmbeddedExecutor, curator: &str) -> FieldElement {
    let cell = executor.cell_id();
    executor.install_program(cell, gallery_program());
    let curator_f = field_from_bytes(curator.as_bytes());
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state.set_field(CURATOR_SLOT, curator_f);
            c.state
                .set_field(PHASE_SLOT, field_from_u64(PHASE_SUBMISSION));
        }
    });
    curator_f
}

/// **`submit` effects** — write the sealed commitment `seal` into the next free
/// submission slot. The ONE coherent transition the installed invariants admit (a
/// fresh `WriteOnce` slot, the phase unchanged). THIS is the turn [`fire_submit`]
/// submits.
pub fn submit_effects(cell: DeosCellId, slot: usize, seal: &Seal) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: slot,
            value: *seal,
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("gallery-submit"), vec![*seal]),
        },
    ]
}

/// **`close_submissions` effects** — advance `PHASE -> REVEAL`, emitting
/// `gallery-closed`. THIS is the turn [`fire_close_submissions`] submits; the executor
/// re-enforces `StrictMonotonic(PHASE)`.
pub fn close_submissions_effects(cell: DeosCellId) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: PHASE_SLOT,
            value: field_from_u64(PHASE_REVEAL),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("gallery-closed"), vec![]),
        },
    ]
}

/// **`reveal` effects** — record the revealed `(artist, piece)` of an opened
/// submission (the phase is not advanced). THIS is the turn [`fire_reveal`] submits.
pub fn reveal_effects(cell: DeosCellId, artist: FieldElement, piece: u64) -> Vec<Effect> {
    vec![Effect::EmitEvent {
        cell,
        event: Event::new(
            symbol("gallery-reveal"),
            vec![artist, field_from_u64(piece)],
        ),
    }]
}

/// **`curate` effects** — advance `PHASE -> CURATED`, write `FEATURED` /
/// `FEATURED_HASH` (frozen by the `Always` `WriteOnce`), and emit `gallery-curated`.
/// THIS is the turn [`fire_curate`] submits; the executor re-enforces
/// `StrictMonotonic(PHASE)` + `WriteOnce(FEATURED/FEATURED_HASH)`.
pub fn curate_effects(
    cell: DeosCellId,
    featured: FieldElement,
    featured_hash: &Seal,
) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: FEATURED_SLOT,
            value: featured,
        },
        Effect::SetField {
            cell,
            index: FEATURED_HASH_SLOT,
            value: *featured_hash,
        },
        Effect::SetField {
            cell,
            index: PHASE_SLOT,
            value: field_from_u64(PHASE_CURATED),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("gallery-curated"), vec![featured]),
        },
    ]
}

/// The next free submission slot on the gallery cell's live `state` — the lowest
/// `SUBMIT_BASE + i` whose value is still zero (unwritten). `None` if the board is
/// full. The honest [`fire_submit`] picks this so each submission lands on a fresh
/// `WriteOnce` slot.
pub fn next_free_submit_slot(state: &dregg_cell::state::CellState) -> Option<usize> {
    (0..SUBMIT_CAPACITY)
        .map(submit_slot)
        .find(|&slot| state.fields[slot] == [0u8; 32])
}

/// **Fire `submit`** — the deos cap∧state PRECONDITION gate (cap ⊇ Either AND the
/// gallery is in SUBMISSION), then the FULL submit turn ([`submit_effects`]) the
/// executor re-enforces the gallery program on. The fire reads the cell's LIVE state
/// to pick the next free submission slot, so two artists never collide on a slot; the
/// `WriteOnce` board then FREEZES the committed submission (a later swap is REFUSED —
/// the anti-tamper tooth). Anti-ghost both ways. Use [`seed_gallery`] first.
pub fn fire_submit(
    app: &DeosApp,
    held: &AuthRequired,
    seal: Seal,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let target = cell.cell();
    cell.fire_gated_through_executor_with("submit", held, cipherclerk, executor, move |live| {
        let slot = next_free_submit_slot(live).unwrap_or_else(|| submit_slot(0));
        submit_effects(target, slot, &seal)
    })
}

/// **Fire `close_submissions`** — the deos cap∧state PRECONDITION gate (cap ⊇ None AND
/// the gallery is in SUBMISSION), then the FULL close turn
/// ([`close_submissions_effects`]). The executor re-enforces `StrictMonotonic(PHASE)`
/// (SUBMISSION -> REVEAL). Use after the submissions.
pub fn fire_close_submissions(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let target = cell.cell();
    cell.fire_gated_through_executor_with(
        "close_submissions",
        held,
        cipherclerk,
        executor,
        move |_live| close_submissions_effects(target),
    )
}

/// **Fire `reveal`** — the deos cap∧state PRECONDITION gate (cap ⊇ Either AND the
/// gallery is in REVEAL), then the FULL reveal turn ([`reveal_effects`]) recording the
/// opened piece. Use after a successful [`fire_close_submissions`].
pub fn fire_reveal(
    app: &DeosApp,
    held: &AuthRequired,
    artist: FieldElement,
    piece: u64,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let target = cell.cell();
    cell.fire_gated_through_executor_with("reveal", held, cipherclerk, executor, move |_live| {
        reveal_effects(target, artist, piece)
    })
}

/// **Fire `curate`** — the deos cap∧state PRECONDITION gate (cap ⊇ None AND the
/// gallery is in REVEAL), then the FULL curate turn ([`curate_effects`]) the executor
/// re-enforces the gallery program on. Advances `PHASE -> CURATED` and writes the
/// `FEATURED` / `FEATURED_HASH` (frozen by `WriteOnce`). `StrictMonotonic(PHASE)`
/// re-enforces the one-way advance. Use after the reveals.
pub fn fire_curate(
    app: &DeosApp,
    held: &AuthRequired,
    featured: FieldElement,
    featured_hash: Seal,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let target = cell.cell();
    cell.fire_gated_through_executor_with("curate", held, cipherclerk, executor, move |_live| {
        curate_effects(target, featured, &featured_hash)
    })
}

/// Read a `u64` from the last 8 big-endian bytes of a field element.
pub fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

// =============================================================================
// StarbridgeAppContext mount.
// =============================================================================

/// Web-constants module (single source of truth for the JS surface).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("gallery")
        .slot("PHASE_SLOT", PHASE_SLOT as u64)
        .slot("CURATOR_SLOT", CURATOR_SLOT as u64)
        .slot("FEATURED_SLOT", FEATURED_SLOT as u64)
        .slot("FEATURED_HASH_SLOT", FEATURED_HASH_SLOT as u64)
        .slot("SUBMIT_BASE", SUBMIT_BASE as u64)
        .slot("SUBMIT_CAPACITY", SUBMIT_CAPACITY as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&GALLERY_FACTORY_VK))
        .topic("SUBMIT", "gallery-submit")
        .topic("CLOSED", "gallery-closed")
        .topic("REVEAL", "gallery-reveal")
        .topic("CURATED", "gallery-curated")
}

/// **Register the gallery starbridge-app** on a shared context — the FLOOR (the
/// factory descriptor whose `state_constraints` ARE the curation policy, installed on
/// every born gallery cell, with the on-ledger `WriteOnce` submission board) AND the
/// deos-native composition surface (the [`DeosApp`], folded into the context's
/// affordance registry). The factory + inspector are where SOUNDNESS lives (swapping a
/// committed submission / rewinding the phase is a real executor refusal on the born
/// cell); the deos surface is the composition skin. Returns the factory VK.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(gallery_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "gallery".into(),
        descriptor: serde_json::json!({
            "component": "dregg-gallery",
            "module": "/starbridge-apps/gallery/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["phase", "curator", "featured", "featured_hash", "submissions"],
            "slot_layout": {
                "phase":         PHASE_SLOT,
                "curator":       CURATOR_SLOT,
                "featured":      FEATURED_SLOT,
                "featured_hash": FEATURED_HASH_SLOT,
                "submit_base":   SUBMIT_BASE,
                "capacity":      SUBMIT_CAPACITY,
            },
            "phase_codes": {
                "submission": PHASE_SUBMISSION,
                "reveal":     PHASE_REVEAL,
                "curated":    PHASE_CURATED,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&gallery_child_program_vk()),
            "methods": ["submit", "close_submissions", "reveal", "curate"],
        }),
    });

    // Mount the deos-native composition surface (the `DeosApp`) on the SAME context.
    register_deos(ctx);

    factory_vk
}

/// **Mount the deos-native surface** ([`gallery_app`]) on a shared context: build the
/// composed [`DeosApp`] from the context's cipherclerk + executor, seed the gallery
/// cell's program + SUBMISSION state (so the gated fires bite), and fold the app into
/// the context's affordance registry ([`DeosApp::register`]). Returns the live
/// [`DeosApp`].
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = gallery_app(ctx.cipherclerk(), ctx.executor());
    seed_gallery(ctx.executor(), "curator");
    app.register(ctx);
    app
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod floor_tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, EmbeddedExecutor};
    use dregg_cell::program::TransitionMeta;
    use dregg_cell::state::CellState;

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [0x6au8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    fn eval_for(
        program: &CellProgram,
        method: &str,
        new: &CellState,
        old: Option<&CellState>,
    ) -> Result<(), dregg_cell::ProgramError> {
        program.evaluate_with_meta(new, old, None, &TransitionMeta::new(symbol(method), 0))
    }

    fn empty() -> CellState {
        CellState::new(0)
    }

    fn submitting() -> CellState {
        let mut s = empty();
        s.fields[CURATOR_SLOT] = field_from_bytes(b"curator");
        s.fields[PHASE_SLOT] = field_from_u64(PHASE_SUBMISSION);
        s
    }

    #[test]
    fn descriptor_is_deterministic() {
        assert_eq!(
            gallery_factory_descriptor().hash(),
            gallery_factory_descriptor().hash()
        );
    }

    #[test]
    fn child_program_vk_is_canonical_recipe() {
        let expected = canonical_program_vk(&gallery_cell_program());
        assert_eq!(gallery_child_program_vk(), expected);
        assert_eq!(
            gallery_factory_descriptor().child_program_vk,
            Some(expected)
        );
    }

    #[test]
    fn factory_bakes_the_submission_board_and_result_caveats() {
        let d = gallery_factory_descriptor();
        // the anti-tamper board: every submission slot is WriteOnce.
        for i in 0..SUBMIT_CAPACITY {
            let idx = submit_slot(i) as u8;
            assert!(
                d.state_constraints.iter().any(|c| matches!(
                    c, StateConstraint::WriteOnce { index } if *index == idx
                )),
                "expected WriteOnce on submission slot {idx}"
            );
        }
        // the result registers freeze once written.
        for idx in [
            CURATOR_SLOT as u8,
            FEATURED_SLOT as u8,
            FEATURED_HASH_SLOT as u8,
        ] {
            assert!(
                d.state_constraints.iter().any(|c| matches!(
                    c, StateConstraint::WriteOnce { index } if *index == idx
                )),
                "expected WriteOnce on result slot {idx}"
            );
        }
        // the StrictMonotonic(PHASE) lifecycle lives in the close_submissions / curate cases.
        let phase_strict = match gallery_cell_program() {
            CellProgram::Cases(cases) => cases.iter().any(|case| {
                matches!(case.guard, TransitionGuard::MethodIs { method } if method == symbol("curate"))
                    && case.constraints.iter().any(|c| matches!(
                        c, StateConstraint::StrictMonotonic { index } if *index == PHASE_SLOT as u8
                    ))
            }),
            _ => false,
        };
        assert!(
            phase_strict,
            "StrictMonotonic(PHASE) missing from the curate case"
        );
    }

    #[test]
    fn a_committed_submission_cannot_be_swapped_the_anti_tamper_tooth() {
        // A committed sealed submission; a turn tries to SWAP it -> WriteOnce rejects.
        let program = gallery_cell_program();
        let sub = Submission::new(7, 50, 9);
        let mut old = submitting();
        old.fields[submit_slot(0)] = sub.seal();
        old.set_nonce(1);
        let mut swap = old.clone();
        swap.fields[submit_slot(0)] = Submission::new(7, 70, 9).seal(); // a different piece
        let err = eval_for(&program, "submit", &swap, Some(&old)).expect_err(
            "swapping a committed sealed submission must be rejected — the anti-tamper tooth",
        );
        assert!(
            matches!(err, dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { index }, ..
            } if index == submit_slot(0) as u8),
            "expected WriteOnce violation on the submission slot, got {err:?}"
        );
    }

    #[test]
    fn a_fresh_submission_to_an_empty_slot_is_accepted() {
        let program = gallery_cell_program();
        let old = submitting();
        let mut new = old.clone();
        new.fields[submit_slot(0)] = Submission::new(7, 50, 9).seal();
        assert!(eval_for(&program, "submit", &new, Some(&old)).is_ok());
    }

    #[test]
    fn the_phase_cannot_rewind_or_stall_on_curate_strictmonotonic() {
        let program = gallery_cell_program();
        let mut old = submitting();
        old.fields[PHASE_SLOT] = field_from_u64(PHASE_REVEAL);
        old.set_nonce(2);
        // a curate that REWINDS the phase (REVEAL -> SUBMISSION) is refused.
        let mut rewind = old.clone();
        rewind.fields[PHASE_SLOT] = field_from_u64(PHASE_SUBMISSION);
        let err = eval_for(&program, "curate", &rewind, Some(&old))
            .expect_err("rewinding the phase must be rejected — the anti-rollback tooth");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::StrictMonotonic { index }
                    | StateConstraint::Monotonic { index }, ..
            } if index == PHASE_SLOT as u8
        ));
        // a curate that does NOT advance (REVEAL -> REVEAL) is also refused (strict).
        let stall = old.clone();
        let err = eval_for(&program, "curate", &stall, Some(&old))
            .expect_err("a no-advance phase must be rejected — StrictMonotonic is strict");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::StrictMonotonic { .. },
                ..
            }
        ));
    }

    #[test]
    fn unknown_method_is_default_denied() {
        let program = gallery_cell_program();
        let err = eval_for(&program, "rig_jury", &submitting(), Some(&empty()))
            .expect_err("an unknown method must be default-denied");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::NoTransitionCaseMatched
        ));
    }

    #[test]
    fn register_installs_factory_and_inspector() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, GALLERY_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("gallery").is_some());
    }
}
