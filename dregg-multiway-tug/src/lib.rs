//! # `dregg-multiway-tug` — a 2-player tug-of-influence card game on the real executor.
//!
//! **Phase 0: the rules on the real dregg executor.** A play is a cap-gated
//! [`spween_dregg::WorldCell`] turn the deployed `EmbeddedExecutor` admits IFF the game
//! teeth pass; an illegal play (an unowned favor, a reused action, a conservation break)
//! is a real [`spween_dregg::WorldError::Refused`]; every committed move is a receipt.
//!
//! The underlying mechanic is derived (mechanics aren't copyrightable) from Hanamikoji
//! (designer Kota Nakayama). This crate ships an ORIGINAL re-theming — "multiway-tug":
//! two players tug over seven **guilds** (influence `[2,2,2,3,3,4,5]`, 21 total) by
//! playing **favor** cards through four once-per-round actions (Secret / Discard / Gift /
//! Competition); win at `>= 11` influence OR `>= 4` guilds controlled.
//!
//! ## The pieces
//!
//! * [`reference`] — the deterministic rules engine. It does not move by itself: a caller
//!   supplies a [`reference::Decision`] to [`reference::Engine::apply`], chosen from
//!   [`reference::Engine::legal_decisions`].
//! * [`state`] — the STATE as a [`dregg_schema`]-allocated Legal layout (16 register
//!   counters/win-registers + 8 used-flags + 14 per-guild scores on the heap) and PLAY TEETH
//!   authored in Lean, emitted as a pinned program artifact, and loaded by Rust.
//! * [`game`] — [`game::MultiwayTug`], the game deployed and driven on a real world-cell.
//! * [`packs`] — **Phase 1, the COLLECTIBLE layer**: a printed favor card is an owned
//!   [`dreggnet_asset`] note, opening a pack is a provably-fair draw ([`packs::CardVault`]).
//! * [`hidden_hand`] — exact-card Poseidon2 openings checked by the executor beside the rules
//!   action in one atomic turn.
//! * [`fold`] — the hidden membership and terminal win leaves on the recursive proof path.
//! * [`surface`] — the playable Offering with public fog and owner-only hand views.
//!
//! ## What the teeth enforce (see [`state`])
//!
//! | rule | tooth |
//! |------|-------|
//! | 21-card conservation (no favor conjured/destroyed) | `SumEquals([counters]) == 21` |
//! | one action per player per round | `HeapAtom::WriteOnce` on each used-flag |
//! | placements never un-placed | `HeapAtom::Monotonic` on each per-guild score |
//! | strict round sequencing | `StrictMonotonic(round_actions)` |
//! | a standing offer must be answered | `pending_kind` `Equals`/`DeltaEquals` per method |
//! | win only at a real threshold | `winner==p ⇒ FieldGte(charm_p,11) ∨ FieldGte(guilds_p,4)` |
//! | scoring only after the round | `FieldGte(round_actions, 12)` |
//! | forged / unknown method | `Cases` method-default-deny (`NoTransitionCaseMatched`) |
//!
//! ## ⚑ I-CUT-YOU-CHOOSE — the seats DECIDE
//!
//! 1. **The Secret is scored** — revealed onto its owner's side before control is computed
//!    ([`reference::Engine::score`]).
//! 2. **The split is the OTHER seat's.** A Gift/Competition only PRESENTS favors into escrow
//!    ([`reference::Decision::Gift`] / [`reference::Decision::Competition`]); the opponent's
//!    [`reference::Decision::Respond`] decides who gets what, and the proposer can never
//!    answer their own cut. The action ORDER is a free choice too — there is no schedule.
//!    A round is 8 actions + 4 responses = 12 committed turns.
//!
//! A response commits under the Lean-emitted `respond_gift` / `respond_comp` case, which is
//! also what may lower the `pending_kind` escrow marker — so the interlock is DEPLOYED teeth,
//! not host bookkeeping.
//!
//! ## Honest scope (per `docs/VERIFIED-GAME-PORTFOLIO.md`)
//!
//! The playable slice includes the Lean-authored rules program, cards-as-assets and fair packs,
//! exact-card witnessed hidden-hand admission, the recursive membership/win leaves, and the
//! per-viewer Offering. The remaining assurance boundary is narrower but real: duplicate
//! consumption is ratcheted by private host state plus fresh replay rather than a dynamic-root /
//! nullifier tooth, witness paths are clear executor inputs rather than succinct per-action
//! proofs, and the reverse `deployed admission -> Lean game move` refinement is not yet closed.

pub mod fold;
pub mod game;
pub mod hidden_hand;
pub mod packs;
mod program_loader;
pub mod reference;
pub mod state;
/// Phase 5 — the [`dreggnet_offerings::Offering`] + the per-player HIDDEN-HAND surface (the
/// guild-lane table, the coordinate-grid hand, the greyed action menu; a play is a real turn).
pub mod surface;

pub use game::MultiwayTug;
pub use hidden_hand::{
    BlindPick, BlindPickError, HandMembershipVerifier, HandTree, HiddenHandLedger, PathLevel,
    PickPhase, PlayProof, check_play, membership_program, membership_registry,
};
pub use packs::{
    CardDraw, CardItem, CardRarity, CardVault, Pack, PackError, reverify_pack, roll_pack,
};
pub use reference::{
    ActionKind, Decision, Engine, MoveError, OfferShape, PendingOffer, Player, Projection,
    ResolvedMove,
};
pub use state::Deployment;
pub use surface::{TugOffering, TugPrivateMatchRecord, TugSession};
