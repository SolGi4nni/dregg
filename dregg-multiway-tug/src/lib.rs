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
//! * [`reference`] — the deterministic oracle engine (a faithful model of the round with
//!   the two rule gaps FIXED and the per-turn draw added). It is the mover.
//! * [`state`] — the STATE as a [`dregg_schema`]-allocated Legal layout (16 register
//!   counters/win-registers + 8 used-flags + 14 per-guild scores on the heap) and the
//!   PLAY TEETH as a hand-rolled [`dregg_app_framework::CellProgram::Cases`].
//! * [`game`] — [`game::MultiwayTug`], the game deployed and driven on a real world-cell.
//! * [`packs`] — **Phase 1, the COLLECTIBLE layer**: a printed favor card is an owned
//!   [`dreggnet_asset`] note, opening a pack is a provably-fair draw ([`packs::CardVault`]).
//!
//! ## What the teeth enforce (see [`state`])
//!
//! | rule | tooth |
//! |------|-------|
//! | 21-card conservation (no favor conjured/destroyed) | `SumEquals([counters]) == 21` |
//! | one action per player per round | `HeapAtom::WriteOnce` on each used-flag |
//! | placements never un-placed | `HeapAtom::Monotonic` on each per-guild score |
//! | strict round sequencing | `StrictMonotonic(round_actions)` |
//! | win only at a real threshold | `winner==p ⇒ FieldGte(charm_p,11) ∨ FieldGte(guilds_p,4)` |
//! | forged / unknown method | `Cases` method-default-deny (`NoTransitionCaseMatched`) |
//!
//! ## The two fixed rule gaps
//!
//! 1. **The Secret is scored** — revealed onto its owner's side before control is computed
//!    ([`reference::Engine::score`]).
//! 2. **The opponent's blind pick is a real choice** — the actor only PRESENTS the
//!    Gift/Competition cards; the opponent decides who keeps what
//!    ([`reference::opponent_gift_pick`] / [`reference::opponent_comp_pick`]).
//!
//! ## Honest scope (per `docs/VERIFIED-GAME-PORTFOLIO.md`)
//!
//! Phase 0 is rules-on-executor with the hand hidden only by NON-REVEAL on a trusted host
//! (the counters are public; card identities live in the reference mover). **Phase 1** is
//! BUILT ([`packs`]): the collectible layer — cards as owned `dreggnet-asset` notes +
//! provably-fair packs. The named next phases: **2** the zk
//! HIDDEN-HAND — `Witnessed{MerkleMembership}` proving a play is from the committed hand +
//! the opponent pick as a sealed-auction commit-reveal (opponent-SIGNED); **3** the STARK
//! fold (a Custom AIR leaf → `prove_turn_chain_recursive`, Lane-D-gated); **4** the Lean
//! refinement (the AIR REFINES `applyTurn`); **5** the Offering + frontends. The schema
//! carries the simple state-shape; these hand-rolled `Cases` carry the play validity that
//! goes beyond the five archetypes.

pub mod fold;
pub mod game;
pub mod hidden_hand;
pub mod packs;
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
pub use reference::{ActionKind, Engine, Player, Projection, ResolvedMove};
pub use state::Deployment;
pub use surface::{TugOffering, TugSession};
