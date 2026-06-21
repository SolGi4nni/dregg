//! # starbridge-first-room — THE FIRST ROOM of the living world (the weld, runnable).
//!
//! dregg read as a WORLD: a persistent place whose inhabitants — human or agent — act ONLY through a
//! MANDATE proven safe-forever. This crate stands up the FIRST ROOM, end to end and runnable, by
//! WELDING the room organs that already landed (it rebuilds none of them):
//!
//!   * the COLONIST'S JOB — `starbridge_compartment_workflow_mandate::colonist_job`: a DAG of steps
//!     (`gather → make → hand-off`) with prerequisites, a per-step clearance, and a spend budget it
//!     provably can't exceed. Three biting legs (DAG/no-skip · clearance · spend-budget), each a real
//!     executor refusal. (The mandate law + the job instance — organs 1 & 2.)
//!   * the ESCROW ECONOMY — `starbridge_escrow_market`: a factory-born escrow cell driven
//!     `list → fund → ship → settle`, value-conserving (`released + refunded == escrowed`). The payer
//!     escrows the reward from a CONSERVED pool; settlement releases it to the inhabitant. (Organ 3.)
//!   * the ROOM + INHABITANT model — this crate's [`Room`]/[`InhabitantView`]: a place that contains
//!     inhabitants, renders each one's held mandate + live (committed) actions, and SURFACES every
//!     refusal in-room with the receipt-why. (Organ 5, mirrored gpui-free from
//!     `starbridge-v2/src/room.rs`.)
//!
//! Both the job cell and the escrow cell live in ONE ledger, driven by ONE real
//! [`EmbeddedExecutor`](dregg_app_framework::EmbeddedExecutor). So a cheat is a REAL executor
//! refusal — not an unhandled case, not a fake. The scenario (the [`scenario`] module) runs the full
//! cycle and the try-to-cheat battery and emits an in-room [`Transcript`] the example prints.
//!
//! THE MAPPING (ember's vision):
//!   - a cell = an ENTITY (the inhabitant, the room, the escrow item);
//!   - a turn = an ACTION (cap-gated + receipted) — every step here is a real signed turn;
//!   - the held workflow-mandate = the colonist's JOB it provably can't exceed;
//!   - the escrow settle = the pay-for-work ECONOMY (a conserving transfer);
//!   - DAVID'S DOOR — the gateway (`starbridge-storage-gateway-mandate`) is where a *buildr* agent
//!     walks IN as a new inhabitant: it births a job cell under the gateway's physics and advances
//!     it with the same three legs; see [`davids_door`] for the seam note.

pub mod room;
pub mod scenario;

pub use room::{InRoomRefusal, InhabitantView, Room, RoomView};
pub use scenario::{
    CheatClass, CheatOutcome, Transcript, davids_door, run_first_room, JobStepRecord,
};
