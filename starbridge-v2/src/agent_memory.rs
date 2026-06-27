//! **AGENT MEMORY AS A umem — checkpoint → handoff → resume on the LIVE path.**
//!
//! THE REVOLUTION, MADE LOAD-BEARING (the agent-memory sibling of the time-travel
//! scrub's `reify_ledger` boundary restore, `b1bd3305`). A confined agent's
//! working-set IS its cell's state on the live [`World`] — its counter, its balance,
//! its nonce, its committed heap, its mandate. [`dregg_turn::umem::project_cell`]
//! lands that whole working-set at `(domain, collection, key) ↦ value` cells of the
//! ONE universal address space: a witnessed, portable, comparable object — a **umem**.
//!
//! So a LIVE agent's session can be CHECKPOINTED to a umem-ref ([`AgentMemoryCheckpoint`])
//! and a FRESH agent context reconstituted from it ([`AgentMemoryCheckpoint::resume_into_fresh_world`]),
//! CONTINUING from exactly where it left off — not a reset. The prototype proved this
//! over a standalone `PortableApplet` (`deos-hermes/tests/agent_memory_as_umem.rs`);
//! this lifts the round-trip onto the real verified [`World`] the cockpit drives, the
//! SAME World a [`crate::agent_attach::attach_agent`]'d confined agent fires onto (a
//! `deos-js` `AttachedApplet::fire` is a thin wrapper over [`World::commit_turn`]).
//!
//! This is pure app/wiring: `project_cell` (checkpoint) + `reify_cell` (resume) +
//! [`World::genesis_install`] (reconstitute) over the per-cell umem Stage A already
//! proved. **No new kernel effect** — the agent's memory is the projection of state it
//! already owns, and the resume is the `reify_cell` inverse fold the umem boundary
//! supplies, fail-closed under the SAME anti-substitution root tooth
//! ([`dregg_cell::Ledger::root`]) the persist/replay/time-travel lane uses.

use dregg_cell::{CellId, Ledger};
use dregg_turn::umem::{self, UProjection};

use crate::world::World;

/// Why a live agent's umem checkpoint could not be resumed. Every variant is a
/// FAIL-CLOSED refusal (the same anti-substitution discipline the time-travel scrub
/// holds): the resumed agent is byte-faithful to its checkpoint, or it does not stand
/// up at all.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgentMemoryError {
    /// The agent's cell was not present on the World being checkpointed.
    AgentNotPresent(CellId),
    /// The checkpoint umem could not be reified back into a live cell — the cell's
    /// state needs a projection plane outside the faithful class (interfaces / cap
    /// tombstones / a revocation gap; see [`dregg_turn::umem::ReifyError`]). Carries the
    /// reify error's text.
    Reify(String),
    /// The reified cell does not reproduce the canonical commitment recorded at
    /// checkpoint — a tampered/corrupt umem carrier. This is the anti-substitution ROOT
    /// tooth (the same [`dregg_cell::Ledger::root`] the time-travel scrub verifies a
    /// reconstructed past against): a tamper to ANY projected plane re-derives a
    /// different root and the resume refuses.
    RootTooth {
        recorded: [u8; 32],
        reified: [u8; 32],
    },
    /// The reified cell does not RE-PROJECT to the checkpoint umem byte-for-byte — the
    /// state-agreement square `project(checkpoint) == project(resume)` (the prototype's
    /// round-trip witness) failed. The carrier drifted.
    ReprojectionDrift,
    /// The reconstituted cell's content-address id is not the checkpointed agent id
    /// (the identity invariant broke).
    IdentityMismatch { expected: CellId, got: CellId },
    /// The carrier bytes could not be (de)serialized.
    Carrier(String),
}

impl std::fmt::Display for AgentMemoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AgentMemoryError::AgentNotPresent(c) => {
                write!(f, "agent cell {c} is not present on the World")
            }
            AgentMemoryError::Reify(e) => write!(f, "umem reify refused: {e}"),
            AgentMemoryError::RootTooth { recorded, reified } => write!(
                f,
                "checkpoint root tooth mismatch: recorded {recorded:?} != reified {reified:?}"
            ),
            AgentMemoryError::ReprojectionDrift => write!(
                f,
                "re-projection drift: the resumed cell does not reproject to the checkpoint umem"
            ),
            AgentMemoryError::IdentityMismatch { expected, got } => {
                write!(f, "resumed cell id {got} != checkpointed agent {expected}")
            }
            AgentMemoryError::Carrier(e) => write!(f, "checkpoint carrier (de)serialize: {e}"),
        }
    }
}

impl std::error::Error for AgentMemoryError {}

/// The canonical commitment of a single cell — the [`dregg_cell::Ledger::root`] over a
/// one-cell ledger. The SAME root the persist/replay lane uses as its anti-substitution
/// tooth, applied to one agent cell. A tamper to ANY projected plane (fields, balance,
/// nonce, heap, caps…) re-derives a different root, so the resume tooth refuses.
fn cell_root_tooth(cell: &dregg_cell::Cell) -> [u8; 32] {
    let mut ledger = Ledger::new();
    ledger
        .insert_cell(cell.clone())
        .expect("a fresh one-cell ledger always accepts the insert");
    ledger.root()
}

/// **A LIVE AGENT'S MEMORY, CHECKPOINTED AS A umem.** The agent's whole working-set
/// (its cell's projected planes) as one structured universal-address object, plus the
/// canonical root tooth that makes the resume fail-closed. Serialize it
/// ([`Self::to_bytes`]) to carry it over the membrane; reconstitute a fresh agent
/// context from it ([`Self::resume_into_fresh_world`]).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct AgentMemoryCheckpoint {
    /// The agent's cell identity (the (public_key, token_id) content-address).
    pub agent: CellId,
    /// THE umem — the agent's working-set projected into the universal address space.
    pub umem: UProjection,
    /// The canonical commitment ([`dregg_cell::Ledger::root`] over a one-cell ledger
    /// holding the agent) the cell carried at checkpoint — the anti-substitution ROOT
    /// tooth re-derived and checked on resume (a tamper to any plane refuses).
    pub root: [u8; 32],
}

impl AgentMemoryCheckpoint {
    /// **CHECKPOINT** a live agent's working-set off a running World — project its cell
    /// into the universal address space (the witnessed umem) and capture the canonical
    /// root tooth. PURE: it never mutates the World.
    pub fn capture(world: &World, agent: CellId) -> Result<Self, AgentMemoryError> {
        let cell = world
            .ledger()
            .get(&agent)
            .ok_or(AgentMemoryError::AgentNotPresent(agent))?;
        let mut umem = UProjection::new();
        umem::project_cell(cell, &mut umem);
        Ok(AgentMemoryCheckpoint {
            agent,
            umem,
            root: cell_root_tooth(cell),
        })
    }

    /// Read one model slot of the checkpointed working-set straight off the umem (a
    /// witnessed read of the carried state — e.g. the agent's counter at checkpoint).
    pub fn working_slot(&self, slot: usize) -> u64 {
        match self.umem.get(&umem::UKey::Field {
            cell: self.agent,
            slot: slot as u64,
        }) {
            Some(umem::UVal::Bytes32(b)) => deos_js_unpack_u64(b),
            _ => 0,
        }
    }

    /// Serialize the checkpoint to the portable carrier bytes (the umem-ref on the wire).
    pub fn to_bytes(&self) -> Result<Vec<u8>, AgentMemoryError> {
        postcard::to_allocvec(self).map_err(|e| AgentMemoryError::Carrier(e.to_string()))
    }

    /// Reconstitute a checkpoint from its carrier bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, AgentMemoryError> {
        postcard::from_bytes(bytes).map_err(|e| AgentMemoryError::Carrier(e.to_string()))
    }

    /// **RESUME** the checkpointed agent INTO a (fresh) World — reify the agent's cell
    /// from the umem boundary, FAIL-CLOSED, and install it via the genesis path. The
    /// World is now a fresh context carrying exactly the checkpointed working-set; a
    /// freshly-attached runtime over it CONTINUES from the checkpoint.
    ///
    /// Fail-closed teeth (held in the same discipline as the time-travel scrub):
    ///  * `reify_cell` refuses an out-of-faithful-class cell ([`AgentMemoryError::Reify`]);
    ///  * the reified cell MUST reproduce the recorded canonical ROOT tooth
    ///    ([`AgentMemoryError::RootTooth`] — a tamper to any plane refuses);
    ///  * the reified cell MUST re-project to the checkpoint umem byte-for-byte (the
    ///    round-trip witness, [`AgentMemoryError::ReprojectionDrift`]);
    ///  * the reconstituted id MUST equal the checkpointed agent
    ///    ([`AgentMemoryError::IdentityMismatch`]).
    pub fn resume_into(&self, world: &mut World) -> Result<CellId, AgentMemoryError> {
        let cell = umem::reify_cell(self.agent, &self.umem)
            .map_err(|e| AgentMemoryError::Reify(e.to_string()))?;
        let reified_root = cell_root_tooth(&cell);
        if reified_root != self.root {
            return Err(AgentMemoryError::RootTooth {
                recorded: self.root,
                reified: reified_root,
            });
        }
        // THE ROUND-TRIP WITNESS: the reified cell projects byte-identically to the
        // checkpoint umem — the agent's working-set crossed the handoff with no drift
        // (the state-agreement square `project(checkpoint) == project(resume)`).
        let mut reproj = UProjection::new();
        umem::project_cell(&cell, &mut reproj);
        if reproj != self.umem {
            return Err(AgentMemoryError::ReprojectionDrift);
        }
        let id = world.genesis_install(cell);
        if id != self.agent {
            return Err(AgentMemoryError::IdentityMismatch {
                expected: self.agent,
                got: id,
            });
        }
        Ok(id)
    }

    /// **RESUME into a fresh World** — the common case: a brand-new World context whose
    /// only inhabitant is the checkpointed agent, reconstituted from the umem boundary.
    /// Returns the fresh World (ready for a fresh confined-agent attach + continue).
    pub fn resume_into_fresh_world(&self) -> Result<World, AgentMemoryError> {
        let mut world = World::new();
        self.resume_into(&mut world)?;
        Ok(world)
    }
}

/// Unpack a u64 from a model field element (the low 8 bytes, little-endian) — the same
/// convention `deos_js::applet::pack_u64`/`unpack_u64` and `Effect::SetField` counter
/// shapes use, re-implemented here so the core does not pull `deos-js`/mozjs.
fn deos_js_unpack_u64(fe: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[..8]);
    u64::from_le_bytes(b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::World;
    use dregg_cell::state::FieldElement;
    use dregg_turn::action::Effect;

    /// Pack a u64 into a model field element (the counter shape — mirror of
    /// `deos_js::applet::pack_u64`, kept local so the test needs no mozjs).
    fn pack_u64(v: u64) -> FieldElement {
        let mut fe = [0u8; 32];
        fe[..8].copy_from_slice(&v.to_le_bytes());
        fe
    }

    /// The EXACT effects a confined agent's `AttachedApplet::fire("bump", arg)` commits
    /// (a `SetField` on the counter slot + an `IncrementNonce`), so this cheap-lane test
    /// drives the SAME verified-turn shape the live deos-js agent does — without mozjs.
    const COUNTER_SLOT: usize = 0;
    fn bump(world: &mut World, agent: CellId, arg: u64) {
        let cur = world
            .ledger()
            .get(&agent)
            .and_then(|c| c.state.get_field(COUNTER_SLOT))
            .map(super::deos_js_unpack_u64)
            .unwrap_or(0);
        let effects = vec![
            Effect::SetField {
                cell: agent,
                index: COUNTER_SLOT,
                value: pack_u64(cur + arg),
            },
            Effect::IncrementNonce { cell: agent },
        ];
        let t = world.turn(agent, effects);
        assert!(
            world.commit_turn(t).is_committed(),
            "the bump turn commits on the live World"
        );
    }

    fn counter(world: &World, agent: CellId) -> u64 {
        world
            .ledger()
            .get(&agent)
            .and_then(|c| c.state.get_field(COUNTER_SLOT))
            .map(super::deos_js_unpack_u64)
            .unwrap_or(0)
    }

    /// **THE LIVE ROUND-TRIP** — a real agent cell on a real verified [`World`] evolves
    /// its working-set, is checkpointed to a umem-ref, dropped, and reconstituted into a
    /// FRESH World that CONTINUES from the checkpoint — proven byte-identical in the
    /// universal address space, and proven to advance (not reset).
    #[test]
    fn live_world_agent_memory_checkpoint_resume_continues() {
        // 1. A live agent (the demo `user` cell) evolves its working-set via REAL turns.
        let (mut world, anchors) = crate::world::demo_world();
        let agent = anchors[2]; // the user cell — a confined agent's vessel
        bump(&mut world, agent, 7);
        bump(&mut world, agent, 5);
        assert_eq!(counter(&world, agent), 12, "live working-set 0+7+5 = 12");

        // 2. CHECKPOINT the working-set as a witnessed umem-ref.
        let checkpoint = AgentMemoryCheckpoint::capture(&world, agent).expect("capture");
        assert_eq!(checkpoint.working_slot(COUNTER_SLOT), 12, "umem carries 12");
        let carrier = checkpoint.to_bytes().expect("serialize");

        // 3. The live World is DROPPED — only the carrier survives.
        drop(world);
        drop(checkpoint);

        // 4. RESUME into a FRESH World from nothing but the carrier.
        let recovered = AgentMemoryCheckpoint::from_bytes(&carrier).expect("load carrier");
        let mut resumed = recovered
            .resume_into_fresh_world()
            .expect("resume (teeth pass)");
        assert_eq!(
            counter(&resumed, agent),
            12,
            "the resumed agent CONTINUES from the checkpoint (12), not a reset"
        );

        // 5. THE WITNESS: the resumed agent's umem is byte-identical to the checkpoint.
        let re = AgentMemoryCheckpoint::capture(&resumed, agent).expect("re-capture");
        assert_eq!(
            re.umem, recovered.umem,
            "the umem crossed the handoff byte-for-byte"
        );
        assert_eq!(re.root, recovered.root, "the root tooth re-derives");

        // 6. CONTINUE: a fresh verified turn advances FROM the checkpoint.
        bump(&mut resumed, agent, 100);
        assert_eq!(
            counter(&resumed, agent),
            112,
            "the resumed agent advanced its working-set FROM the checkpoint (12 + 100)"
        );
    }

    /// **FAIL-CLOSED** — a tampered umem carrier refuses to resume via the root tooth.
    #[test]
    fn tampered_umem_refuses_to_resume() {
        let (mut world, anchors) = crate::world::demo_world();
        let agent = anchors[2];
        bump(&mut world, agent, 7);
        let checkpoint = AgentMemoryCheckpoint::capture(&world, agent).expect("capture");

        let mut tampered = checkpoint.clone();
        tampered.umem.insert(
            umem::UKey::Field {
                cell: agent,
                slot: COUNTER_SLOT as u64,
            },
            umem::UVal::Bytes32(pack_u64(999)),
        );
        match tampered.resume_into_fresh_world() {
            Err(AgentMemoryError::RootTooth { .. }) => {}
            Err(e) => panic!("a tampered umem must refuse via the root tooth, got {e:?}"),
            Ok(_) => panic!("a tampered umem must NOT resume — it bypassed the root tooth"),
        }

        // The untampered checkpoint still resumes cleanly (sanity).
        assert!(checkpoint.resume_into_fresh_world().is_ok());
    }

    /// A SECOND handoff hop — the umem is a durable relay baton, not a one-shot: resume,
    /// continue, RE-checkpoint, resume AGAIN. Each context picks up where the last left.
    #[test]
    fn agent_memory_relays_across_multiple_contexts() {
        let (mut world, anchors) = crate::world::demo_world();
        let agent = anchors[2];
        bump(&mut world, agent, 3);
        let cp_a = AgentMemoryCheckpoint::capture(&world, agent).unwrap();
        drop(world);

        let mut b = cp_a.resume_into_fresh_world().expect("B resumes A");
        assert_eq!(counter(&b, agent), 3, "B continues A (3)");
        bump(&mut b, agent, 4);
        let cp_b = AgentMemoryCheckpoint::capture(&b, agent).unwrap();
        drop(b);

        let c = cp_b.resume_into_fresh_world().expect("C resumes B");
        assert_eq!(
            counter(&c, agent),
            7,
            "C continues B (3 + 4) across two hops"
        );
    }
}
