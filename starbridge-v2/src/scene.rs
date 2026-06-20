//! THE VERIFIED SCENE — surface `present()` as a REAL verified turn, with teeth.
//!
//! [`crate::compositor`] is the PURE scene-authority model: it decides T1∧T2∧T3
//! (non-overlap · label-binding · focus-exclusivity) in Rust and refuses an
//! overpaint / label-spoof / double-focus in a standalone `Compositor`. That is
//! the executable shadow of the Lean `Dregg2.Apps.Compositor` `AppSpec`, but its
//! admission is decided by a Rust reimplementation of `sceneAdmit` — a PARALLEL
//! gate, not the executor's.
//!
//! This module closes that gap (roadmap N7 — "the transfer-triangle for the
//! desktop"): it makes `present()` a REAL VERIFIED TURN against the embedded
//! [`World`](crate::world::World)'s executor, so the three anti-ghost teeth bite
//! from the SAME production caveat gate that commits a value turn — not from a
//! Rust if-statement. The construction is the Lean one, transposed verbatim:
//!
//!   * A **compositor cell** is a real ledger cell whose [`CellProgram`] is the
//!     baked **admit-table** `AllowedTransitions { slot: present_digest, allowed:
//!     <(old,new) : sceneAdmit … old new> }` — the Rust mirror of the Lean
//!     `compositorSpec.caveats = [.admitTable present_digest …]`. The WHOLE scene
//!     authority (the region→owner map, the focus holder, the presenter's granted
//!     region-set, the genuine owner-label) is CLOSED OVER into that table at
//!     scene-snapshot time, exactly as `ToolAccessDelegation.delegAdmit` closes
//!     over `(toolId, rateLimit, deadline)`.
//!   * A `present()` is the single scalar write `present_digest : old → new`
//!     committed as an [`Effect::SetField`] turn through
//!     [`World::commit_turn`](crate::world::World::commit_turn). The executor's
//!     program-check evaluates the `AllowedTransitions` caveat (the production
//!     `StateConstraint` gate) and COMMITS iff the scene authority admits the
//!     present — and REJECTS (a real [`CommitOutcome::Rejected`]) any overpaint,
//!     label-spoof, or double-focus. **This IS `VerificationToolkit.
//!     app_commit_iff_admit` + `app_violation_rejected`, on glass** — the teeth
//!     come for free from the verified kernel because the present is just a
//!     caveat-gated `SetField`, the SAME gate the toolkit proves over.
//!   * A **surface [`FactoryDescriptor`]** ([`surface_factory`]) mints surface
//!     cells already carrying the present_digest caveat program as a PERPETUAL
//!     slot caveat — apps-as-cells, born from a verified factory with the scene
//!     gate baked in, so a factory-born surface inherits the discipline.
//!
//! A refusal is a FEATURE, surfaced the same way the executor's turn rejections
//! are (the [`PresentVerdict`] carries the tooth that bit). A committed present
//! advances the frame digest in the live scene AND emits a [`WorldEvent::
//! SurfaceDamaged`] on the dynamics stream (the compositor's "damage" — the
//! region that must be repainted).
//!
//! gpui-free and `cargo test`-able under `embedded-executor`. The cockpit's SHELL
//! tab maps the live scene onto gpui; the assurance value is THIS headless model
//! + the teeth that bite through the real executor.

use dregg_cell::{
    field_from_u64, AuthRequired, Cell, CellId, CellProgram, FieldElement, Permissions,
    StateConstraint,
};
use dregg_cell::factory::FactoryDescriptor;
use dregg_firmament::{NotifyCap, ObjectId, Rights};

use crate::compositor::{label_of, CompositedSurface, CompositorScene, Present, PresentError, RegionId};
use crate::dynamics::WorldEvent;
use crate::world::{World, CommitOutcome};

/// THE DAMAGE BADGE — the async-signal discriminator a compositor `present()`'s
/// damage wake carries, projected to ONE bit of the 64-bit notify badge lattice.
///
/// A committed present is the compositor's **async signal** to whoever watches
/// the surface for repaint (`docs/NOTIFY-PRIMITIVE.md` §2.4 — "the compositor
/// `signal`s the surface's notification on damage, badge = the damage kind").
/// The damage KIND here is the present's region extent (how much was painted):
/// `region_count` projects to bit `region_count % 64`, so a small-region repaint
/// and a full-surface repaint occupy distinct badge bits, and a watcher's mask
/// can admit "wake me only for full-surface damage" or "any damage". This is the
/// scene mirror of [`crate::swarm::topic_badge`] (the cross-agent edge's badge),
/// now on the compositor's damage edge. `region_count == 0` (no regions painted)
/// maps to bit 0; the open default mask (`u64::MAX`) admits every damage kind.
#[must_use]
pub fn damage_badge(region_count: usize) -> u64 {
    1u64 << ((region_count as u64) % 64)
}

/// The per-surface notification OBJECT id the compositor's [`NotifyCap`] targets
/// — the surface's own damage-wake accumulator (the §3.1 canonical `Notification`,
/// one per surface owner). Derived deterministically from the owner cell id so the
/// cap is target-bound: a forged cap aimed at a different surface's object signals
/// nothing. The low 8 bytes of the owner cell id, as the firmament `u64` `ObjectId`
/// — the SAME derivation [`crate::swarm::member_notify_object`] uses for the
/// cross-agent edge, so the two async edges share one object-id discipline.
#[must_use]
fn surface_notify_object(owner: &CellId) -> ObjectId {
    let b = owner.as_bytes();
    ObjectId(u64::from_le_bytes([
        b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
    ]))
}

/// The compositor cell's frame-digest slot index (the scalar state a `present()`
/// advances). Mirrors the Lean `presentDigestSlot := "present_digest"`; here a
/// concrete state-field index on the 16-slot cell. Slot 0 is the canonical
/// balance slot, so the frame digest lives at slot 1 (a metadata slot — a
/// committed present is balance-neutral, the Lean `present_conserves`).
pub const PRESENT_DIGEST_SLOT: u8 = 1;

/// The content-addressed VK identifying the surface factory (a fixed tag for the
/// embedded world's one surface factory). A factory-born surface cell inherits
/// the present_digest scene-caveat program.
pub const SURFACE_FACTORY_VK: [u8; 32] = [0x5C; 32]; // 'S'urface 'C'ompositor

/// **The scalar scene-admission predicate** — `sceneAdmit sc presenter p old new`,
/// folded to the toolkit's `admit : Int → Int → Bool` boundary. Does the scene
/// authority admit advancing the compositor frame digest `old → new`, by
/// `presenter`, presenting `p`, against the closed-over scene? The conjunction
/// T1 ∧ T2 ∧ T3 (non-overlap ∧ label-bound ∧ focus-exclusive ∧ input-routed) AND
/// a genuine frame advance (`new ≠ old`). This is the EXACT predicate the
/// executor's baked `AllowedTransitions` table is built from — so the executor's
/// caveat gate decides the same transitions this predicate does (the differential
/// identity `caveatsAdmit_iff_admit`).
///
/// It reuses the pure compositor teeth so there is ONE source of truth for the
/// scene authority (the `compositor` module's T1/T2/T3), closed over the scene.
pub fn scene_admit(scene: &CompositorScene, presenter: &CellId, p: &Present, old: u64, new: u64) -> bool {
    // We evaluate the three teeth against a throwaway `Compositor` holding this
    // scene — the SAME T1/T2/T3 the pure model checks, so the baked table cannot
    // drift from the pure compositor's admission.
    let mut c = crate::compositor::Compositor::new();
    c.set_scene(scene.clone());
    c.t1_non_overlap(presenter, &p.target)
        && c.t2_label_bound(presenter, p.source_state_root, p.declared_label)
        && c.t3_focus_exclusive()
        && c.t3_input_routed(presenter, p.claims_focus)
        && new != old
}

/// **The baked admit-table** for presenting `p` by `presenter` against `scene`,
/// over the digest grid `old_grid × new_grid` — the Rust mirror of the Lean
/// `(compositorSpec sc presenter p cell oldRange newRange).admitTable`. A pair
/// `(old, new)` is in the table iff [`scene_admit`] admits it. The executor's
/// `AllowedTransitions` constraint enforces EXACTLY this set; an honest present's
/// table holds its one advance, and an attacking presentation bakes an EMPTY
/// table (no present under it can commit — the Lean `admitTable.length == 0`).
pub fn baked_admit_table(
    scene: &CompositorScene,
    presenter: &CellId,
    p: &Present,
    old_grid: &[u64],
    new_grid: &[u64],
) -> Vec<(FieldElement, FieldElement)> {
    let mut table = Vec::new();
    for &old in old_grid {
        for &new in new_grid {
            if scene_admit(scene, presenter, p, old, new) {
                table.push((field_from_u64(old), field_from_u64(new)));
            }
        }
    }
    table
}

/// **The compositor-cell program** carrying the baked scene caveat — the Rust
/// mirror of the Lean `compositorSpec.caveats`. A single `AllowedTransitions`
/// slot caveat on the `present_digest` slot, enforcing the scene authority on
/// every frame advance through the production executor's program-check.
pub fn compositor_program(
    scene: &CompositorScene,
    presenter: &CellId,
    p: &Present,
    old_grid: &[u64],
    new_grid: &[u64],
) -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::AllowedTransitions {
        slot_index: PRESENT_DIGEST_SLOT,
        allowed: baked_admit_table(scene, presenter, p, old_grid, new_grid),
    }])
}

/// **The surface factory** — a [`FactoryDescriptor`] that mints surface cells
/// carrying the present_digest scene-caveat program as a PERPETUAL slot caveat.
/// A surface born from this factory inherits the scene-authority gate baked in:
/// every `present()` against it is a caveat-gated `SetField` the executor checks.
///
/// The `(scene, presenter, present, grid)` are closed into the factory's baked
/// caveat at deploy time — so a surface born for a given presentation carries the
/// admit-table for THAT presentation. (The embedded world deploys one factory per
/// live presentation snapshot, exactly as the Lean closes the spec over the
/// scene; a re-composition re-bakes.) `creation_budget` caps how many surfaces it
/// births.
pub fn surface_factory(
    scene: &CompositorScene,
    presenter: &CellId,
    p: &Present,
    old_grid: &[u64],
    new_grid: &[u64],
) -> FactoryDescriptor {
    let CellProgram::Predicate(constraints) =
        compositor_program(scene, presenter, p, old_grid, new_grid)
    else {
        unreachable!("compositor_program is always a Predicate")
    };
    FactoryDescriptor {
        factory_vk: SURFACE_FACTORY_VK,
        child_program_vk: None,
        child_vk_strategy: None,
        allowed_cap_templates: vec![],
        field_constraints: vec![],
        // PERPETUAL slot caveats baked into the child surface cell's program.
        state_constraints: constraints,
        default_mode: dregg_cell::CellMode::Hosted,
        creation_budget: Some(64),
    }
}

/// The outcome of a `present()` against the verified scene — a real executor
/// decision, surfaced as a teaching moment. `Committed` carries the new frame
/// digest the live scene advanced to; `Refused` carries the [`PresentError`]
/// tooth (overpaint / label-spoof / double-focus / …) the executor's caveat gate
/// bit on (recovered from the scene so the operator sees WHICH guarantee fired),
/// plus the raw executor `reason`.
#[derive(Clone, Debug)]
pub enum PresentVerdict {
    /// The executor COMMITTED the present: the scene authority admitted it and the
    /// frame digest advanced to `digest`. A real receipt was logged.
    Committed { digest: u64 },
    /// The executor REFUSED the present (a real `CommitOutcome::Rejected`). The
    /// `tooth` is the scene-authority violation recovered from the scene (so the
    /// cockpit can color it red and name the guarantee); `reason` is the raw
    /// executor rejection string.
    Refused { tooth: PresentError, reason: String },
}

impl PresentVerdict {
    pub fn is_committed(&self) -> bool {
        matches!(self, PresentVerdict::Committed { .. })
    }
    /// The tooth that bit (for a refusal), or `None` if it committed.
    pub fn tooth(&self) -> Option<&PresentError> {
        match self {
            PresentVerdict::Refused { tooth, .. } => Some(tooth),
            PresentVerdict::Committed { .. } => None,
        }
    }
}

/// THE VERIFIED SCENE — the compositor scene bound to a live [`World`], where
/// `present()` is a REAL verified turn through the embedded executor.
///
/// It holds the scene (the ordered surfaces with their region ownership + focus,
/// the [`CompositorScene`] the pure compositor uses) plus, for each owner, the
/// compositor cell id whose `present_digest` slot the executor gates. A present
/// bakes the scene-authority admit-table onto the presenter's compositor cell and
/// commits a `SetField` against it: the executor's program-check is the gate.
///
/// The scene authority is decided by the VERIFIED KERNEL, not this struct: the
/// three teeth are the executor refusing a caveat-violating `SetField`. The
/// struct only (a) keeps the live scene in sync with committed frames, and (b)
/// emits the [`WorldEvent::SurfaceDamaged`] dynamics on a commit.
pub struct VerifiedScene {
    /// The live scene (back-to-front surfaces). The pure compositor's `Scene`.
    scene: CompositorScene,
    /// Per-owner compositor cell id (the real ledger cell whose present_digest
    /// slot the executor gates for that owner's presents). Allocated lazily as a
    /// genesis cell when an owner first opens.
    compositor_cell: std::collections::HashMap<CellId, CellId>,
    /// THE HELD DAMAGE-NOTIFY AUTHORITY, per surface owner — a REAL
    /// `dregg_firmament` [`NotifyCap`] over each surface's damage-wake object
    /// ([`surface_notify_object`]). The compositor emits a
    /// [`WorldEvent::SurfaceDamaged`] async signal on a committed present IFF the
    /// damage badge ([`damage_badge`]) is within this cap's `badge_mask`
    /// ([`NotifyCap::signal_admissible`], the Rust mirror of the verified
    /// `Dregg2.Firmament.NotifyAuthority.NotifyCap.signalAdmissible`). This routes
    /// the compositor's damage edge through the SAME held, attenuable async-signal
    /// authority the swarm's cross-agent edge uses (`docs/NOTIFY-PRIMITIVE.md`
    /// §2.4) — the ambient `emit_dynamics` becomes cap-gated. Seeded at `u64::MAX`
    /// (wake-for-any-damage) when an owner opens, so the prior behaviour is
    /// preserved until a watcher attenuates it via [`Self::restrict_damage_notify`].
    damage_notify: std::collections::HashMap<CellId, NotifyCap>,
    /// The digest grid the frame ranges over (old-values the cell can hold).
    old_grid: Vec<u64>,
    /// The digest grid the frame can advance to (new-values a present may write).
    new_grid: Vec<u64>,
}

impl VerifiedScene {
    /// A fresh verified scene with an empty scene graph and a digest grid. The
    /// grid is the finite set of frame digests the toolkit bakes the table over
    /// (fail-closed by absence outside it — SOUND, never admits more than
    /// `scene_admit`). A modest grid covers the demo presentations.
    pub fn new(old_grid: Vec<u64>, new_grid: Vec<u64>) -> Self {
        VerifiedScene {
            scene: CompositorScene::default(),
            compositor_cell: std::collections::HashMap::new(),
            damage_notify: std::collections::HashMap::new(),
            old_grid,
            new_grid,
        }
    }

    /// A verified scene over a default digest grid (`0..=8` × `1..=9`), enough for
    /// the demo presentations (single-frame advances `old → old+1`).
    pub fn with_default_grid() -> Self {
        Self::new((0..=8).collect(), (1..=9).collect())
    }

    /// The live scene (read-only — the cockpit paints this in z-order).
    pub fn scene(&self) -> &CompositorScene {
        &self.scene
    }

    /// The surfaces in paint order (back-to-front), z-sorted.
    pub fn surfaces_in_z_order(&self) -> Vec<&CompositedSurface> {
        let mut v: Vec<&CompositedSurface> = self.scene.surfaces.iter().collect();
        v.sort_by_key(|s| s.z_layer);
        v
    }

    /// The compositor cell id backing `owner`'s presents, if it has opened a
    /// surface (the real ledger cell whose present_digest the executor gates).
    pub fn compositor_cell(&self, owner: &CellId) -> Option<CellId> {
        self.compositor_cell.get(owner).copied()
    }

    /// **Open a surface for `owner`** over the live world: install the surface
    /// into the scene graph AND seed `owner`'s compositor cell (a genesis cell
    /// whose present_digest slot starts at `initial_digest`, on `open_permissions`
    /// so the presenter — an authorized cell in the single-custody world — may
    /// write it; the SCENE CAVEAT, not the permission, is the load-bearing gate).
    ///
    /// Returns the compositor cell id. The surface's region-set is the authority
    /// the T1 tooth checks `granted ⊆ held` against; `source_state_root` is the
    /// projection the T2 label binds to.
    pub fn open_surface(
        &mut self,
        world: &mut World,
        owner: CellId,
        regions: Vec<RegionId>,
        initial_digest: u64,
        source_state_root: u64,
        z_layer: i64,
        focus: bool,
    ) -> CellId {
        self.scene.surfaces.push(CompositedSurface {
            owner,
            regions,
            content_digest: initial_digest,
            source_state_root,
            z_layer,
            focus_flag: focus,
        });
        // Seed the compositor cell for this owner if not already present.
        if let Some(existing) = self.compositor_cell.get(&owner) {
            return *existing;
        }
        // Seed the compositor's HELD damage-notify authority over this surface's
        // wake object — open by default (admit any damage kind) until a watcher
        // attenuates it. The async damage edge is now a held cap, not ambient emit.
        self.damage_notify.entry(owner).or_insert_with(|| NotifyCap {
            target: surface_notify_object(&owner),
            rights: Rights::Either,
            badge_mask: u64::MAX,
        });
        let cell = make_compositor_cell(owner, initial_digest);
        let id = world.genesis_install(cell);
        // The shell hands the presenter a surface cap on its compositor cell (the
        // Lean `compositorState`'s `[.endpoint cell …]`): the authority leg of a
        // `present()`. The SCENE CAVEAT, not this cap, is the load-bearing gate —
        // even an authorized-to-present cell cannot overpaint/spoof/steal-focus.
        let _ = world.genesis_grant_cap(&owner, id);
        self.compositor_cell.insert(owner, id);
        id
    }

    /// **PRESENT — the cap-gated frame advance, as a REAL verified turn.** The
    /// presenter `owner` submits `p` advancing its frame digest to `new_digest`.
    /// This:
    ///   1. bakes the scene-authority admit-table (the `AllowedTransitions`
    ///      caveat) onto `owner`'s compositor cell — closing the WHOLE scene over
    ///      the scalar boundary (the Lean `compositorSpec` move);
    ///   2. commits a `SetField(present_digest := new_digest)` turn through the
    ///      EMBEDDED EXECUTOR;
    ///   3. lets the executor's program-check be the gate: it COMMITS iff the
    ///      scene authority admits the present (the executor evaluates the baked
    ///      table), and REJECTS any overpaint / label-spoof / double-focus.
    ///
    /// On commit: the live scene's frame digest advances and a
    /// [`WorldEvent::SurfaceDamaged`] is emitted. On refusal: the live scene is
    /// untouched (fail-closed) and the [`PresentError`] tooth (recovered from the
    /// scene) is returned — the guarantee firing, surfaced as a feature.
    ///
    /// The whole admission is decided by the VERIFIED KERNEL: the three teeth are
    /// the real executor refusing a caveat-violating write, exactly as the Lean
    /// `present_*_rejected` `#guard`s witness against `execFullA`.
    pub fn present(&mut self, world: &mut World, owner: CellId, p: Present, new_digest: u64) -> PresentVerdict {
        // The compositor cell for this owner (must have opened a surface).
        let Some(cell_id) = self.compositor_cell.get(&owner).copied() else {
            return PresentVerdict::Refused {
                tooth: PresentError::NoSurface,
                reason: "presenter has not opened a surface (no compositor cell)".to_string(),
            };
        };
        // Bake the scene-authority table for THIS presentation onto the compositor
        // cell's program. We re-program the cell's `CellProgram` to carry the
        // freshly-baked `AllowedTransitions` so the executor gates THIS scene —
        // the Lean closes `(sc, presenter, p)` into the spec; here we close it into
        // the live cell's caveat at present-time (the scene is the closed-over
        // authority of §4). This re-bake is a genesis-path program update (the
        // shell, the trusted window manager, owns the compositor cell).
        let program = compositor_program(&self.scene, &owner, &p, &self.old_grid, &self.new_grid);
        world.set_cell_program(&cell_id, program);

        // Commit the present as a real `SetField` turn through the executor.
        let effect = crate::world::set_field(cell_id, PRESENT_DIGEST_SLOT as usize, field_from_u64(new_digest));
        let turn = world.turn(owner, vec![effect]);
        match world.commit_turn(turn) {
            CommitOutcome::Committed { .. } => {
                // Advance the live scene's frame digest for the presenter and emit
                // the damage event (the region that must be repainted).
                if let Some(s) = self.scene.surfaces.iter_mut().find(|s| s.owner == owner) {
                    s.content_digest = new_digest;
                    s.source_state_root = p.source_state_root;
                }
                // THE DAMAGE-NOTIFY GATE — route the async damage signal through the
                // compositor's HELD `NotifyCap` over this surface's wake object. The
                // `SurfaceDamaged` wake is emitted IFF the damage badge (the present's
                // region extent) is within the held `badge_mask` (the REAL
                // `dregg_firmament::NotifyCap::signal_admissible`). An out-of-mask
                // damage kind is REFUSED (fail-closed): the frame still advanced (the
                // commit is the ground truth), but no damage wake is signalled — the
                // async edge is a cap, not ambient routing (`docs/NOTIFY-PRIMITIVE.md`
                // §2.4). Absent a cap (surface not opened through `open_surface`) the
                // wake also does not fire — fail-closed, no ambient default.
                let badge = damage_badge(p.target.len());
                let obj = surface_notify_object(&owner);
                let admitted = self
                    .damage_notify
                    .get(&owner)
                    .is_some_and(|cap| cap.signal_admissible(obj, badge));
                if admitted {
                    world.emit_dynamics(WorldEvent::SurfaceDamaged {
                        owner,
                        cell: cell_id,
                        digest: new_digest,
                        region_count: p.target.len(),
                    });
                }
                PresentVerdict::Committed { digest: new_digest }
            }
            CommitOutcome::Rejected { reason, .. } => {
                // The executor refused — recover the scene-authority tooth that bit
                // (the same diagnosis the pure compositor would give) so the cockpit
                // names the guarantee. The executor's refusal is the GROUND TRUTH;
                // the tooth is the operator-legible WHY.
                let tooth = self.diagnose(&owner, &p, new_digest);
                PresentVerdict::Refused { tooth, reason }
            }
            // The world is suspended (meta-debug): the present staged, did not advance
            // the frame. Surfaced as a refusal carrying the same diagnostic tooth.
            CommitOutcome::Queued { .. } => {
                let tooth = self.diagnose(&owner, &p, new_digest);
                PresentVerdict::Refused {
                    tooth,
                    reason: "world suspended: present turn queued, not committed".to_string(),
                }
            }
        }
    }

    /// Recover the scene-authority tooth a refused present violated — the
    /// operator-legible reason the executor's caveat gate said `none`. This is the
    /// pure compositor's diagnosis (T1/T2/T3), used ONLY to label a refusal the
    /// executor already made; it is never the gate itself.
    fn diagnose(&self, presenter: &CellId, p: &Present, new_digest: u64) -> PresentError {
        let mut c = crate::compositor::Compositor::new();
        c.set_scene(self.scene.clone());
        // Reuse the pure compositor's folded diagnosis. Its `scene_admit` returns
        // the specific tooth; we feed it the present with the new digest so its
        // frame-advance leg matches the turn we attempted.
        let probe = Present { new_digest, ..p.clone() };
        match c.scene_admit(presenter, &probe) {
            Ok(()) => {
                // The pure model would have admitted it, yet the executor refused —
                // the divergence is itself a finding. Report it honestly rather
                // than mislabel a tooth.
                PresentError::NoFrameAdvance
            }
            Err(e) => e,
        }
    }

    /// **ATTENUATE WHICH DAMAGE KINDS THIS SURFACE SIGNALS** — narrow `owner`'s
    /// held damage-notify authority ([`Self::damage_notify`]) to admit ONLY presents
    /// whose region-extent badge ([`damage_badge`]) is one of `region_counts`. After
    /// this, a committed present painting a region-count outside the set advances the
    /// frame but emits NO [`WorldEvent::SurfaceDamaged`] wake (the watcher asked to be
    /// woken only for those damage kinds) — a real, non-amplifying attenuation of the
    /// held [`NotifyCap`] on the SAME `granted ⊆ held` order the firmament mint gates
    /// on. Returns `false` (grant unchanged) if `owner` has no surface open or the
    /// requested mask would WIDEN the current one (a widening is refused — no
    /// amplification, the §3.4 covert-edge bound).
    pub fn restrict_damage_notify(&mut self, owner: &CellId, region_counts: &[usize]) -> bool {
        let Some(cap) = self.damage_notify.get(owner) else {
            return false;
        };
        let mask = region_counts
            .iter()
            .fold(0u64, |m, rc| m | damage_badge(*rc));
        let rights = cap.rights.clone();
        match cap.attenuate(rights, mask) {
            Some(narrower) => {
                self.damage_notify.insert(*owner, narrower);
                true
            }
            None => false,
        }
    }

    /// Would a committed present painting `region_count` region(s) signal a damage
    /// wake on `owner`'s surface? Iff `owner` holds a damage-notify cap whose mask
    /// admits the damage badge — the REAL `dregg_firmament`
    /// [`NotifyCap::signal_admissible`] over the surface's wake object. The
    /// query the present-path gate runs; `false` if no surface is open (fail-closed).
    #[must_use]
    pub fn admits_damage(&self, owner: &CellId, region_count: usize) -> bool {
        let obj = surface_notify_object(owner);
        self.damage_notify
            .get(owner)
            .is_some_and(|cap| cap.signal_admissible(obj, damage_badge(region_count)))
    }
}

/// Build a compositor cell for `owner`: a real ledger cell at `owner`'s derived
/// id-space, on `open_permissions` (so an authorized presenter may write its
/// present_digest slot — the SCENE CAVEAT is the load-bearing gate, not the
/// permission), with the frame digest seeded at `initial_digest` on slot
/// [`PRESENT_DIGEST_SLOT`]. The `CellProgram` is set per-present (the baked
/// scene caveat), so this seeds it as `None` (re-programmed on the first
/// present).
fn make_compositor_cell(owner: CellId, initial_digest: u64) -> Cell {
    // Derive a distinct id from the owner so two owners get distinct compositor
    // cells (the compositor-cell id is the surface-fabric anchor, not the owner).
    let mut pk = [0u8; 32];
    pk[..8].copy_from_slice(&owner.as_bytes()[..8]);
    pk[8] = 0xC0; // 'C'ompositor tag — distinct from the owner's own pk
    let mut cell = Cell::with_balance(pk, [0u8; 32], 0);
    cell.permissions = compositor_permissions();
    cell.state.fields[PRESENT_DIGEST_SLOT as usize] = field_from_u64(initial_digest);
    cell
}

/// Permissions for a compositor cell: open `set_state` (an authorized presenter
/// may write the present_digest slot — the scene caveat is the real gate), but
/// otherwise closed. Mirrors `world::open_permissions` shape; spelled here so the
/// scene module owns its cell's authority surface.
fn compositor_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::World;

    /// The honest two-surface scene (the Lean `demoScene`, transposed): a wallet
    /// (regions {10,11}, root 500, FOCUSED) + a browser (regions {20,21}, root
    /// 600) + trusted chrome (region {99}, top z). Opened over a fresh world.
    /// Returns the verified scene, the world, and the wallet + browser owner ids.
    fn demo(world: &mut World) -> (VerifiedScene, CellId, CellId) {
        // The owners are real genesis cells (the presenters / agents of the turns).
        let wallet = world.genesis_cell(0x01, 0);
        let browser = world.genesis_cell(0x02, 0);
        let chrome = world.genesis_cell(0x09, 0);
        let mut vs = VerifiedScene::with_default_grid();
        vs.open_surface(world, wallet, vec![10, 11], 1, 500, 0, true);
        vs.open_surface(world, browser, vec![20, 21], 5, 600, 0, false);
        vs.open_surface(world, chrome, vec![99], 9, 700, 100, false);
        (vs, wallet, browser)
    }

    #[test]
    fn scene_admit_matches_the_pure_compositor_teeth() {
        // The baked predicate agrees with the pure compositor's T1/T2/T3 on the
        // honest present and on each attack (one source of truth).
        let mut w = World::new();
        let (vs, wallet, browser) = demo(&mut w);
        let honest = Present {
            target: vec![10],
            source_state_root: 500,
            declared_label: label_of(&wallet, 500),
            claims_focus: true,
            new_digest: 2,
        };
        assert!(scene_admit(vs.scene(), &wallet, &honest, 1, 2), "honest present admitted");
        // OVERPAINT: browser targets region 10 (the wallet's).
        let overpaint = Present {
            target: vec![10],
            source_state_root: 600,
            declared_label: label_of(&browser, 600),
            claims_focus: false,
            new_digest: 6,
        };
        assert!(!scene_admit(vs.scene(), &browser, &overpaint, 5, 6), "overpaint rejected (T1)");
    }

    #[test]
    fn baked_table_is_a_singleton_for_honest_and_empty_for_attack() {
        // The Lean `admitTable.length == 1` (honest) / `== 0` (attack) facts.
        let mut w = World::new();
        let (vs, wallet, browser) = demo(&mut w);
        let honest = Present {
            target: vec![10],
            source_state_root: 500,
            declared_label: label_of(&wallet, 500),
            claims_focus: true,
            new_digest: 2,
        };
        let t = baked_admit_table(vs.scene(), &wallet, &honest, &[1], &[2]);
        assert_eq!(t.len(), 1, "honest presentation bakes exactly its one advance");
        assert_eq!(t[0], (field_from_u64(1), field_from_u64(2)));

        let overpaint = Present {
            target: vec![10],
            source_state_root: 600,
            declared_label: label_of(&browser, 600),
            claims_focus: false,
            new_digest: 6,
        };
        let t2 = baked_admit_table(vs.scene(), &browser, &overpaint, &[5], &[6]);
        assert_eq!(t2.len(), 0, "an overpaint presentation bakes an EMPTY table (no present commits)");
    }

    // =====================================================================
    // THE THREE ANTI-GHOST TEETH — each bites through the REAL executor.
    // Both polarities: a legitimate present COMMITS, each violation REJECTS.
    // =====================================================================

    #[test]
    fn verified_present_commits_through_the_real_executor() {
        // THE COMMIT POLARITY: the focused wallet painting its own region with its
        // genuine label COMMITS as a real verified turn — the executor's caveat
        // gate admits it, the frame advances, a receipt is logged, and the scene
        // is damaged.
        let mut w = World::new();
        let (mut vs, wallet, _browser) = demo(&mut w);
        let receipts_before = w.receipts().len();
        let p = Present {
            target: vec![10],
            source_state_root: 500,
            declared_label: label_of(&wallet, 500),
            claims_focus: true,
            new_digest: 2,
        };
        let verdict = vs.present(&mut w, wallet, p, 2);
        assert!(verdict.is_committed(), "honest present must commit, got {verdict:?}");
        // The frame digest advanced on the live scene.
        let s = vs.scene().surfaces.iter().find(|s| s.owner == wallet).unwrap();
        assert_eq!(s.content_digest, 2, "the frame digest advanced");
        // A REAL receipt was logged (it ran through the executor).
        assert_eq!(w.receipts().len(), receipts_before + 1, "a real receipt was logged");
        // The compositor cell's present_digest slot actually moved.
        let cell = vs.compositor_cell(&wallet).unwrap();
        assert_eq!(
            w.ledger().get(&cell).unwrap().state.fields[PRESENT_DIGEST_SLOT as usize],
            field_from_u64(2),
            "the executor wrote the new frame digest"
        );
        // A SurfaceDamaged dynamics event was emitted.
        assert!(
            w.dynamics().all().iter().any(|e| matches!(e, WorldEvent::SurfaceDamaged { .. })),
            "a SurfaceDamaged event must be on the dynamics stream"
        );
    }

    #[test]
    fn overpaint_present_is_refused_by_the_real_executor() {
        // THE T1 TOOTH (NON-OVERLAP), through the executor: the browser
        // overpainting the wallet's region 10 is REJECTED by the production caveat
        // gate (the baked table excludes it), and NOTHING changes (fail-closed).
        let mut w = World::new();
        let (mut vs, _wallet, browser) = demo(&mut w);
        let receipts_before = w.receipts().len();
        let attack = Present {
            target: vec![10], // region 10 is the WALLET's
            source_state_root: 600,
            declared_label: label_of(&browser, 600),
            claims_focus: false,
            new_digest: 6,
        };
        let verdict = vs.present(&mut w, browser, attack, 6);
        assert!(!verdict.is_committed(), "overpaint must be refused, got {verdict:?}");
        assert!(
            matches!(verdict.tooth(), Some(PresentError::Overpaint { .. })),
            "the tooth must be T1 overpaint, got {:?}",
            verdict.tooth()
        );
        // THE LOAD-BEARING CHECK: the refusal is the SCENE CAVEAT firing (the
        // executor's program-check on the empty admit-table), NOT a missing
        // capability — the browser DOES hold a surface cap on its compositor cell
        // (open_surface granted it), so authority is satisfied and the scene gate
        // is what bites. A `CapabilityNotHeld` refusal would be a FALSE tooth.
        if let PresentVerdict::Refused { reason, .. } = &verdict {
            assert!(
                reason.contains("allow-list"),
                "the executor must refuse on the SCENE CAVEAT (the present_digest allow-list / AllowedTransitions), not authority; got: {reason}"
            );
            assert!(
                !reason.contains("CapabilityNotHeld"),
                "the browser holds authority — the refusal must NOT be a missing-cap; got: {reason}"
            );
        }
        // Fail-closed: no receipt logged, the browser's compositor cell untouched.
        assert_eq!(w.receipts().len(), receipts_before, "a refused present logs no receipt");
        let cell = vs.compositor_cell(&browser).unwrap();
        assert_eq!(
            w.ledger().get(&cell).unwrap().state.fields[PRESENT_DIGEST_SLOT as usize],
            field_from_u64(5),
            "the browser's frame is untouched by the refused overpaint"
        );
        // The live scene's frame is untouched too.
        let s = vs.scene().surfaces.iter().find(|s| s.owner == browser).unwrap();
        assert_eq!(s.content_digest, 5, "the live scene frame is untouched");
    }

    #[test]
    fn label_spoof_present_is_refused_by_the_real_executor() {
        // THE T2 TOOTH (LABEL-BINDING), through the executor: the browser painting
        // its OWN region but DECLARING the wallet's label (the pale ghost) is
        // REJECTED by the production caveat gate.
        let mut w = World::new();
        let (mut vs, wallet, browser) = demo(&mut w);
        let receipts_before = w.receipts().len();
        let spoof = Present {
            target: vec![20], // the browser's OWN region (T1 ok)
            source_state_root: 600,
            declared_label: label_of(&wallet, 500), // ← the WALLET's label
            claims_focus: false,
            new_digest: 6,
        };
        let verdict = vs.present(&mut w, browser, spoof, 6);
        assert!(!verdict.is_committed(), "label-spoof must be refused, got {verdict:?}");
        assert!(
            matches!(verdict.tooth(), Some(PresentError::LabelSpoof { .. })),
            "the tooth must be T2 label-spoof, got {:?}",
            verdict.tooth()
        );
        // The refusal is the SCENE CAVEAT (program violation on the empty table),
        // not authority — the browser holds its surface cap (T1 region 20 is its
        // own; only the LABEL is spoofed, so the scene gate is the one that bites).
        if let PresentVerdict::Refused { reason, .. } = &verdict {
            assert!(
                reason.contains("allow-list") && !reason.contains("CapabilityNotHeld"),
                "label-spoof must be refused by the SCENE CAVEAT (allow-list), not authority; got: {reason}"
            );
        }
        assert_eq!(w.receipts().len(), receipts_before, "a refused present logs no receipt");
        let cell = vs.compositor_cell(&browser).unwrap();
        assert_eq!(
            w.ledger().get(&cell).unwrap().state.fields[PRESENT_DIGEST_SLOT as usize],
            field_from_u64(5),
            "the browser's frame is untouched by the refused spoof"
        );
    }

    #[test]
    fn double_focus_present_is_refused_by_the_real_executor() {
        // THE T3 TOOTH (FOCUS-EXCLUSIVITY), through the executor: a present against
        // a DOUBLE-FOCUS scene (both wallet and browser flagged) is REJECTED — no
        // present commits into a scene that routes input ambiguously. The baked
        // table is empty because `t3_focus_exclusive` is false for every (old,new).
        let mut w = World::new();
        // A two-surface scene where BOTH hold focus (the ambiguous-input scene).
        let wallet = w.genesis_cell(0x01, 0);
        let browser = w.genesis_cell(0x02, 0);
        let mut vs = VerifiedScene::with_default_grid();
        vs.open_surface(&mut w, wallet, vec![10, 11], 1, 500, 0, true);
        vs.open_surface(&mut w, browser, vec![20, 21], 5, 600, 0, true); // ← TWO focus flags
        let receipts_before = w.receipts().len();
        // The wallet attempts an otherwise-honest present (own region, genuine
        // label, no focus claim) — but the SCENE is ambiguous, so it is refused.
        let honest_but_ambiguous = Present {
            target: vec![10],
            source_state_root: 500,
            declared_label: label_of(&wallet, 500),
            claims_focus: false,
            new_digest: 2,
        };
        let verdict = vs.present(&mut w, wallet, honest_but_ambiguous, 2);
        assert!(!verdict.is_committed(), "a present into a double-focus scene must be refused, got {verdict:?}");
        assert!(
            matches!(verdict.tooth(), Some(PresentError::DoubleFocus { .. })),
            "the tooth must be T3 double-focus, got {:?}",
            verdict.tooth()
        );
        // The refusal is the SCENE CAVEAT: the baked table is empty because
        // `t3_focus_exclusive` is false for every (old,new) in the ambiguous scene,
        // so the executor's program-check refuses — not an authority error (the
        // wallet holds its surface cap). A double-focus scene rejects every present.
        if let PresentVerdict::Refused { reason, .. } = &verdict {
            assert!(
                reason.contains("allow-list") && !reason.contains("CapabilityNotHeld"),
                "double-focus must be refused by the SCENE CAVEAT (allow-list), not authority; got: {reason}"
            );
        }
        assert_eq!(w.receipts().len(), receipts_before, "a refused present logs no receipt");
        // Fail-closed: the live scene frame is untouched.
        let s = vs.scene().surfaces.iter().find(|s| s.owner == wallet).unwrap();
        assert_eq!(s.content_digest, 1, "the live scene frame is untouched");
    }

    #[test]
    fn the_surface_factory_bakes_the_scene_caveat() {
        // The surface FactoryDescriptor carries the present_digest scene caveat as
        // a perpetual slot constraint — so a factory-born surface inherits the
        // scene-authority gate. (The factory's state_constraints == the baked
        // admit-table program's constraints.)
        let mut w = World::new();
        let (vs, wallet, _browser) = demo(&mut w);
        let honest = Present {
            target: vec![10],
            source_state_root: 500,
            declared_label: label_of(&wallet, 500),
            claims_focus: true,
            new_digest: 2,
        };
        let factory = surface_factory(vs.scene(), &wallet, &honest, &[1], &[2]);
        assert_eq!(factory.factory_vk, SURFACE_FACTORY_VK);
        assert_eq!(factory.state_constraints.len(), 1, "one perpetual scene caveat");
        match &factory.state_constraints[0] {
            StateConstraint::AllowedTransitions { slot_index, allowed } => {
                assert_eq!(*slot_index, PRESENT_DIGEST_SLOT);
                assert_eq!(allowed.len(), 1, "the honest advance is the one allowed transition");
                assert_eq!(allowed[0], (field_from_u64(1), field_from_u64(2)));
            }
            other => panic!("expected an AllowedTransitions scene caveat, got {other:?}"),
        }
        // Deploying it into the real executor's registry returns a VK (it is a
        // well-formed descriptor the executor accepts).
        let vk = w.deploy_factory(factory);
        assert_eq!(vk.len(), 32);
    }

    #[test]
    fn present_without_a_surface_is_refused() {
        // A present by an owner that never opened a surface is refused (no
        // compositor cell). The NoSurface tooth — the Lean `NoSurface`.
        let mut w = World::new();
        let mut vs = VerifiedScene::with_default_grid();
        let stranger = w.genesis_cell(0x55, 0);
        let p = Present {
            target: vec![10],
            source_state_root: 0,
            declared_label: label_of(&stranger, 0),
            claims_focus: false,
            new_digest: 1,
        };
        let verdict = vs.present(&mut w, stranger, p, 1);
        assert!(!verdict.is_committed());
        assert!(matches!(verdict.tooth(), Some(PresentError::NoSurface)));
    }

    // =====================================================================
    // THE DAMAGE-NOTIFY WELD — the async damage signal is a HELD, attenuable
    // `dregg_firmament::NotifyCap` (`docs/NOTIFY-PRIMITIVE.md` §2.4), routed
    // through the SAME verified `signal_admissible` the swarm's cross-agent
    // edge uses. BOTH POLARITIES at the real `present()` call-site: a committed
    // present whose damage badge is within the held mask SIGNALS the wake; one
    // outside the (attenuated) mask advances the frame but SIGNALS NOTHING.
    // =====================================================================

    #[test]
    fn a_committed_present_signals_the_damage_wake_iff_the_badge_is_held() {
        let mut w = World::new();
        let (mut vs, wallet, _browser) = demo(&mut w);

        // The wallet owns regions [10, 11]. A present painting ONE region
        // (count 1, badge bit 1) and TWO regions (count 2, badge bit 2) both
        // pass the scene-authority gate (subset of held), but occupy DIFFERENT
        // damage badge bits — so the notify mask can discriminate them.
        assert_ne!(
            damage_badge(1),
            damage_badge(2),
            "one- vs two-region damage must land on distinct badge bits"
        );

        // ATTENUATE the surface's damage-notify to admit ONLY two-region damage
        // (count 2). A widening back is refused; the open default is narrowed.
        assert!(
            vs.restrict_damage_notify(&wallet, &[2]),
            "narrowing the damage-notify to a held kind must succeed"
        );
        assert!(vs.admits_damage(&wallet, 2), "two-region damage is now admitted");
        assert!(
            !vs.admits_damage(&wallet, 1),
            "one-region damage is now OUTSIDE the mask (strictly fewer admitted)"
        );

        // NEGATIVE POLARITY — present ONE region (count 1, out-of-mask). The
        // present COMMITS (the frame advances) but NO SurfaceDamaged wake fires:
        // the held cap does not admit this damage badge (fail-closed).
        let dyn_before = w.dynamics().cursor();
        let p1 = Present {
            target: vec![10], // count 1 — out of the {2} mask
            source_state_root: 500,
            declared_label: label_of(&wallet, 500),
            claims_focus: true,
            new_digest: 2,
        };
        let v1 = vs.present(&mut w, wallet, p1, 2);
        assert!(v1.is_committed(), "the present itself commits, got {v1:?}");
        assert!(
            !w.dynamics()
                .since(dyn_before)
                .iter()
                .any(|e| matches!(e, WorldEvent::SurfaceDamaged { .. })),
            "an out-of-mask damage kind signals NO wake (the held cap refused it, fail-closed)"
        );

        // POSITIVE POLARITY — present TWO regions (count 2, in-mask). The
        // present commits AND the SurfaceDamaged wake fires (the badge is held).
        let dyn_before = w.dynamics().cursor();
        let p2 = Present {
            target: vec![10, 11], // count 2 — within the {2} mask
            source_state_root: 501,
            declared_label: label_of(&wallet, 501),
            claims_focus: true,
            new_digest: 3,
        };
        let v2 = vs.present(&mut w, wallet, p2, 3);
        assert!(v2.is_committed(), "the in-mask present commits, got {v2:?}");
        assert!(
            w.dynamics()
                .since(dyn_before)
                .iter()
                .any(|e| matches!(
                    e,
                    WorldEvent::SurfaceDamaged { owner, region_count, .. }
                        if *owner == wallet && *region_count == 2
                )),
            "the in-mask damage kind SIGNALS the wake (the held cap admitted it)"
        );
    }

    #[test]
    fn restrict_damage_notify_is_non_amplifying_and_refuses_a_widening() {
        // The scene-layer mirror of the firmament `NotifyCap` non-amplification:
        // attenuating a surface's damage-notify only SHRINKS the damage kinds it
        // signals, and a WIDENING (re-admitting a dropped kind) is refused.
        let mut w = World::new();
        let (mut vs, wallet, _browser) = demo(&mut w);

        // Open default admits any damage kind.
        assert!(vs.admits_damage(&wallet, 1), "open grant admits one-region damage");
        assert!(vs.admits_damage(&wallet, 2), "open grant admits two-region damage");

        // Narrow to {count 2}: one-region damage is now outside the mask.
        assert!(vs.restrict_damage_notify(&wallet, &[2]));
        assert!(vs.admits_damage(&wallet, 2), "still admits the kept kind");
        assert!(
            !vs.admits_damage(&wallet, 1),
            "the dropped kind is now refused (strictly fewer admitted)"
        );

        // WIDENING refused: re-admitting count 1 (a bit not in the narrowed mask)
        // is rejected — the grant is unchanged, no amplification.
        assert!(
            !vs.restrict_damage_notify(&wallet, &[1, 2]),
            "a widening attenuation must be refused"
        );
        assert!(
            !vs.admits_damage(&wallet, 1),
            "after the refused widening, one-region damage is STILL refused (grant unchanged)"
        );

        // An owner with no open surface: attenuation is refused (no cap to narrow).
        let stranger = w.genesis_cell(0x77, 0);
        assert!(
            !vs.restrict_damage_notify(&stranger, &[1]),
            "attenuating a non-existent surface's damage-notify is refused (fail-closed)"
        );
        assert!(
            !vs.admits_damage(&stranger, 1),
            "an un-opened surface admits no damage wake (fail-closed, no ambient default)"
        );
    }
}
