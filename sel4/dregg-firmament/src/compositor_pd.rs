//! The COMPOSITOR-PD — the minimal framebuffer/input multiplexer (`docs/DREGG-
//! DESKTOP-OS.md §2 L5` + `§6 R3 Stage D`, native-now on the semihost
//! [`EmulatedKernel`]).
//!
//! ## What this is (and is NOT)
//!
//! L5 names "**THE COMPOSITOR-PD (the new minimal multiplexer — the ONLY new
//! TCB)**: the third device-holding organ, SOLE holder of framebuffer/GPU + HID
//! device caps. Models its scene as a verified dregg cell. **NO app logic, NO
//! widget toolkit, NO placement policy.** CPU-composited first." This module is
//! exactly that and nothing more: a deliberately-tiny multiplexer that
//!
//! 1. **SOLELY holds the framebuffer region** — an [`EmulatedKernel`] shm region
//!    ([`EmulatedKernel::create_region`]); on the semihost this is a host
//!    in-memory framebuffer. No app-PD is ever handed this region cap; the only
//!    way a pixel reaches it is through a `present()` the compositor itself
//!    composites after the scene authority admits it.
//! 2. **Models its scene as a dregg cell** — an ordered list of [`Surface`]s,
//!    each `(owner, regions, zLayer, focusFlag, …)`, mirroring the Lean
//!    `Dregg2.Apps.Compositor` `Scene`/`Surface` and the starbridge
//!    `compositor.rs` `CompositorScene`/`CompositedSurface`.
//! 3. **Enforces the verified scene AS THE GATE** on every `present(region,
//!    contentDigest)` an app-PD submits over an Endpoint ([`EmulatedKernel`]
//!    `pp_call`):
//!    - **T1 NON-OVERLAP** — an app composites ONLY its cap-authorized region;
//!      an overpaint of another surface's region is **REFUSED** ([`Refusal::Overpaint`]).
//!    - **T3 FOCUS-EXCLUSIVITY** — input routes ONLY to the focused surface; a
//!      misroute (a non-focused cell asserting focus) is **REFUSED**
//!      ([`Refusal::InputMisroute`]); an ambiguous two-focus scene refuses every
//!      present ([`Refusal::DoubleFocus`]).
//!    - **T2 LABEL-BINDING** — the label is the COMPOSITOR's, a function of the
//!      cell's authority lineage (`owner` + `sourceStateRoot`), read by the
//!      compositor, **never** the app's; a label-spoof is **REFUSED**
//!      ([`Refusal::LabelSpoof`]).
//!
//! ## Fidelity (honestly labeled — NOT laundered, §5 F1/F2/F3)
//!
//! [`CompositorPd::FIDELITY`] states it plainly: the framebuffer is a **host
//! buffer** on the semihost, and the compositor-PD enforces **scene AUTHORITY**,
//! not scanned-out pixels. Binding the scanned-out framebuffer to the cell's
//! `contentDigest` (F1 last-hop frame attestation), IOMMU/DMA confinement of a
//! malicious display PD (F2), and a verified GPU/servo compositor (F3) are the
//! named hardware-trust assumptions — the graphics frontier (R3 Stage C). This
//! module is the CPU-composited software-compositor cell (à la EROS/Nitpicker)
//! where T1–T3 are real; **the pixels are the renderer's, the authority is the
//! compositor's.** We do NOT claim verified graphics.
//!
//! ## Reuse, not reinvention (the WELD method)
//!
//! The scene-authority predicates (`t1_non_overlap` / `t2_label_bound` /
//! `t3_focus_exclusive` / `t3_input_routed` / [`Scene::scene_admit`]) mirror the
//! `Dregg2.Apps.Compositor` Lean `AppSpec` (which PROVES T1∧T2∧T3 as anti-ghost
//! teeth via the production caveat-gated executor) and the gpui-side starbridge
//! `compositor.rs` — same shape, same fail-closed sense, same `labelOf owner
//! root := owner * 1000003 + root`. The IPC + shm + cap substrate is the
//! existing [`EmulatedKernel`] (Endpoint `recv`/`reply`, regions); the rights
//! lattice is the genuine [`dregg_cell::is_attenuation`] (`granted ⊆ held`),
//! the SAME gate the firmament, the local Mint, and the distributed delegate
//! use. NOTHING here is a parallel model.

use std::collections::BTreeMap;
use std::vec::Vec;

use dregg_types::CellId;

use crate::emulated_kernel::{EmulatedKernel, Message, ObjectId};

/// An opaque region (rectangle / tile) identity — the unit of compositor
/// ownership. The regions partition the glass; a surface owns a SET of regions;
/// two surfaces' region-sets must be disjoint (T1 non-overlap). Mirrors the Lean
/// `RegionId := Nat` and the starbridge `RegionId`.
pub type RegionId = u32;

/// **`label_of owner root`** — the genuine surface label the compositor renders
/// for a surface owned by `owner` projecting state-root `root` (T2's binding).
///
/// A pure function of the authority lineage. The owning APP NEVER supplies this;
/// the COMPOSITOR computes it from the cell's `(owner, sourceStateRoot)`, so a
/// window cannot label itself as a cell it is not. Mirrors the Lean `labelOf
/// owner root := owner * 1000003 + root` and the starbridge `label_of`, lifting
/// the owner's 32-byte CellId into the same `owner * 1000003 + root` mixing so
/// distinct `(owner, root)` pairs give distinct labels (renderer-agnostic — the
/// real compositor uses Poseidon2 over the provenance lattice, §8 CryptoPortal;
/// the BINDING DISCIPLINE is what T2 enforces, not this particular function).
pub fn label_of(owner: &CellId, source_state_root: u64) -> u128 {
    // Fold the owner CellId into a u128 lineage scalar (the executable model's
    // stand-in for the structured provenance lattice), then the SAME affine mix
    // the Lean `labelOf` uses (`owner * 1000003 + root`). Injective-enough for
    // the model: a different owner OR a different root ⇒ a different label.
    let b = owner.as_bytes();
    let mut acc: u128 = 0;
    for chunk in b.chunks(8) {
        let mut w = [0u8; 8];
        w[..chunk.len()].copy_from_slice(chunk);
        // splitmix-fold the 32 bytes into one lineage scalar.
        acc = acc
            .wrapping_mul(0x1_0000_0000_0000_0000u128.wrapping_add(1))
            .wrapping_add(u64::from_le_bytes(w) as u128);
    }
    acc.wrapping_mul(1_000_003)
        .wrapping_add(source_state_root as u128)
}

/// One surface in the compositor's scene graph — the §5 per-surface tuple
/// `(owningCellId, regionRect, contentDigest, sourceStateRoot, zLayer,
/// focusFlag)`, made concrete. The compositor READS these from its own cell
/// state (it does NOT trust the app to supply the label or the owner). Mirrors
/// the Lean `Surface` and the starbridge `CompositedSurface`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Surface {
    /// The cell that owns this surface — the authority lineage the compositor
    /// reads (NOT app-supplied). T2's label binds to this owner.
    pub owner: CellId,
    /// The set of regions (tiles) this surface occupies. Non-overlap (T1) =
    /// these are pairwise-disjoint across surfaces; a present by `owner` may
    /// target ONLY regions in this set (`granted ⊆ held`).
    pub regions: Vec<RegionId>,
    /// The content digest currently shown (the projection of `source_state_root`).
    /// Advanced by a committed `present()`.
    pub content_digest: u64,
    /// The cell state-root the content is a genuine projection of (the
    /// light-client-checkable bind — T2 binds the label to it).
    pub source_state_root: u64,
    /// The z-layer (stacking order). The trusted-chrome overlay lives at a layer
    /// no app cell holds a cap to (§5 SAK).
    pub z_layer: i64,
    /// Whether this surface holds input focus (T3: at-most-one across the scene).
    pub focus_flag: bool,
}

impl Surface {
    /// Does this surface own `region`? (The T1 region-set membership.)
    pub fn owns_region(&self, region: RegionId) -> bool {
        self.regions.contains(&region)
    }
}

/// The compositor's scene — the ordered list of surfaces. THIS is the verified
/// dregg cell's state (§5: "Its state IS the scene graph — an ordered list of
/// surfaces"). The scene-authority teeth decide every present against it.
/// Mirrors the Lean `Scene` and the starbridge `CompositorScene`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Scene {
    /// Surfaces in paint order (back-to-front; the front-most is last).
    pub surfaces: Vec<Surface>,
}

/// What a `present()` call presents — the Lean `Present` tuple. Submitted by an
/// app-PD over the Endpoint; the compositor folds the whole scene authority into
/// a single admission decision against it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Present {
    /// The region-set this present writes (T1: must be `⊆` the presenter's owned
    /// regions AND disjoint from every foreign surface's regions).
    pub target: Vec<RegionId>,
    /// The state-root the presented content projects (T2: binds the label; also
    /// the root a light client checks the content against).
    pub source_state_root: u64,
    /// The label the present DECLARES (T2: must equal `label_of(presenter,
    /// source_state_root)` — a spoof is refused). An honest app declares the
    /// genuine binding; the gate is what makes the declaration load-bearing.
    pub declared_label: u128,
    /// Whether this present asserts input focus (T3: only the scene's unique
    /// focus holder may — delivering input elsewhere is keystroke theft).
    pub claims_focus: bool,
    /// The new content digest this present commits for its region (the frame
    /// advance; must differ from the current digest — a present changes the frame).
    pub new_digest: u64,
}

/// Why the compositor's scene authority REFUSED a `present()`. Each variant is a
/// tooth of the Lean `*_rejected` theorems (`present_overpaint_rejected` /
/// `present_label_spoof_rejected` / `present_double_focus_rejected` /
/// `present_input_misroute_rejected`). A refusal changes NOTHING (fail-closed —
/// the Rust analogue of the Lean executor returning `none`; the framebuffer the
/// renderer scans can only ever reflect a T1∧T2∧T3-respecting scene).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// **T1** — the present overpaints: its target region-set is NOT `⊆` the
    /// presenter's owned regions, OR it overlaps a region another surface owns.
    /// A cell cannot paint a region another cell holds (no-amplification at the
    /// pixel layer). Carries the offending region(s) for the operator log.
    Overpaint { offending: Vec<RegionId> },
    /// **T2** — the present's declared label is NOT the genuine owner-binding
    /// (`declared_label ≠ label_of(presenter, source_state_root)`). The pale
    /// ghost cannot paint a window labelled as a cell it is not.
    LabelSpoof { declared: u128, genuine: u128 },
    /// **T3 (input)** — the present asserts input focus but the presenter is NOT
    /// the scene's unique focus holder. Input routes only to the focused surface.
    InputMisroute { focus_holder: Option<CellId> },
    /// **T3 (scene)** — the scene already has TWO+ focus flags (ambiguous input);
    /// no present can commit into a scene that routes input ambiguously.
    DoubleFocus { focus_count: usize },
    /// The presenter owns no surface in the scene (it cannot present against a
    /// scene it has no surface in).
    NoSurface,
    /// The present does not advance the frame (`new_digest == current`); a
    /// present must genuinely change the frame (the Lean `new ≠ old` leg).
    NoFrameAdvance,
}

impl Refusal {
    /// A short operator-legible tag (the tooth that bit).
    pub fn tooth(&self) -> &'static str {
        match self {
            Refusal::Overpaint { .. } => "T1 overpaint",
            Refusal::LabelSpoof { .. } => "T2 label-spoof",
            Refusal::InputMisroute { .. } => "T3 input-misroute",
            Refusal::DoubleFocus { .. } => "T3 double-focus",
            Refusal::NoSurface => "no surface",
            Refusal::NoFrameAdvance => "no frame advance",
        }
    }
}

impl Scene {
    // ── The three scene-authority teeth (decidable, fail-closed) ──────────────
    //
    // These mirror the Lean `t1NonOverlap` / `t2LabelBound` / `t3FocusExclusive`
    // / `t3InputRouted` predicates EXACTLY — same shape, same fail-closed sense.

    /// **T1 NON-OVERLAP.** Is a present by `presenter` targeting `target`
    /// T1-admissible? Iff (a) `presenter` owns a surface AND `target ⊆` its owned
    /// region-set (`granted ⊆ held`), AND (b) `target` is disjoint from EVERY
    /// foreign surface's regions (no overpaint of a region another cell owns).
    /// Mirrors the Lean `t1NonOverlap sc presenter target`.
    pub fn t1_non_overlap(&self, presenter: &CellId, target: &[RegionId]) -> bool {
        // (a) the presenter owns a surface whose region-set covers `target`:
        let owns_all = self
            .surfaces
            .iter()
            .any(|s| &s.owner == presenter && target.iter().all(|r| s.owns_region(*r)));
        if !owns_all {
            return false;
        }
        // (b) `target` is disjoint from every FOREIGN surface's regions:
        self.surfaces
            .iter()
            .all(|s| &s.owner == presenter || target.iter().all(|r| !s.owns_region(*r)))
    }

    /// The specific target regions that would overpaint (the refusal reason):
    /// regions the presenter does not own, plus any that collide with a foreign
    /// surface. Empty iff T1 holds.
    fn overpaint_regions(&self, presenter: &CellId, target: &[RegionId]) -> Vec<RegionId> {
        let owned: Vec<RegionId> = self
            .surfaces
            .iter()
            .filter(|s| &s.owner == presenter)
            .flat_map(|s| s.regions.iter().copied())
            .collect();
        let foreign: Vec<RegionId> = self
            .surfaces
            .iter()
            .filter(|s| &s.owner != presenter)
            .flat_map(|s| s.regions.iter().copied())
            .collect();
        target
            .iter()
            .copied()
            .filter(|r| !owned.contains(r) || foreign.contains(r))
            .collect()
    }

    /// **T2 LABEL-BINDING.** Is a present declaring `declared_label` while
    /// projecting `source_state_root`, by `presenter`, T2-admissible? Iff
    /// `declared_label == label_of(presenter, source_state_root)` — the label is
    /// the genuine owner-binding the COMPOSITOR computes, not an app-chosen one.
    /// Mirrors the Lean `t2LabelBound presenter sourceStateRoot declaredLabel`.
    pub fn t2_label_bound(
        &self,
        presenter: &CellId,
        source_state_root: u64,
        declared_label: u128,
    ) -> bool {
        declared_label == label_of(presenter, source_state_root)
    }

    /// **T3 FOCUS-EXCLUSIVITY (scene).** Is the scene T3-admissible? Iff
    /// AT-MOST-ONE surface holds `focus_flag`. Mirrors the Lean `t3FocusExclusive
    /// sc` / `countFocus sc ≤ 1`.
    pub fn t3_focus_exclusive(&self) -> bool {
        self.focus_count() <= 1
    }

    /// The number of focused surfaces (Lean `countFocus`). At-most-one is the T3
    /// invariant; two is an ambiguous-input scene.
    pub fn focus_count(&self) -> usize {
        self.surfaces.iter().filter(|s| s.focus_flag).count()
    }

    /// The unique focus holder (the owner of the focused surface), if any. Input
    /// routes ONLY here. Mirrors the Lean `focusHolder sc`.
    pub fn focus_holder(&self) -> Option<CellId> {
        self.surfaces.iter().find(|s| s.focus_flag).map(|s| s.owner)
    }

    /// **T3 INPUT-ROUTING.** Is a present that may assert focus (`claims_focus`)
    /// input-route-admissible? When it asserts focus, the presenter MUST be the
    /// scene's unique focus holder; a non-input present (`claims_focus == false`)
    /// is vacuously routed. Mirrors the Lean `t3InputRouted sc presenter
    /// claimsFocus`.
    pub fn t3_input_routed(&self, presenter: &CellId, claims_focus: bool) -> bool {
        !claims_focus || self.focus_holder().as_ref() == Some(presenter)
    }

    /// **THE FOLDED SCENE ADMISSION** — does the scene authority admit this
    /// present? The conjunction T1 ∧ T2 ∧ T3 (non-overlap ∧ label-bound ∧
    /// focus-exclusive ∧ input-routed) AND a genuine frame advance, computed from
    /// the closed-over scene. `Ok(())` if admitted, else the specific tooth that
    /// bit. Mirrors the Lean `sceneAdmit sc presenter p old new` (the whole scene
    /// authority folded to the scalar boundary).
    pub fn scene_admit(&self, presenter: &CellId, p: &Present) -> Result<(), Refusal> {
        // The current frame digest the presenter's surface shows (the Lean `old`).
        let current = self
            .surfaces
            .iter()
            .find(|s| &s.owner == presenter)
            .map(|s| s.content_digest);
        let Some(current) = current else {
            return Err(Refusal::NoSurface);
        };
        // T3 scene: at-most-one focus flag (an ambiguous scene rejects every
        // present, the Lean double-focus tooth).
        if !self.t3_focus_exclusive() {
            return Err(Refusal::DoubleFocus {
                focus_count: self.focus_count(),
            });
        }
        // T1: non-overlap / granted ⊆ held.
        if !self.t1_non_overlap(presenter, &p.target) {
            return Err(Refusal::Overpaint {
                offending: self.overpaint_regions(presenter, &p.target),
            });
        }
        // T2: label = the genuine owner-binding.
        if !self.t2_label_bound(presenter, p.source_state_root, p.declared_label) {
            return Err(Refusal::LabelSpoof {
                declared: p.declared_label,
                genuine: label_of(presenter, p.source_state_root),
            });
        }
        // T3 input: input routes only to the focus holder.
        if !self.t3_input_routed(presenter, p.claims_focus) {
            return Err(Refusal::InputMisroute {
                focus_holder: self.focus_holder(),
            });
        }
        // A present genuinely advances the frame (the Lean `new ≠ old` leg).
        if p.new_digest == current {
            return Err(Refusal::NoFrameAdvance);
        }
        Ok(())
    }
}

/// One committed present in the compositor's frame log — the analogue of an
/// on-ledger receipt (Lean §10 "the present recorded on-ledger"). The log is the
/// scene's provenance: every genuine frame advance is recorded. A refused
/// present never appears here (fail-closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrameCommit {
    /// The presenter that advanced the frame.
    pub presenter: CellId,
    /// The region-set it painted (all `⊆` its owned set, disjoint from foreign).
    pub regions: Vec<RegionId>,
    /// The content digest it committed (the new frame).
    pub digest: u64,
    /// The state-root the content projects (the light-client bind).
    pub source_state_root: u64,
    /// The genuine owner-label bound to this frame (T2).
    pub label: u128,
}

// ─────────────────────────── the present() wire ─────────────────────────────
//
// An app-PD submits `present(region, contentDigest)` over the Endpoint via
// `Channel::pp_call`, which carries a `Message { label, bytes }`. The compositor
// is the Endpoint SERVER: it `recv`s, decodes the `Present`, runs the scene
// gate, composites the authorized region into the framebuffer (its SOLE region),
// and `reply`s the verdict. The presenter is named in the wire bytes (in a real
// CapDL boot the executor binds the presenter to the calling PD's surface-cap;
// the boot test threads it explicitly, exactly as the boot_pds slice wires
// channels explicitly).

/// The Endpoint message label for a `present()` request (the `MessageInfo` tag
/// the receiver dispatches on).
pub const LABEL_PRESENT: u64 = 1;

/// The reply label when a present COMMITTED (the frame advanced).
pub const LABEL_PRESENT_OK: u64 = 2;

/// The reply label when a present was REFUSED by the scene authority (a tooth
/// bit). The reply payload's first byte is the [`Refusal`] discriminant.
pub const LABEL_PRESENT_REFUSED: u64 = 3;

/// Encode a `present()` request into the Endpoint message bytes. Hand-rolled +
/// dependency-free (the firmament keeps a minimal dep graph — same discipline as
/// the process-kernel control wire). Layout: presenter(32) ‖ source_root(8) ‖
/// declared_label(16) ‖ new_digest(8) ‖ claims_focus(1) ‖ region_count(4) ‖
/// regions(4·n), all little-endian.
pub fn encode_present(presenter: &CellId, p: &Present) -> Vec<u8> {
    let mut v = Vec::with_capacity(32 + 8 + 16 + 8 + 1 + 4 + 4 * p.target.len());
    v.extend_from_slice(presenter.as_bytes());
    v.extend_from_slice(&p.source_state_root.to_le_bytes());
    v.extend_from_slice(&p.declared_label.to_le_bytes());
    v.extend_from_slice(&p.new_digest.to_le_bytes());
    v.push(p.claims_focus as u8);
    v.extend_from_slice(&(p.target.len() as u32).to_le_bytes());
    for r in &p.target {
        v.extend_from_slice(&r.to_le_bytes());
    }
    v
}

/// Decode a `present()` request from the Endpoint message bytes (the inverse of
/// [`encode_present`]). Returns `None` on a malformed frame — which the
/// compositor treats as a refused present (fail-closed; a garbage frame from an
/// app never advances the frame).
pub fn decode_present(b: &[u8]) -> Option<(CellId, Present)> {
    let presenter = CellId::from_bytes(b.get(0..32)?.try_into().ok()?);
    let source_state_root = u64::from_le_bytes(b.get(32..40)?.try_into().ok()?);
    let declared_label = u128::from_le_bytes(b.get(40..56)?.try_into().ok()?);
    let new_digest = u64::from_le_bytes(b.get(56..64)?.try_into().ok()?);
    let claims_focus = *b.get(64)? != 0;
    let count = u32::from_le_bytes(b.get(65..69)?.try_into().ok()?) as usize;
    let mut target = Vec::with_capacity(count);
    let mut off = 69;
    for _ in 0..count {
        target.push(u32::from_le_bytes(b.get(off..off + 4)?.try_into().ok()?));
        off += 4;
    }
    Some((
        presenter,
        Present {
            target,
            source_state_root,
            declared_label,
            claims_focus,
            new_digest,
        },
    ))
}

// ─────────────────────────── the framebuffer layout ─────────────────────────
//
// The semihost framebuffer is a host byte buffer (an EmulatedKernel region) the
// compositor SOLELY holds. We model it as a flat array of one byte per region
// (a tile's composited digest, low byte) — enough to PROVE the authority gate:
// only the cap-authorized region of an admitted present is written, and an
// overpaint never reaches the buffer. The pixels' real format is the renderer's
// (F1/F2/F3 frontier); the buffer here witnesses WHICH region the compositor
// composited, the load-bearing authority observable.

/// The number of region-tiles the semihost framebuffer addresses (one byte each
/// in the host buffer). A present's region ids index into this; the boot test's
/// scene uses small ids well within it.
pub const FRAMEBUFFER_TILES: usize = 256;

/// THE COMPOSITOR-PD — the minimal framebuffer/input multiplexer on the
/// [`EmulatedKernel`] (`docs/DREGG-DESKTOP-OS.md §2 L5` + `§6 R3 Stage D`).
///
/// It is the SOLE holder of the framebuffer region ([`Self::framebuffer`], an
/// EmulatedKernel shm region no app-PD is granted), models its scene as a dregg
/// cell ([`Self::scene`]), and enforces T1∧T2∧T3 as the gate on every
/// `present()`. NO app logic, NO widget toolkit, NO placement policy — the scene
/// is composed by the shell (L6) and handed in; the compositor only multiplexes
/// authority over it. It is the ONLY new TCB.
pub struct CompositorPd {
    /// The shared [`EmulatedKernel`] (the n=1 microkernel) — the compositor holds
    /// it to own its framebuffer region + serve its Endpoint.
    kernel: EmulatedKernel,
    /// THE FRAMEBUFFER — the EmulatedKernel region the compositor SOLELY holds.
    /// On the semihost this is a host in-memory buffer; no app-PD is handed this
    /// region cap, so the only path to a pixel is a `present()` the compositor
    /// composites after the gate admits it.
    framebuffer: ObjectId,
    /// The scene graph — the compositor cell's state (ordered surfaces). The
    /// scene authority decides every present against it.
    scene: Scene,
    /// The append-only frame log (committed presents, in order) — the scene's
    /// provenance. A refused present never appears here (fail-closed).
    frames: Vec<FrameCommit>,
    /// Per-presenter present counts (for the boot test / operator log).
    present_counts: BTreeMap<CellId, u64>,
}

impl CompositorPd {
    /// A short, honest statement of the fidelity boundary — it travels WITH the
    /// code, NEVER laundered (`docs/DREGG-DESKTOP-OS.md §5` F1/F2/F3, the
    /// don't-launder-vacuity discipline). The compositor-PD enforces scene
    /// AUTHORITY (T1∧T2∧T3 — verified here, mirroring the Lean AppSpec proofs);
    /// the PIXELS are the renderer's.
    pub const FIDELITY: &'static str = "\
        The compositor-PD enforces SCENE AUTHORITY (T1 non-overlap / T2 \
        label-binding / T3 focus-exclusivity), the anti-ghost teeth proven in \
        the Lean Dregg2.Apps.Compositor AppSpec. On the SEMIHOST the framebuffer \
        is a HOST in-memory buffer (an EmulatedKernel region), NOT a scanned-out \
        panel; this is NOT verified graphics. Binding scanned-out pixels to the \
        cell's contentDigest (F1 last-hop frame attestation), IOMMU/DMA \
        confinement of a malicious display PD (F2), and a verified GPU/servo \
        compositor (F3) are the named hardware-trust frontier (R3 Stage C) — \
        severe problems with closure lanes, never walls, NOT solved here. The \
        compositor mediates AUTHORITY over the scene (verified); the pixels it \
        produces are the renderer's.";

    /// Boot the compositor-PD on the [`EmulatedKernel`]: it allocates and SOLELY
    /// holds a framebuffer region of [`FRAMEBUFFER_TILES`] bytes, starting with
    /// the given `scene`. The framebuffer region cap is never handed to an
    /// app-PD; the compositor is the only writer.
    pub fn boot(kernel: EmulatedKernel, scene: Scene) -> Self {
        let framebuffer = kernel.create_region(FRAMEBUFFER_TILES);
        CompositorPd {
            kernel,
            framebuffer,
            scene,
            frames: Vec::new(),
            present_counts: BTreeMap::new(),
        }
    }

    /// The framebuffer region id (the compositor's SOLE-held region). Exposed so
    /// the boot harness can READ it as the observable — it is NEVER granted to an
    /// app-PD (an app reaches a pixel only by a `present()` the gate admits).
    pub fn framebuffer(&self) -> ObjectId {
        self.framebuffer
    }

    /// The current scene (read-only).
    pub fn scene(&self) -> &Scene {
        &self.scene
    }

    /// Replace the whole scene (the shell L6 composes it from its owned surfaces;
    /// the compositor enforces the teeth against THIS scene — NO placement policy
    /// of its own). The scene is the closed-over authority of §4.
    pub fn set_scene(&mut self, scene: Scene) {
        self.scene = scene;
    }

    /// The committed frame log (the scene's provenance — every genuine present).
    pub fn frames(&self) -> &[FrameCommit] {
        &self.frames
    }

    /// Read a snapshot of the framebuffer (the host buffer) — the boot
    /// observable. Byte `r` is the low byte of the digest last composited into
    /// region `r`; `0` means never composited (so an overpaint that never
    /// committed leaves the victim's region's byte unchanged).
    pub fn framebuffer_snapshot(&self) -> Vec<u8> {
        self.kernel
            .region_read(self.framebuffer)
            .unwrap_or_default()
    }

    /// **PRESENT — the cap-gated frame advance + composite.** An app-PD submits a
    /// present against the compositor; the scene authority is folded in
    /// ([`Scene::scene_admit`]) and, IFF every tooth admits it, the compositor
    /// (a) advances the presenter's surface frame digest, (b) composites the
    /// authorized region(s) into the framebuffer it SOLELY holds, and (c) records
    /// the present in the frame log. A present any tooth forbids is REFUSED and
    /// changes NOTHING — no pixel written, no frame logged (fail-closed, the Rust
    /// analogue of the Lean executor returning `none`).
    ///
    /// This is the in-process entry the Endpoint server ([`Self::serve_present`])
    /// calls after decoding; it is also directly callable (the boot test drives
    /// both the in-process path and the IPC path).
    pub fn present(&mut self, presenter: &CellId, p: Present) -> Result<FrameCommit, Refusal> {
        // THE GATE: the scene authority decides. A refusal returns here, before
        // any pixel or state mutation — fail-closed.
        self.scene.scene_admit(presenter, &p)?;

        // Admitted. Composite the authorized region(s) into the framebuffer the
        // compositor SOLELY holds — the ONLY write path to a pixel. By T1 every
        // target region is `⊆` the presenter's owned set and disjoint from
        // foreign surfaces, so this writes ONLY the presenter's own tiles.
        let digest_byte = (p.new_digest & 0xFF) as u8;
        let target = p.target.clone();
        self.kernel
            .region_with_mut(self.framebuffer, |fb| {
                for &r in &target {
                    if let Some(slot) = fb.get_mut(r as usize) {
                        *slot = digest_byte;
                    }
                }
            })
            .expect("compositor holds its framebuffer region");

        // Advance the presenter's surface frame digest + source-root in the scene.
        if let Some(s) = self
            .scene
            .surfaces
            .iter_mut()
            .find(|s| &s.owner == presenter)
        {
            s.content_digest = p.new_digest;
            s.source_state_root = p.source_state_root;
        }

        let commit = FrameCommit {
            presenter: *presenter,
            regions: p.target,
            digest: p.new_digest,
            source_state_root: p.source_state_root,
            label: p.declared_label,
        };
        self.frames.push(commit.clone());
        *self.present_counts.entry(*presenter).or_insert(0) += 1;
        Ok(commit)
    }

    /// Serve ONE `present()` request off an Endpoint: `recv` a call, decode the
    /// `Present`, run [`Self::present`] (the gate + composite), and `reply` the
    /// verdict ([`LABEL_PRESENT_OK`] / [`LABEL_PRESENT_REFUSED`]). This is the
    /// compositor-PD's protected-procedure body — the cross-PD form of the gate.
    /// Blocks until an app-PD calls (faithful seL4 Endpoint synchrony). Returns
    /// the verdict it replied (so a single-threaded harness can assert it).
    ///
    /// A malformed frame is replied REFUSED (fail-closed) — a garbage call from
    /// an app never advances the frame.
    pub fn serve_present(
        &mut self,
        endpoint: ObjectId,
    ) -> Result<Result<FrameCommit, Refusal>, crate::IpcError> {
        let (msg, token) = self.kernel.recv(endpoint)?;
        let verdict = self.dispatch_present_message(&msg);
        let reply = match &verdict {
            Ok(commit) => Message::new(
                LABEL_PRESENT_OK,
                (commit.digest & 0xFF).to_le_bytes().to_vec(),
            ),
            Err(refusal) => {
                Message::new(LABEL_PRESENT_REFUSED, vec![refusal_discriminant(refusal)])
            }
        };
        self.kernel.reply(token, reply)?;
        Ok(verdict)
    }

    /// Serve one `present()` request whose call was staged INLINE (the
    /// single-threaded `call_served_by` convenience) — decode + gate + the reply
    /// message, with no second thread. The boot test uses this to run the
    /// compositor's protected body on the SAME thread as the calling app-PD stub
    /// (exactly as `EmulatedKernel::call_served_by` collapses a rendezvous for a
    /// simple boot test). Returns the reply message; the gate's side effects
    /// (composite + log) land on `self`.
    pub fn serve_present_inline(&mut self, call: Message) -> Message {
        let verdict = self.dispatch_present_message(&call);
        match verdict {
            Ok(commit) => Message::new(
                LABEL_PRESENT_OK,
                (commit.digest & 0xFF).to_le_bytes().to_vec(),
            ),
            Err(refusal) => {
                Message::new(LABEL_PRESENT_REFUSED, vec![refusal_discriminant(&refusal)])
            }
        }
    }

    /// Decode + gate a `present()` message (shared by the cross-thread and inline
    /// serve paths). A malformed frame is a refused present (fail-closed).
    fn dispatch_present_message(&mut self, msg: &Message) -> Result<FrameCommit, Refusal> {
        if msg.label != LABEL_PRESENT {
            // An unknown verb is refused (the compositor serves only present()).
            return Err(Refusal::NoFrameAdvance);
        }
        match decode_present(&msg.bytes) {
            Some((presenter, p)) => self.present(&presenter, p),
            None => Err(Refusal::NoFrameAdvance), // garbage frame ⇒ no advance
        }
    }

    /// **ROUTE INPUT — the T3 input gate.** Deliver an input event to the
    /// `claimed` surface, returning its owner — or REFUSE if `claimed` is not the
    /// scene's unique focus holder. Input is delivered ONLY to the cell the user
    /// demonstrably chose (the focus holder); a misroute is refused (keystroke
    /// theft prevented). Mirrors the starbridge `route_input` and the Lean T3
    /// input-routing tooth.
    pub fn route_input(&self, claimed: &CellId) -> Result<CellId, Refusal> {
        match self.scene.focus_holder() {
            Some(holder) if &holder == claimed => Ok(holder),
            holder => Err(Refusal::InputMisroute {
                focus_holder: holder,
            }),
        }
    }

    /// How many presents `presenter` has committed (the operator log / boot
    /// observable).
    pub fn present_count(&self, presenter: &CellId) -> u64 {
        self.present_counts.get(presenter).copied().unwrap_or(0)
    }
}

/// The [`Refusal`] discriminant byte for the reply wire (so an app-PD learns
/// WHICH tooth bit without a full codec). Stable small tags.
fn refusal_discriminant(r: &Refusal) -> u8 {
    match r {
        Refusal::Overpaint { .. } => 1,
        Refusal::LabelSpoof { .. } => 2,
        Refusal::InputMisroute { .. } => 3,
        Refusal::DoubleFocus { .. } => 4,
        Refusal::NoSurface => 5,
        Refusal::NoFrameAdvance => 6,
    }
}

/// A tiny, deterministic [`CellId`] derivation for tests / boot scenes — the
/// SAME `seed → CellId` shape the firmament's other tests + the Lean demo use
/// (`pk[0] = seed`), so a surface is addressable by seed across the slice.
pub fn cell_seed(seed: u8) -> CellId {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(7);
    CellId::derive_raw(&pk, &[0u8; 32])
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The honest two-surface scene from the Lean `demoScene`, transposed to
    /// CellIds: wallet (seed 1, regions {10,11}, root 500, FOCUSED) + browser
    /// (seed 2, regions {20,21}, root 600) + trusted chrome (seed 9, region {99},
    /// top z). The compositor cell holds THIS as its state.
    fn demo_scene() -> (Scene, CellId, CellId, CellId) {
        let wallet = cell_seed(1);
        let browser = cell_seed(2);
        let chrome = cell_seed(9);
        let scene = Scene {
            surfaces: vec![
                Surface {
                    owner: wallet,
                    regions: vec![10, 11],
                    content_digest: 1234,
                    source_state_root: 500,
                    z_layer: 0,
                    focus_flag: true,
                },
                Surface {
                    owner: browser,
                    regions: vec![20, 21],
                    content_digest: 5678,
                    source_state_root: 600,
                    z_layer: 0,
                    focus_flag: false,
                },
                Surface {
                    owner: chrome,
                    regions: vec![99],
                    content_digest: 9999,
                    source_state_root: 700,
                    z_layer: 100,
                    focus_flag: false,
                },
            ],
        };
        (scene, wallet, browser, chrome)
    }

    // ── The scene-authority predicates mirror the Lean teeth (unit level) ──────

    #[test]
    fn label_of_binds_owner_and_root_injectively() {
        let a = cell_seed(1);
        let b = cell_seed(2);
        assert_ne!(
            label_of(&a, 500),
            label_of(&b, 500),
            "owner changes the label"
        );
        assert_ne!(
            label_of(&a, 500),
            label_of(&a, 600),
            "root changes the label"
        );
        assert_eq!(
            label_of(&a, 500),
            label_of(&a, 500),
            "the binding is a function"
        );
    }

    #[test]
    fn t1_owner_paints_its_region_but_a_foreigner_cannot() {
        let (scene, wallet, browser, _) = demo_scene();
        assert!(
            scene.t1_non_overlap(&wallet, &[10]),
            "wallet owns region 10"
        );
        assert!(
            scene.t1_non_overlap(&wallet, &[10, 11]),
            "wallet owns both its regions"
        );
        assert!(
            !scene.t1_non_overlap(&browser, &[10]),
            "the browser overpainting the wallet's region 10 is refused (T1)"
        );
        assert!(
            !scene.t1_non_overlap(&wallet, &[99]),
            "the wallet cannot paint the chrome's region 99 (T1)"
        );
    }

    #[test]
    fn t2_genuine_label_binds_and_a_spoof_is_refused() {
        let (scene, wallet, browser, _) = demo_scene();
        let wallet_label = label_of(&wallet, 500);
        assert!(
            scene.t2_label_bound(&wallet, 500, wallet_label),
            "wallet's genuine label binds"
        );
        assert!(
            !scene.t2_label_bound(&browser, 600, wallet_label),
            "the browser declaring the wallet's label fails (T2 spoof)"
        );
    }

    #[test]
    fn t3_at_most_one_focus_and_input_routes_only_there() {
        let (scene, wallet, browser, _) = demo_scene();
        assert!(
            scene.t3_focus_exclusive(),
            "the honest scene has at-most-one focus"
        );
        assert_eq!(scene.focus_count(), 1, "exactly one focus holder");
        assert_eq!(scene.focus_holder(), Some(wallet), "the wallet holds focus");
        assert!(
            scene.t3_input_routed(&wallet, true),
            "the focus holder may assert focus"
        );
        assert!(
            !scene.t3_input_routed(&browser, true),
            "the non-focused browser asserting focus mis-routes (T3)"
        );
        assert!(
            scene.t3_input_routed(&browser, false),
            "a non-input present is fine"
        );
    }

    #[test]
    fn double_focus_scene_refuses_every_present() {
        let wallet = cell_seed(1);
        let browser = cell_seed(2);
        let scene = Scene {
            surfaces: vec![
                Surface {
                    owner: wallet,
                    regions: vec![10],
                    content_digest: 1,
                    source_state_root: 500,
                    z_layer: 0,
                    focus_flag: true,
                },
                Surface {
                    owner: browser,
                    regions: vec![20],
                    content_digest: 2,
                    source_state_root: 600,
                    z_layer: 0,
                    focus_flag: true,
                },
            ],
        };
        assert!(
            !scene.t3_focus_exclusive(),
            "two focus flags ⇒ not exclusive"
        );
        assert_eq!(scene.focus_count(), 2);
        let honest = Present {
            target: vec![10],
            source_state_root: 500,
            declared_label: label_of(&wallet, 500),
            claims_focus: false,
            new_digest: 4242,
        };
        assert!(
            matches!(
                scene.scene_admit(&wallet, &honest),
                Err(Refusal::DoubleFocus { .. })
            ),
            "an ambiguous-input scene rejects every present (T3)"
        );
    }

    // ── The encode/decode wire round-trips (the present() IPC framing) ─────────

    #[test]
    fn present_wire_round_trips() {
        let presenter = cell_seed(1);
        let p = Present {
            target: vec![10, 11, 12],
            source_state_root: 0xDEAD_BEEF,
            declared_label: 0x0123_4567_89AB_CDEF_0011_2233_4455_6677,
            claims_focus: true,
            new_digest: 0xCAFE,
        };
        let (q_presenter, q) = decode_present(&encode_present(&presenter, &p)).unwrap();
        assert_eq!(q_presenter, presenter);
        assert_eq!(q, p);
    }

    #[test]
    fn malformed_present_frame_decodes_to_none() {
        assert!(
            decode_present(&[0u8; 10]).is_none(),
            "a short frame is rejected"
        );
    }
}
