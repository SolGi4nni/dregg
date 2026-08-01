//! The **reactive predicate** — the deos gate the Leptos view lights/darkens on.
//!
//! This is the load-bearing module of the prototype and the answer to MAPPING 1
//! (signals ↔ the Reactive rung): a deos cell's state is a Leptos signal, and an
//! affordance renders as a reactive view that lights iff `cap ∧ state` — the runtime
//! dual of the Lean `fireReactive` / `gatedOK` (the htmx tooth).
//!
//! THE DISCIPLINE: this module imports the GENUINE dregg gate, never a parallel one.
//! It depends ONLY on `dregg-cell` — the home of:
//!   * [`Requirement::satisfied_by`] (THE decision function — `required ⊆ held` over
//!     the proven attenuation lattice, i.e. the SAME
//!     [`dregg_cell::is_attenuation`] predicate the firmament runs for every
//!     capability, with the two degenerate lattice ends given their own names),
//!   * [`AuthRequired`] (the real cap lattice, on the HELD side),
//!   * [`CellState`] + [`CellProgram`] + [`StateConstraint`] (the real live-state gate
//!     — the SAME `CellProgram::evaluate` the executor runs every turn).
//!
//! Because `dregg-cell` is execution-engine-free (no `dregg-turn` / no Lean FFI), it
//! compiles to **both** the SSR (native) target AND the **WASM** client island. So the
//! reactive predicate that lights the button on the client is BYTE-FOR-BYTE the gate the
//! server's `EmbeddedExecutor` enforces — the convergence the deos thesis demands.
//!
//! The cap∧state conjunction here is the Rust twin of `Dregg2.Deos.GatedAffordance`'s
//! `gatedOK` (`metatheory/Dregg2/Deos/GatedAffordance.lean`); the WINDOW gate is the
//! twin of `Dregg2.Deos.Reactive`'s `inWindow` (`metatheory/Dregg2/Deos/Reactive.lean`).
//! We reuse the framework's own `GatedAffordance` for the server fire (mapping 3);
//! here we expose the *gate verdict* in a form the reactive view can compute every time
//! the signal changes — the runtime dual of those Lean predicates.

use dregg_cell::state::{CellState, FieldElement, STATE_SLOTS};
use dregg_cell::{AuthRequired, CellProgram, Credential, Requirement, StateConstraint};

/// Slot 0 of the proposal cell carries its `status` (the council exemplar's state machine).
pub const STATUS_SLOT: usize = 0;
/// Slot 1 carries the running `tally` (votes cast) — the reactive counter dimension.
pub const TALLY_SLOT: usize = 1;

/// `status` values.
pub const PENDING: u64 = 1;
pub const RESOLVED: u64 = 2;

/// A field element holding `n` big-endian in its last 8 bytes — exactly the encoding
/// the council exemplar (`app-framework/examples/deos_council_board.rs`) and the field's
/// `FieldEquals` atom read.
pub fn fe(n: u64) -> FieldElement {
    let mut b = [0u8; 32];
    b[24..32].copy_from_slice(&n.to_be_bytes());
    b
}

/// Read the `u64` packed into a field element's last 8 bytes.
pub fn fe_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// A plain, `Clone`/`PartialEq` snapshot of the load-bearing cell slots — the value a
/// Leptos signal carries (a `CellState` is large and not `PartialEq`-friendly to diff in
/// the reactive system, so the signal holds this projection; the gate still evaluates the
/// REAL `CellState`, reconstructed from these slots via [`CellSlots::to_cell_state`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CellSlots {
    /// slot 0 — the proposal status (PENDING / RESOLVED).
    pub status: u64,
    /// slot 1 — the running tally of votes.
    pub tally: u64,
    /// the executor turn height (the `EvalContext::height` the reactive WINDOW gates on).
    pub height: u64,
}

impl CellSlots {
    /// The seed state: a fresh PENDING proposal, zero tally, height 0.
    pub fn pending() -> Self {
        CellSlots {
            status: PENDING,
            tally: 0,
            height: 0,
        }
    }

    /// Project the load-bearing slots out of a REAL [`CellState`] (the read the
    /// server fn returns after a verified turn — so the signal re-seeds from the
    /// executor's own post-state).
    pub fn from_cell_state(s: &CellState) -> Self {
        let status = s.get_field(STATUS_SLOT).map(fe_u64).unwrap_or(0);
        let tally = s.get_field(TALLY_SLOT).map(fe_u64).unwrap_or(0);
        CellSlots {
            status,
            tally,
            height: 0,
        }
    }

    /// Reconstruct a REAL [`CellState`] from these slots — so the gate evaluates the
    /// GENUINE `CellProgram::evaluate` against a genuine `CellState`, never a mock.
    pub fn to_cell_state(&self) -> CellState {
        let mut st = CellState::new(0);
        st.set_field(STATUS_SLOT, fe(self.status));
        st.set_field(TALLY_SLOT, fe(self.tally));
        st
    }

    /// The slot state after a successful `vote` (tally += 1, still PENDING).
    pub fn after_vote(&self) -> Self {
        CellSlots {
            status: PENDING,
            tally: self.tally + 1,
            height: self.height,
        }
    }

    /// The slot state after a successful `resolve` (status := RESOLVED).
    pub fn after_resolve(&self) -> Self {
        CellSlots {
            status: RESOLVED,
            tally: self.tally,
            height: self.height,
        }
    }

    /// Whether the proposal is open (PENDING).
    pub fn is_pending(&self) -> bool {
        self.status == PENDING
    }
}

impl Default for CellSlots {
    fn default() -> Self {
        Self::pending()
    }
}

/// The `vote` affordance's live-state PRECONDITION as a REAL [`CellProgram`]: the
/// proposal must currently be PENDING (`slot[0] == PENDING`). The SAME predicate
/// language the executor enforces every turn — evaluated by the gate against the cell's
/// CURRENT state. (The Rust twin of the council exemplar's `pending_precondition`.)
pub fn pending_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: STATUS_SLOT as u8,
        value: fe(PENDING),
    }])
}

/// The viewer's identity, named by the authority they HOLD (the REAL `is_attenuation`
/// lattice). Three exemplar viewers, exactly as the council board:
///   * the COUNCILLOR holds `Either` (a signature OR a proof clears `vote`/`resolve`);
///   * the MEMBER holds only `Signature` (enough to `comment`, NOT to `vote`);
///   * the OUTSIDER holds an incomparable `Custom` identity (neither attenuates the
///     others — the structural no-peek that drives `membrane_two_viewers_distinct`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Viewer {
    /// A human label for the chrome.
    pub label: &'static str,
    /// The authority this viewer HOLDS — the left side of `is_attenuation(held, required)`.
    pub held: AuthRequired,
}

impl Viewer {
    pub fn councillor() -> Self {
        Viewer {
            label: "councillor",
            held: AuthRequired::Either,
        }
    }
    pub fn member() -> Self {
        Viewer {
            label: "member",
            held: AuthRequired::Signature,
        }
    }
    pub fn outsider() -> Self {
        Viewer {
            label: "outsider",
            held: AuthRequired::Custom {
                vk_hash: [0x9E; 32],
            },
        }
    }
    /// All three exemplar viewers (for the rehydration two-viewers panel).
    pub fn exemplars() -> Vec<Viewer> {
        vec![Self::councillor(), Self::member(), Self::outsider()]
    }
}

/// The **cap-gate** — is a holder of `held` admitted by `required`? THE decision
/// function [`Requirement::satisfied_by`], not a parallel role check: for the four
/// credential rungs it IS the GENUINE [`dregg_cell::is_attenuation`] (`required ⊆
/// held`), the same predicate `delegate.rs` runs to admit a child surface and the
/// membrane runs to compose a reshare.
///
/// ⚑ `required` is a [`Requirement`], NOT an [`AuthRequired`]. This entry point used
/// to take the raw lattice element, which made `AuthRequired::None` spellable here —
/// the value that read as "ungated" to some gates in the workspace and "root only" to
/// others. It is not spellable now: a caller demanding the lattice TOP must say
/// [`Requirement::Root`] and one demanding nothing must say [`Requirement::Public`],
/// and the two are visibly different predicates (see the oracle in this module's
/// tests). The HELD side stays [`AuthRequired`] — there the TOP genuinely means "the
/// widest authority", which is exactly what the holder of it has.
pub fn cap_ok(held: &AuthRequired, required: &Requirement) -> bool {
    required.satisfied_by(held)
}

/// The **state-gate** — does the REAL [`CellProgram::evaluate`] admit firing in the
/// current slot state? The same evaluator the executor runs every turn. For a
/// precondition (no pending write yet) we gate on the current state as both `old` and
/// `new` — "may this button fire right now, in the state the cell is in" (exactly as the
/// framework's `DeosCell::project_gated_for` does).
pub fn state_ok(program: &CellProgram, slots: &CellSlots) -> bool {
    let st = slots.to_cell_state();
    program.evaluate(&st, Some(&st), None).is_ok()
}

/// The **window-gate** — `open ≤ height ≤ close` (the Rust twin of the Lean
/// `Reactive.inWindow`). The temporal dimension of reactivity: a `resolve` button that
/// only lights inside the `[open, close]` voting window.
pub fn in_window(height: u64, open: u64, close: u64) -> bool {
    open <= height && height <= close
}

/// **THE REACTIVE VERDICT** — the cap∧state(∧window) conjunction the Leptos button
/// computes EVERY time the cell signal changes. The runtime dual of the Lean
/// `GatedAffordance.gatedOK` / `Reactive.reactiveOK`: lit IFF the holder's authority
/// admits the cap AND the cell-program admits the state AND (if windowed) the height is
/// in range. Drop ANY conjunct and the button is dark.
///
/// This is the single function the whole prototype's reactivity rests on: the view calls
/// it inside a Leptos reactive closure over `(viewer, slots)`, so the button lights and
/// darkens as the signal moves — no manual DOM poke, the runtime tracks the dependency.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GateVerdict {
    pub cap: bool,
    pub state: bool,
    pub window: bool,
}

impl GateVerdict {
    /// All conjuncts pass — the button is LIT.
    pub fn lit(&self) -> bool {
        self.cap && self.state && self.window
    }

    /// A precise human reason for the FIRST failing tooth (the in-band refusal the
    /// chrome shows — the anti-ghost message, never a silent dark button).
    pub fn dark_reason(&self) -> Option<&'static str> {
        if !self.cap {
            Some("cap tooth: your held authority does not satisfy the required rights")
        } else if !self.state {
            Some("state tooth: the cell's live state forbids this fire right now")
        } else if !self.window {
            Some("window tooth: outside the [open, close] voting window")
        } else {
            None
        }
    }
}

/// Evaluate the cap∧state verdict (no window) for a gated affordance like `vote`/`approve`.
pub fn gated_verdict(
    held: &AuthRequired,
    required: &Requirement,
    program: &CellProgram,
    slots: &CellSlots,
) -> GateVerdict {
    GateVerdict {
        cap: cap_ok(held, required),
        state: state_ok(program, slots),
        window: true,
    }
}

/// Evaluate the cap∧state∧window verdict for a windowed reactive affordance like
/// `resolve` (the deadline tooth — twin of `Reactive.fireReactive_after_deadline_refuses`).
pub fn reactive_verdict(
    held: &AuthRequired,
    required: &Requirement,
    program: &CellProgram,
    slots: &CellSlots,
    open: u64,
    close: u64,
) -> GateVerdict {
    GateVerdict {
        cap: cap_ok(held, required),
        state: state_ok(program, slots),
        window: in_window(slots.height, open, close),
    }
}

/// A guard so the prototype notices if `STATE_SLOTS` ever shrinks below what we index.
const _: () = assert!(STATE_SLOTS > TALLY_SLOT);

#[cfg(test)]
mod tests {
    use super::*;

    /// The councillor/member ballot requirement, in `Requirement` spelling.
    fn either_req() -> Requirement {
        Requirement::AtLeast(Credential::Either)
    }

    #[test]
    fn cap_tooth_is_the_real_is_attenuation() {
        // councillor (Either) clears a Signature-or-Either requirement; member (Signature)
        // does NOT clear an Either requirement; outsider (Custom) is incomparable.
        assert!(cap_ok(&AuthRequired::Either, &either_req()));
        assert!(!cap_ok(&AuthRequired::Signature, &either_req()));
        assert!(!cap_ok(
            &AuthRequired::Custom {
                vk_hash: [0x9E; 32]
            },
            &either_req()
        ));
        // and a Signature holder clears a Signature requirement (the `comment` baseline).
        assert!(cap_ok(
            &AuthRequired::Signature,
            &Requirement::AtLeast(Credential::Signature)
        ));
    }

    /// Every `Requirement` shape, for the exhaustive oracle sweep.
    fn all_requirements() -> Vec<Requirement> {
        vec![
            Requirement::Public,
            Requirement::AtLeast(Credential::Signature),
            Requirement::AtLeast(Credential::Proof),
            Requirement::AtLeast(Credential::Either),
            Requirement::AtLeast(Credential::Custom {
                vk_hash: [0x9E; 32],
            }),
            Requirement::Root,
            Requirement::Never,
        ]
    }

    /// Every authority a viewer can HOLD — including the lattice TOP, the value that
    /// used to be spellable on the required side too.
    fn all_held() -> Vec<AuthRequired> {
        vec![
            AuthRequired::None,
            AuthRequired::Signature,
            AuthRequired::Proof,
            AuthRequired::Either,
            AuthRequired::Impossible,
            AuthRequired::Custom {
                vk_hash: [0x9E; 32],
            },
        ]
    }

    #[test]
    fn the_cap_tooth_is_exactly_the_one_requirement_decision_function() {
        // THE ORACLE. This prototype's reactive gate must return what
        // `Requirement::satisfied_by` returns — for EVERY requirement shape against
        // EVERY holding, on BOTH polarities, not just the pair the council demo
        // exercises. A local special-case here (the historic `None => true`) is
        // exactly what this kills.
        for required in all_requirements() {
            for held in all_held() {
                assert_eq!(
                    cap_ok(&held, &required),
                    required.satisfied_by(&held),
                    "the leptos cap tooth diverged from Requirement::satisfied_by \
                     for required={required:?} held={held:?}"
                );
                // …and the cap conjunct of the FULL verdict is the same function, so
                // a special case cannot hide one layer up.
                let v = gated_verdict(
                    &held,
                    &required,
                    &pending_precondition(),
                    &CellSlots::pending(),
                );
                assert_eq!(v.cap, required.satisfied_by(&held));
            }
        }
    }

    #[test]
    fn root_public_and_never_admit_independently_known_viewer_sets() {
        // The oracle above is an equality against the shared function; this one states
        // the ANSWER independently, so a change to BOTH sides still fails.
        let admitted = |req: Requirement| -> Vec<AuthRequired> {
            all_held().into_iter().filter(|h| cap_ok(h, &req)).collect()
        };

        // `Root` admits EXACTLY the lattice top — a councillor's `Either` does NOT
        // clear it. This is the half of the old `AuthRequired::None` reading that
        // three crates meant.
        assert_eq!(admitted(Requirement::Root), vec![AuthRequired::None]);
        // `Public` admits everyone, including a viewer holding nothing usable. This is
        // the OTHER half two crates meant by the same value.
        assert_eq!(admitted(Requirement::Public), all_held());
        // `Never` admits nobody, not even root.
        assert!(admitted(Requirement::Never).is_empty());
        // The councillor tier: the top and Either — NOT Signature (a member), NOT
        // Proof, NOT the outsider's incomparable Custom.
        assert_eq!(
            admitted(Requirement::AtLeast(Credential::Either)),
            vec![AuthRequired::None, AuthRequired::Either]
        );
        // The outsider's own identity clears its own Custom gate and nothing else's.
        assert_eq!(
            admitted(Requirement::AtLeast(Credential::Custom {
                vk_hash: [0x9E; 32]
            })),
            vec![
                AuthRequired::None,
                AuthRequired::Custom {
                    vk_hash: [0x9E; 32]
                }
            ]
        );
    }

    #[test]
    fn state_tooth_is_the_real_cellprogram() {
        let prog = pending_precondition();
        let pending = CellSlots::pending();
        let resolved = CellSlots {
            status: RESOLVED,
            tally: 3,
            height: 0,
        };
        // PENDING admits the fire; RESOLVED forbids it — the htmx tooth, evaluated by the
        // genuine CellProgram::evaluate.
        assert!(state_ok(&prog, &pending));
        assert!(!state_ok(&prog, &resolved));
    }

    #[test]
    fn gated_verdict_is_the_conjunction() {
        let prog = pending_precondition();
        let pending = CellSlots::pending();
        // councillor + PENDING ⇒ LIT.
        let v = gated_verdict(&AuthRequired::Either, &either_req(), &prog, &pending);
        assert!(v.lit());
        // member + PENDING ⇒ DARK on the cap tooth (right state, wrong caps).
        let v = gated_verdict(&AuthRequired::Signature, &either_req(), &prog, &pending);
        assert!(!v.lit() && v.dark_reason().unwrap().starts_with("cap tooth"));
        // councillor + RESOLVED ⇒ DARK on the state tooth (right caps, wrong state).
        let resolved = CellSlots {
            status: RESOLVED,
            tally: 1,
            height: 0,
        };
        let v = gated_verdict(&AuthRequired::Either, &either_req(), &prog, &resolved);
        assert!(!v.lit() && v.dark_reason().unwrap().starts_with("state tooth"));
    }

    #[test]
    fn window_tooth_closes_the_deadline() {
        let prog = pending_precondition();
        let mut pending = CellSlots::pending();
        pending.height = 5;
        // inside [0,10] ⇒ window passes; at height 11 ⇒ window tooth darkens.
        let v = reactive_verdict(&AuthRequired::Either, &either_req(), &prog, &pending, 0, 10);
        assert!(v.lit());
        pending.height = 11;
        let v = reactive_verdict(&AuthRequired::Either, &either_req(), &prog, &pending, 0, 10);
        assert!(!v.lit() && v.dark_reason().unwrap().starts_with("window tooth"));
    }

    #[test]
    fn slots_roundtrip_through_real_cellstate() {
        let s = CellSlots {
            status: RESOLVED,
            tally: 7,
            height: 0,
        };
        let cs = s.to_cell_state();
        let back = CellSlots::from_cell_state(&cs);
        assert_eq!(s.status, back.status);
        assert_eq!(s.tally, back.tally);
    }
}
