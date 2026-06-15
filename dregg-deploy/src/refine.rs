//! `refine`: a deploy-time **behavioral REFINEMENT** gate over a DreggDL plan,
//! decided by a Rust mirror of `metatheory/Dregg2/Deos/FlowRefine.lean`'s
//! `decideRefines` (the sound+complete simulation-game decision procedure for
//! the right-skewed flow order `≤ᶠ`).
//!
//! ## The idea (DreggDL's lowered turn-sequence IS a flow)
//!
//! [`crate::apply::build_turn_sequence`] lowers a DreggDL spec into an ordered,
//! receipt-chained turn sequence — births, then funds, then grants (the
//! delegation forest nested), in dependency order. That sequence is precisely a
//! **flow** in the sense of `Dregg2.Deos.FlowAlgebra`: a state-threaded sequence
//! of observable affordance-fires. Each effect the deployment performs is one
//! *visible letter* (the affordance fired, with its capability shape); the
//! phase/dependency order is sequential composition `⋆`.
//!
//! `FlowAlgebra` proved this algebra is **right-skewed** (`≤ᶠ` is online
//! step-by-step simulation, NOT trace language), and `FlowRefine` made the
//! refinement question `A ≤ᶠ B` a **decidable** simulation game
//! (`decideRefines`, sound+complete, σ-free — the state never decides a move).
//! So a DreggDL plan can gain a deploy-time **refinement** check on top of its
//! existing static no-amplification **safety** check.
//!
//! ## Two new checks (what refinement buys, beyond no-amplification)
//!
//!   * **safe-upgrade** ([`refines_upgrade`]): *does the NEW deploy spec refine
//!     the RUNNING one?* If `new ≤ᶠ old`, the new deployment only NARROWS
//!     behavior — every effect-sequence the new plan can perform, the old one
//!     already could; no new reachable effect is introduced. An upgrade that
//!     WIDENS (adds an effect / a wider capability the running plan never had)
//!     is rejected, with the divergence named.
//!   * **intent-conformance** ([`refines_intent`]): *does the LOWERED sequence
//!     refine the declared ABSTRACT intent?* The operator writes an intent flow
//!     (the effects they MEANT to authorize, as a [`FlowSpec`]); the gate decides
//!     `lowered ≤ᶠ intent`. A lowering that does MORE than the intent declared
//!     (a stray grant, a wider cap) fails — the lowering is held to its stated
//!     envelope.
//!
//! ## The honest boundary (static no-amplification vs behavioral refinement)
//!
//! These are DIFFERENT properties and neither subsumes the other:
//!
//!   * `dregg-userspace-verify::check_no_amplification` is a **static** graph
//!     property of ONE forest: along each delegation edge, the child cap is `⊆`
//!     the parent cap (no re-delegation amplifies). It says nothing about how the
//!     deployment relates to a *previous* deployment or to an *intent*.
//!   * The refinement check here is a **behavioral** relation between TWO flows:
//!     does plan `A` only do what plan/intent `B` permits, move-for-move, in the
//!     online simulation order `≤ᶠ`? It is the `decideRefines` game, run over the
//!     deploy's effect-letters.
//!
//! A spec can pass no-amplification (its own grant graph attenuates) yet FAIL
//! safe-upgrade (it widens relative to what was running), and vice versa. The
//! `apply` gate runs no-amplification; this module adds the optional refinement
//! gate when a target (a running plan or an intent) is supplied.
//!
//! ## The verified procedure runs the gate (Lean-FFI, with a σ-free fallback)
//!
//! [`decide_refines`] routes its `A ≤ᶠ B` decision through the verified Lean
//! `@[export] dregg_decide_refines` (the PROVEN `FlowRefine.decideRefines`) when
//! the linked archive exports it — so on a native build the deploy gate runs the
//! *proven* decision procedure, whose soundness + completeness against `≤ᶠ` is the
//! Lean theorem `decideRefines_iff` (LAW #1). The two flows are serialized to the
//! export's preorder-token wire ([`encode_proc`], the byte-exact inverse of
//! `FlowRefine.encodeProcToks`/`decodeProc`).
//!
//! The in-process σ-free game ([`decide_refines_mirror`]) remains as the FALLBACK
//! for targets that cannot link the Lean archive (`wasm32`, the zkvm guest) or a
//! stale archive predating the export. It AGREES with the verified procedure by
//! construction: the game is **σ-free** (`FlowRefine` §3 — the threaded state never
//! decides a move; `PStep`/`moves` are purely syntactic), so the decision is a
//! finite, state-free recursion the Lean and the Rust run identically. The
//! differential test in `tests.rs` asserts FFI-verdict == mirror-verdict on both
//! polarities of `FlowAlgebra`'s counterexample.

use dregg_turn::action::Effect;
use dregg_turn::{CallForest, CallTree};

use crate::apply::AppliedPlan;
use crate::facet::describe_allowed_effects;

// ════════════════════════════════════════════════════════════════════════════
//  §1 — The σ-free `Proc` + `decideRefines` mirror (FlowRefine.lean §1, §4).
// ════════════════════════════════════════════════════════════════════════════

/// A σ-free process — the `Proc`-only projection of `FlowAlgebra.Proc`, exactly
/// the fragment `FlowRefine.PStep` / `moves` operate on. The threaded `Value`
/// is dropped: per `FlowRefine` §3 (σ-uniformity) the state never decides a
/// move, so refinement is decided on this purely syntactic object.
///
/// `Emit ℓ` is the observable-letter atom: an affordance fires letter `ℓ`, then
/// halts. (It carries both `FlowAlgebra.Proc.emit` and the σ-free projection of
/// `Proc.wr` — `PStep.wr` fires its letter and goes to `done` ignoring the
/// write, so a deploy effect, whether or not it writes state, projects to an
/// `Emit`.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Proc {
    /// The halted process (`Proc.done`; `procSize = 0`).
    Done,
    /// Fire a visible letter, then halt (`Proc.emit` / σ-free `Proc.wr`).
    Emit(u64),
    /// BRANCH — offer both continuations (`Proc.ch`, the choice `⊔`).
    Ch(Box<Proc>, Box<Proc>),
    /// SEQUENTIAL composition (`Proc.seqp`, the compose `⋆`): the RIGHT factor
    /// runs FIRST (Pradic's order), then the left.
    Seqp(Box<Proc>, Box<Proc>),
}

/// `procSize p` — the payload-free node-count, `procSize Done = 0` (the
/// well-founded measure; `FlowRefine.procSize`). The decision fuel is
/// `proc_size + 1`, always sufficient (`pstep_decreases`: every move shrinks it).
fn proc_size(p: &Proc) -> usize {
    match p {
        Proc::Done => 0,
        Proc::Emit(_) => 1,
        Proc::Ch(a, b) => 1 + proc_size(a) + proc_size(b),
        Proc::Seqp(a, b) => 1 + proc_size(a) + proc_size(b),
    }
}

/// The finite list of `(letter, successor)` moves of a `Proc` under `PStep` —
/// the game's out-edges. An EXACT mirror of `FlowRefine.moves`:
///
///   * `Done` → `[]` (cannot move).
///   * `Emit ℓ` → `[(ℓ, Done)]`.
///   * `Ch p q` → `moves p ++ moves q` (offer both branches).
///   * `Seqp p Done` → `moves p` (right factor done: hand off to the left's moves).
///   * `Seqp p r` (steppable `r`) → each of `r`'s moves, wrapped `Seqp p ·`
///     (thread the right factor first).
fn moves(p: &Proc) -> Vec<(u64, Proc)> {
    match p {
        Proc::Done => Vec::new(),
        Proc::Emit(l) => vec![(*l, Proc::Done)],
        Proc::Ch(a, b) => {
            let mut m = moves(a);
            m.extend(moves(b));
            m
        }
        Proc::Seqp(pp, r) => match r.as_ref() {
            Proc::Done => moves(pp),
            other => moves(other)
                .into_iter()
                .map(|(l, r2)| (l, Proc::Seqp(pp.clone(), Box::new(r2))))
                .collect(),
        },
    }
}

/// `decideFuel n p q` — does `q` simulate `p` within `n` rounds (the bounded
/// greatest-simulation on the σ-free move-graph)? EXACT mirror of
/// `FlowRefine.decideFuel`: at each round every Spoiler move of `p` must have a
/// SAME-letter Duplicator answer of `q` that continues to simulate (one fewer
/// round). Structurally recursive in the fuel ⟹ terminating.
fn decide_fuel(n: usize, p: &Proc, q: &Proc) -> bool {
    if n == 0 {
        return false;
    }
    moves(p).iter().all(|(lp, p2)| {
        moves(q)
            .iter()
            .any(|(lq, q2)| lp == lq && decide_fuel(n - 1, p2, q2))
    })
}

/// The in-process σ-free simulation-game decision — the Rust MIRROR of
/// `FlowRefine.decideRefines`, kept as the FALLBACK for targets that cannot link
/// the verified Lean archive (`wasm32`, the zkvm guest) or a stale archive that
/// predates the `dregg_decide_refines` export. On a normal native build the
/// linked-archive path ([`decide_refines`]) runs the PROVEN procedure instead;
/// [`decide_refines_via_ffi_then_mirror`] proves the two AGREE on every comparison
/// the gate makes (the differential tooth in `tests.rs`).
fn decide_refines_mirror(a: &Proc, b: &Proc) -> bool {
    decide_fuel(proc_size(a) + 1, a, b)
}

/// Encode a σ-free [`Proc`] as the preorder (Polish-prefix) token stream the Lean
/// export `dregg_decide_refines` reads — a space-separated traversal where each node
/// emits ONE token and its children follow (fixed arity per token ⇒ unambiguous):
/// `d` = `Done`, `e<ℓ>` = `Emit ℓ`, `c` = `Ch`(2 children), `s` = `Seqp`(2 children).
/// This is the byte-exact inverse of `FlowRefine.encodeProcToks` / `decodeProc`, so a
/// `Proc` built here decodes to the SAME `Proc` in Lean (the round-trip `#guard`s pin it).
fn encode_proc(p: &Proc, out: &mut String) {
    match p {
        Proc::Done => out.push('d'),
        Proc::Emit(l) => {
            out.push('e');
            out.push_str(&l.to_string());
        }
        Proc::Ch(a, b) => {
            out.push('c');
            out.push(' ');
            encode_proc(a, out);
            out.push(' ');
            encode_proc(b, out);
        }
        Proc::Seqp(a, b) => {
            out.push('s');
            out.push(' ');
            encode_proc(a, out);
            out.push(' ');
            encode_proc(b, out);
        }
    }
}

/// The full `INPUT` wire for the refinement export: `"A=<procW>;B=<procW>"`.
fn refine_wire(a: &Proc, b: &Proc) -> String {
    let mut wa = String::new();
    encode_proc(a, &mut wa);
    let mut wb = String::new();
    encode_proc(b, &mut wb);
    format!("A={wa};B={wb}")
}

/// **`decide_refines A B`** — the refinement DECISION. Returns `true` iff `A`
/// refines `B` in the online simulation order `≤ᶠ`.
///
/// When the linked Lean archive exports the verified gate
/// ([`dregg_lean_ffi::decide_refines_gate_available`]), this routes the decision
/// through `@[export] dregg_decide_refines` — the PROVEN `FlowRefine.decideRefines`,
/// whose SOUNDNESS + COMPLETENESS against `≤ᶠ` is the Lean theorem `decideRefines_iff`
/// (LAW #1). So the deploy gate runs the verified procedure, not a re-implementation.
/// On a target that cannot link the archive (or a stale one lacking the export) it
/// falls back to the in-process σ-free mirror [`decide_refines_mirror`] (the two AGREE
/// by construction — the algorithm is identical and σ-free; the differential test pins it).
pub fn decide_refines(a: &Proc, b: &Proc) -> bool {
    if dregg_lean_ffi::decide_refines_gate_available() {
        match dregg_lean_ffi::shadow_decide_refines(&refine_wire(a, b)) {
            Ok(v) if v == "1" => return true,
            Ok(v) if v == "0" => return false,
            // "ERR" (a wire the proven gate rejected) or any FFI error: fall through to the mirror
            // rather than silently mis-deciding. (A well-formed deploy `Proc` never hits this; the
            // fallback is defense-in-depth, and the differential test asserts FFI == mirror.)
            _ => {}
        }
    }
    decide_refines_mirror(a, b)
}

// ════════════════════════════════════════════════════════════════════════════
//  §2 — Mapping a DreggDL plan / intent to a flow `Proc`.
// ════════════════════════════════════════════════════════════════════════════

/// One observable affordance-fire of a deployment: an effect, reduced to the
/// LETTER that distinguishes it. The letter encodes the effect's KIND and its
/// capability/value SHAPE — so a *widening* (a grant of a wider facet, a
/// re-target, a different recipient) yields a DIFFERENT letter and therefore a
/// move the narrower plan cannot match. This is the granularity at which the
/// simulation game decides refinement.
///
/// Determinism: the letter is a function of the effect's serde-stable bytes, so
/// the same effect always maps to the same letter (the reproducibility the rest
/// of `dregg-deploy` relies on).
fn effect_letter(eff: &Effect) -> u64 {
    // A discriminant tag keeps DISTINCT kinds in distinct letter-spaces even if
    // two effects of different kinds happened to hash-collide on their bodies.
    let tag: u64 = match eff {
        Effect::CreateCellFromFactory { .. } => 1,
        Effect::Transfer { .. } => 2,
        Effect::GrantCapability { .. } => 3,
        Effect::CreateCell { .. } => 4,
        Effect::SetField { .. } => 5,
        Effect::RevokeCapability { .. } => 6,
        Effect::AttenuateCapability { .. } => 7,
        _ => 0, // any other effect kind shares the "other" tag-space
    };
    // The body letter: a stable digest of the effect's serialized form. Two
    // effects with the same observable shape (same kind, same target, same cap
    // facet, same amount) get the SAME letter — so re-granting the IDENTICAL
    // facet is a matchable move (an attenuation/equal refines), while a wider
    // facet changes the bytes and so the letter (a widening does NOT refine).
    let body = match serde_json::to_vec(eff) {
        Ok(bytes) => {
            let h = blake3::hash(&bytes);
            // fold the 32-byte hash into a u64 letter (collision-resistant enough
            // for distinguishing deployment effects; the game only needs equality)
            let b = h.as_bytes();
            u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]])
        }
        Err(_) => 0,
    };
    // Mix the tag into the high bits so kind and body both matter.
    (tag << 56) ^ (body & 0x00FF_FFFF_FFFF_FFFF)
}

/// The faithful `⋆`-chain for `effects[i..]`, firing `effects[i]` FIRST.
///
/// `Seqp head tail` fires `tail` (the right factor) first. So to fire
/// `effects[i]` first and the rest after, we set the RIGHT factor to
/// `Emit(effects[i])` and the LEFT factor to the chain for `effects[i+1..]`:
///   `Seqp( chain(i+1), Emit(effects[i]) )`
/// `moves` of that: right factor `Emit` is steppable, so it threads first →
/// fires `effects[i]`, lands in `Seqp( chain(i+1), Done )` → `moves` = `moves
/// (chain(i+1))`, firing `effects[i+1]` next. Exactly the effect order.
fn seq_in_order(effects: &[&Effect], i: usize) -> Proc {
    if i >= effects.len() {
        return Proc::Done;
    }
    let head = Proc::Emit(effect_letter(effects[i]));
    let rest = seq_in_order(effects, i + 1);
    // rest ⋆ head  ==  Seqp(rest, head): right factor `head` runs first.
    Proc::Seqp(Box::new(rest), Box::new(head))
}

/// The deterministic letter TRACE of a LINEAR flow (one move per step). A
/// lowered DreggDL deployment is a `⋆`-chain of effect-`Emit`s with NO real
/// choice, so its transition graph is a single path; this returns that path's
/// letters in firing order. (Used for witness extraction and the linear-flow
/// intent decision; capped to avoid runaway on a malformed non-linear flow.)
///
/// For a genuinely branching `Proc` this returns ONE path (the left-preferred
/// move at each step) — deploy flows are never branching, so for them it is the
/// full, exact trace.
fn trace_of(p: &Proc) -> Vec<u64> {
    let mut out = Vec::new();
    let mut cur = p.clone();
    // A lowered deploy fires at most (#effects) letters; 4096 is a generous cap
    // that no real deployment approaches, guarding a malformed input only.
    for _ in 0..4096 {
        let ms = moves(&cur);
        let Some((l, next)) = ms.into_iter().next() else {
            break;
        };
        out.push(l);
        cur = next;
    }
    out
}

/// Build the flow `Proc` of a whole [`AppliedPlan`]: the per-root turn sequence
/// is itself a `⋆`-chain (births ⋆ funds ⋆ grants, in the plan's dependency
/// order), each root contributing its tree's effect-flow. The result is the
/// deployment read as ONE flow — the object the refinement game decides over.
pub fn flow_of_plan(plan: &AppliedPlan) -> Proc {
    // Each planned turn carries a single-root call forest; collect all effects
    // across the whole plan in turn order (births → funds → grants), then DFS
    // within each tree. This is the deployment's total observable effect-flow.
    let mut all: Vec<&Effect> = Vec::new();
    let mut trees: Vec<&CallTree> = Vec::new();
    for pt in &plan.turns {
        for root in &pt.turn.call_forest.roots {
            trees.push(root);
        }
    }
    for t in &trees {
        all.extend(t.all_effects());
    }
    seq_in_order(&all, 0)
}

/// Build the flow `Proc` of a bare [`CallForest`] (e.g. a lowered forest before
/// it is split into turns) — the same total-effect-flow, in `walk`/DFS order.
pub fn flow_of_forest(forest: &CallForest) -> Proc {
    let effects = forest.total_effects();
    seq_in_order(&effects, 0)
}

// ════════════════════════════════════════════════════════════════════════════
//  §3 — A declared ABSTRACT INTENT as a flow (for intent-conformance).
// ════════════════════════════════════════════════════════════════════════════

/// An abstract effect the operator declares they MEANT to authorize — the
/// alphabet of an intent [`FlowSpec`]. Each variant pins the OBSERVABLE shape
/// (kind + capability/value envelope) at the same granularity
/// [`effect_letter`] distinguishes, so an intent letter matches the lowered
/// effect's letter exactly when the lowered effect is within the declared shape.
///
/// An intent is permissive by being a CHOICE (`⊔`) over the effects it allows,
/// repeated/sequenced as needed — `lowered ≤ᶠ intent` then means every effect
/// the lowering fires is one the intent offered.
#[derive(Clone, Debug)]
pub enum IntentEffect {
    /// A concrete effect, taken at face value (its letter is `effect_letter`).
    /// The most precise intent: "this exact effect is authorized."
    Exact(Effect),
}

impl IntentEffect {
    fn letter(&self) -> u64 {
        match self {
            IntentEffect::Exact(e) => effect_letter(e),
        }
    }
}

/// A declared abstract intent: the menu of effect-shapes the operator
/// authorized, as a flow the lowered sequence is held to refine.
///
/// The intent is the **repeat-menu** `μ = ⊔_{ℓ ∈ allowed} (ℓ ⋆ μ)`: at every
/// step it offers a CHOICE among the allowed letters and then returns to the
/// same menu, so ANY finite sequence drawn from the alphabet is simulable. For a
/// LINEAR lowered deploy flow `A` (a single path of letters — deploys never
/// branch), refinement against this menu collapses to a membership check:
///
/// > **`A ≤ᶠ μ`  ⟺  every letter in `A`'s trace is in `allowed`.**
///
/// (`→` each move of `A` is a letter `ℓ`, which `μ` matches iff `ℓ ∈ allowed`,
/// landing back at `μ`; `←` if every `A`-letter is allowed, the relation "the
/// remaining `A`-suffix vs `μ`" is a simulation. The repeat-menu has no `⋆`-skew
/// to exploit because its right factor is `μ` at every node.) So we decide
/// intent-conformance by [`Self::allows_trace`] over `A`'s trace — O(|A|·|menu|)
/// — instead of materializing `μ` (which, unrolled to depth `|A|`, is
/// exponential in the alphabet size; the `decide_refines` game would agree but
/// pay that cost). [`Self::to_menu_proc`] still builds a bounded `μ` for callers
/// who want to run the game directly on a small instance.
#[derive(Clone, Debug)]
pub struct FlowSpec {
    allowed: Vec<u64>,
}

impl FlowSpec {
    /// An intent that authorizes exactly the given effects (by observable
    /// shape). Order does not matter — the menu offers all of them at every step.
    pub fn from_intent(effects: &[IntentEffect]) -> Self {
        let mut allowed: Vec<u64> = effects.iter().map(|e| e.letter()).collect();
        allowed.sort_unstable();
        allowed.dedup();
        FlowSpec { allowed }
    }

    /// An intent that authorizes exactly the effect-letters of a reference plan
    /// — "do no more than THIS plan does" as a behavioral envelope. (The
    /// reference plan itself trivially refines this.)
    pub fn from_plan_envelope(plan: &AppliedPlan) -> Self {
        let mut allowed: Vec<u64> = Vec::new();
        for pt in &plan.turns {
            for root in &pt.turn.call_forest.roots {
                for eff in root.all_effects() {
                    allowed.push(effect_letter(eff));
                }
            }
        }
        allowed.sort_unstable();
        allowed.dedup();
        FlowSpec { allowed }
    }

    /// `true` iff every letter in `trace` is in the allowed alphabet — the
    /// linear-flow decision of `A ≤ᶠ μ` (see the struct doc for the equivalence).
    /// Returns the FIRST out-of-alphabet letter on failure (the divergence
    /// witness) via the `Err`.
    fn allows_trace(&self, trace: &[u64]) -> Result<(), u64> {
        let set: std::collections::BTreeSet<u64> = self.allowed.iter().copied().collect();
        for &l in trace {
            if !set.contains(&l) {
                return Err(l);
            }
        }
        Ok(())
    }

    /// A BOUNDED materialization of the repeat-menu `μ` to a given depth
    /// `μ_d = ⊔_{ℓ ∈ allowed} (ℓ ⋆ μ_{d-1})`, for callers who want to run the
    /// `decide_refines` game directly on a small instance (the game AGREES with
    /// [`Self::allows_trace`] on linear inputs). Exponential in the alphabet
    /// size at large depth — the gate itself uses `allows_trace`, not this.
    pub fn to_menu_proc(&self, depth: usize) -> Proc {
        if depth == 0 || self.allowed.is_empty() {
            return Proc::Done;
        }
        let tail = self.to_menu_proc(depth - 1);
        // `Emit ℓ ⋆ tail` = Seqp(tail, Emit ℓ): Emit (right factor) fires first,
        // then `tail` re-offers the menu.
        let mut branches: Vec<Proc> = self
            .allowed
            .iter()
            .map(|l| Proc::Seqp(Box::new(tail.clone()), Box::new(Proc::Emit(*l))))
            .collect();
        let last = branches.pop().unwrap();
        branches
            .into_iter()
            .rev()
            .fold(last, |acc, b| Proc::Ch(Box::new(b), Box::new(acc)))
    }
}

// ════════════════════════════════════════════════════════════════════════════
//  §4 — The refinement GATE (the deploy-side `assurance.refines` check).
// ════════════════════════════════════════════════════════════════════════════

/// A located refinement finding: WHERE the divergence is and WHY `A` does not
/// refine `B`. Mirrors the shape of `dregg_userspace_verify::Finding` so the
/// refinement gate reads like the existing assurance findings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RefineFinding {
    /// Which refinement check this is (`"safe-upgrade"` / `"intent-conformance"`).
    pub check: String,
    /// Human-readable explanation of the divergence (names the kind of widening).
    pub message: String,
    /// The effect-letter the refining side could fire but the target could not
    /// match (the witness of non-refinement), if one was isolated.
    pub diverging_letter: Option<u64>,
    /// A HUMAN label for the diverging letter: the actual effect whose firing
    /// `B` could not match, resolved by scanning the refining side's effects for
    /// the one whose [`effect_letter`] equals `diverging_letter`. E.g.
    /// `"GrantCapability deal → bank over deal (facet unrestricted (all effect
    /// kinds))"`. `None` if the letter could not be resolved to a concrete
    /// effect (it is still pinned numerically in `diverging_letter`).
    pub diverging_effect_label: Option<String>,
}

/// The verdict of a refinement check: `Refines` (the relation holds) or
/// `Diverges` with the located finding(s).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RefineVerdict {
    /// `A ≤ᶠ B` holds: `A` only does what `B` permits.
    Refines,
    /// `A ⋠ B`: a divergence was found (a move of `A` `B` cannot match).
    Diverges(Vec<RefineFinding>),
}

impl RefineVerdict {
    /// `true` iff the refinement holds.
    pub fn is_refine(&self) -> bool {
        matches!(self, RefineVerdict::Refines)
    }
    /// The findings (empty on `Refines`).
    pub fn findings(&self) -> &[RefineFinding] {
        match self {
            RefineVerdict::Refines => &[],
            RefineVerdict::Diverges(f) => f,
        }
    }
}

/// Isolate a WITNESS of non-refinement along a LINEAR `A` (a deploy flow): walk
/// `A`'s single move at each step while tracking the set of `B`-states reachable
/// in lockstep (B may branch, so it is a SET). Report the first `A`-letter that
/// NO live `B`-state can match — the exact game position where `A ≤ᶠ B` breaks,
/// which for deploy flows is the diverging effect (e.g. the extra grant that is
/// `A`'s 5th effect, not its 1st). Returns `None` only if the walk exhausts
/// `A` with `B` still matching (i.e. `A` actually refines `B` — no witness).
fn diverging_letter(a: &Proc, b: &Proc) -> Option<u64> {
    let mut a_cur = a.clone();
    // The live set of B-states that have matched A's trace so far.
    let mut b_states: Vec<Proc> = vec![b.clone()];
    for _ in 0..4096 {
        let a_moves = moves(&a_cur);
        let Some((l, a_next)) = a_moves.into_iter().next() else {
            // A halted with B still live: A's trace was fully matched → no witness.
            return None;
        };
        // Advance every live B-state by an `l`-move; dedup the successor set.
        let mut next_b: Vec<Proc> = Vec::new();
        for bs in &b_states {
            for (bl, bn) in moves(bs) {
                if bl == l && !next_b.contains(&bn) {
                    next_b.push(bn);
                }
            }
        }
        if next_b.is_empty() {
            // No live B-state can fire `l`: this is the diverging letter.
            return Some(l);
        }
        a_cur = a_next;
        b_states = next_b;
    }
    None
}

/// A human label for a single deploy effect — the inverse intent of
/// [`effect_letter`] for diagnostics. Names the KIND and the
/// capability/value SHAPE the way an operator reads it, using the friendly facet
/// describer for a `GrantCapability`. (`effect_letter` is a hash and not
/// invertible; this is applied to the CONCRETE effect once the scan has matched
/// the letter — see [`describe_diverging_effect`].)
pub fn describe_effect(eff: &Effect) -> String {
    match eff {
        Effect::GrantCapability { from, to, cap } => format!(
            "GrantCapability {} → {} over {} (facet {})",
            short(&from.0),
            short(&to.0),
            short(&cap.target.0),
            describe_allowed_effects(cap.allowed_effects),
        ),
        Effect::Transfer { from, to, amount } => {
            format!(
                "Transfer {} → {} amount {amount}",
                short(&from.0),
                short(&to.0)
            )
        }
        Effect::CreateCellFromFactory { factory_vk, .. } => {
            format!("CreateCellFromFactory from factory {}", short(factory_vk))
        }
        Effect::SetField { cell, index, .. } => {
            format!("SetField cell {} slot {index}", short(&cell.0))
        }
        Effect::RevokeCapability { .. } => "RevokeCapability".to_string(),
        Effect::AttenuateCapability { .. } => "AttenuateCapability".to_string(),
        other => format!("{other:?}")
            .split(['{', ' '])
            .next()
            .unwrap_or("effect")
            .to_string(),
    }
}

fn short(b: &[u8; 32]) -> String {
    let h: String = b.iter().take(4).map(|x| format!("{x:02x}")).collect();
    format!("0x{h}…")
}

/// Resolve a diverging LETTER to the concrete effect (and its human label) by
/// scanning a plan's effects for the one whose [`effect_letter`] equals it. The
/// diverging letter is, by construction, a letter the REFINING side (`A`) can
/// fire — so we scan `A`'s plan. Returns the first matching effect's
/// [`describe_effect`]. Used to put a HUMAN name on the refinement divergence.
pub fn describe_diverging_effect(plan: &AppliedPlan, letter: u64) -> Option<String> {
    for pt in &plan.turns {
        for root in &pt.turn.call_forest.roots {
            for eff in root.all_effects() {
                if effect_letter(eff) == letter {
                    return Some(describe_effect(eff));
                }
            }
        }
    }
    None
}

/// **safe-upgrade**: does the NEW plan refine the RUNNING (old) plan? `new ≤ᶠ
/// old` — the new deployment introduces NO behavior the old one lacked. A
/// widening (a new effect / wider capability) is rejected with the divergence
/// named.
///
/// This is the gate for "is this redeploy safe to roll forward?": a safe
/// upgrade only narrows (or matches) the running behavior, so nothing the new
/// spec does was outside what the running spec already authorized.
pub fn refines_upgrade(new_plan: &AppliedPlan, old_plan: &AppliedPlan) -> RefineVerdict {
    let new_flow = flow_of_plan(new_plan);
    let old_flow = flow_of_plan(old_plan);
    if decide_refines(&new_flow, &old_flow) {
        RefineVerdict::Refines
    } else {
        let witness = diverging_letter(&new_flow, &old_flow);
        // Resolve the diverging letter to the CONCRETE effect of the new plan
        // (the refining side), for a human label of WHAT widened.
        let label = witness.and_then(|l| describe_diverging_effect(new_plan, l));
        RefineVerdict::Diverges(vec![RefineFinding {
            check: "safe-upgrade".to_string(),
            message: match (&witness, &label) {
                (Some(_), Some(desc)) => format!(
                    "the new deployment WIDENS the running one: at the diverging step it fires \
                     `{desc}` — an effect the running deployment cannot match from that point (a \
                     new reachable effect/capability, not a narrowing). The upgrade is NOT a \
                     refinement of what is running (new ⋠ old). Drop or narrow that effect to roll \
                     forward safely."
                ),
                (Some(l), None) => format!(
                    "the new deployment WIDENS the running one: at the diverging step it fires an \
                     effect (letter {l:#018x}) the running deployment cannot match from that point \
                     — a new reachable effect/capability, not a narrowing. The upgrade is NOT a \
                     refinement of what is running (new ⋠ old)."
                ),
                (None, _) => "the new deployment does not refine the running one in the online \
                     simulation order (new ⋠ old): some effect-sequence the new plan can \
                     perform is not matchable by the running plan. The upgrade introduces \
                     behavior the running deployment did not authorize."
                    .to_string(),
            },
            diverging_letter: witness,
            diverging_effect_label: label,
        }])
    }
}

/// **intent-conformance**: does the LOWERED plan refine the declared abstract
/// INTENT? `lowered ≤ᶠ intent` — every effect the lowering fires is one the
/// intent authorized. A lowering that does MORE than declared (a stray grant, a
/// wider cap) fails, with the out-of-envelope effect named.
pub fn refines_intent(plan: &AppliedPlan, intent: &FlowSpec) -> RefineVerdict {
    let lowered = flow_of_plan(plan);
    // The lowered deploy flow is LINEAR, so `lowered ≤ᶠ μ(intent)` ⟺ every
    // letter in its trace is in the allowed alphabet (the struct-doc equivalence).
    // We decide that directly — O(|trace|·|alphabet|) — rather than materializing
    // the exponential menu `Proc`.
    let trace = trace_of(&lowered);
    match intent.allows_trace(&trace) {
        Ok(()) => RefineVerdict::Refines,
        Err(l) => {
            let label = describe_diverging_effect(plan, l);
            RefineVerdict::Diverges(vec![RefineFinding {
                check: "intent-conformance".to_string(),
                message: match &label {
                    Some(desc) => format!(
                        "the lowered deployment does MORE than the declared intent: it fires \
                         `{desc}` — an effect the intent did not authorize. The lowering exceeds \
                         its stated envelope (lowered ⋠ intent)."
                    ),
                    None => format!(
                        "the lowered deployment does MORE than the declared intent: it fires an \
                         effect (letter {l:#018x}) the intent did not authorize. The lowering \
                         exceeds its stated envelope (lowered ⋠ intent)."
                    ),
                },
                diverging_letter: Some(l),
                diverging_effect_label: label,
            }])
        }
    }
}

#[cfg(test)]
mod tests;
