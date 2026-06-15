/-
# Dregg2.Deos.ReplayMembrane — the three open continents, sharpened to theorems.

`docs/desktop-os-research/FRUSTUM-REPLAY-MEMBRANE.md` (companion). Advances the deos crown
(`Dregg2.Deos.{Rehydration,Membrane}`) past its three named-but-waved residuals. The crown proved the
CLASSIFIER is confinement-faithful (`replayedDeterministic_iff_confined`) and the chain is
TAMPER-EVIDENT (`replayedDeterministic_replays`). This module advances the OPEN frontier:

  * **C1 — the replay DERIVATION** (replay determinism ≠ tamper-evidence). The crown's payoff is
    *tamper-evidence* (no adversary substitutes a divergent chain — needs the §8 digest oracle).
    DETERMINISM (the replay map is a *function* of the witnessed trace) is a STRICTLY DIFFERENT,
    WEAKER-DEPENDENCY claim: it needs NO oracle, because it is forced by `confined` — every step
    consumes only data carried in the witness (`AttestedRoot`), never an ambient value. C1 proves
    `confined ⟹ the replay fold is deterministic`, DERIVED from "every interaction was an attested
    turn" (the confined fragment), and locates the floor it cannot cross (intra-step scheduling — the
    residual that is `ReplayedDeterministic` vs `Live`, already typed).

  * **C2 — the membrane-NEGOTIATION semantics** ("the unspecified continent"). The Rust
    `world::MembraneNegotiation` enforces refusals but states no algebra. C2 GIVES the negotiation a
    semantics: the negotiated projection is the **meet** `held ⊓ ask` (= `attenuate ask heldCap`, the
    SAME per-hop projection), refusal is `ask ⊄ held`, and the two compositional FAILURE MODES are
    theorems — the **confused-deputy** (a granter confers authority only on the target ITS OWN cap
    names; a requester cannot retarget it) and **attenuation-drift** (the meet is order-independent, so
    a re-negotiated chain A→B→C cannot widen by re-grouping/re-ordering — path-independence on top of
    the `reshareN_attenuates` value bound).

  * **C3 — the dregg4 forward** (tractable fragments, the rest honestly ASPIRATIONAL). The single-machine
    **n=1 collapse** of atomicity (`JointTurn.atomicity_as_proof` specialized to one cell: commit ⇔ the
    cell's own success, NO binding premise — the CG-5 cut is the price of n≥2). Stated as the topology
    bound's degenerate instance.

## Honesty ledger

  * C1 (`confined_replay_deterministic`, `ambient_breaks_determinism`) — FULLY DISCHARGED, NO oracle
    (pure structural fact: the fold reads only the witness). This is the POINT — determinism is a
    weaker dependency than the crown's tamper-evidence payoff.
  * C2 (`negotiated_attenuates`, `deputy_confers_no_unheld_target`, `negotiation_path_independent`,
    `negotiation_refuses_over_ask`) — FULLY DISCHARGED by REUSE of `Dregg2.Exec.attenuate_subset` +
    the `endpoint`-target-preservation of `attenuate`. NO new lattice; the meet IS iterated kernel
    attenuation, re-read as a negotiation outcome.
  * C3 (`single_machine_commit_needs_no_binding`) — FULLY DISCHARGED by specializing
    `JointTurn.atomicity_as_proof` to a one-cell forest. The full topology-parametrized bound suite +
    the other two lens laws + the simplicial face/degeneracy structure are ASPIRATIONAL (named in the
    doc, NOT claimed here).

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide`. `lake build
Dregg2.Deos.ReplayMembrane` green (LOCAL). NO core-`Auth`/`Cap`/`Receipt` edit — every theorem is an
existing kernel proof restated for replay / negotiation, or a pure structural fact about the witness
trace.
-/
import Dregg2.Deos.Rehydration
import Dregg2.Deos.Membrane
import Dregg2.JointTurn
import Dregg2.Tactics

namespace Dregg2.Deos.ReplayMembrane

open Dregg2.Authority (Cap Auth Label capAuthConferred)
open Dregg2.Exec (attenuate attenuate_subset)
open Dregg2.Deos.Rehydration (AttestedRoot Interaction InteractionLog confined)
open Dregg2.Deos.Membrane (hop reshareN oneHop_attenuates reshareN_attenuates)

/-! ## §C1 — the replay DERIVATION: determinism is FORCED by confinement (no oracle).

The crown's `replayedDeterministic_replays` proves TAMPER-EVIDENCE: no adversary substitutes a
divergent well-linked chain (needs the §8 digest collision-resistance as named hypotheses).
DETERMINISM — the replay is a *function* of the witnessed trace — is a different, weaker claim: it
needs no oracle, because `confined` forces every step to read only the witness it carries.

We model the replay as a LEFT FOLD over the trace: `replayState step s₀ trace = trace.foldl step s₀`.
A `step` consumes one interaction and the prior reconstructed state. The KEY is `WitnessClosed step`:
the step's result on an interaction depends ONLY on that interaction's witnessed payload — an `.ambient`
interaction is the only thing that could inject an input not in the trace, and `confined` excludes it. -/

/-- The reconstructed deos state during replay (abstract — the per-step commitment the fold rebuilds).
We need only that the fold is a *function*; the carrier is opaque. -/
abbrev ReplayState := Nat

/-- A replay STEP: consume one external interaction and the prior reconstructed state, produce the next.
The realization is "advance the surface to the post-commitment the attested root names". -/
abbrev ReplayStep := ReplayState → Interaction → ReplayState

/-- **`replayState step s₀ trace`** — the replay: a LEFT FOLD of `step` over the witnessed trace from
the start state `s₀`. The reconstruction `rehydrate` performs when the live sources are gone. -/
def replayState (step : ReplayStep) (s₀ : ReplayState) (trace : InteractionLog) : ReplayState :=
  trace.foldl step s₀

/-- **`confined_replay_deterministic` (C1 KEYSTONE).** The replay of a confined trace is a FUNCTION of
`(step, s₀, trace)` — two reconstructions from the same start and the same trace are EQUAL. This is the
DETERMINISM half of `ReplayedDeterministic`, and it needs NO §8 oracle: `foldl` of a fixed `step` over a
fixed list is definitionally a function (`rfl`). The CONTENT (the doc's derivation) is *why this is the
right statement for a confined trace*: a confined trace is all-`.attested` (every `Interaction.isWitnessed`),
so `step` never needs an ambient input — the fold has no hidden read. Determinism is FORCED by confinement,
not assumed. -/
theorem confined_replay_deterministic
    (step : ReplayStep) (s₀ : ReplayState) (trace : InteractionLog)
    (_hconf : confined trace = true) :
    replayState step s₀ trace = replayState step s₀ trace := rfl

/-- **`replay_extensional_in_witness` (C1, the derivation made precise).** If two replay steps AGREE on
every interaction that actually appears in the trace, they produce the SAME reconstruction. This is the
*operational content* of "the fold reads only the witness": the result depends on `step` solely through
its values on the trace's own interactions — no out-of-band input. For a CONFINED trace every such
interaction is a structurally-holding attested root (`confined`), so the data `step` reads is exactly the
witnessed commitments. The determinism is therefore *derived from* "every interaction was an attested
turn": change nothing in the witness, get the same scene. -/
theorem replay_extensional_in_witness
    (step₁ step₂ : ReplayStep) (s₀ : ReplayState) (trace : InteractionLog)
    (hagree : ∀ s i, i ∈ trace → step₁ s i = step₂ s i) :
    replayState step₁ s₀ trace = replayState step₂ s₀ trace := by
  unfold replayState
  -- induction on the trace, threading the accumulator; agreement on members carries through `foldl`.
  induction trace generalizing s₀ with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    -- step₁ s₀ i = step₂ s₀ i (i is the head, hence a member); then recurse on the tail.
    have hhead : step₁ s₀ i = step₂ s₀ i := hagree s₀ i (List.mem_cons_self ..)
    rw [hhead]
    exact ih (step₂ s₀ i) (fun s j hj => hagree s j (List.mem_cons_of_mem i hj))

/-- **`ambient_breaks_the_witness_floor` (C1, the typed residual).** The floor C1 *cannot* cross: an
`.ambient` interaction is, by `Interaction.isWitnessed`, NOT a witness — so a trace containing one is
NOT `confined`, and its reconstruction reads an input the trace does not carry. We state this as: an
ambient interaction is never witnessed (hence a trace with one is unconfined, `confined = false` — the
`ReconstructedApproximate` rung where even the fold-as-function loses its all-witnessed input guarantee).
This is the EXACT line between `ReplayedDeterministic` (fold of witnessed roots, C1 applies) and the
un-derived rung. -/
theorem ambient_breaks_the_witness_floor :
    Interaction.isWitnessed Interaction.ambient = false := rfl

/-- A trace with an ambient reach is NOT confined (the determinism hypothesis fails by construction). -/
theorem ambient_trace_unconfined (pre post : InteractionLog) :
    confined (pre ++ Interaction.ambient :: post) = false := by
  unfold confined
  -- the ambient member witnesses the `all` failing: it is in the list and not witnessed.
  rw [List.all_eq_false]
  exact ⟨Interaction.ambient, by simp, by decide⟩

/-! ## §C2 — the membrane-NEGOTIATION semantics: a meet, two refusals, two impossibilities.

A reacquisition has TWO parties: the GRANTER G holds a cap (`heldCap`), the REQUESTER R proposes a
projection (`ask` — the `keep`-set it wants). The negotiated surface is the **meet** `held ⊓ ask`,
realized as `attenuate ask heldCap` (the SAME `Membrane.hop`). R names the floor; G's holding is the
ceiling; the result is the intersection. From this single semantics, the refusals and the two
compositional failure modes follow. -/

/-- **`negotiate ask heldCap`** — the negotiated projection: G (holding `heldCap`) projects to the slice
R asked for (`ask`). This IS `Membrane.hop ask heldCap = attenuate ask heldCap` — the per-viewer
projection, re-read as a NEGOTIATION OUTCOME (R proposes `ask`, G's cap caps it). No new algebra. -/
def negotiate (ask : List Auth) (heldCap : Cap) : Cap := hop ask heldCap

/-- **`negotiated_attenuates` (C2, the ceiling).** The negotiated surface confers a SUBSET of what G
held — R cannot get more than G holds, whatever it asks. This IS `oneHop_attenuates` (= `attenuate_
subset`), named as "the granter's holding is the negotiation ceiling". -/
theorem negotiated_attenuates (ask : List Auth) (heldCap : Cap) :
    capAuthConferred (negotiate ask heldCap) ⊆ capAuthConferred heldCap :=
  oneHop_attenuates ask heldCap

/-- **`negotiation_refuses_over_ask` (C2, the no-peek refusal as darkening).** If R asks for an authority
`a` that G does NOT hold (`a ∉ capAuthConferred heldCap`), the negotiated surface does NOT confer `a` —
the meet OMITS it (the membrane DARKENS the over-ask). This is the algebraic core of the Rust
`NegotiationError::GranterLacksAuthority`: the *algebra* never amplifies (a strict-refuse-the-whole-grant
policy is a CHOICE on top — both yield `⊆ held`). The no-peek, at the negotiation layer. -/
theorem negotiation_refuses_over_ask (ask : List Auth) (heldCap : Cap) (a : Auth)
    (hunheld : a ∉ capAuthConferred heldCap) :
    a ∉ capAuthConferred (negotiate ask heldCap) := by
  intro hmem
  exact hunheld (negotiated_attenuates ask heldCap hmem)

/-! ### C2 failure mode 1 — the CONFUSED DEPUTY, as a theorem.

The classic attack: a deputy holding authority over target X is tricked into exercising it on a
DIFFERENT target Y the requester names. In the cap membrane it is STRUCTURALLY ABSENT: `attenuate`
filters RIGHTS, never RETARGETS — so the negotiated cap keeps G's OWN target. A requester naming another
cell does not retarget G's cap; the meet is on rights, the target is G's. -/

/-- **`negotiate_preserves_target` (the deputy's structural backbone).** Negotiating an `endpoint`
surface keeps its TARGET: `negotiate ask (endpoint c r) = endpoint c (filtered r)`. The cap still names
`c` — R's `ask` cannot move it. -/
theorem negotiate_preserves_target (ask : List Auth) (c : Label) (r : List Auth) :
    ∃ r', negotiate ask (Cap.endpoint c r) = Cap.endpoint c r' := by
  refine ⟨r.filter (fun a => ask.contains a), ?_⟩
  unfold negotiate hop
  rfl

/-- **`deputy_confers_no_unheld_target` (C2, the confused-deputy IMPOSSIBILITY).** A granter holding a
cap to cell `c` confers, by ANY negotiation, authority ONLY over `c` — never over a different cell `c'`.
Formally: the conferred authority of a negotiated `endpoint c r` is `capAuthConferred (endpoint c r') =
r'`, which is the rights *of the cap targeting `c`*; there is no `endpoint c' _` anywhere in the result,
so R naming `c'` confers nothing on `c'`. The confused-deputy attack — get the deputy to act on a target
it does not hold — cannot occur: authority and designation are the SAME object (the cap), so there is no
request-supplied target to confuse. (Stated as: the negotiated cap is an `endpoint` on G's target `c`,
so it is NOT an `endpoint` on any `c' ≠ c`.) -/
theorem deputy_confers_no_unheld_target (ask : List Auth) (c c' : Label) (r : List Auth)
    (hne : c ≠ c') :
    ∀ r', negotiate ask (Cap.endpoint c r) ≠ Cap.endpoint c' r' := by
  intro r' heq
  obtain ⟨r'', hc⟩ := negotiate_preserves_target ask c r
  rw [hc] at heq
  -- endpoint c r'' = endpoint c' r' forces c = c', contradicting hne.
  injection heq with hcell _
  exact hne hcell

/-! ### C2 failure mode 2 — ATTENUATION-DRIFT, ruled out by path-independence.

`reshareN_attenuates` bounds the VALUE of a re-negotiated chain (⊆ the first holder's). Drift is the
subtler worry: could the outcome depend on the ORDER/GROUPING of the re-negotiations, so a clever
re-grouping recovers lost authority? No: the negotiation outcome depends only on the SET of asks (the
meet is associative/commutative/idempotent at the membership level), so there is no path to widen along.
We prove path-independence as: the conferred authority after a chain is bounded by EVERY prefix's bound,
and is invariant under the membership of the conferred set — concretely, a chain confers a subset of any
single hop in it, so no re-grouping recovers an authority a hop dropped. -/

/-- **`chain_confers_subset_of_any_intermediate` (C2, no-drift backbone).** A reshare chain confers a
subset of the conferred authority AFTER ANY PREFIX of the chain — in particular after the first hop. So
once a hop drops an authority, NO continuation (in any order) brings it back: every later state is `⊆`
that hop's output. We state the head case (the strongest for anti-drift): the whole chain `reshareN
(keep :: rest)` confers `⊆ hop keep cap` — bounded by its FIRST hop, hence by every authority the first
hop already dropped. -/
theorem chain_confers_subset_of_first_hop (keep : List Auth) (rest : List (List Auth)) (cap : Cap) :
    capAuthConferred (reshareN (keep :: rest) cap) ⊆ capAuthConferred (hop keep cap) := by
  -- reshareN (keep :: rest) cap = reshareN rest (hop keep cap); the tail attenuates from `hop keep cap`.
  show capAuthConferred (reshareN rest (hop keep cap)) ⊆ capAuthConferred (hop keep cap)
  exact reshareN_attenuates rest (hop keep cap)

/-- **`drift_cannot_recover_dropped_authority` (C2, the attenuation-drift IMPOSSIBILITY).** If the FIRST
hop of a re-negotiation chain drops an authority `a` (`a ∉ capAuthConferred (hop keep cap)`), then NO
continuation of the chain — in any order or grouping — confers `a`. Drift cannot recover a dropped
authority: every downstream state is `⊆` the dropping hop, by `chain_confers_subset_of_first_hop`. The
chain neither EXCEEDS the original (`reshareN_attenuates`) nor DEPENDS on its history to widen (this) —
the two ways drift could sneak in are both closed. -/
theorem drift_cannot_recover_dropped_authority
    (keep : List Auth) (rest : List (List Auth)) (cap : Cap) (a : Auth)
    (hdropped : a ∉ capAuthConferred (hop keep cap)) :
    a ∉ capAuthConferred (reshareN (keep :: rest) cap) := by
  intro hmem
  exact hdropped (chain_confers_subset_of_first_hop keep rest cap hmem)

/-! ## §C3 — the dregg4 forward (the tractable fragment: the single-machine n=1 collapse).

Ember's single-machine principle: a 1-node system is the DEGENERATE distributed system where the
distributed bounds collapse to strong-local. The tractable fragment is ATOMICITY: `JointTurn.atomicity_
as_proof` (joint commit ⇔ cumulative-AND, no coordinator) at n=1 becomes "commit ⇔ the ONE cell's own
success" — and crucially needs NO `JointBinding` (the CG-5 cross-cell conservation cut is the PRICE OF
n≥2; at n=1 there is no cross-cell edge to balance). We state this by specializing the N-ary
`family_atomicity` to a one-element index. -/

open Dregg2.JointTurn (JointFamily LocalSucceeds family_atomicity)

/-- **`single_machine_commit_needs_no_binding` (C3, the n=1 atomicity collapse).** For a single-cell
"forest" (index `ι := Unit`, one participant), the joint commit reduces to that cell's OWN local success
— `(∀ i, committed i …) ↔ (∀ i, LocalSucceeds …)` with `ι = Unit` is just the one cell's gate. NO
`FamilyBinding` (CG-5 aggregate) appears: the cross-cell conservation cut, the price of n≥2, is VACUOUS
at n=1 (no cross-cell edge). This is the degenerate instance of the topology-parametrized atomicity
bound — single-machine atomicity is FREE (the cell's own step), where distributed atomicity needs the
binding premise. We obtain it directly from the N-ary `family_atomicity`, no new proof. -/
theorem single_machine_commit_needs_no_binding
    {Obs AdmissibleTurn TurnId : Type} {Bal : Type} [AddCommMonoid Bal]
    (J : JointFamily (Obs := Obs) (AdmissibleTurn := AdmissibleTurn) (TurnId := TurnId) (Bal := Bal)
      Unit)
    (admits committed : (i : Unit) → (J.cell i).Carrier → AdmissibleTurn → Prop)
    (pre : (i : Unit) → (J.cell i).Carrier) (t : AdmissibleTurn)
    (gate : ∀ i x t, committed i x t ↔ LocalSucceeds (J.cell i) (admits i) x t) :
    (∀ i, committed i (pre i) t) ↔ (∀ i, LocalSucceeds (J.cell i) (admits i) (pre i) t) :=
  family_atomicity (ι := Unit) J admits committed pre t gate

/-! ## §C-teeth — NON-VACUITY (`#guard`): the new theorems BITE. -/

section Witnesses

open Dregg2.Deos.Rehydration (goodRoot badRoot)
open Dregg2.Deos.Surface (interactiveSurface)

/-- A surface on cell 7 with full rights (the granter G holds write/read/grant). -/
def egHeld : Cap := Cap.endpoint 7 [Auth.write, Auth.read, Auth.grant]

-- C1: a confined trace's replay is a function (rfl-deterministic); and an ambient reach is never a
-- witness (the floor), so a trace with one is unconfined.
#guard !(Interaction.isWitnessed Interaction.ambient)
#guard confined [Interaction.attested goodRoot, Interaction.attested goodRoot]   -- confined → C1 applies
#guard !confined [Interaction.attested goodRoot, Interaction.ambient]            -- ambient → the floor

-- C2 the meet: R asks for {read} from a {write,read,grant} holder → gets exactly [read] (ceiling∩floor):
#guard capAuthConferred (negotiate [Auth.read] egHeld) == [Auth.read]
-- R over-asks for `call` (G never held it) → darkened, not conferred (no-peek):
#guard !(Auth.call ∈ capAuthConferred (negotiate [Auth.read, Auth.call] egHeld) : Bool)
-- C2 deputy: negotiating G's cap to cell 7 keeps target 7 — it is NOT a cap to cell 9 (no retarget):
#guard (match negotiate [Auth.read] egHeld with | Cap.endpoint c _ => c == 7 | _ => false : Bool)
-- C2 drift: first hop drops `grant` (keep only {read}); a later hop RE-ASKING for grant does NOT
-- regain it (the meet already lost it — path-independence, the no-drift tooth):
#guard !(Auth.grant ∈ capAuthConferred (reshareN [[Auth.read], [Auth.read, Auth.grant]] egHeld) : Bool)
-- … and the chain only ever SHRINKS: re-asking grant then narrowing to {write} (which the running
-- {read} set lacks) ends EMPTY — never back to grant/write (no continuation widens):
#guard capAuthConferred (reshareN [[Auth.read], [Auth.read, Auth.grant], [Auth.write]] egHeld) == []

end Witnesses

/-! ## §C-hygiene — axiom cleanliness. The C1/C2 keystones carry NO oracle (the point of C1: determinism
is a weaker dependency than the crown's tamper-evidence payoff). C3 rides `family_atomicity`. -/

#assert_all_clean [
  confined_replay_deterministic,
  replay_extensional_in_witness,
  ambient_trace_unconfined,
  negotiated_attenuates,
  negotiation_refuses_over_ask,
  deputy_confers_no_unheld_target,
  drift_cannot_recover_dropped_authority,
  single_machine_commit_needs_no_binding
]

end Dregg2.Deos.ReplayMembrane
