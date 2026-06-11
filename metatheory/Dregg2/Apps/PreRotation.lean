/-
# Dregg2.Apps.PreRotation — KERI pre-rotation for identity-as-council: the next key set is
committed BEFORE it is exposed, so compromising the CURRENT signing keys cannot rotate.

The resonance study's best single steal, adopted outright (`docs/ORGANS.md:131-138`, the identity
rider): *every key-state event in an identity cell commits to the digest of the NEXT, unexposed key
set; rotation must exhibit the preimage. Compromise of current keys no longer suffices to rotate.
One register + one guarded-write rule; composes with the recovery cooling period.* The identity
cell itself is a council (`docs/REFINEMENT-DESIGN.md:89-109`, Decision 2: identity = a small
governance cell; recovery = a friend-council rotation under the cooling-period TemporalGate).

## The model

* **§1 — the key state, abstractly.** `KeyState` = the exposed `current` key set + `nextDigest`,
  the commitment to the next, UNEXPOSED key set. `rotateStep` is the rotate verb: it admits an
  event iff `hash ev.newKeys = ks.nextDigest` (the preimage EXHIBITED), installs `ev.newKeys` as
  current, and commits the event's FRESH `freshNext` digest. The crypto floor is the named CR
  carrier `KeySetCR` — the same shape as `Crypto.CommitmentBinding.Compress1CR` /
  `Circuit.Poseidon2Binding.Poseidon2SpongeCR`: an explicit hypothesis discharged at the deployed
  hash (BLAKE3 / Poseidon2, `Crypto/PortalFloor.lean`), never `True`.

* **§2 — the keystones.**
  - `rotate_exhibits_preimage` — PRE-ROTATION SOUNDNESS: a rotation is admitted ONLY exhibiting
    the preimage of the committed next-digest.
  - `rotate_current_keys_irrelevant` — admission is a function of the COMMITMENT alone (`rfl`!):
    the current key set does not occur in the guard, so holding the current signing keys
    contributes literally nothing toward rotating.
  - `rotate_compromise_resistant` — under the named CR, an adversary presenting ANY key set other
    than the pre-committed one is REFUSED: an admitted forgery would BE a hash collision. (This
    subsumes preimage-finding: producing an admitted `newKeys ≠ next` exhibits
    `hash newKeys = hash next` with `newKeys ≠ next`.)
  - `rotate_install_unique` — two admitted rotations from the same state install the SAME keys.
  - `rotChain_pinned_by_commitments` — THE FORWARD CHAIN: each rotation commits the next, so the
    public commitment stream + CR pins the ENTIRE key history; no alternative admitted history
    exists under the same commitments. (KERI's chained `rot` events, exactly.)

* **§3 — the cooling composition.** `rotateStepCooled` conjoins the council's recovery cooling
  gate — `TemporalAtom.cooledSince`, THE polis cooling primitive
  (`Authority/TemporalAlgebra.lean:457-480`, `polisCooling`) — with the preimage gate. The two
  defenses are ORTHOGONAL and the composition STRICTLY DOMINATES either alone:
  pre-rotation removes the attacker's **ability** (no next-preimage ⇒ no admissible event, at any
  height), cooling removes their **speed/stealth** (even a preimage-holding event is refused
  inside the window, so a contested rotation is slow and VISIBLE to the council — time to revoke).
  Witnessed both ways: `cooling_blocks_admitted_preimage` (preimage-only would admit; the
  composition refuses) and `preimage_blocks_cooled_rotation` (cooling-only would admit; the
  composition refuses).

* **§4 — the register carrier.** The identity cell holds ONE register, `next_keys_digest`
  (precedent: the `heap_root` register, `Substrate/HeapKernel.lean:74-83`), and the rotate verb is
  a GUARDED WRITE through the live caveat-gated step `stateStepGuarded`
  (`Exec/EffectsState.lean:258`): authority ∧ membership ∧ lifecycle-liveness ∧ per-slot caveats
  (the council's own slot caveats — threshold, monotone counters — compose for free,
  `rotateWrite_caveats_enforced`). On commit the register holds the FRESH digest
  (`rotateWrite_commits_fresh`); the PREVIOUS register value is the installed key set's own
  commitment (`rotateWrite_exhibits_preimage`) — so the register's receipt-chained history IS the
  key-event log. Balance-neutral, cap-table-neutral, audited (one receipt row). The kernel-widen
  revocation path (`delegation_epoch`, `Exec/RecordKernel.lean`) is ORTHOGONAL: rotation edits the
  key-state register, never `caps`.

## KERI export (named, not built here)

The identity cell's rotation events export as KERI `rot` events: `nextDigest` = KERI's `n` (next
key digest), the exhibited `newKeys` = `k`, the receipt chain = the witness-receipted KEL. The
chained/signed/witness-receipted export is the interop lane (`docs/ORGANS.md:134-138`,
W-organ-3); this module is the kernel-side semantics it exports.

l4v bar: `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; crypto enters ONLY as the
named `KeySetCR` hypothesis; no `sorry`, no `:= True`, no `native_decide`. Non-vacuity both
polarities: honest rotations COMMIT (#guard, executed), forged/uncooled rotations REFUSE.
-/
import Dregg2.Exec.EffectsState
import Dregg2.Authority.TemporalAlgebra
import Dregg2.Tactics

namespace Dregg2.Apps.PreRotation

open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Authority.TemporalAlgebra (TemporalAtom polisCooling polisCooling_is_cooledSince
  cooledSince_refuses_inside cooledSince_admits_after cooledSince_upward_closed)

/-! ## §0 — the `next_keys_digest` register (ORGANS: "one register + one guarded-write rule"). -/

/-- **The `next_keys_digest` register** — the ONE named field of the identity cell carrying the
commitment to the next, unexposed key set (the `heap_root`-register shape,
`Substrate/HeapKernel.lean §0`). A non-`balance` metadata field, so the `write`-verb regime
invariants apply verbatim. -/
def nextKeysDigestField : FieldName := "next_keys_digest"

/-- `next_keys_digest` is NOT the conserved `balance` field — the side condition every
balance-neutrality lift consumes. -/
theorem nextKeysDigestField_ne_balance : nextKeysDigestField ≠ balanceField := by decide

/-! ## §1 — the key state and the rotate verb (abstract spec). -/

variable {Key : Type}

/-- **`KeySetCR hash`** — the NAMED hash-CR carrier for the key-set digest: equal digests force
equal key sets. The same shape as `Crypto.CommitmentBinding.Compress1CR`; at the deployed hash it
discharges to the BLAKE3/Poseidon2 floor (`Crypto/PortalFloor.lean`), an explicit hypothesis —
never `True`. Constructively this also covers preimage-finding: an adversary producing an admitted
key set ≠ the committed one EXHIBITS a collision. -/
def KeySetCR (hash : List Key → Int) : Prop :=
  ∀ a b : List Key, hash a = hash b → a = b

/-- **The identity cell's key state** — the exposed `current` signing key set + the commitment
`nextDigest` to the NEXT, unexposed set (KERI's `k` / `n` pair). -/
structure KeyState (Key : Type) where
  /-- The current (exposed, signing) key set. -/
  current    : List Key
  /-- The digest of the next, UNEXPOSED key set — committed before exposure. -/
  nextDigest : Int

/-- **A rotation event** — the presented new key set (must hash to the committed `nextDigest`)
plus the FRESH commitment to the set after it (KERI `rot`: expose `k`, commit the new `n`). -/
structure RotationEvent (Key : Type) where
  /-- The presented new key set — admitted iff it is the committed preimage. -/
  newKeys   : List Key
  /-- The fresh next-digest the rotation commits (the forward chain). -/
  freshNext : Int

/-- **`rotateStep` — the rotate verb (computable, FAIL-CLOSED).** Admits iff the presented key set
hashes to the stored `nextDigest` (the preimage EXHIBITED); on commit, installs `ev.newKeys` as
current and commits the event's fresh next-digest. The guard never reads `ks.current` — current
keys are powerless here (`rotate_current_keys_irrelevant`). -/
def rotateStep (hash : List Key → Int) (ks : KeyState Key) (ev : RotationEvent Key) :
    Option (KeyState Key) :=
  if hash ev.newKeys = ks.nextDigest then
    some { current := ev.newKeys, nextDigest := ev.freshNext }
  else
    none

/-- **`rotate_factors`.** A committed rotation exhibited the preimage AND produced exactly the
install-new/commit-fresh post-state. The bridge every keystone reuses. -/
theorem rotate_factors {hash : List Key → Int} {ks ks' : KeyState Key} {ev : RotationEvent Key}
    (h : rotateStep hash ks ev = some ks') :
    hash ev.newKeys = ks.nextDigest ∧
      ks' = { current := ev.newKeys, nextDigest := ev.freshNext } := by
  unfold rotateStep at h
  by_cases hg : hash ev.newKeys = ks.nextDigest
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **PRE-ROTATION SOUNDNESS (`rotate_exhibits_preimage`).** A rotation is admitted ONLY if it
exhibits the preimage of the committed next-digest. The identity rider's defining guard. -/
theorem rotate_exhibits_preimage {hash : List Key → Int} {ks ks' : KeyState Key}
    {ev : RotationEvent Key} (h : rotateStep hash ks ev = some ks') :
    hash ev.newKeys = ks.nextDigest :=
  (rotate_factors h).1

/-- **The install/commit shape.** On commit: the presented key set IS the new current set, and the
event's fresh digest IS the new commitment (the next link of the forward chain). -/
theorem rotate_installs {hash : List Key → Int} {ks ks' : KeyState Key} {ev : RotationEvent Key}
    (h : rotateStep hash ks ev = some ks') :
    ks'.current = ev.newKeys ∧ ks'.nextDigest = ev.freshNext := by
  rw [(rotate_factors h).2]; exact ⟨rfl, rfl⟩

/-- **FAIL-CLOSED.** A rotation whose presented key set does NOT hash to the committed
next-digest is refused. The refusal polarity of the soundness guard. -/
theorem rotate_wrong_preimage_fails {hash : List Key → Int} (ks : KeyState Key)
    (ev : RotationEvent Key) (hne : hash ev.newKeys ≠ ks.nextDigest) :
    rotateStep hash ks ev = none := by
  unfold rotateStep; rw [if_neg hne]

/-- **CURRENT KEYS ARE POWERLESS (`rotate_current_keys_irrelevant`) — and it is `rfl`.** The
rotate verb is the SAME function of the commitment for ANY current key set: admission and
post-state read only `nextDigest` and the event. So an attacker who exfiltrates every current
signing key has gained exactly nothing toward rotating — the structural half of compromise
resistance, with no crypto hypothesis at all. -/
theorem rotate_current_keys_irrelevant (hash : List Key → Int) (c c' : List Key) (d : Int)
    (ev : RotationEvent Key) :
    rotateStep hash { current := c, nextDigest := d } ev
      = rotateStep hash { current := c', nextDigest := d } ev := rfl

/-- **COMPROMISE RESISTANCE (`rotate_compromise_resistant`).** An adversary holding the current
signing keys but NOT the pre-committed next key set cannot produce an admitted rotation: under the
named CR, ANY presented key set other than the committed `next` is refused — an admitted forgery
would exhibit `hash forged = hash next` with `forged ≠ next`, i.e. a collision. Combined with
`rotate_current_keys_irrelevant`, current-key compromise alone can never rotate. -/
theorem rotate_compromise_resistant {hash : List Key → Int} (hCR : KeySetCR hash)
    {ks : KeyState Key} {next : List Key} (hcommit : ks.nextDigest = hash next)
    {ev : RotationEvent Key} (hne : ev.newKeys ≠ next) :
    rotateStep hash ks ev = none :=
  rotate_wrong_preimage_fails ks ev
    (fun hguard => hne (hCR _ _ (hguard.trans hcommit)))

/-- **INSTALL UNIQUENESS.** Under the named CR, any two admitted rotations from the same key state
install the SAME current key set — the commitment pins the exposed set; the only freedom left to a
rotation event is its own fresh commitment. -/
theorem rotate_install_unique {hash : List Key → Int} (hCR : KeySetCR hash)
    {ks k₁ k₂ : KeyState Key} {ev₁ ev₂ : RotationEvent Key}
    (h₁ : rotateStep hash ks ev₁ = some k₁) (h₂ : rotateStep hash ks ev₂ = some k₂) :
    k₁.current = k₂.current := by
  obtain ⟨hp₁, hk₁⟩ := rotate_factors h₁
  obtain ⟨hp₂, hk₂⟩ := rotate_factors h₂
  rw [hk₁, hk₂]
  exact hCR _ _ (hp₁.trans hp₂.symm)

/-! ## §1b — rotation CHAINS: the unforgeable forward chain. -/

/-- **`rotChain`** — fold the rotate verb over a list of rotation events (the key-event log /
KERI KEL), fail-closed: one refused link kills the whole chain. -/
def rotChain (hash : List Key → Int) (ks : KeyState Key) :
    List (RotationEvent Key) → Option (KeyState Key)
  | []        => some ks
  | ev :: evs => (rotateStep hash ks ev).bind fun ks' => rotChain hash ks' evs

/-- **`rotChain_cons_factors`.** A committed nonempty chain factors as one committed rotation then
the committed tail. The `stateStepGuarded_eq`-shaped bridge for chains. -/
theorem rotChain_cons_factors {hash : List Key → Int} {ks k : KeyState Key}
    {ev : RotationEvent Key} {evs : List (RotationEvent Key)}
    (h : rotChain hash ks (ev :: evs) = some k) :
    ∃ ks₁, rotateStep hash ks ev = some ks₁ ∧ rotChain hash ks₁ evs = some k := by
  simp only [rotChain] at h
  cases hs : rotateStep hash ks ev with
  | none => rw [hs] at h; simp at h
  | some ks₁ => rw [hs] at h; exact ⟨ks₁, rfl, by simpa using h⟩

/-- **THE FORWARD CHAIN (`rotChain_pinned_by_commitments`).** Each rotation commits the next, so
under the named CR the PUBLIC commitment stream pins the ENTIRE key history: two admitted chains
from the same genesis publishing the same fresh-digest stream expose the SAME key sets, link for
link, and land in the SAME final state. No alternative admitted key history exists under the same
commitments — the chain is unforgeable given the genesis commitment (KERI's chained `rot` events,
as a theorem). -/
theorem rotChain_pinned_by_commitments {hash : List Key → Int} (hCR : KeySetCR hash)
    (evs₁ : List (RotationEvent Key)) :
    ∀ (evs₂ : List (RotationEvent Key)) (ks k₁ k₂ : KeyState Key),
      rotChain hash ks evs₁ = some k₁ → rotChain hash ks evs₂ = some k₂ →
      evs₁.map RotationEvent.freshNext = evs₂.map RotationEvent.freshNext →
      evs₁.map RotationEvent.newKeys = evs₂.map RotationEvent.newKeys ∧ k₁ = k₂ := by
  induction evs₁ with
  | nil =>
      intro evs₂ ks k₁ k₂ h₁ h₂ hfresh
      cases evs₂ with
      | nil =>
          simp only [rotChain, Option.some.injEq] at h₁ h₂
          exact ⟨rfl, h₁ ▸ h₂⟩
      | cons ev₂ evs₂' => simp at hfresh
  | cons ev evs ih =>
      intro evs₂ ks k₁ k₂ h₁ h₂ hfresh
      cases evs₂ with
      | nil => simp at hfresh
      | cons ev₂ evs₂' =>
          simp only [List.map_cons, List.cons.injEq] at hfresh
          obtain ⟨hfh, hft⟩ := hfresh
          obtain ⟨ks₁, hs₁, h₁'⟩ := rotChain_cons_factors h₁
          obtain ⟨ks₂, hs₂, h₂'⟩ := rotChain_cons_factors h₂
          obtain ⟨hp₁, hk₁⟩ := rotate_factors hs₁
          obtain ⟨hp₂, hk₂⟩ := rotate_factors hs₂
          have hkeys : ev.newKeys = ev₂.newKeys := hCR _ _ (hp₁.trans hp₂.symm)
          have hstate : ks₁ = ks₂ := by rw [hk₁, hk₂, hkeys, hfh]
          obtain ⟨hmap, hk⟩ := ih evs₂' ks₁ k₁ k₂ h₁' (by rw [hstate]; exact h₂') hft
          exact ⟨by rw [List.map_cons, List.map_cons, hkeys, hmap], hk⟩

/-! ## §2 — the COOLING composition (pre-rotation × the polis cooling gate).

`TemporalAtom.cooledSince` is THE polis cooling primitive — the recovery cooling period of
REFINEMENT-DESIGN Decision 2 ("the cooling-period TemporalGate making theft-by-recovery slow and
visible"), proven equal to the amendment machinery's `polisCooling`
(`polisCooling_is_cooledSince`). The composition is the BOTH-gates meet, fail-closed on either. -/

/-- **`rotateStepCooled`** — the rotate verb under the council's cooling gate: a rotation staged
at `lastRotatedAt` is admissible at height `ht` only once `lastRotatedAt + period ≤ ht`, AND only
exhibiting the preimage. Orthogonal defenses, conjoined. -/
def rotateStepCooled (hash : List Key → Int) (lastRotatedAt period ht : Nat) (rec : Value)
    (ks : KeyState Key) (ev : RotationEvent Key) : Option (KeyState Key) :=
  if (TemporalAtom.cooledSince lastRotatedAt period).eval ht rec = true then
    rotateStep hash ks ev
  else
    none

/-- **TIGHTEN-ONLY.** A committed cooled rotation IS the underlying rotation — the cooling gate
only restricts the domain (the `stateStepGuarded_eq` shape), so every §1 keystone lifts. -/
theorem rotateStepCooled_eq {hash : List Key → Int} {lastRotatedAt period ht : Nat} {rec : Value}
    {ks ks' : KeyState Key} {ev : RotationEvent Key}
    (h : rotateStepCooled hash lastRotatedAt period ht rec ks ev = some ks') :
    rotateStep hash ks ev = some ks' := by
  unfold rotateStepCooled at h
  by_cases hg : (TemporalAtom.cooledSince lastRotatedAt period).eval ht rec = true
  · rwa [if_pos hg] at h
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **COOLING REFUSES INSIDE — even WITH the right preimage.** Strictly inside the cooling period
the composition refuses EVERY rotation event, honest or not: a stolen-next-set rotation (or a
coerced recovery) is at minimum SLOW and VISIBLE — the council sees the staged event and can
revoke before the boundary. -/
theorem rotateStepCooled_refuses_inside {hash : List Key → Int} {lastRotatedAt period ht : Nat}
    (hin : ht < lastRotatedAt + period) (rec : Value) (ks : KeyState Key)
    (ev : RotationEvent Key) :
    rotateStepCooled hash lastRotatedAt period ht rec ks ev = none := by
  unfold rotateStepCooled
  rw [if_neg (by rw [cooledSince_refuses_inside hin rec]; simp)]

/-- **COOLING ADMITS AFTER (no over-tightening).** At/after the boundary the composition IS the
bare rotate verb — cooling never blocks a cooled honest rotation. Non-vacuous against the refusal
half. -/
theorem rotateStepCooled_admits_after {hash : List Key → Int} {lastRotatedAt period ht : Nat}
    (hc : lastRotatedAt + period ≤ ht) (rec : Value) (ks : KeyState Key)
    (ev : RotationEvent Key) :
    rotateStepCooled hash lastRotatedAt period ht rec ks ev = rotateStep hash ks ev := by
  unfold rotateStepCooled
  rw [if_pos (cooledSince_admits_after hc rec)]

/-- **BOTH GATES, witnessed on every commit.** A committed cooled rotation exhibited the preimage
AND had cooled — the conjunction the composition enforces. -/
theorem rotateStepCooled_factors {hash : List Key → Int} {lastRotatedAt period ht : Nat}
    {rec : Value} {ks ks' : KeyState Key} {ev : RotationEvent Key}
    (h : rotateStepCooled hash lastRotatedAt period ht rec ks ev = some ks') :
    hash ev.newKeys = ks.nextDigest ∧
      (TemporalAtom.cooledSince lastRotatedAt period).eval ht rec = true := by
  refine ⟨rotate_exhibits_preimage (rotateStepCooled_eq h), ?_⟩
  unfold rotateStepCooled at h
  by_cases hg : (TemporalAtom.cooledSince lastRotatedAt period).eval ht rec = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **Compromise resistance LIFTS through cooling** — at EVERY height: the no-next-preimage
adversary is refused whether cooled or not. -/
theorem rotateStepCooled_compromise_resistant {hash : List Key → Int} (hCR : KeySetCR hash)
    {lastRotatedAt period ht : Nat} {rec : Value} {ks : KeyState Key} {next : List Key}
    (hcommit : ks.nextDigest = hash next) {ev : RotationEvent Key} (hne : ev.newKeys ≠ next) :
    rotateStepCooled hash lastRotatedAt period ht rec ks ev = none := by
  unfold rotateStepCooled
  rw [rotate_compromise_resistant hCR hcommit hne, ite_self]

/-! ### Strict domination — the composition is strictly tighter than EITHER gate alone, both
witnessed. Orthogonality: pre-rotation removes the attacker's ABILITY (no preimage ⇒ no admissible
event at any height), cooling removes their SPEED/STEALTH (even an able event waits in the open). -/

/-- **The composition refuses what preimage-ALONE admits**: an event the bare rotate verb commits
(it exhibits the right preimage — say the attacker ALSO stole the next set, or recovery is coerced)
is still refused inside the cooling window. Pre-rotation alone lacks this tooth. -/
theorem cooling_blocks_admitted_preimage {hash : List Key → Int} {lastRotatedAt period ht : Nat}
    (hin : ht < lastRotatedAt + period) (rec : Value) {ks ks' : KeyState Key}
    {ev : RotationEvent Key} (_hadm : rotateStep hash ks ev = some ks') :
    rotateStepCooled hash lastRotatedAt period ht rec ks ev = none :=
  rotateStepCooled_refuses_inside hin rec ks ev

/-- **The composition refuses what cooling-ALONE admits**: after the boundary the cooling gate is
open (`.eval = true`), yet a no-next-preimage adversary is STILL refused. Cooling alone lacks this
tooth — it would admit any patient attacker. -/
theorem preimage_blocks_cooled_rotation {hash : List Key → Int} (hCR : KeySetCR hash)
    {lastRotatedAt period ht : Nat} (hc : lastRotatedAt + period ≤ ht) (rec : Value)
    {ks : KeyState Key} {next : List Key} (hcommit : ks.nextDigest = hash next)
    {ev : RotationEvent Key} (hne : ev.newKeys ≠ next) :
    (TemporalAtom.cooledSince lastRotatedAt period).eval ht rec = true ∧
      rotateStepCooled hash lastRotatedAt period ht rec ks ev = none :=
  ⟨cooledSince_admits_after hc rec,
   by rw [rotateStepCooled_admits_after hc]; exact rotate_compromise_resistant hCR hcommit hne⟩

/-! ## §3 — the REGISTER CARRIER: the rotate verb as a guarded write on the live substrate.

The identity cell's `next_keys_digest` register, written ONLY through `stateStepGuarded` — so the
rotate verb inherits, by construction: the authority gate (the council must hold the cell), the
membership + lifecycle-liveness gates (R6), and the cell's OWN slot caveats (the council's
threshold/monotone constitution composes for free). The PREVIOUS register value is the installed
key set's commitment — the register's receipt-chained history is the key-event log; one register
suffices (KERI: the KEL's `n` chain). -/

/-- **`rotateWrite` — the rotate verb on the live record kernel (computable, FAIL-CLOSED).**
Admits iff the presented key set hashes to the committed `next_keys_digest` register, THEN runs the
caveat-gated guarded write installing the FRESH digest. Two gates, fail-closed on either. -/
def rotateWrite (hash : List Key → Int) (s : RecChainedState) (actor idCell : CellId)
    (newKeys : List Key) (freshNext : Int) : Option RecChainedState :=
  if hash newKeys = fieldOf nextKeysDigestField (s.kernel.cell idCell) then
    stateStepGuarded s nextKeysDigestField actor idCell freshNext
  else
    none

/-- **`rotateWrite_factors`.** A committed register rotation exhibited the preimage of the
COMMITTED register AND is exactly the underlying guarded field write. -/
theorem rotateWrite_factors {hash : List Key → Int} {s s' : RecChainedState}
    {actor idCell : CellId} {newKeys : List Key} {freshNext : Int}
    (h : rotateWrite hash s actor idCell newKeys freshNext = some s') :
    hash newKeys = fieldOf nextKeysDigestField (s.kernel.cell idCell) ∧
      stateStep s nextKeysDigestField actor idCell (.int freshNext) = some s' := by
  unfold rotateWrite at h
  by_cases hg : hash newKeys = fieldOf nextKeysDigestField (s.kernel.cell idCell)
  · rw [if_pos hg] at h; exact ⟨hg, stateStepGuarded_eq h⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **PRE-ROTATION SOUNDNESS, on the register.** A committed rotation exhibited the preimage of
the cell's committed `next_keys_digest`. Equivalently: the installed key set's commitment IS the
pre-state register — so the register history is the chain of key-set commitments. -/
theorem rotateWrite_exhibits_preimage {hash : List Key → Int} {s s' : RecChainedState}
    {actor idCell : CellId} {newKeys : List Key} {freshNext : Int}
    (h : rotateWrite hash s actor idCell newKeys freshNext = some s') :
    hash newKeys = fieldOf nextKeysDigestField (s.kernel.cell idCell) :=
  (rotateWrite_factors h).1

/-- **THE FRESH COMMITMENT IS INSTALLED.** On commit the register reads back EXACTLY the fresh
next-digest — the forward chain's next link, in the committed cell state (the
`heapStep_root_written` shape). -/
theorem rotateWrite_commits_fresh {hash : List Key → Int} {s s' : RecChainedState}
    {actor idCell : CellId} {newKeys : List Key} {freshNext : Int}
    (h : rotateWrite hash s actor idCell newKeys freshNext = some s') :
    fieldOf nextKeysDigestField (s'.kernel.cell idCell) = freshNext :=
  state_field_written (rotateWrite_factors h).2

/-- **BALANCE-NEUTRAL.** Rotation is a metadata move: the conserved total is untouched. -/
theorem rotateWrite_conserves {hash : List Key → Int} {s s' : RecChainedState}
    {actor idCell : CellId} {newKeys : List Key} {freshNext : Int}
    (h : rotateWrite hash s actor idCell newKeys freshNext = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  state_conserves nextKeysDigestField_ne_balance (rotateWrite_factors h).2

/-- **CAP-TABLE-NEUTRAL.** Rotation never edits authority — the `delegation_epoch` revocation
path (`Exec/RecordKernel.lean`) is orthogonal machinery, untouched by the key-state write. -/
theorem rotateWrite_caps_unchanged {hash : List Key → Int} {s s' : RecChainedState}
    {actor idCell : CellId} {newKeys : List Key} {freshNext : Int}
    (h : rotateWrite hash s actor idCell newKeys freshNext = some s') :
    s'.kernel.caps = s.kernel.caps :=
  state_caps_unchanged (rotateWrite_factors h).2

/-- **AUDITED.** Every committed rotation appends exactly one receipt row — the key-state event
log the KERI export serializes (`rot` events, witness-receipted). -/
theorem rotateWrite_audited {hash : List Key → Int} {s s' : RecChainedState}
    {actor idCell : CellId} {newKeys : List Key} {freshNext : Int}
    (h : rotateWrite hash s actor idCell newKeys freshNext = some s') :
    s'.log.length = s.log.length + 1 :=
  state_obsadvance (rotateWrite_factors h).2

/-- **THE COUNCIL'S CONSTITUTION COMPOSES.** A committed rotation passed EVERY slot caveat bound
to the `next_keys_digest` register — the identity-as-council cell's own constraints (threshold
gates, monotone counters, immutables) gate rotation with no extra wiring. -/
theorem rotateWrite_caveats_enforced {hash : List Key → Int} {s s' : RecChainedState}
    {actor idCell : CellId} {newKeys : List Key} {freshNext : Int}
    (h : rotateWrite hash s actor idCell newKeys freshNext = some s') :
    caveatsAdmit s.kernel nextKeysDigestField actor idCell freshNext = true := by
  unfold rotateWrite at h
  by_cases hg : hash newKeys = fieldOf nextKeysDigestField (s.kernel.cell idCell)
  · rw [if_pos hg] at h; exact stateStepGuarded_admits h
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **COMPROMISE RESISTANCE, on the register.** Under the named CR, if the cell's register
commits to `next` and the adversary presents ANY other key set, the rotation is refused —
current-key compromise alone cannot rotate the identity cell. -/
theorem rotateWrite_compromise_resistant {hash : List Key → Int} (hCR : KeySetCR hash)
    {s : RecChainedState} {actor idCell : CellId} {next : List Key}
    (hcommit : fieldOf nextKeysDigestField (s.kernel.cell idCell) = hash next)
    {newKeys : List Key} (hne : newKeys ≠ next) (freshNext : Int) :
    rotateWrite hash s actor idCell newKeys freshNext = none := by
  unfold rotateWrite
  rw [if_neg (fun hguard => hne (hCR _ _ (hguard.trans hcommit)))]

/-- **`rotateWriteCooled`** — the production shape: preimage gate × cooling gate × the guarded
write (authority/membership/liveness/slot-caveats). The recovery-cooling composition of
REFINEMENT-DESIGN Decision 2, on the live substrate. -/
def rotateWriteCooled (hash : List Key → Int) (lastRotatedAt period ht : Nat)
    (s : RecChainedState) (actor idCell : CellId) (newKeys : List Key) (freshNext : Int) :
    Option RecChainedState :=
  if (TemporalAtom.cooledSince lastRotatedAt period).eval ht (s.kernel.cell idCell) = true then
    rotateWrite hash s actor idCell newKeys freshNext
  else
    none

/-- **TIGHTEN-ONLY (register).** A committed cooled register rotation IS the underlying
register rotation — so every §3 keystone (preimage soundness, fresh-commit, conservation,
caps-frame, audit, caveats) lifts verbatim. -/
theorem rotateWriteCooled_eq {hash : List Key → Int} {lastRotatedAt period ht : Nat}
    {s s' : RecChainedState} {actor idCell : CellId} {newKeys : List Key} {freshNext : Int}
    (h : rotateWriteCooled hash lastRotatedAt period ht s actor idCell newKeys freshNext
          = some s') :
    rotateWrite hash s actor idCell newKeys freshNext = some s' := by
  unfold rotateWriteCooled at h
  by_cases hg : (TemporalAtom.cooledSince lastRotatedAt period).eval ht
      (s.kernel.cell idCell) = true
  · rwa [if_pos hg] at h
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **COOLING REFUSES INSIDE (register)** — even the honest council's rotation waits out the
window: slow and visible, by the executor. -/
theorem rotateWriteCooled_refuses_inside {hash : List Key → Int} {lastRotatedAt period ht : Nat}
    (hin : ht < lastRotatedAt + period) (s : RecChainedState) (actor idCell : CellId)
    (newKeys : List Key) (freshNext : Int) :
    rotateWriteCooled hash lastRotatedAt period ht s actor idCell newKeys freshNext = none := by
  unfold rotateWriteCooled
  rw [if_neg (by rw [cooledSince_refuses_inside hin]; simp)]

/-- **BOTH GATES on every committed production rotation**: the preimage was exhibited AND the
cooling boundary had passed. -/
theorem rotateWriteCooled_factors {hash : List Key → Int} {lastRotatedAt period ht : Nat}
    {s s' : RecChainedState} {actor idCell : CellId} {newKeys : List Key} {freshNext : Int}
    (h : rotateWriteCooled hash lastRotatedAt period ht s actor idCell newKeys freshNext
          = some s') :
    hash newKeys = fieldOf nextKeysDigestField (s.kernel.cell idCell) ∧
      (TemporalAtom.cooledSince lastRotatedAt period).eval ht (s.kernel.cell idCell) = true := by
  refine ⟨rotateWrite_exhibits_preimage (rotateWriteCooled_eq h), ?_⟩
  unfold rotateWriteCooled at h
  by_cases hg : (TemporalAtom.cooledSince lastRotatedAt period).eval ht
      (s.kernel.cell idCell) = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §4 — NON-VACUITY, both polarities, EXECUTED.

A CR hash that genuinely holds (`demoHash`, the injective `Encodable` encoding — the
`CommitmentBinding.refCompress1` pattern) so the CR-consuming keystones FIRE; a colliding hash
falsifying the carrier (it is not `True`); and a fast register demo (`tinyHash` + a real
`RecChainedState`) with `#guard` executions: honest rotation commits/installs/conserves/audits;
forged rotation refused; uncooled rotation refused; cooled-but-forged refused — the
strict-domination witnesses, concrete. -/

/-- A reference CR key-set hash: the injective `Encodable` encoding (the `refCompress1` shape). -/
def demoHash (ks : List Nat) : Int := ((Encodable.encode ks : ℕ) : ℤ)

/-- The reference hash IS collision-resistant — the `KeySetCR` carrier is witnessed TRUE. -/
theorem demoHash_CR : KeySetCR demoHash := by
  intro a b h
  unfold demoHash at h
  exact Encodable.encode_injective (by exact_mod_cast h)

/-- A COLLIDING hash (constant) FALSIFIES `KeySetCR` — the carrier is witnessed FALSE, so it is
not `True`-shaped. -/
def badHash (_ : List Nat) : Int := 0

theorem badHash_not_CR : ¬ KeySetCR badHash := fun hbad =>
  absurd (hbad [0] [1] rfl) (by decide)

/-- HONEST rotation FIRES: exhibiting the committed preimage installs the new set + the fresh
commitment. -/
example :
    rotateStep demoHash { current := [1, 2], nextDigest := demoHash [3, 4] }
        { newKeys := [3, 4], freshNext := demoHash [5, 6] }
      = some { current := [3, 4], nextDigest := demoHash [5, 6] } := by
  unfold rotateStep
  rw [if_pos rfl]

/-- FORGED rotation REFUSED: compromise resistance fires on the reference CR hash — a wrong key
set (the current-key thief's best output) is rejected. -/
example :
    rotateStep demoHash { current := [1, 2], nextDigest := demoHash [3, 4] }
        { newKeys := [9, 9], freshNext := 0 }
      = none :=
  rotate_compromise_resistant demoHash_CR rfl (by decide)

/-- A fast executable key-set hash for the `#guard` register demos (injective on the demo
points; the CR-consuming theorems use `demoHash`). -/
def tinyHash (ks : List Nat) : Int := ks.foldl (fun a k => a * 100 + (k : Int) + 1) 0

/-- The identity COUNCIL cell (cell `0`): balance `0`, the `next_keys_digest` register committing
to the (unexposed) key set `[3, 4]`. Empty cap table — authority by ownership (the council acts
as the cell), the `ss0` demo shape. -/
def idState : RecChainedState :=
  { kernel :=
      { accounts := {0}
        cell := fun c =>
          if c = 0 then
            .record [("balance", .int 0), (nextKeysDigestField, .int (tinyHash [3, 4]))]
          else .record [("balance", .int 0)]
        caps := fun _ => [] }
    log := [] }

-- HONEST rotation (exhibits the committed preimage `[3,4]`) COMMITS:
#guard (rotateWrite tinyHash idState 0 0 [3, 4] (tinyHash [5, 6])).isSome
-- ...and the register now holds the FRESH commitment (the next chain link):
#guard ((rotateWrite tinyHash idState 0 0 [3, 4] (tinyHash [5, 6])).map
    (fun s => fieldOf nextKeysDigestField (s.kernel.cell 0))) == some (tinyHash [5, 6])
-- ...balance-neutral (the conserved total is untouched):
#guard ((rotateWrite tinyHash idState 0 0 [3, 4] (tinyHash [5, 6])).map
    (fun s => recTotal s.kernel)) == some 0
-- ...audited (exactly one receipt row — the exported `rot` event):
#guard ((rotateWrite tinyHash idState 0 0 [3, 4] (tinyHash [5, 6])).map
    (fun s => s.log.length)) == some 1
-- FORGED rotation (wrong key set ⇒ wrong preimage) REFUSED — current-key compromise rotates nothing:
#guard (rotateWrite tinyHash idState 0 0 [9, 9] (tinyHash [5, 6])).isNone
-- An unauthorized actor cannot rotate even WITH the right preimage (the authority gate):
#guard (rotateWrite tinyHash idState 9 0 [3, 4] (tinyHash [5, 6])).isNone

-- THE STRICT-DOMINATION TRIANGLE, executed (staged at 100, cooling 50):
-- inside the window, even the honest preimage-exhibiting rotation is refused (slow + visible):
#guard (rotateWriteCooled tinyHash 100 50 149 idState 0 0 [3, 4] (tinyHash [5, 6])).isNone
-- at the boundary, the honest rotation commits (cooling does not over-tighten):
#guard (rotateWriteCooled tinyHash 100 50 150 idState 0 0 [3, 4] (tinyHash [5, 6])).isSome
-- cooled but FORGED: still refused (cooling alone would have admitted the patient attacker):
#guard (rotateWriteCooled tinyHash 100 50 150 idState 0 0 [9, 9] (tinyHash [5, 6])).isNone

-- Chains execute: a two-link honest chain commits; a forged first link kills the chain.
#guard (rotChain tinyHash ⟨[1, 2], tinyHash [3, 4]⟩
    [⟨[3, 4], tinyHash [5, 6]⟩, ⟨[5, 6], tinyHash [7, 8]⟩]).isSome
#guard (rotChain tinyHash ⟨[1, 2], tinyHash [3, 4]⟩
    [⟨[9, 9], tinyHash [5, 6]⟩, ⟨[5, 6], tinyHash [7, 8]⟩]).isNone

/-! ## §5 — axiom hygiene: every keystone pins {propext, Classical.choice, Quot.sound}. -/

#assert_axioms rotate_exhibits_preimage
#assert_axioms rotate_current_keys_irrelevant
#assert_axioms rotate_compromise_resistant
#assert_axioms rotate_install_unique
#assert_axioms rotChain_pinned_by_commitments
#assert_axioms rotateStepCooled_refuses_inside
#assert_axioms rotateStepCooled_admits_after
#assert_axioms rotateStepCooled_compromise_resistant
#assert_axioms cooling_blocks_admitted_preimage
#assert_axioms preimage_blocks_cooled_rotation
#assert_axioms rotateWrite_exhibits_preimage
#assert_axioms rotateWrite_commits_fresh
#assert_axioms rotateWrite_conserves
#assert_axioms rotateWrite_caps_unchanged
#assert_axioms rotateWrite_caveats_enforced
#assert_axioms rotateWrite_compromise_resistant
#assert_axioms rotateWriteCooled_refuses_inside
#assert_axioms rotateWriteCooled_factors
#assert_axioms demoHash_CR
#assert_axioms badHash_not_CR

end Dregg2.Apps.PreRotation
