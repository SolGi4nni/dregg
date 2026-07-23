/-
# Dregg2.Distributed.FinalityCertWidth — the felt-width binding of the BFT finality certificate.

**What this proves, and why it was missing.** `FinalizedLightClient` proves the THREE-LEG finalized
light client at the resolution of the *quorum* (`CertValid` = the node's real super-ratification
leader rule) and an *abstract* root: its `FinalityCert.finalizedRoot : ℤ` is a single opaque field
value, and its `Bound` seam is a plain `ℤ` equality. At that resolution the model is BLIND to the
felt-width of the root — a lane-0 pin and a full 8-lane pin are indistinguishable, because the root is
one integer and the committee *signature* over it is not modeled at all. That blindness is the
`docs/WOUND-felt-width-boundaries-2026-07-19.md` #1 launder: the compensating "segment tooth" binds
the aggregate to *its own execution*, never the committee's *signature* to the *wide* root.

This module supplies the formal content the abstract model omits. It models the finalized root at
felt resolution (`Fin 8 → Felt`, faithful to the Rust `finalized_root : [BabyBear; SEG_ANCHOR_WIDTH]`)
and the domain-separated signing message the Rust `lightclient/src/lib.rs::finality_signing_message`
builds, in its two shapes:

  * **v1** (`dregg-finality-cert-v1`, the historical hole) — absorbed ONLY lane 0.
  * **v2** (`dregg-finality-cert-v2`, HEAD) — absorbs ALL EIGHT lanes.

and proves, as theorems over ALL inputs (not the two-witness Rust case-test
`finality_cert_rejects_lane0_colliding_fork`, which is `#[ignore]`-gated):

  * **THE FALSIFIER (`v1_forges`, `sigMsgV1_forkRoot`).** The v1 message is NOT injective in the wide
    root: for every root `r` there is a DISTINCT root `forkRoot r` (lane 0 unchanged, lane 1 bumped)
    with a byte-identical v1 message, so a genuine committee signature over `r` verifies UNCHANGED
    over `forkRoot r` — the ~2^31 finality-substitution forgery is admitted by the v1 binding.
  * **THE LAUNDER, exposed (`narrow_seam_underdetermines` vs `wide_seam_determines`).** A binding that
    pins only the lane-0 projection — what a v1 signature, and equally the abstract-`ℤ`
    `FinalizedLightClient.Bound.cert_binds` seam, actually constrains — does NOT determine the wide
    root; two distinct wide roots satisfy it. The all-8-lane binding does. The launder is the gap
    between those two, PROVED, not asserted.
  * **THE FIX, sound (`sigMsgV2_inj`, `v2_binds_unique`, `v1_ne_v2`).** The v2 message is injective in
    `(root, participant_count)`: distinct wide roots — even ones sharing lane 0 — produce distinct
    messages, so no genuine signature replays onto a different finalized root; the collision closes.
    A v1 certificate never verifies under the v2 message (domain-tag separation).

**Byte-safe / posture.** The Rust v2 widening ALREADY LANDED at HEAD (`beb2661fc1`); this module does
not touch the deployed format. It is the machine-checked proof that the (deployed) Kind-E widening is
correct AND that the narrow binding it replaced was genuinely broken — the proof the launder hid.

**Resolution note.** A lane is modeled by its canonical `as_u32()` value (a `Felt := ℤ`); the real
message appends `to_le_bytes` per felt and `to_le_bytes` of a `u64` count — all FIXED-WIDTH fields, so
the flat `Vec<u8>` is a bijection with this word tuple: injectivity here holds byte-for-byte in the
wire message. The ~31-bit range (`< 2013265921`) that prices the offline grind at ~2^31 is orthogonal
to the binding's injectivity — it sets the forgery COST, not whether the forgery exists.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Distributed.FinalityCertWidth`.
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Distributed.FinalityCertWidth

/-! ## 1. The wide finalized root — felt resolution. -/

/-- `SEG_ANCHOR_WIDTH = 8` — the `lightclient` constant; the wide finalized root is 8 BabyBear lanes
(~124 bits). An `abbrev` so `Fin SEG_ANCHOR_WIDTH` reduces to `Fin 8` for numeral instances. -/
abbrev SEG_ANCHOR_WIDTH : ℕ := 8

/-- One field lane, modeled by its canonical `as_u32()` value. The BabyBear range `< 2013265921`
prices the offline grind (~2^31) but is irrelevant to the binding's injectivity, so we keep the lane
an integer. -/
abbrev Felt : Type := ℤ

/-- The wide finalized root the finality certificate attests — faithful to the Rust
`finalized_root : [BabyBear; SEG_ANCHOR_WIDTH]`. -/
abbrev WideRoot : Type := Fin SEG_ANCHOR_WIDTH → Felt

/-! ## 2. The domain-separated signing message (`finality_signing_message`), v1 and v2.

The domain tags stand for the 23-byte ASCII prefixes `b"dregg-finality-cert-v1\0"` /
`b"dregg-finality-cert-v2\0"`; the only property used of them is that they are DISTINCT (the tag bump
that makes a v1 certificate dead under the v2 message). -/

/-- v1 domain tag (`dregg-finality-cert-v1`). -/
def domainTagV1 : Felt := 1
/-- v2 domain tag (`dregg-finality-cert-v2`). -/
def domainTagV2 : Felt := 2

/-- **The v1 (BROKEN) signing message** — Rust `dregg-finality-cert-v1` absorbed ONLY lane 0 of the
wide root. As a function of the WIDE root it reads `r 0` alone. -/
def sigMsgV1 (r : WideRoot) (pc : ℕ) : List Felt :=
  [domainTagV1, r 0, (pc : Felt)]

/-- **The v2 (WIDENED) signing message** — Rust `dregg-finality-cert-v2` absorbs ALL EIGHT lanes
(`for f in finalized_root { m.extend(f.as_u32().to_le_bytes()) }`), then the participant count. -/
def sigMsgV2 (r : WideRoot) (pc : ℕ) : List Felt :=
  (domainTagV2 :: List.ofFn r) ++ [(pc : Felt)]

/-! ## 3. The fork — a distinct wide root sharing lane 0 (the ~2^31 grind's target shape). -/

/-- `forkRoot r` — `r` with lane 0 UNCHANGED and lane 1 bumped by one. This is exactly the fork
`W'` the Rust forge tooth constructs (`w_fork[1] += 1`, `w_fork[0] == w[0]`): a different wide root
that a ~2^31 offline `wire_commit_8` grind buys, colliding with `r` on lane 0. -/
def forkRoot (r : WideRoot) : WideRoot :=
  fun i => if i = 1 then r 1 + 1 else r i

@[simp] theorem forkRoot_apply_zero (r : WideRoot) : forkRoot r 0 = r 0 := by
  simp [forkRoot]

@[simp] theorem forkRoot_apply_one (r : WideRoot) : forkRoot r 1 = r 1 + 1 := by
  simp [forkRoot]

/-- The fork is a GENUINELY different wide root (it differs at lane 1). -/
theorem forkRoot_ne (r : WideRoot) : forkRoot r ≠ r := by
  intro h
  have h1 : forkRoot r 1 = r 1 := congrFun h 1
  rw [forkRoot_apply_one] at h1
  simp at h1

/-! ## 4. THE FALSIFIER — the v1 binding admits the finality-substitution forgery.

The v1 message reads only lane 0, so the fork's v1 message is byte-identical: a signature (which binds
the message bytes alone) over the true root verifies UNCHANGED over the fork. This is the
`~2^31`-cheap forgery the wound prices. -/

/-- **The v1 collision.** `forkRoot r` and `r` have byte-identical v1 signing messages — the v1
message does not mention lanes 1..7, so bumping lane 1 leaves it fixed. -/
theorem sigMsgV1_forkRoot (r : WideRoot) (pc : ℕ) :
    sigMsgV1 (forkRoot r) pc = sigMsgV1 r pc := by
  simp only [sigMsgV1, forkRoot_apply_zero]

/-- **`v1_forges` (THE FALSIFIER, signature form).** Model a committee signature by the predicate
`SigValid`: it holds for exactly the message(s) the honest committee's Ed25519 + ML-DSA signatures
verify over — and verify treats the message as opaque bytes, so `SigValid` respects message equality.
Then a genuine v1 signature over the true wide root `r` ALSO authorizes a DISTINCT wide root
`forkRoot r ≠ r`: the same certificate finalizes two different roots. Binding only lane 0 does NOT
determine the wide root. -/
theorem v1_forges (SigValid : List Felt → Prop) (r : WideRoot) (pc : ℕ)
    (honest : SigValid (sigMsgV1 r pc)) :
    ∃ r', r' ≠ r ∧ SigValid (sigMsgV1 r' pc) :=
  ⟨forkRoot r, forkRoot_ne r, by rw [sigMsgV1_forkRoot]; exact honest⟩

/-! ## 5. THE LAUNDER, exposed — narrow (lane-0) seam vs wide (all-8) seam.

`FinalizedLightClient.Bound.cert_binds` is a plain `ℤ` equality against a single abstract root. A
v1-signed cert only pins that abstract root to the lane-0 word — so the seam, at felt resolution, is
`narrowSeam` below. The launder is that `narrowSeam` looks like it pins "the root" but leaves lanes
1..7 free. `wideSeam` (the v2 all-lanes compare) is what actually pins it. -/

/-- The lane-0 projection a v1 signature / an abstract-`ℤ` seam pins. -/
def lane0 (r : WideRoot) : Felt := r 0

/-- What the NARROW (v1 / abstract-`ℤ`) binding constrains: the wide root's lane 0 equals the shown
value. -/
def narrowSeam (shown : Felt) (r : WideRoot) : Prop := r 0 = shown

/-- What the WIDE (v2, all-8-lanes) binding constrains: the whole wide root equals the shown root. -/
def wideSeam (shown : WideRoot) (r : WideRoot) : Prop := r = shown

/-- **`narrow_seam_underdetermines` (the launder, PROVED).** For every shown lane-0 value there are
TWO DISTINCT wide roots that both satisfy the narrow seam — so pinning lane 0 does not determine the
wide root the committee finalized. This is precisely what the abstract-`ℤ` `Bound` seam leaves free
under a v1-signed certificate. -/
theorem narrow_seam_underdetermines (shown : Felt) :
    ∃ r r' : WideRoot, r ≠ r' ∧ narrowSeam shown r ∧ narrowSeam shown r' := by
  refine ⟨(fun _ => shown), forkRoot (fun _ => shown), ?_, ?_, ?_⟩
  · exact fun h => forkRoot_ne (fun _ => shown) h.symm
  · rfl
  · simp only [narrowSeam, forkRoot_apply_zero]

/-- **`wide_seam_determines` (the fix, PROVED).** The wide seam pins the root UNIQUELY: two roots
that both satisfy it are equal. Binding all eight lanes determines the wide root; the narrow seam's
freedom is gone. -/
theorem wide_seam_determines (shown r r' : WideRoot)
    (h : wideSeam shown r) (h' : wideSeam shown r') : r = r' := by
  rw [wideSeam] at h h'; rw [h, h']

/-! ## 6. THE FIX, sound — the v2 message is injective in `(root, count)`; the collision closes. -/

/-- **`sigMsgV2_inj` (WIDENED-BINDING SOUNDNESS).** The v2 signing message is injective in the wide
root AND the participant count: equal v2 messages force equal roots and equal counts. So a genuine
committee signature over the v2 message binds exactly one `(finalized_root, participant_count)` pair —
no lane-0 collision, no threshold shrink. -/
theorem sigMsgV2_inj {r r' : WideRoot} {pc pc' : ℕ}
    (h : sigMsgV2 r pc = sigMsgV2 r' pc') : r = r' ∧ pc = pc' := by
  unfold sigMsgV2 at h
  have hlen : (domainTagV2 :: List.ofFn r).length = (domainTagV2 :: List.ofFn r').length := by
    simp
  obtain ⟨hpre, hsuf⟩ := List.append_inj h hlen
  rw [List.cons.injEq] at hpre
  refine ⟨List.ofFn_inj.mp hpre.2, ?_⟩
  injection hsuf with hcast _
  exact_mod_cast hcast

/-- **`v2_binds_unique` (the fix, signature form).** A committee signature over `r`'s v2 message
authorizes `r` ALONE: any wide root whose v2 message that signature also verifies over IS `r`. The
finality-substitution replay is impossible. -/
theorem v2_binds_unique {r r' : WideRoot} {pc : ℕ}
    (hmsg : sigMsgV2 r' pc = sigMsgV2 r pc) : r' = r :=
  (sigMsgV2_inj hmsg).1

/-- **`sigMsgV2_forkRoot_ne` (the fix bites the specific fork).** Under v2 the fork's message DIFFERS
from the honest root's — exactly where the v1 message was byte-identical. The replayed signatures are
dead. -/
theorem sigMsgV2_forkRoot_ne (r : WideRoot) (pc : ℕ) :
    sigMsgV2 (forkRoot r) pc ≠ sigMsgV2 r pc :=
  fun h => forkRoot_ne r (sigMsgV2_inj h).1

/-- **`v1_ne_v2` (domain separation).** A v1 (lane-0-only) certificate NEVER verifies under the v2
message: the leading domain tags differ, so the messages differ regardless of root or count. This is
the tag bump `dregg-finality-cert-v1` → `-v2`. -/
theorem v1_ne_v2 (r r' : WideRoot) (pc pc' : ℕ) :
    sigMsgV1 r pc ≠ sigMsgV2 r' pc' := by
  intro h
  unfold sigMsgV1 sigMsgV2 at h
  rw [List.cons_append] at h
  injection h with hhead _
  simp only [domainTagV1, domainTagV2] at hhead
  exact absurd hhead (by decide)

/-! ## 7. NON-VACUITY — the theorems FIRE on a concrete wide root (executable witnesses).

A false `#guard` is a build error, so these machine-check that the v1 collision and v2 separation are
REAL on a concrete fork, and that lane 0 collides while lane 1 does not (the shape the ~2^31 grind
buys). -/

/-- A concrete wide root (all lanes 7 — non-trivial beyond lane 0, so the fork bites). -/
def rDemo : WideRoot := fun _ => 7

-- The v1 messages of the fork and the honest root are byte-identical (the replay hole).
#guard sigMsgV1 (forkRoot rDemo) 4 = sigMsgV1 rDemo 4
-- Under v2 they DIFFER (the replay is dead).
#guard decide (sigMsgV2 (forkRoot rDemo) 4 = sigMsgV2 rDemo 4) = false
-- The two roots collide on lane 0 …
#guard forkRoot rDemo 0 = rDemo 0
-- … but genuinely differ on lane 1 (so they are distinct wide roots).
#guard decide (forkRoot rDemo 1 = rDemo 1) = false
-- A v1 certificate never matches the v2 message shape (domain separation).
#guard decide (sigMsgV1 rDemo 4 = sigMsgV2 rDemo 4) = false

/-! ## 8. Axiom hygiene. -/

#assert_axioms sigMsgV1_forkRoot
#assert_axioms forkRoot_ne
#assert_axioms v1_forges
#assert_axioms narrow_seam_underdetermines
#assert_axioms wide_seam_determines
#assert_axioms sigMsgV2_inj
#assert_axioms v2_binds_unique
#assert_axioms sigMsgV2_forkRoot_ne
#assert_axioms v1_ne_v2

end Dregg2.Distributed.FinalityCertWidth
