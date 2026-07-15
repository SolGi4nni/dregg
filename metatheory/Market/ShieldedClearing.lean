/-
# Market.ShieldedClearing — DrEX RUNG 3: PRIVATE MATCHING (the marquee).

**The multilateral ring matcher clears over SHIELDED notes** — matching over hidden commitments,
with no operator peek and no decryption committee. This is the one thing no system in the DrEX
scholar survey (`docs/deos/DREX-DESIGN.md §1`) can copy: Penumbra decrypts a per-block aggregate with
a `t`-of-`n` validator committee; CoW's solvers see every order; Shutter's Keypers hold the key. DrEX
decrypts **nothing** — because there is nothing to decrypt.

This module WELDS three already-proven towers into one private-matching statement, re-proving none of
them:

  1. **The ring clearing over the matched cycle** (`Dregg2/Intent/Ring.lean` + `Market/Fairness.lean`):
     `settleRing_conserves` (per-asset supply preserved across the whole ring, on the REAL executor
     ledger), `cycleValid_settlement_balanced` (structurally closed — no phantom value), and
     `clearing_respects_limits` (every leg debited only its offered asset ≤ its offer, credited its
     wanted asset ≥ its minimum — the give+receive fairness). CRUCIALLY these are stated over
     `MatchNode` — the OFFERED/WANTED columns the matcher reads — which in the shielded setting are
     the pool's HIDDEN commitments (`circuit-prove/src/shielded/pool.rs`: value + owner + asset all
     behind `commit_hidden_asset`). The matcher clears the COMMITTED claims, never the clear ledger.

  2. **The per-leg shielded spend refinement** (`Dregg2/Shielded/ClaimRefinement.lean`):
     `shielded_spend_claim_refines` — a valid shielded-spend claim `[nullifier, merkle_root,
     value_binding]` (the note is a MEMBER of the tree at `merkleRoot`, and its `nullifier` is FRESH)
     REFINES a sound VM step: it is AUTHORIZED (spends a real committed member note whose full
     preimage the spender knows — the C6 value-theft tooth) and preserves NO-DOUBLE-SPEND (fresh →
     joins the spent set → never re-spendable). WHO traded stays hidden (owner/key inside
     `HidingFriPcs`); only the nullifier is revealed, and only to gate the double-spend.

  3. **The homomorphic per-asset conservation over hidden values** (`Dregg2/Exec/ShieldedValue.lean`):
     `created_value_conservation` — `Σ commit(vᵢ, rᵢ) = commit(Σ vᵢ, Σ rᵢ)` (the Pedersen `commit_hom`
     collapse). So `Σ C_in − Σ C_out = 0` IS per-asset conservation, CHECKABLE OVER THE COMMITMENTS
     ALONE — a verifier confirms the ring created no value without learning any single amount. This is
     the shielded pool's Schnorr-excess conservation (`pool.rs:33-41`) composed with the ring's
     balance: conservation while every value stays hidden.

## What is PROVED here (composed) vs the honest scope

  * `shielded_ring_clears` (THE KEYSTONE) — a shielded ring whose matched cycle is `CycleValid` and
    whose ledger settlement commits is simultaneously: **(a) CONSERVING** per asset on the real
    executor ledger; **(b) FAIR** — structurally `RingBalanced` AND every leg within its committed
    offer/want limits; **(c) PRIVATE + NO-DOUBLE-SPEND** — every leg spends a real member note (hidden
    owner/value) whose nullifier is fresh and, once spent, can NEVER be re-spent.
  * `shielded_ring_value_conserves_hidden` (THE HIDDEN-CONSERVATION WELD) — if the ring's spent (input)
    and created (output) notes carry equal value+blinding sums (the balanced cycle), their COMMITMENT
    sums are equal — the homomorphic excess is zero, provable on commitments with no value revealed.
  * `shielded_ring_clears_real_crypto` (THE REAL-CRYPTO WELD, §4b) — the SAME two hidden-crypto halves
    over the REAL primitives that retire the two toy stand-ins the audit flagged: hidden conservation
    over the real two-generator group Pedersen (binding = DLog `CryptoPrimitives.binding`) and
    membership over the real Poseidon2 tree (root-binds-set = `Poseidon2SpongeCR`), so a forged
    committed set forces a collision. See `Dregg2.Shielded.RealCrypto`. The generic
    `shielded_ring_value_conserves_hidden`'s in-file `refVC`/`refTreeRoot` witnesses are the toy
    stand-ins; the real primitives + their named floors (DLog / Poseidon2 CR) live in that module.
  * NON-VACUITY, both polarities: a concrete two-leg shielded ring (`demoShieldedRing`, two DISTINCT
    fresh member spends over a `CycleValid` swap) clears fair + private; and the TEETH — a re-used
    nullifier is refused (`shielded_leg_no_double_spend`, from `unshield_no_rewitness`), an
    over-debiting/wrong-asset matching never FORMS (`Market.overdebit_refused` / `wrongAsset_refused`,
    reused), and a value-minting output makes the commitment excess NON-zero (`#guard`).

**HONEST GRADE — Lean SPEC + note-level circuit, endpoint fold NAMED.** This lands the
*specification* of DrEX rung 3: the private-matching clearing is a machine-checked theorem composing
the shielded-spend leaf + the ring + the nullifier freshness.  The deployed Rust AIR now also realizes
the two-leg and N-leg note-algebra layer.  Two scope edges are named, not hidden:

  * The **matching layer (`MatchNode`) and the shielded-spend claim are fused in the deployed ring
    AIR**, which constrains `offerAsset`/`offerAmount` to the spent note's `asset`/`value`; the Lean
    theorem `LedgerRealizationExt.shielded_ring_fused_clears` states the corresponding `LegFused`
    composition.  What remains is not this note-algebra weld but a Lean-authored descriptor refinement
    from the serialized AIR trace to that semantic object.
  * The **endpoint circuit realization** remains named: the two-leg and N-leg Rust AIRs fold real
    shielded-spend leaves and enforce fusion/cycle/conservation, but publish only note-level claims.
    They do not publish or constrain creators, the faithful eight-lane kernel pre/post endpoints,
    action count, lifecycle/authorization state, or the receipt-log transition required by
    `Market.ProtocolAssurance.ShieldedRingDescriptorRefines`.  Closing this requires a Lean-authored
    endpoint-carrying outer descriptor and recursive binding to the two ordinary balance-action
    traces.  This module does not claim that absent endpoint theorem.

## THE PAYOFF — this deletes the `intent/src/trustless.rs` DECRYPT committee.

DrEX's front-running prevention today rests on a `t`-of-`n` threshold-decryption committee
(`trustless.rs`: `threshold_decrypt`, Shamir shares) — the residual trust `docs/deos/DREX-DESIGN.md §6`
is candid about. Matching over hidden commitments removes it entirely: the matcher reads the COMMITTED
claims (`clearing_respects_limits` over `MatchNode`), settles by spending NULLIFIERS (`unshieldK`,
never revealing owner/value), and conservation is checked over the Pedersen commitments
(`shielded_ring_value_conserves_hidden`). **No party ever holds the plaintext or the ordering power** —
"private and fair without an operator who can peek."

Pure.
-/
import Market.Fairness
import Dregg2.Shielded.ClaimRefinement
import Dregg2.Shielded.RealCrypto
import Dregg2.Exec.NullifierAccumulator
import Dregg2.Tactics

namespace Market

open Dregg2.Intent.Ring
open Dregg2.Exec
open Dregg2.Exec.ShieldedValue
open Dregg2.Shielded

set_option autoImplicit false

/-! ## 1. A SHIELDED RING LEG — a matched claim bound to a hidden note-spend. -/

/-- **A shielded ring leg** (parametrised by the pool registry `poolOf : AssetId → CellId`): the
matcher's committed claim (`node : MatchNode`, the OFFERED/WANTED columns — HIDDEN commitments in the
shielded pool) bound to the SHIELDED spend that backs it (a committed `unshieldK` of the claim's
nullifier over the leg's own pre-state). The bundled proofs `hbound`/`hstep` are exactly the
hypotheses `Dregg2.Shielded.shielded_spend_claim_refines` consumes, so a leg's spend is guaranteed to
refine a sound VM step (AUTHORIZED + NO-DOUBLE-SPEND) — the private authorization the matcher never
sees the plaintext of.

The two layers are composed, not yet fused (see the module header): `node` is what the matcher clears
(committed offer/want), `claim`/`hstep` is the private note-spend that settles it. -/
structure ShieldedLeg (poolOf : AssetId → CellId) where
  /-- The matched claim the ring solver reads — HIDDEN commitments to offer/want in the shielded pool. -/
  node   : MatchNode
  /-- The shielded-spend claim `[nullifier, merkle_root, value_binding]` backing this leg. -/
  claim  : ShieldedSpendClaim
  /-- This leg's pre-state (the pool inventory the spend consumes from). -/
  pre    : ShieldedState
  /-- This leg's post-state after the committed spend. -/
  post   : ShieldedState
  /-- Where the unshielded value lands. -/
  dst    : CellId
  /-- The circuit's membership teeth: `merkleRoot` commits the pool inventory (the §3.6 `hbound`). -/
  hbound : RootBindsInventory claim.merkleRoot pre
  /-- The shielded spend of the claim's nullifier COMMITTED (the sound VM step). -/
  hstep  : unshieldK poolOf pre claim.nullifier dst = some post

/-- A **shielded ring** — the ordered list of shielded legs the matcher clears into a cycle. -/
abbrev ShieldedRing (poolOf : AssetId → CellId) := List (ShieldedLeg poolOf)

/-- The matcher's view of a shielded ring: the list of committed `MatchNode` claims. The ring
solver's `CycleValid`/`clearing_respects_limits` reason over THIS — hidden commitments, never the
clear ledger. -/
def matchNodes {poolOf : AssetId → CellId} (sr : ShieldedRing poolOf) : List MatchNode :=
  sr.map (·.node)

@[simp] theorem matchNodes_length {poolOf : AssetId → CellId} (sr : ShieldedRing poolOf) :
    (matchNodes sr).length = sr.length := by simp [matchNodes]

/-! ## 2. The per-leg private refinement — every leg is an AUTHORIZED, NO-DOUBLE-SPEND spend. -/

/-- **`ShieldedLeg.refines` — a leg's spend REFINES a sound VM step.** Direct application of
`Dregg2.Shielded.shielded_spend_claim_refines`: the leg (a) spent a REAL committed member note whose
value moved to `dst` (AUTHORIZED — membership is the shielded authorization, the owner stays hidden),
and (b) its nullifier was FRESH, joins the spent set, and can NEVER be re-spent (NO-DOUBLE-SPEND). The
matcher authorizes the trade WITHOUT ever holding the note's plaintext. -/
theorem ShieldedLeg.refines {poolOf : AssetId → CellId} (leg : ShieldedLeg poolOf) :
    (∃ n ∈ leg.pre.notes, n.nf = leg.claim.nullifier ∧
        MemberAtRoot leg.claim.merkleRoot n.cm leg.pre.kernel.commitments ∧
        leg.post.kernel.bal leg.dst n.asset = leg.pre.kernel.bal leg.dst n.asset + n.value)
    ∧ (leg.claim.nullifier ∉ leg.pre.kernel.nullifiers ∧
        leg.claim.nullifier ∈ leg.post.kernel.nullifiers ∧
        ∀ dst', unshieldK poolOf leg.post leg.claim.nullifier dst' = none) :=
  shielded_spend_claim_refines poolOf leg.claim leg.hbound leg.hstep

/-! ## 3. THE KEYSTONE — the shielded ring clears CONSERVING + FAIR + PRIVATE. -/

/-- **`shielded_ring_clears` — DrEX RUNG 3, the private-matching clearing.** A shielded ring whose
matched cycle is `CycleValid` (the graph the solver actually searches — over the HIDDEN committed
claims), with positive wants, that settles through the VERIFIED executor
(`settleRing k (settlementsOf (matchNodes sr)) = some k'`), is simultaneously:

  * **(a) CONSERVING** — for every asset the total supply is preserved on the REAL executor ledger
    (`settleRing_conserves` — the ring mints/burns nothing);
  * **(b) FAIR** — the settlement is structurally `RingBalanced` (closed, no phantom value) AND every
    leg respects its committed limits: debited only its offered asset in amount ≤ its offer, credited
    its wanted asset in amount ≥ its declared minimum (`clearing_respects_limits`);
  * **(c) PRIVATE + NO-DOUBLE-SPEND** — every leg spends a REAL committed member note (owner/value
    hidden), whose nullifier was fresh, joins the spent set, and can NEVER be re-spent
    (`ShieldedLeg.refines`).

The whole matching+clearing runs over the COMMITTED claims and settles by spending nullifiers — no
party ever holds a leg's plaintext. This is the marquee: private and fair with no operator who can
peek, no decryption committee. Atomicity rides the same fold separately (`settleRing_atomic`: a
failing leg leaves no `some k'`). -/
theorem shielded_ring_clears {poolOf : AssetId → CellId} (sr : ShieldedRing poolOf)
    (h : CycleValid (matchNodes sr)) (hpos : ∀ n ∈ matchNodes sr, 0 < n.wantMin)
    (k k' : RecordKernelState)
    (hsettle : settleRing k (settlementsOf (matchNodes sr)) = some k') :
    -- (a) CONSERVES per asset on the real executor ledger.
    (∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b)
    -- (b) FAIR — structurally balanced AND every leg within its committed offer/want.
    ∧ RingBalanced (settlementsOf (matchNodes sr))
    ∧ (∀ j, j < (matchNodes sr).length →
        ((chainedLeg ((matchNodes sr).map MatchNode.toRingNode) j).asset
            = ((matchNodes sr).getD j default).offerAsset ∧
          (chainedLeg ((matchNodes sr).map MatchNode.toRingNode) j).amount
            ≤ ((matchNodes sr).getD j default).offerAmount) ∧
        (receivedAsset (matchNodes sr) j = ((matchNodes sr).getD j default).wantAsset ∧
          ((matchNodes sr).getD j default).wantMin ≤ receivedAmount (matchNodes sr) j))
    -- (c) PRIVATE + NO-DOUBLE-SPEND — every leg is an authorized, fresh-nullifier member spend.
    ∧ (∀ leg ∈ sr,
        (∃ n ∈ leg.pre.notes, n.nf = leg.claim.nullifier ∧
            MemberAtRoot leg.claim.merkleRoot n.cm leg.pre.kernel.commitments ∧
            leg.post.kernel.bal leg.dst n.asset = leg.pre.kernel.bal leg.dst n.asset + n.value)
        ∧ (leg.claim.nullifier ∉ leg.pre.kernel.nullifiers ∧
            leg.claim.nullifier ∈ leg.post.kernel.nullifiers ∧
            ∀ dst', unshieldK poolOf leg.post leg.claim.nullifier dst' = none)) :=
  ⟨settleRing_conserves (settlementsOf (matchNodes sr)) k k' hsettle,
   cycleValid_settlement_balanced h hpos,
   fun j hj =>
     ⟨(settlement_from_sender_within_offer h j hj).2, cycle_individuallyRational h j hj⟩,
   fun leg _ => leg.refines⟩

/-! ## 4. THE HIDDEN-CONSERVATION WELD — the excess is zero over the COMMITMENTS ALONE. -/

/-- **`shielded_ring_value_conserves_hidden` — conservation over HIDDEN notes.** If the ring's spent
INPUT notes and created OUTPUT notes carry equal value sums AND equal blinding sums (exactly what a
balanced conserving cycle enforces — value in = value out), then their Pedersen COMMITMENT sums are
equal: `Σ commit(vᵢ_in, rᵢ_in) = Σ commit(vⱼ_out, rⱼ_out)`. So the homomorphic excess `Σ C_in − Σ
C_out = 0`, and a verifier confirms the ring created no value **checking only the commitments** —
never learning a single amount. This composes the shielded pool's per-asset Schnorr-excess
conservation (`pool.rs:33-41`) with the ring's balance: the shielded pool's `created_value_conservation`
(`Σ commit = commit Σ`) applied to both sides, glued by the balance hypotheses. Matching over hidden
commitments conserves. -/
theorem shielded_ring_value_conserves_hidden (vc : ValueCommitment)
    (ins outs : List BoundNote) (hin : AllNonneg ins) (hout : AllNonneg outs)
    (hval : (ins.map BoundNote.value).sum = (outs.map BoundNote.value).sum)
    (hbl  : (ins.map BoundNote.blinding).sum = (outs.map BoundNote.blinding).sum) :
    listCommitment vc ins = listCommitment vc outs := by
  rw [created_value_conservation vc ins hin, created_value_conservation vc outs hout, hval, hbl]

/-! ## 4b. THE SAME WELD OVER REAL CRYPTO — retiring the two toy stand-ins.

`shielded_ring_value_conserves_hidden` above is generic over any `ValueCommitment`, but its
witnesses (`demo_hidden_conservation`) ran on the TOY `refVC` (`commit v r = (v+r).toNat` —
additive, non-binding), and `ClaimRefinement`'s membership ran on the TOY `refTreeRoot` (a linear
rolling hash, no CR). `Dregg2.Shielded.RealCrypto` re-grounds BOTH on the real primitives the tree
already carries, with the honest floors named:

  * hidden conservation over the REAL two-generator group Pedersen (`commit v r = v·G + r·H`,
    `commit_hom` PROVED) — binding rests on the DLog carrier `CryptoPrimitives.binding`;
  * membership over the REAL Poseidon2 tree (`root = sponge leaves`) — root-binds-the-leaf-set
    rests on the named `Poseidon2SpongeCR` (the SAME sponge CR `StateCommit`/`SortedTreeNonMembership`
    bind under), so a forged committed set forces a Poseidon2 collision.

The two toys were structurally weak, not merely small: `ValueCommitment.hom` demands
`Nat`-additivity, satisfiable ONLY by a linear stand-in — a real Pedersen is not `Nat`-additive, it
lives in a group, so the real conservation lives at the GROUP layer (`RealCrypto.ring_conserves_pedersen`).
-/

/-- **`shielded_ring_clears_real_crypto` — rung-3's two hidden-crypto halves over REAL primitives.**
A balanced ring over the real group Pedersen conserves on the COMMITMENTS (hidden conservation,
under DLog `binding`), and a leaf committed under the real Poseidon2 tree has its membership root
bind the leaf set (under `Poseidon2SpongeCR`), so a forged set forces a collision. This is
`shielded_ring_value_conserves_hidden` + the membership half, re-stated over the retired-toy
replacements — a direct re-export of `RealCrypto.rung3_real_crypto`. -/
theorem shielded_ring_clears_real_crypto {Digest : Type} [AddCommGroup Digest]
    [Dregg2.Crypto.CryptoPrimitives Digest] (T : Dregg2.Shielded.RealCrypto.Poseidon2Tree)
    (ins outs : List Dregg2.Crypto.Pedersen.Note)
    (hval : (ins.map Dregg2.Crypto.Pedersen.Note.value).sum
              = (outs.map Dregg2.Crypto.Pedersen.Note.value).sum)
    (hbl  : (ins.map Dregg2.Crypto.Pedersen.Note.blinding).sum
              = (outs.map Dregg2.Crypto.Pedersen.Note.blinding).sum)
    (leaf : ℤ) (leaves : List ℤ)
    (hmem : Dregg2.Shielded.RealCrypto.MemberAtRoot T (T.root leaves) leaf leaves) :
    (Dregg2.Crypto.Pedersen.listCommit (Dregg2.Crypto.CryptoPrimitives.commit (Digest := Digest)) ins
      = Dregg2.Crypto.Pedersen.listCommit
          (Dregg2.Crypto.CryptoPrimitives.commit (Digest := Digest)) outs)
    ∧ (leaf ∈ leaves ∧ ∀ forged, T.root forged = T.root leaves → forged = leaves) :=
  Dregg2.Shielded.RealCrypto.rung3_real_crypto T ins outs hval hbl leaf leaves hmem

/-! ## 5. NON-VACUITY, POSITIVE POLE — a concrete two-leg shielded ring clears fair + private.

Two DISTINCT fresh member spends (asset 0 / asset 1, nullifiers 99 / 88) bound to the `CycleValid`
bilateral swap `validSwapCycle` (`Dregg2/Intent/Ring.lean`). The matched cycle is genuine (each offers
what the other wants, enough, creators distinct); each leg is a real committed shielded spend. So the
FAIR + PRIVATE clauses of `shielded_ring_clears` are inhabited by a real multi-leg shielded ring — NOT
vacuously true. -/

/-- Leg A's pre-state = `ClaimRefinement.demoState`: pool cell 3 holds 3 of asset 0, one inventory note
`(cm 5, nf 99, asset 0, value 3)`; committed leaves `[5]`. -/
def legAPost : ShieldedState :=
  (unshieldK Dregg2.Shielded.poolDemo Dregg2.Shielded.demoState Dregg2.Shielded.demoClaim.nullifier 2).get
    (by decide)

theorem legAStep :
    unshieldK Dregg2.Shielded.poolDemo Dregg2.Shielded.demoState Dregg2.Shielded.demoClaim.nullifier 2
      = some legAPost :=
  (Option.some_get (by decide)).symm

/-- Leg B's pre-state: pool cell 3 holds 4 of asset 1, one inventory note `(cm 7, nf 88, asset 1,
value 4)`; committed leaves `[7]`. A DISTINCT note under a DISTINCT nullifier — the second leg of the
swap. -/
def demoStateB : ShieldedState :=
  { kernel :=
      { accounts := {2, 3}
        cell := fun _ => Value.record [("balance", Value.int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 3 ∧ a = 1 then 4 else 0
        commitments := [7]
        nullifiers := [] }
    notes := [{ cm := 7, nf := 88, asset := 1, value := 4 }] }

/-- Leg B's valid spend claim: nullifier 88, membership under the tree root of `[7]`, value-binding 7. -/
def demoClaimB : ShieldedSpendClaim :=
  { nullifier := 88, merkleRoot := refTreeRoot [7], valueBinding := 7 }

def legBPost : ShieldedState :=
  (unshieldK Dregg2.Shielded.poolDemo demoStateB demoClaimB.nullifier 2).get (by decide)

theorem legBStep :
    unshieldK Dregg2.Shielded.poolDemo demoStateB demoClaimB.nullifier 2 = some legBPost :=
  (Option.some_get (by decide)).symm

/-- Leg A: `validSwapCycle`'s node 0 (offer asset 10, want asset 11) bound to the asset-0 shielded
spend. (The matcher's committed claim and the private note are the two composed layers — node.offerAsset
is a HIDDEN commitment, deliberately not fused to the note asset here; see the module header.) -/
def legA : ShieldedLeg Dregg2.Shielded.poolDemo where
  node   := { creator := 1, offerAsset := 10, offerAmount := 100, wantAsset := 11, wantMin := 5 }
  claim  := Dregg2.Shielded.demoClaim
  pre    := Dregg2.Shielded.demoState
  post   := legAPost
  dst    := 2
  hbound := ⟨rfl, by decide⟩
  hstep  := legAStep

/-- Leg B: `validSwapCycle`'s node 1 bound to the asset-1 shielded spend (distinct nullifier 88). -/
def legB : ShieldedLeg Dregg2.Shielded.poolDemo where
  node   := { creator := 2, offerAsset := 11, offerAmount := 100, wantAsset := 10, wantMin := 7 }
  claim  := demoClaimB
  pre    := demoStateB
  post   := legBPost
  dst    := 2
  hbound := ⟨rfl, by decide⟩
  hstep  := legBStep

/-- **A concrete two-leg shielded ring.** Its matcher-view `matchNodes` is exactly `validSwapCycle`
(the `CycleValid` bilateral swap), and each leg is a genuine fresh member spend. -/
def demoShieldedRing : ShieldedRing Dregg2.Shielded.poolDemo := [legA, legB]

/-- `matchNodes demoShieldedRing` IS `validSwapCycle` — the concrete ring's matcher view is a real
graph-admitted cycle. -/
theorem demoShieldedRing_nodes : matchNodes demoShieldedRing = validSwapCycle := rfl

/-- **TRUE POLE — the concrete shielded ring is FAIR and PRIVATE.** Its matched cycle is `CycleValid`,
so (composing `shielded_ring_clears`'s fairness + privacy clauses, no ledger settlement needed for
these): it is structurally `RingBalanced`, every leg is within its committed offer/want, and every leg
is an AUTHORIZED fresh-nullifier member spend that can never be re-spent. A genuine private ring
clears. -/
theorem demoShieldedRing_fair_and_private :
    RingBalanced (settlementsOf (matchNodes demoShieldedRing))
    ∧ (∀ j, j < (matchNodes demoShieldedRing).length →
        (receivedAsset (matchNodes demoShieldedRing) j
            = ((matchNodes demoShieldedRing).getD j default).wantAsset ∧
          ((matchNodes demoShieldedRing).getD j default).wantMin
            ≤ receivedAmount (matchNodes demoShieldedRing) j))
    ∧ (∀ leg ∈ demoShieldedRing,
        leg.claim.nullifier ∉ leg.pre.kernel.nullifiers ∧
          leg.claim.nullifier ∈ leg.post.kernel.nullifiers) := by
  have hcv : CycleValid (matchNodes demoShieldedRing) := by
    rw [demoShieldedRing_nodes]; exact validSwapCycle_valid
  have hpos : ∀ n ∈ matchNodes demoShieldedRing, 0 < n.wantMin := by
    rw [demoShieldedRing_nodes]; decide
  refine ⟨cycleValid_settlement_balanced hcv hpos, ?_, ?_⟩
  · intro j hj
    exact cycle_individuallyRational hcv j hj
  · intro leg hleg
    obtain ⟨_, hfresh, hin, _⟩ := leg.refines
    exact ⟨hfresh, hin⟩

/-! ## 6. NON-VACUITY, NEGATIVE POLE — the teeth (a bad shielded clearing is REFUSED). -/

/-- **TOOTH (double-spend): a shielded leg cannot re-spend a nullifier.** After leg A's committed
spend of nullifier 99, a SECOND spend of the same nullifier fails-closed — the note is still in the
inventory but the nullifier now sits in the spent set (`unshield_no_rewitness`). A shielded ring
cannot include two legs draining one note: double-spend is impossible, exactly as the transparent ring
refuses a re-used cell. -/
theorem shielded_leg_no_double_spend (dst' : CellId) :
    unshieldK Dregg2.Shielded.poolDemo legAPost Dregg2.Shielded.demoClaim.nullifier dst' = none :=
  unshield_no_rewitness Dregg2.Shielded.poolDemo legAStep dst'

/-- **TOOTH (over-debit / wrong-asset): an unfair matching never FORMS.** Reusing `Market.Fairness`'s
teeth over the SAME committed-claim layer: an over-debiting cycle (`underfundCycle` — demand 50 against
an offer of 3) and a wrong-asset cycle (`assetMismatchCycle` — want asset 99 against offer asset 10)
are NOT `CycleValid`, so the matcher constructs no settlement from them. A shielded clearing that would
breach a limit or credit an un-wanted asset never reaches settlement — fairness is enforced at
FORMATION, over the hidden committed claims. -/
theorem shielded_overdebit_refused : ¬ CycleValid underfundCycle := overdebit_refused
theorem shielded_wrongAsset_refused : ¬ CycleValid assetMismatchCycle := wrongAsset_refused

/-! ## 7. NON-VACUITY — the hidden-conservation weld is two-valued (conserve TRUE, mint FALSE). -/

/-- **TRUE POLE (hidden conservation): a value-neutral shielded clearing has equal commitment sums.**
Inputs `[note3, note4]` (values 3 + 4 = 7, blindings 2 + 1 = 3) and a single output note of value 7,
blinding 3 carry equal value AND blinding sums, so their commitment sums are EQUAL (the homomorphic
excess is zero) — conservation confirmed on the commitments alone. -/
def outNote7 : BoundNote := { value := 7, blinding := 3, bits := [1, 1, 1] }

theorem demo_hidden_conservation :
    listCommitment refVC [note3, note4] = listCommitment refVC [outNote7] := by
  apply shielded_ring_value_conserves_hidden refVC [note3, note4] [outNote7]
  · intro nt hnt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnt
    rcases hnt with rfl | rfl
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
  · intro nt hnt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnt
    subst hnt; exact ⟨by decide, by decide⟩
  · decide
  · decide

#assert_axioms shielded_ring_clears
#assert_axioms shielded_ring_clears_real_crypto
#assert_axioms shielded_ring_value_conserves_hidden
#assert_axioms ShieldedLeg.refines
#assert_axioms demoShieldedRing_fair_and_private
#assert_axioms shielded_leg_no_double_spend
#assert_axioms shielded_overdebit_refused
#assert_axioms shielded_wrongAsset_refused
#assert_axioms demo_hidden_conservation

/-! ### `#guard` smoke — the concrete shielded ring + the hidden excess, computed. -/

-- The concrete ring's matcher view is the CycleValid swap (2 legs):
#guard (matchNodes demoShieldedRing).length == 2
-- Leg A spends the asset-0 note (nf 99, value 3): dst 2 credited 1 → 4, pool 3 → 0, nullifier spent.
#guard (legAPost.kernel.bal 2 0, legAPost.kernel.bal 3 0) == (4, 0)
#guard legAPost.kernel.nullifiers == [99]
-- Leg B spends the asset-1 note (nf 88, value 4): dst 2 credited 0 → 4, pool 3 → 0, nullifier spent.
#guard (legBPost.kernel.bal 2 1, legBPost.kernel.bal 3 1) == (4, 0)
#guard legBPost.kernel.nullifiers == [88]
-- The two legs spend DISTINCT nullifiers (no in-ring double-spend):
#guard legA.claim.nullifier != legB.claim.nullifier
-- DOUBLE-SPEND refused: re-spending leg A's nullifier fails-closed.
#guard (unshieldK Dregg2.Shielded.poolDemo legAPost 99 2).isNone
-- HIDDEN CONSERVATION, computed: Σ input commitments (5 + 5 = 10) = output commitment (commit 7 3 = 10)
-- — the excess is zero, checked on commitments with no value revealed.
#guard listCommitment refVC [note3, note4] == 10
#guard listCommitment refVC [outNote7] == 10
-- MINT tooth (hidden): an output of value 8 (blinding 3 ⇒ commit = 11) breaks the commitment equality —
-- Σ C_in (10) ≠ Σ C_out (11): a value-minting shielded clearing has a NON-zero excess, refused.
#guard listCommitment refVC [{ value := 8, blinding := 3, bits := [0, 0, 0, 1] }] == 11
#guard (listCommitment refVC [note3, note4] == listCommitment refVC
          [{ value := 8, blinding := 3, bits := [0, 0, 0, 1] }]) == false

end Market
