/-
# Dregg2.Apps.GalleryGated — the art gallery as a VERIFIED USERSPACE APP on the ONE GATED executor.

The legacy `apps/gallery` is a federated art gallery (`apps/gallery/src/artwork.rs`): an artist
**registers** (mints) an artwork — a dregg cell carrying `title`/`artist`/`current_owner`/`image_hash`,
with EXACTLY ONE ownership token (`amount: 1` — the NFT) — and ownership later **transfers** to the
auction winner (`transfer_ownership`). The artwork ID is content-addressed (a BLAKE3 of the creation
params), so a registration is permanent: there is no re-mint over an already-bound artwork id
(`AlreadyRegistered`).

This module re-models that gallery's registry DISCIPLINE through the ONE production turn entry —
`Dregg2.Exec.FullForestAuth.execFullForestG` (the `dregg_exec_full_forest_auth` 4-leg gate:
credential ∧ cap-authority ∧ caveats-discharged ∧ not-revoked) — at the Demo carriers, so the
end-user theorems are about the EXECUTED, credential-gated, caveat-enforcing gallery turn. It is the
LAST of the eight starbridge-apps verified on the gated executor (8/8).

## The real ops (`apps/gallery/src/artwork.rs`)

Each op is a single `SetField` on the artwork cell, modelled as a GATED leaf node
`⟨ mkAuth cred [], .setFieldA actor cell slot value, [] ⟩` run through `execFullForestG`:

  * **mint**         — `SetField item` (binds the artwork id — `register`; the permanent, content-addressed
                       identity → no re-mint, modelling `AlreadyRegistered`);
  * **transfer**     — `SetField owner` (`transfer_ownership` — ownership moves to the auction winner);
  * **set-metadata** — `SetField metadata` (title/description/image-hash edits — free, no caveat).

## The artwork cell's SLOT CAVEATS (the executor-enforced gallery invariants)

The artwork cell carries (`s.kernel.slotCaveats artworkCell`):
  * `WriteOnce item`   — the artwork-id binding, once set (≠0), can never be silently overwritten →
                         **no item-id collision** (the content-addressed identity is permanent; this is
                         exactly `AlreadyRegistered` enforced BY THE EXECUTOR).

`stateStepGuarded` (the `setFieldA` arm of `execFullA`) reads exactly this and FAILS CLOSED on a
violating write — so the gallery invariant is enforced BY THE EXECUTOR, not merely carried.

## End-user theorems (general where possible; concrete `#guard` witnesses for non-vacuity)

  1. `gallery_forged_rejected` — a forged credential ⇒ the whole gated turn rejects (`none`), ∀ pre-state;
  2. `gallery_revoked_rejected` — a revoked credential (nullifier in `s.kernel.revoked`) ⇒ `none`, ∀ op;
  3. `gallery_item_immutable`  — re-minting over an already-bound `item` slot ⇒ `none` (`WriteOnce`);
  4. `gallery_conserves`       — a committed gallery turn moves NO asset's supply (per-asset Δ = 0).

Plus a concrete artwork-cell state (`gal0`/`galFresh`/`galRevoked`) whose `#guard`s show a GOOD mint
over a FRESH item COMMITS, a re-mint over a bound item ⇒ `none`, a forged credential ⇒ `none`, a
revoked credential ⇒ `none`, and a transfer COMMITS (the gate + the caveat are REAL, not vacuous).

Does NOT touch `FullForestAuth.lean` nor `Dregg2.lean`.
Reuses ONLY the proved gated-executor keystones + the proved `stateStepGuarded` fail-closed teeth.
-/
import Dregg2.Exec.GatedForestCfg

namespace Dregg2.Apps.GalleryGated

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.StarbridgeGated

/-! ## §1 — The gallery DOMAIN at the Demo carriers (artworks, owners, the artwork cell, the slots). -/

/-- The artwork cell holding one artwork's on-chain identity (the gallery's `artwork cell`). We use cell
`0` so the actor can be `0` too — `stateAuthB` is then trivially satisfied (`actor == src`), letting the
credential-gate and the SLOT CAVEAT be the load-bearing admission conditions (not the cap-list). -/
abbrev artworkCell : CellId := 0

/-- The gallery actor (the artist key registering/transferring the artwork). Equal to `artworkCell` so
`stateAuthB` holds by `actor == src` — the app's authority story rides on the §8 CREDENTIAL gate. -/
abbrev galleryActor : CellId := 0

/-- The `item` slot (the content-addressed artwork id) — `WriteOnce`: once an artwork is minted its
identity is permanent (no re-mint over it → no item-id collision; this is `AlreadyRegistered`). -/
abbrev itemSlot : FieldName := "item"
/-- The `owner` slot (`current_owner`) — transfer rewrites this (no caveat: ownership moves to the winner). -/
abbrev ownerSlot : FieldName := "owner"
/-- The `metadata` slot (title/description/image-hash) — no caveat: gallery metadata is free to update. -/
abbrev metadataSlot : FieldName := "metadata"

/-- The artwork cell's factory-installed SLOT CAVEATS — exactly the gallery program: `WriteOnce { item }`
(the permanent, content-addressed artwork identity). The executor reads this on EVERY `SetField` to the
artwork cell (`stateStepGuarded`). -/
def galleryCaveats : List SlotCaveat :=
  [ .writeOnce itemSlot ]

/-! ## §2 — Each op as a GATED LEAF NODE through the production turn entry `execFullForestG`.

A gallery op is a single `SetField` on the artwork cell, decorated with a credential (the WHO) and run
through the 4-leg gate. `mkAuth cred []` (from `FullForestAuth.Demo`) supplies an admitting cap-mode
(`.unchecked (Guard.all [])`), an empty within-cell caveat list (so the GATE's caveat leg is vacuously
discharged — the SLOT caveats are enforced separately by `stateStepGuarded` inside `execFullA`), no
chain, and a non-revoked nullifier. So `gateOK` reduces to the CREDENTIAL leg (and the revocation leg
once a nullifier is committed to `s.kernel.revoked`). -/

/-- A gated gallery node: credential `cred`, a `SetField slot value` on the artwork cell, no children.
The production-entry shape `⟨ mkAuth cred [], action, [] ⟩`. -/
def galNode (cred : Authorization Dg Pf) (slot : FieldName) (value : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA galleryActor artworkCell slot value, [] ⟩

/-- **mint** — bind the artwork id (the load-bearing `SetField item`; dregg1 `register_artwork`). A
genuine credential ⇒ the gate passes; the `WriteOnce item` slot caveat then permits the FIRST write
(`old = 0`) and forbids any later overwrite (`AlreadyRegistered` BY THE EXECUTOR). -/
def mintNode (cred : Authorization Dg Pf) (itemVal : Int) : DForest :=
  galNode cred itemSlot itemVal
/-- **transfer** — change ownership (`SetField owner`; dregg1 `transfer_ownership`). No slot caveat ⇒
ownership is freely moved to the auction winner (authority/credential alone gate it). -/
def transferNode (cred : Authorization Dg Pf) (newOwner : Int) : DForest :=
  galNode cred ownerSlot newOwner
/-- **set-metadata** — update title/description/image-hash (`SetField metadata`). No caveat ⇒ free. -/
def setMetadataNode (cred : Authorization Dg Pf) (newMeta : Int) : DForest :=
  galNode cred metadataSlot newMeta

/-! ## §3 — The leaf-collapse bridge: a childless gated forest runs EXACTLY its single gated node. -/

/-- **`execFullForestG_leaf` (the load-bearing collapse).** A gated forest with NO children
runs EXACTLY its root gated node step: `execFullForestG s ⟨na, a, []⟩ = execFullAGated s na a`. (Both
branches of `execFullForestG`'s match collapse because `execFullChildrenG _ s' [] = some s'`.) This is
the bridge through which every gallery op's `none`/`some` is read off `execFullAGated` directly. -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

/-- **`execFullForestG_galNode` — the gallery-op collapse.** A childless gallery op runs
`if gateOK then execFullA (.setFieldA …) else none`, and `execFullA (.setFieldA …) = stateStepGuarded`.
The unfolding every theorem below rests on. -/
theorem execFullForestG_galNode (s : RecChainedState) (cred : Authorization Dg Pf)
    (slot : FieldName) (value : Int) :
    execFullForestG s (galNode cred slot value)
      = (if gateOK (mkAuth cred []) s = true
         then stateStepDev s slot galleryActor artworkCell value
         else none) := by
  rw [galNode, execFullForestG_leaf, execFullAGated]
  rfl

/-! ## §4 — The CREDENTIAL gate: `goodCred` admits, `forgedCred` (and any forged cred) fail-closed.

`gateOK (mkAuth cred []) s = credentialValidG (mkAuth cred []) && capAuthorityG (mkAuth cred []) &&
caveatsDischarged (mkAuth cred []) s && revocationGate (mkAuth cred []) s`. For `mkAuth`: the cap mode
is `.unchecked (Guard.all [])` (admits), the within-cell caveat list is `[]` (vacuously discharged, no
chain), the nullifier is `0` (not in `gal0.kernel.revoked = []`). So `gateOK` on a non-revoking state is
exactly the credential leg `credentialValidG (mkAuth cred [])` — `portalVerify cred`. -/

/-- The forged credential's gate leg is FALSE (`portalVerify (.signature 7 8) = decide (7 = 8) = false`)
— independent of state, so the whole gate `gateOK (mkAuth forgedCred []) s = false`. -/
theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK
  rw [hcred]
  simp

/-! ## §5 — END-USER THEOREM 1: a FORGED credential ⇒ the whole gated turn REJECTS. -/

/-- **`gallery_forged_rejected` (END-USER THEOREM 1).** A gallery op (any slot/value) presented
with a FORGED credential is rejected by the production turn entry: `execFullForestG s (galNode forgedCred
…) = none`, for EVERY pre-state `s`. The §8 credential leg fail-closes ⇒ the whole forest rolls back —
nobody can mint/transfer/edit a gallery artwork without a genuine credential. -/
theorem gallery_forged_rejected (s : RecChainedState) (slot : FieldName) (value : Int) :
    execFullForestG s (galNode forgedCred slot value) = none := by
  rw [galNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.setFieldA galleryActor artworkCell slot value) [] (gateOK_forged_false s)

/-- Specialization to `mintNode` (the headline shape `mintNode forgedCred …`). -/
theorem gallery_forged_mint_rejected (s : RecChainedState) (itemVal : Int) :
    execFullForestG s (mintNode forgedCred itemVal) = none :=
  gallery_forged_rejected s itemSlot itemVal

/-! ## §6 — END-USER THEOREM 2: a REVOKED credential ⇒ the whole gated turn REJECTS.

The gate's REVOCATION leg reads the COMMITTED revocation registry `s.kernel.revoked` (the MDB root,
adversary-uncontrollable). If the node's nullifier `na.credNul` sits there, `gateOK = false` and the
whole forest rolls back — single-machine ⇒ immediate revocation. -/

/-- **`gallery_revoked_rejected` (END-USER THEOREM 2).** A gallery op whose credential nullifier
is in the committed revocation registry (`s.kernel.revoked.contains (mkAuth cred []).credNul = true`) is
rejected: `execFullForestG s (galNode cred slot value) = none`, for EVERY pre-state and ANY op. A revoked
artist (or stolen key) can mint/transfer NOTHING, no matter how valid the signature. -/
theorem gallery_revoked_rejected (s : RecChainedState) (cred : Authorization Dg Pf)
    (slot : FieldName) (value : Int)
    (hrev : s.kernel.revoked.contains (mkAuth cred []).credNul = true) :
    execFullForestG s (galNode cred slot value) = none := by
  rw [galNode]
  exact execFullForestG_unauthorized_fails s (mkAuth cred [])
    (.setFieldA galleryActor artworkCell slot value) [] (gateOK_revoked_fails (mkAuth cred []) s hrev)

/-! ## §7 — END-USER THEOREM 3: the `item` WriteOnce caveat bites (gate passes for `goodCred`, write fails).

The COMPOSITION: the gate passes (genuine credential, admitting cap, discharged caveats, not revoked) so
`execFullForestG s (galNode goodCred …) = stateStepGuarded …`; then the `WriteOnce item` slot caveat on
a contested (already-bound) slot makes `caveatsAdmit = false`, so `stateStepGuarded = none`
(`stateStepGuarded_caveat_violation_fails`). The whole turn rejects — enforced BY THE EXECUTOR. -/

/-- **`gallery_good_node_runs_write` — the gate-passing collapse for `goodCred`.** When the genuine
credential admits, the gallery op IS its caveat-gated `SetField` — `execFullForestG s (galNode goodCred
slot value) = stateStepDev s slot galleryActor artworkCell value`. The hinge for theorem 3: any
later caveat-rejection of the WRITE rejects the whole turn. -/
theorem gallery_good_node_runs_write (s : RecChainedState) (slot : FieldName) (value : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true) :
    execFullForestG s (galNode goodCred slot value)
      = stateStepDev s slot galleryActor artworkCell value := by
  rw [execFullForestG_galNode, if_pos hgate]

/-- **`gallery_item_immutable` (END-USER THEOREM 3).** If the artwork's `item` slot already
holds a DIFFERENT non-zero binding (the artwork id is taken: `WriteOnce`, `old ≠ 0`, `value ≠ old`),
then a re-mint over it is rejected by the executor — `execFullForestG s (mintNode goodCred value) = none`
— EVEN with a genuine credential. No one can re-mint over a registered artwork id (`AlreadyRegistered`).
NON-VACUOUS: the hypothesis `caveatsAdmit … = false` is forced by the `WriteOnce item` caveat. -/
theorem gallery_item_immutable (s : RecChainedState) (value : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hbound : caveatsAdmit s.kernel itemSlot galleryActor artworkCell value = false) :
    execFullForestG s (mintNode goodCred value) = none := by
  rw [mintNode, gallery_good_node_runs_write s itemSlot value hgate]
  exact stateStepDev_caveat_violation_fails s itemSlot galleryActor artworkCell value hbound

/-! ## §8 — END-USER THEOREM 4: a committed gallery turn CONSERVES every asset.

A gallery op is a single `SetField`, which has `ledgerDeltaAsset = 0` for EVERY asset — so its per-asset
turn delta is `0`, and `execFullForestG_conserves_per_asset` gives supply-preservation for free. The
credential/caveat gate is balance-orthogonal: passing the gate does not move money, and failing it
commits nothing. (The legacy gallery mints an NFT-style 1-token alongside, but the metadata-cell write
modelled here is balance-neutral; the conserved quantity is the per-asset supply.) -/

/-- The per-asset turn delta of any gallery op is `0` (a `SetField` is balance-neutral) — for EVERY
asset `b`. The conservation hypothesis, discharged once and reused for every op. -/
theorem galNode_delta_zero (cred : Authorization Dg Pf) (slot : FieldName) (value : Int) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (galNode cred slot value)).map Prod.snd) b = 0 := by
  simp [galNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- **`gallery_conserves` (END-USER THEOREM 4).** A COMMITTED gallery turn preserves EVERY
asset's total supply: `recTotalAsset s'.kernel b = recTotalAsset s.kernel b`, for
every asset `b`. The artwork write touches metadata, never balance — so a mint/transfer/edit moves no
money. A one-liner off `execFullForestG_conserves_per_asset` with the `SetField`-is-balance-neutral
hypothesis discharged by `galNode_delta_zero`. Holds for EVERY op (same shape). -/
theorem gallery_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf)
    (slot : FieldName) (value : Int) (b : AssetId)
    (h : execFullForestG s (galNode cred slot value) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  execFullForestG_conserves_per_asset s s' (galNode cred slot value) b h
    (galNode_delta_zero cred slot value b)

/-- The conservation theorem specialized to `mint` (the headline op). -/
theorem gallery_mint_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (itemVal : Int)
    (b : AssetId) (h : execFullForestG s (mintNode cred itemVal) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  gallery_conserves s s' cred itemSlot itemVal b h

/-! ## §9 — NON-VACUITY: a concrete artwork-cell state with the real slot caveat + `#guard` witnesses.

`gal0` is the artwork cell `0`, born with the `WriteOnce item` caveat and a BOUND artwork id
(`item = 42`, owner `7`, metadata `0`). Actor `0 == artworkCell`, so `stateAuthB` holds; the cell is
Live (default lifecycle `0`); accounts `{0, 1}`; the revocation registry is empty. On `gal0` we exhibit:
(i) a GOOD mint over a FRESH item COMMITS; (ii) a forged credential ⇒ `none`; (iii) a re-mint over the
bound item ⇒ `none`; (iv) a transfer (no caveat) COMMITS; (v) a REVOKED credential ⇒ `none`; (vi) the
committed mint CONSERVES both assets — so every theorem above is witnessed REAL, not vacuous. -/

/-- An artwork-cell pre-state: cell `0` carries the `WriteOnce item` caveat; the `item` slot is ALREADY
bound to `42` (registered), owner `7`, metadata `0`. -/
def gal0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then
                  .record [("balance", .int 0), (itemSlot, .int 42), (ownerSlot, .int 7),
                           (metadataSlot, .int 0)]
                else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        slotCaveats := fun c => if c = 0 then galleryCaveats else [] }
    log := [] }

/-- An artwork-cell pre-state whose `item` slot is FRESH (`item = 0`) — a GOOD mint here COMMITS (the
`WriteOnce item` caveat permits the first write). Everything else as `gal0`. -/
def galFresh : RecChainedState :=
  { gal0 with kernel := { gal0.kernel with
      cell := fun c => if c = 0 then
                .record [("balance", .int 0), (itemSlot, .int 0), (ownerSlot, .int 0),
                         (metadataSlot, .int 0)]
              else .record [("balance", .int 0)] } }

/-- An artwork-cell pre-state whose committed revocation registry holds the demo nullifier (`0`, the
`mkAuth` default `credNul`) — a genuine credential is REVOKED here, so EVERY op fail-closes. -/
def galRevoked : RecChainedState :=
  { gal0 with kernel := { gal0.kernel with revoked := [0] } }

-- The gate passes for the genuine credential on the non-revoking states (the credential leg is live):
#guard (gateOK (mkAuth goodCred []) gal0)        --  true  (genuine credential admits)
#guard (gateOK (mkAuth goodCred []) galFresh)    --  true
#guard (gateOK (mkAuth forgedCred []) gal0) == false  --  false (forged ⇒ fail-closed)
-- ...and FAILS for the genuine credential once its nullifier is in the committed revocation registry:
#guard (gateOK (mkAuth goodCred []) galRevoked) == false  --  false (revoked ⇒ fail-closed)

-- (i) a GOOD mint over a FRESH item slot COMMITS (the WriteOnce caveat permits the genesis write):
#guard ((execFullForestG galFresh (mintNode goodCred 42)).isSome)  --  true (minted!)
-- ...and the committed item slot reads back `42`:
#guard ((execFullForestG galFresh (mintNode goodCred 42)).map
        (fun s => fieldOf itemSlot (s.kernel.cell 0))) == some 42  --  some 42

-- (ii) a FORGED credential ⇒ none (credential gate fail-closes), even on the fresh state:
#guard ((execFullForestG galFresh (mintNode forgedCred 42)).isSome) == false  --  false

-- (iii) ITEM IMMUTABLE: minting a DIFFERENT value over the bound `item = 42` slot ⇒ none
--       (WriteOnce: old = 42 ≠ 0 and new = 99 ≠ 42 ⇒ caveatsAdmit = false):
#guard (caveatsAdmit gal0.kernel itemSlot galleryActor artworkCell 99) == false  --  false (taken)
#guard ((execFullForestG gal0 (mintNode goodCred 99)).isSome) == false  --  false (re-mint rejected)
-- ...rewriting the SAME value (42) is a WriteOnce no-op and is admitted (the binding is idempotent):
#guard (caveatsAdmit gal0.kernel itemSlot galleryActor artworkCell 42)  --  true (no-op rewrite)

-- (iv) a TRANSFER (no slot caveat on `owner`) COMMITS with a genuine credential:
#guard ((execFullForestG gal0 (transferNode goodCred 8)).isSome)  --  true (ownership moved)
-- ...and the committed owner slot reads back `8`:
#guard ((execFullForestG gal0 (transferNode goodCred 8)).map
        (fun s => fieldOf ownerSlot (s.kernel.cell 0))) == some 8  --  some 8
-- (v) set-metadata (no caveat) COMMITS:
#guard ((execFullForestG gal0 (setMetadataNode goodCred 5)).isSome)  --  true (metadata set)

-- (vi) REVOKED credential ⇒ none through the FULL gated turn (any op), even with a genuine signature:
#guard ((execFullForestG galRevoked (mintNode goodCred 7)).isSome) == false  --  false (revoked artist)
#guard ((execFullForestG galRevoked (transferNode goodCred 8)).isSome) == false  --  false (revoked)

-- (vii) CONSERVATION: a committed mint moves NO asset's supply (per-asset Δ = 0):
#guard ((execFullForestG galFresh (mintNode goodCred 42)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (unchanged)
-- ...and so does a committed transfer:
#guard ((execFullForestG gal0 (transferNode goodCred 8)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7) (unchanged)

/-! ## §10 — Axiom-hygiene tripwires (the honesty pins). Every keystone depends ONLY on the three
standard kernel axioms `{propext, Classical.choice, Quot.sound}`. (The portal soundness
is a Prop carrier in `FullForestAuth`, never an axiom, so it does not appear.) -/

#assert_axioms execFullForestG_leaf
#assert_axioms execFullForestG_galNode
#assert_axioms gateOK_forged_false
#assert_axioms gallery_forged_rejected
#assert_axioms gallery_revoked_rejected
#assert_axioms gallery_good_node_runs_write
#assert_axioms gallery_item_immutable
#assert_axioms gallery_conserves
#assert_axioms gallery_mint_conserves

end Dregg2.Apps.GalleryGated
