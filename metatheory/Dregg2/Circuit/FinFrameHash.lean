/-
# Dregg2.Circuit.FinFrameHash — DEBT-B lane R2: the canonical frame hash of the finite kernel
state + the injectivity theorem that discharges the "unrealizable" `RestHashIffFrame`.

Lane R1 (`FinKernelState.lean`) made the kernel model FINITE (sorted-nodup maps) and proved the
load-bearing `denote_injective` (UNCONDITIONAL). This lane builds the CANONICAL SERIALIZATION of a
`FinKernelState` into `List ℤ`, proves it INJECTIVE, and hashes it through the Poseidon2 sponge:

  * `serializeFin : FinKernelState → List ℤ` — one canonical `Encodable`-code per field (position is
    the domain-separation tag; the 16-field list is fixed-length, so concatenation is injective).
    `serializeFin_injective` — PROVED (each field code is an injective serialization: `Encodable.encode`
    of the field's sorted-canonical entries; the `cell` field routes its `Value`s through the proved
    injective `encV`; equal codes ⇒ equal entries ⇒ equal maps by R1's `CanonMap.ext`/`SortedMap.ext`).
  * `frameHashFin sponge f := sponge (serializeFin f)`.
  * `restHashIffFrame_fin` — the HEADLINE: `frameHashFin sponge f = frameHashFin sponge f' → f = f'`,
    RESIDUAL `Poseidon2SpongeCR sponge` ALONE (equal hashes ⇒[CR] equal serializations ⇒[injectivity]
    equal `FinKernelState`). NO new carrier.
  * `RH_fin` + `restHashIffFrame_of_fin` — THE DISCHARGE-LIFT to the actual carrier
    `StateCommit.RestHashIffFrame`. `RestHashIffFrame` binds the NON-`cell` components, and is stated
    over ALL `RecordKernelState` (including non-reachable, infinite-support ones — the unrealizable
    part). We define `RH_fin sponge` via the finite representative (`serializeRestFin`, the non-`cell`
    fields) and prove the `RestHashIffFrame`-shaped binding EXACTLY ON THE DENOTE IMAGE (the reachable
    subclass — which is all the apex ever sees, since every real state is `denote` of a finite one).
    We do NOT claim it for non-finite-support states. `image_of_full` records that the full carrier
    would imply the image version, and the `RestHashIffFrame`-body drift tripwire (`rest_body_matches`)
    keeps this welded to `StateCommit.RestHashIffFrame`.

NO carrier laundering: `serializeFin_injective`, `restHashIffFrame_fin`, `restHashIffFrame_of_fin` are
THEOREMS; the SOLE crypto residual is `Poseidon2SpongeCR` (the existing floor). The value-type
serializers are honest `Encodable` encoders (a canonical serialization is provably injective — the
same stance as `Poseidon2Binding`'s `LeafRealization.encodeLeaf_inj`), NEVER a `def …Sound`.
-/
import Dregg2.Circuit.FinKernelState
import Dregg2.Circuit.Poseidon2Binding
import Mathlib.Tactic.DeriveEncodable

namespace Dregg2.Circuit.FinFrameHash

open Dregg2.Exec Dregg2.Authority
open Dregg2.Circuit.FinKernelState
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Poseidon2Binding.Reference (encV encV_injective)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — `Encodable` for the value types (honest canonical serializers, not crypto).

`Char`/`String` inject via `Char.toNat`/`String.toList` (the same injective-serialization stance as
`Poseidon2Binding.Reference.strCode`); the flat/finite value inductives derive `Encodable`. `Value`
is NOT `Encodable` (nested through `List (FieldName × Value)`), so `cell`'s `Value`s route through the
proved-injective `encV` instead. These are provably-injective encoders — the STRUCTURAL content, never
a cryptographic assumption. -/

/-- `Char` injects to `ℕ` via its codepoint. -/
instance instEncChar : Encodable Char :=
  Encodable.ofLeftInjection Char.toNat (fun n => some (Char.ofNat n))
    (fun c => by simp [Char.ofNat_toNat])

/-- `String` injects to `List Char`. -/
instance instEncString : Encodable String :=
  Encodable.ofLeftInjection String.toList (fun l => some (String.ofList l))
    (fun s => by simp [String.ofList_toList])

deriving instance Encodable for Dregg2.Authority.Auth
deriving instance Encodable for Dregg2.Authority.ClearanceGraph.Label
deriving instance Encodable for Dregg2.Authority.ClearanceGraph.Graph
deriving instance Encodable for Dregg2.Authority.Cap
deriving instance Encodable for Dregg2.Exec.SlotCaveat
deriving instance Encodable for Dregg2.Exec.FactoryEntry

/-! ## §1 — `zcode`: the per-field canonical ℤ code (`Encodable.encode`, then cast). Injective. -/

/-- `zcode a` — the canonical ℤ serialization code of an `Encodable` value (`encode` into `ℕ`, cast to
`ℤ`). Injective (`Encodable.encode` is injective; `ℕ ↪ ℤ`). -/
def zcode {α : Type} [Encodable α] (a : α) : ℤ := (Encodable.encode a : ℤ)

theorem zcode_inj {α : Type} [Encodable α] {a b : α} (h : zcode a = zcode b) : a = b := by
  unfold zcode at h
  exact Encodable.encode_injective (by exact_mod_cast h)

/-! ## §2 — the `SortedMap`/`CanonMap` entries-equality bridges (from proof irrelevance). -/

/-- Two `SortedMap`s with equal entries lists are equal (the sortedness proof is irrelevant). -/
theorem SortedMap.eq_of_entries {K V : Type} [LinearOrder K] {a b : SortedMap K V}
    (h : a.entries = b.entries) : a = b := by
  obtain ⟨ea, sa⟩ := a; obtain ⟨eb, sb⟩ := b; cases h; rfl

/-- Two `CanonMap`s with equal entries lists are equal (sortedness + canonicity proofs irrelevant). -/
theorem CanonMap.eq_of_entries {K V : Type} [LinearOrder K] {d : V} {a b : CanonMap K V d}
    (h : a.toMap.entries = b.toMap.entries) : a = b := by
  obtain ⟨⟨ea, sa⟩, ca⟩ := a; obtain ⟨⟨eb, sb⟩, cb⟩ := b
  simp only at h; cases h; rfl

/-! ## §3 — the per-field codes.

`cell`'s `Value`s route through the injective `encV : Value → ℕ`; all other fields' entry lists are
directly `Encodable`. Each code is `zcode` of the field's sorted-canonical entries (already canonical
by R1's `SortedMap` invariant), so no canonicalization step is needed. -/

/-- The `cell` field's canonical data: entries with each `Value` replaced by its injective `encV`. -/
def cellData (f : FinKernelState) : List (CellId × ℕ) :=
  f.cell.toMap.entries.map (fun p => (p.1, encV p.2))

/-- The `bal` field's canonical data: entries with the lexicographic key flattened via `ofLex`. -/
def balData (f : FinKernelState) : List ((CellId × AssetId) × ℤ) :=
  f.bal.toMap.entries.map (fun p => (ofLex p.1, p.2))

/-- **`serializeRestFin f`** — the canonical serialization of the 15 NON-`cell` fields (the "rest").
The finite representative `RestHashIffFrame` binds. -/
def serializeRestFin (f : FinKernelState) : List ℤ :=
  [ zcode f.accounts
  , zcode f.caps.toMap.entries
  , zcode f.nullifiers
  , zcode f.revoked
  , zcode f.commitments
  , zcode (balData f)
  , zcode f.slotCaveats.toMap.entries
  , zcode f.factories
  , zcode f.lifecycle.toMap.entries
  , zcode f.deathCert.toMap.entries
  , zcode f.delegate.entries
  , zcode f.delegations.toMap.entries
  , zcode f.delegationEpoch.toMap.entries
  , zcode f.delegationEpochAt.toMap.entries
  , zcode f.heaps.toMap.entries ]

/-- **`serializeFin f`** — the canonical serialization of the WHOLE finite kernel state: the `cell`
code, then the 15 non-`cell` codes. Fixed-length (16 entries), so position is the field tag and
concatenation is injective. -/
def serializeFin (f : FinKernelState) : List ℤ :=
  zcode (cellData f) :: serializeRestFin f

/-! ## §4 — `serializeFin_injective` (the whole-state injectivity). -/

/-- `cellData` is injective (`encV` injective ⇒ the per-entry map is injective ⇒ `List.map` injective;
then `CanonMap.eq_of_entries`). -/
theorem cell_eq_of_cellData {f f' : FinKernelState} (h : cellData f = cellData f') :
    f.cell = f'.cell := by
  unfold cellData at h
  have hg : Function.Injective (fun p : CellId × Value => (p.1, encV p.2)) := by
    rintro ⟨c, v⟩ ⟨c', v'⟩ he
    simp only [Prod.mk.injEq] at he
    exact Prod.ext he.1 (encV_injective he.2)
  have := List.map_injective_iff.mpr hg h
  exact CanonMap.eq_of_entries this

/-- `balData` is injective (`ofLex` injective on the key ⇒ the per-entry map is injective). -/
theorem bal_eq_of_balData {f f' : FinKernelState} (h : balData f = balData f') :
    f.bal = f'.bal := by
  unfold balData at h
  have hg : Function.Injective (fun p : BalKey × ℤ => (ofLex p.1, p.2)) := by
    rintro ⟨k, z⟩ ⟨k', z'⟩ he
    simp only [Prod.mk.injEq] at he
    exact Prod.ext (ofLex_inj.mp he.1) he.2
  have := List.map_injective_iff.mpr hg h
  exact CanonMap.eq_of_entries this

/-- **`restAgree_of_serializeRestFin`** — equal rest serializations force all 15 non-`cell` fields
equal. Each field code is `zcode` of an injective serialization. -/
theorem restAgree_of_serializeRestFin {f f' : FinKernelState}
    (h : serializeRestFin f = serializeRestFin f') :
    f.accounts = f'.accounts ∧ f.caps = f'.caps ∧ f.nullifiers = f'.nullifiers
      ∧ f.revoked = f'.revoked ∧ f.commitments = f'.commitments ∧ f.bal = f'.bal
      ∧ f.slotCaveats = f'.slotCaveats ∧ f.factories = f'.factories ∧ f.lifecycle = f'.lifecycle
      ∧ f.deathCert = f'.deathCert ∧ f.delegate = f'.delegate ∧ f.delegations = f'.delegations
      ∧ f.delegationEpoch = f'.delegationEpoch ∧ f.delegationEpochAt = f'.delegationEpochAt
      ∧ f.heaps = f'.heaps := by
  simp only [serializeRestFin, List.cons.injEq, and_true] at h
  obtain ⟨hAcc, hCaps, hNul, hRev, hCom, hBal, hSlot, hFac, hLife, hDeath, hDel, hDels, hEp, hEpat,
    hHeaps⟩ := h
  refine ⟨zcode_inj hAcc, ?_, zcode_inj hNul, zcode_inj hRev, zcode_inj hCom, ?_, ?_, zcode_inj hFac,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact CanonMap.eq_of_entries (zcode_inj hCaps)
  · exact bal_eq_of_balData (zcode_inj hBal)
  · exact CanonMap.eq_of_entries (zcode_inj hSlot)
  · exact CanonMap.eq_of_entries (zcode_inj hLife)
  · exact CanonMap.eq_of_entries (zcode_inj hDeath)
  · exact SortedMap.eq_of_entries (zcode_inj hDel)
  · exact CanonMap.eq_of_entries (zcode_inj hDels)
  · exact CanonMap.eq_of_entries (zcode_inj hEp)
  · exact CanonMap.eq_of_entries (zcode_inj hEpat)
  · exact CanonMap.eq_of_entries (zcode_inj hHeaps)

/-- **`serializeFin_injective` — PROVED.** Equal whole-state serializations force equal
`FinKernelState`s: the `cell` code fixes `cell` (`cell_eq_of_cellData`), the 15 rest codes fix the
rest (`restAgree_of_serializeRestFin`), then `FinKernelState.ext`. -/
theorem serializeFin_injective {f f' : FinKernelState} (h : serializeFin f = serializeFin f') :
    f = f' := by
  simp only [serializeFin, List.cons.injEq] at h
  obtain ⟨hcell, hrest⟩ := h
  have hc : f.cell = f'.cell := cell_eq_of_cellData (zcode_inj hcell)
  obtain ⟨hAcc, hCaps, hNul, hRev, hCom, hBal, hSlot, hFac, hLife, hDeath, hDel, hDels, hEp, hEpat,
    hHeaps⟩ := restAgree_of_serializeRestFin hrest
  ext1 <;>
    first
      | exact hAcc | exact hc | exact hCaps | exact hNul | exact hRev | exact hCom | exact hBal
      | exact hSlot | exact hFac | exact hLife | exact hDeath | exact hDel | exact hDels
      | exact hEp | exact hEpat | exact hHeaps

/-! ## §5 — `frameHashFin` + the HEADLINE `restHashIffFrame_fin` (residual `Poseidon2SpongeCR`). -/

/-- **`frameHashFin sponge f`** — the Poseidon2 frame hash of the finite kernel state: the sponge of
its canonical serialization. -/
def frameHashFin (sponge : List ℤ → ℤ) (f : FinKernelState) : ℤ := sponge (serializeFin f)

/-- **`restHashIffFrame_fin` — THE HEADLINE.** The frame hash binds the WHOLE finite kernel state:
`frameHashFin sponge f = frameHashFin sponge f' → f = f'`. RESIDUAL `Poseidon2SpongeCR sponge` ALONE —
equal hashes ⇒[CR] equal serializations ⇒[`serializeFin_injective`] equal state. NO new carrier. -/
theorem restHashIffFrame_fin (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    {f f' : FinKernelState} (h : frameHashFin sponge f = frameHashFin sponge f') : f = f' :=
  serializeFin_injective (hCR _ _ h)

/-! ## §6 — THE DISCHARGE-LIFT to `StateCommit.RestHashIffFrame` (on the denote image). -/

/-- **`RH_fin sponge k`** — the rest-hash on `RecordKernelState`, defined via the finite representative:
for a `denote` image, the sponge of its (unique, by `denote_injective`) preimage's non-`cell`
serialization; off the image, `0`. This is the carrier that discharges `RestHashIffFrame` on the
reachable subclass. -/
noncomputable def RH_fin (sponge : List ℤ → ℤ) (k : RecordKernelState) : ℤ :=
  open Classical in
  if h : ∃ f : FinKernelState, denote f = k then sponge (serializeRestFin (Classical.choose h)) else 0

/-- On the `denote` image `RH_fin` computes the sponge of the preimage's rest serialization (the
preimage is unique by `denote_injective`). -/
theorem RH_fin_denote (sponge : List ℤ → ℤ) (f : FinKernelState) :
    RH_fin sponge (denote f) = sponge (serializeRestFin f) := by
  have hex : ∃ g : FinKernelState, denote g = denote f := ⟨f, rfl⟩
  unfold RH_fin
  rw [dif_pos hex]
  have : Classical.choose hex = f := denote_injective (Classical.choose_spec hex)
  rw [this]

/-- The `denote`-projection ↔ raw-field correspondence for the 15 non-`cell` fields: two `denote`
images agree on every non-`cell` component (the `RestHashIffFrame` body, roots included) iff their
finite preimages agree on all 15 non-`cell` fields. The two accumulator-root clauses are vacuous on
the image (`denote` leaves them at the empty-tree default). -/
theorem restBody_iff_restAgree (f f' : FinKernelState) :
    ((denote f').accounts = (denote f).accounts ∧ (denote f').caps = (denote f).caps
        ∧ (denote f').bal = (denote f).bal
        ∧ (denote f').nullifiers = (denote f).nullifiers ∧ (denote f').revoked = (denote f).revoked
        ∧ (denote f').commitments = (denote f).commitments
        ∧ (denote f').slotCaveats = (denote f).slotCaveats
        ∧ (denote f').factories = (denote f).factories ∧ (denote f').lifecycle = (denote f).lifecycle
        ∧ (denote f').deathCert = (denote f).deathCert ∧ (denote f').delegate = (denote f).delegate
        ∧ (denote f').delegations = (denote f).delegations
        ∧ (denote f').delegationEpoch = (denote f).delegationEpoch
        ∧ (denote f').delegationEpochAt = (denote f).delegationEpochAt
        ∧ (denote f').heaps = (denote f).heaps
        ∧ (denote f').nullifierRoot = (denote f).nullifierRoot
        ∧ (denote f').revokedRoot = (denote f).revokedRoot)
      ↔ (f'.accounts = f.accounts ∧ f'.caps = f.caps ∧ f'.nullifiers = f.nullifiers
          ∧ f'.revoked = f.revoked ∧ f'.commitments = f.commitments ∧ f'.bal = f.bal
          ∧ f'.slotCaveats = f.slotCaveats ∧ f'.factories = f.factories ∧ f'.lifecycle = f.lifecycle
          ∧ f'.deathCert = f.deathCert ∧ f'.delegate = f.delegate ∧ f'.delegations = f.delegations
          ∧ f'.delegationEpoch = f.delegationEpoch ∧ f'.delegationEpochAt = f.delegationEpochAt
          ∧ f'.heaps = f.heaps) := by
  constructor
  · rintro ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hSlot, hFac, hLife, hDeath, hDel, hDels, hEp, hEpat,
      hHeaps, _, _⟩
    refine ⟨hAcc, ?_, hNul, hRev, hCom, ?_, ?_, hFac, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact CanonMap.ext (fun l => congrFun hCaps l)
    · exact CanonMap.ext (fun key => by obtain ⟨c, a⟩ := key; exact congrFun (congrFun hBal c) a)
    · exact CanonMap.ext (fun c => congrFun hSlot c)
    · exact CanonMap.ext (fun c => congrFun hLife c)
    · exact CanonMap.ext (fun c => congrFun hDeath c)
    · exact SortedMap.ext (fun c => congrFun hDel c)
    · exact CanonMap.ext (fun c => congrFun hDels c)
    · exact CanonMap.ext (fun c => congrFun hEp c)
    · exact CanonMap.ext (fun c => congrFun hEpat c)
    · exact CanonMap.ext (fun c => congrFun hHeaps c)
  · rintro ⟨hAcc, hCaps, hNul, hRev, hCom, hBal, hSlot, hFac, hLife, hDeath, hDel, hDels, hEp, hEpat,
      hHeaps⟩
    refine ⟨hAcc, ?_, ?_, hNul, hRev, hCom, ?_, hFac, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
    · simp only [denote]; rw [hCaps]
    · simp only [denote]; rw [hBal]
    · simp only [denote]; rw [hSlot]
    · simp only [denote]; rw [hLife]
    · simp only [denote]; rw [hDeath]
    · simp only [denote]; rw [hDel]
    · simp only [denote]; rw [hDels]
    · simp only [denote]; rw [hEp]
    · simp only [denote]; rw [hEpat]
    · simp only [denote]; rw [hHeaps]

/-- Rebuild an equal rest serialization from the 15 raw field equalities. -/
theorem serializeRestFin_of_restAgree {f f' : FinKernelState}
    (h : f'.accounts = f.accounts ∧ f'.caps = f.caps ∧ f'.nullifiers = f.nullifiers
      ∧ f'.revoked = f.revoked ∧ f'.commitments = f.commitments ∧ f'.bal = f.bal
      ∧ f'.slotCaveats = f.slotCaveats ∧ f'.factories = f.factories ∧ f'.lifecycle = f.lifecycle
      ∧ f'.deathCert = f.deathCert ∧ f'.delegate = f.delegate ∧ f'.delegations = f.delegations
      ∧ f'.delegationEpoch = f.delegationEpoch ∧ f'.delegationEpochAt = f.delegationEpochAt
      ∧ f'.heaps = f.heaps) :
    serializeRestFin f = serializeRestFin f' := by
  obtain ⟨hAcc, hCaps, hNul, hRev, hCom, hBal, hSlot, hFac, hLife, hDeath, hDel, hDels, hEp, hEpat,
    hHeaps⟩ := h
  simp only [serializeRestFin, balData, hAcc, hCaps, hNul, hRev, hCom, hBal, hSlot, hFac, hLife,
    hDeath, hDel, hDels, hEp, hEpat, hHeaps]

/-- Flip the orientation of the 15-field rest-agreement conjunction. -/
private theorem restAgree_symm {f f' : FinKernelState}
    (h : f.accounts = f'.accounts ∧ f.caps = f'.caps ∧ f.nullifiers = f'.nullifiers
      ∧ f.revoked = f'.revoked ∧ f.commitments = f'.commitments ∧ f.bal = f'.bal
      ∧ f.slotCaveats = f'.slotCaveats ∧ f.factories = f'.factories ∧ f.lifecycle = f'.lifecycle
      ∧ f.deathCert = f'.deathCert ∧ f.delegate = f'.delegate ∧ f.delegations = f'.delegations
      ∧ f.delegationEpoch = f'.delegationEpoch ∧ f.delegationEpochAt = f'.delegationEpochAt
      ∧ f.heaps = f'.heaps) :
    f'.accounts = f.accounts ∧ f'.caps = f.caps ∧ f'.nullifiers = f.nullifiers
      ∧ f'.revoked = f.revoked ∧ f'.commitments = f.commitments ∧ f'.bal = f.bal
      ∧ f'.slotCaveats = f.slotCaveats ∧ f'.factories = f.factories ∧ f'.lifecycle = f.lifecycle
      ∧ f'.deathCert = f.deathCert ∧ f'.delegate = f.delegate ∧ f'.delegations = f.delegations
      ∧ f'.delegationEpoch = f.delegationEpoch ∧ f'.delegationEpochAt = f.delegationEpochAt
      ∧ f'.heaps = f.heaps := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm,
    h11.symm, h12.symm, h13.symm, h14.symm, h15.symm⟩

/-- **`restHashIffFrame_of_fin` — THE DISCHARGE-LIFT (honest scope: the DENOTE IMAGE).** For any two
reachable (`denote`-image) `RecordKernelState`s, `RH_fin sponge` satisfies the exact
`StateCommit.RestHashIffFrame` biconditional: equal rest hashes ⟺ every non-`cell` component agrees.
RESIDUAL `Poseidon2SpongeCR sponge` ALONE. This is the discharge every real state needs (every real
`RecordKernelState` is a `denote` image); it is NOT claimed for non-reachable, infinite-support states
(where no finite serialization exists — the honestly-named residual scope). Cf. the drift tripwire
`rest_body_matches` welding this body to `StateCommit.RestHashIffFrame`. -/
theorem restHashIffFrame_of_fin (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (f f' : FinKernelState) :
    RH_fin sponge (denote f) = RH_fin sponge (denote f') ↔
      ((denote f').accounts = (denote f).accounts ∧ (denote f').caps = (denote f).caps
        ∧ (denote f').bal = (denote f).bal
        ∧ (denote f').nullifiers = (denote f).nullifiers ∧ (denote f').revoked = (denote f).revoked
        ∧ (denote f').commitments = (denote f).commitments
        ∧ (denote f').slotCaveats = (denote f).slotCaveats
        ∧ (denote f').factories = (denote f).factories ∧ (denote f').lifecycle = (denote f).lifecycle
        ∧ (denote f').deathCert = (denote f).deathCert ∧ (denote f').delegate = (denote f).delegate
        ∧ (denote f').delegations = (denote f).delegations
        ∧ (denote f').delegationEpoch = (denote f).delegationEpoch
        ∧ (denote f').delegationEpochAt = (denote f).delegationEpochAt
        ∧ (denote f').heaps = (denote f).heaps
        ∧ (denote f').nullifierRoot = (denote f).nullifierRoot
        ∧ (denote f').revokedRoot = (denote f).revokedRoot) := by
  rw [RH_fin_denote, RH_fin_denote, restBody_iff_restAgree]
  constructor
  · intro h
    exact restAgree_symm (restAgree_of_serializeRestFin (hCR _ _ h))
  · intro h
    exact congrArg sponge (serializeRestFin_of_restAgree h)

/-- **Drift tripwire.** `StateCommit.RestHashIffFrame RH` is DEFINITIONALLY the universal (all-`k`)
biconditional whose body `restHashIffFrame_of_fin` proves on the image. If `StateCommit`'s body ever
drifts from this one, this `Iff.rfl` breaks — keeping the discharge welded to the real carrier. -/
theorem rest_body_matches (RH : RecordKernelState → ℤ) :
    Dregg2.Circuit.StateCommit.RestHashIffFrame RH ↔
      ∀ k k' : RecordKernelState, RH k = RH k' ↔
        (k'.accounts = k.accounts ∧ k'.caps = k.caps ∧ k'.bal = k.bal
          ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
          ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
          ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
          ∧ k'.delegationEpoch = k.delegationEpoch ∧ k'.delegationEpochAt = k.delegationEpochAt
          ∧ k'.heaps = k.heaps ∧ k'.nullifierRoot = k.nullifierRoot
          ∧ k'.revokedRoot = k.revokedRoot) := Iff.rfl

/-- **`image_of_full`.** The full (unrealizable) carrier would imply the image discharge — recording
that `restHashIffFrame_of_fin` is the honestly-scoped shadow of `StateCommit.RestHashIffFrame`, and
what R4 re-seats the apex on. -/
theorem image_of_full (RH : RecordKernelState → ℤ)
    (hFull : Dregg2.Circuit.StateCommit.RestHashIffFrame RH) (f f' : FinKernelState) :
    RH (denote f) = RH (denote f') ↔
      ((denote f').accounts = (denote f).accounts ∧ (denote f').caps = (denote f).caps
        ∧ (denote f').bal = (denote f).bal
        ∧ (denote f').nullifiers = (denote f).nullifiers ∧ (denote f').revoked = (denote f).revoked
        ∧ (denote f').commitments = (denote f).commitments
        ∧ (denote f').slotCaveats = (denote f).slotCaveats
        ∧ (denote f').factories = (denote f).factories ∧ (denote f').lifecycle = (denote f).lifecycle
        ∧ (denote f').deathCert = (denote f).deathCert ∧ (denote f').delegate = (denote f).delegate
        ∧ (denote f').delegations = (denote f).delegations
        ∧ (denote f').delegationEpoch = (denote f).delegationEpoch
        ∧ (denote f').delegationEpochAt = (denote f).delegationEpochAt
        ∧ (denote f').heaps = (denote f).heaps
        ∧ (denote f').nullifierRoot = (denote f).nullifierRoot
        ∧ (denote f').revokedRoot = (denote f).revokedRoot) :=
  hFull (denote f) (denote f')

/-! ## §7 — TEETH (`#guard`, both polarities). -/

section Teeth

/-- A concrete lifecycle map (cell `1 ↦ 7`), reusing R1's canonical-map shape. -/
private def demoLife : CanonMap CellId Nat 0 :=
  ⟨⟨[(1, 7)], by decide⟩, by
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl; decide⟩

/-- Two concrete distinct finite states: `fA` stores `lifecycle 1 ↦ 7`; `fB` is empty. -/
private def fA : FinKernelState := { finInit with lifecycle := demoLife }
private def fB : FinKernelState := finInit

-- serializeFin is REFLEXIVE and DISTINGUISHES the two distinct states (both polarities):
#guard decide (serializeFin fA = serializeFin fA)             -- reflexive: true
#guard decide (serializeFin fA = serializeFin fB) == false    -- distinct states ⇒ distinct serialization

-- serializeFin distinguishes a STORED-NONDEFAULT (`lifecycle 1 ↦ 7`) from ABSENT (ties to R1's CanonMap):
#guard decide (serializeRestFin fA = serializeRestFin fB) == false

-- A Poseidon2CR-VIOLATING collapsing sponge (`fun _ => 0`) COLLIDES the two distinct states — so the
-- CR floor is LOAD-BEARING (without it the frame hash binds nothing):
#guard decide (frameHashFin (fun _ => 0) fA = frameHashFin (fun _ => 0) fB)   -- collides: true

/-- The collapsing sponge is NOT collision-resistant (it maps `[]` and `[0]` to the same value though
`[] ≠ [0]`) — so `restHashIffFrame_fin`'s `Poseidon2SpongeCR` hypothesis is genuinely FALSE for it,
i.e. the floor cannot be dropped. -/
theorem collapsing_not_CR : ¬ Poseidon2SpongeCR (fun _ : List ℤ => (0 : ℤ)) := by
  intro hCR
  have := hCR [] [0] rfl
  exact absurd this (by decide)

end Teeth

end Dregg2.Circuit.FinFrameHash
