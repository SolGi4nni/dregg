/-
# Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat — the WIDENED CAVEAT OPERAND (staged).

The live in-circuit caveat operand is `SlotCaveatEntry { type_tag, slot_index: u8, params }`
(`circuit/src/effect_vm/trace.rs`) — SLOT-ONLY. The rotation makes the heap the app-state
lane (heap-keyed `StateConstraint`s landed `5e0558fdc`: `heapKey k = FieldsMap.userKey` by
`rfl`, `HeapAtom.lift`), so capability attenuation must reach HEAP KEYS before the cutover
freezes the wire (`HORIZONLOG.md` "HEAP-KEYED CAVEATS — rotation-URGENT"). THIS module is the
Lean-first design + staged emission of the widened operand, at the CONFIRMED register count
R=24 (`docs/ROTATION-CUTOVER.md` §2b, ember 2026-06-12):

  * **§1 the operand** — `(domain, key)`: the domain is the universal-memory `Domain`
    (`Crypto/UniversalMemory.lean`), wire-coded by THE one `DescriptorIR2.domainCode`
    (registers 0 · heap 1 — identical to `turn/src/umem.rs::UDomain`); the key widens
    `u8 → felt` (heap keys are felts). **THE NO-ALIASING KEYSTONE**
    `caveat_operand_no_aliasing`: a register (slot) operand and a heap operand can NEVER
    collide — domain separation as a theorem, the same discipline as the umem `Domain` tags
    (`caveatOperand_wire_injective` is the general form). Decode FAILS CLOSED
    (`operand?_unknown_refuses`).
  * **§2 the entry + manifest layout** — `RotCaveatEntry` = 7 felts
    `[type_tag, domain_tag, key, p0, p1, p2, p3]` (`toList_length`, positional
    `toList_injective`); the manifest = 1 count + 4 entries = 29 felts
    (`RotCaveatManifest.toList_length`). Rust twin: `trace.rs::RotCaveatEntry` +
    `columns.rs::rotation::caveat` (staged constants).
  * **§3 the chained caveat commitment** — `caveatCommit` (the `chunk31` arity-{2,4}
    chunking over the 29 manifest limbs: 4-wide head + 8×(digest+3) + 1×(digest+1) = 10
    chip sites). `caveatCommit_binds`: equal commits force equal manifests under the ONE
    `Poseidon2SpongeCR` floor — tampering a domain tag, a heap key, a type tag, a param,
    or the count moves the commit (#guard both polarities).
  * **§4 the staged probe** — `rotationCaveatProbeVmDescriptor2`: the R=24 rotated state
    block + the caveat manifest block + the caveat chain, 21 chip sites, THREE PI pins
    (published state commit · committed height · published caveat commit).
    `rotationCaveatProbe_binds_published`: two `Satisfied2` witnesses publishing the same
    commits agree on the WHOLE rotated block AND the WHOLE caveat manifest — a forged
    domain tag or a tampered heap key moves the published caveat commit (REFUSED).
  * **§5 the semantics bridge (statement-level)** — a heap-domain entry's runtime meaning
    is `HeapAtom`-shaped (the landed lift): `tagHeapAtom` decodes the wire type tag into
    the `Exec.Program.HeapAtom` vocabulary (tags aligned with `pi::SLOT_CAVEAT_TAG_*`);
    `heapAdmits_strictMono_iff` is PROVEN (the decode meets the landed heap-admit
    characterizations at `heapKey k`). The EXECUTOR leg — runtime discharge of heap-keyed
    caveats — DOES NOT EXIST YET: it is the NAMED PREMISE `HeapCaveatRuntimeDischarge`
    (HORIZONLOG'd as the follow-up; the slot-caveat manifest discharge is the template).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; crypto only as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `native_decide`. STAGED: nothing here rides
the live v1 wire (the live `SlotCaveatEntry` manifest at PI 101..126 is untouched); the
Rust consumers are the recursion-gated IR-v2 tests + the drift guards.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationR
import Dregg2.Exec.Program

namespace Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotation (PUB_COMMIT PUB_HEIGHT)
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Crypto
open Dregg2.Substrate.Heap (refSponge)
open Dregg2.Exec (HeapAtom evalHeap heapKey Value evalHeap_strictMono_iff)

set_option autoImplicit false

deriving instance BEq for Dregg2.Exec.HeapAtom

/-! ## §1 — the widened operand: `(domain, key)`, domain-separated by theorem.

The pre-rotation operand is a bare `slot_index : u8` — there is no carrier for "which state
plane". The rotated operand is the universal-memory address discipline applied to caveats:
`(domain, key)` with the domain wire-coded by THE one `domainCode` (the same codes the umem
rows carry — registers 0, heap 1) and the key a full felt. Only the registers and heap
domains are caveat-scopable (caps/nullifiers/index are kernel planes; a cell program cannot
caveat them — decode refuses everything else, fail closed). -/

/-- A widened caveat operand: WHICH state plane × WHICH key in it. The abstract form of the
wire pair `(domainCode domain, key)`. -/
structure CaveatOperand where
  domain : UniversalMemory.Domain
  key : ℤ
deriving Repr, DecidableEq

/-- The wire encoding of an operand: `(domain_tag, key)`. -/
def CaveatOperand.wire (o : CaveatOperand) : ℤ × ℤ := (domainCode o.domain, o.key)

/-- The wire encoding is injective — domains AND keys are recovered exactly
(`domainCode_injective` lifts to the pair). -/
theorem caveatOperand_wire_injective : Function.Injective CaveatOperand.wire := by
  rintro ⟨d, k⟩ ⟨d', k'⟩ h
  simp only [CaveatOperand.wire, Prod.mk.injEq] at h
  cases domainCode_injective h.1
  cases h.2
  rfl

/-- **THE NO-ALIASING KEYSTONE** — a register (slot) operand and a heap operand can NEVER
collide, REGARDLESS of their keys: register index 7 and heap key 7 are different addresses
because the domain tag separates them (the umem `Domain`-tag discipline, applied to the
caveat operand). The u8 `slot_index` had no such carrier; the widened entry does, by
construction and by THIS theorem. -/
theorem caveat_operand_no_aliasing (i k : ℤ) :
    CaveatOperand.wire ⟨.registers, i⟩ ≠ CaveatOperand.wire ⟨.heap, k⟩ := by
  intro h
  have hfst := congrArg Prod.fst h
  simp [CaveatOperand.wire, domainCode] at hfst

/-! ## §2 — the entry and manifest: 7-felt entries, 29-felt manifest. -/

/-- **`RotCaveatEntry`** — the widened caveat entry: the constraint type tag (the live
`pi::SLOT_CAVEAT_TAG_*` vocabulary, zero = "no caveat"), the DOMAIN TAG (`domainCode`:
registers 0 · heap 1), the key (a felt — a register index in the registers domain, a heap
key in the heap domain), and up to 4 numeric params. Rust twin:
`circuit/src/effect_vm/trace.rs::RotCaveatEntry` (7-felt packing, same order). -/
structure RotCaveatEntry where
  typeTag : ℤ
  domainTag : ℤ
  key : ℤ
  p0 : ℤ
  p1 : ℤ
  p2 : ℤ
  p3 : ℤ
deriving Repr, DecidableEq

/-- The 7-felt wire packing: `[type_tag, domain_tag, key, p0, p1, p2, p3]`. -/
def RotCaveatEntry.toList (e : RotCaveatEntry) : List ℤ :=
  [e.typeTag, e.domainTag, e.key, e.p0, e.p1, e.p2, e.p3]

/-- The entry width: 7 felts (the live entry's 6 + the domain tag; the key column widens
`u8 → felt` at no extra cost — it was already a felt slot on the wire). -/
theorem RotCaveatEntry.toList_length (e : RotCaveatEntry) : e.toList.length = 7 := rfl

/-- Positional binding: equal packings force equal entries — nothing hides. -/
theorem RotCaveatEntry.toList_injective {e e' : RotCaveatEntry}
    (h : e.toList = e'.toList) : e = e' := by
  cases e; cases e'
  simp only [toList, List.cons.injEq, and_true] at h
  simp only [mk.injEq]
  exact h

/-- The decoded operand of an entry — FAIL CLOSED: only the registers and heap domains are
caveat-scopable; an unknown domain tag decodes to `none` (the Rust `from_felts` REFUSES). -/
def RotCaveatEntry.operand? (e : RotCaveatEntry) : Option CaveatOperand :=
  if e.domainTag = domainCode .registers then some ⟨.registers, e.key⟩
  else if e.domainTag = domainCode .heap then some ⟨.heap, e.key⟩
  else none

/-- A forged domain tag REFUSES (decode is fail-closed — there is no "default plane"). -/
theorem operand?_unknown_refuses (e : RotCaveatEntry)
    (h0 : e.domainTag ≠ domainCode .registers) (h1 : e.domainTag ≠ domainCode .heap) :
    e.operand? = none := by
  simp [RotCaveatEntry.operand?, h0, h1]

/-- Encode-then-decode is the identity on the two caveat-scopable domains. -/
theorem operand?_roundtrip (o : CaveatOperand)
    (h : o.domain = .registers ∨ o.domain = .heap)
    (tag p0 p1 p2 p3 : ℤ) :
    (RotCaveatEntry.mk tag (domainCode o.domain) o.key p0 p1 p2 p3).operand? = some o := by
  obtain ⟨d, k⟩ := o
  rcases h with h | h <;> subst h <;> simp [RotCaveatEntry.operand?, domainCode]

/-- **`RotCaveatManifest`** — the fixed-size caveat table the staged PI region carries:
1 count felt + `MAX_CAVEATS` = 4 entries × 7 felts = **29 felts** (the live manifest is
1 + 4 × 6 = 25). Unused entries are zero (typeTag 0 = "no caveat", same sentinel as live). -/
structure RotCaveatManifest where
  count : ℤ
  e0 : RotCaveatEntry
  e1 : RotCaveatEntry
  e2 : RotCaveatEntry
  e3 : RotCaveatEntry
deriving Repr, DecidableEq

/-- The maximum number of caveat entries the staged region carries (unchanged from live). -/
abbrev MAX_CAVEATS : Nat := 4

/-- Entry `i` of the manifest. -/
def RotCaveatManifest.entry (m : RotCaveatManifest) : Fin MAX_CAVEATS → RotCaveatEntry
  | ⟨0, _⟩ => m.e0
  | ⟨1, _⟩ => m.e1
  | ⟨2, _⟩ => m.e2
  | ⟨3, _⟩ => m.e3

/-- The manifest wire packing: count first, then the four entries in order. -/
def RotCaveatManifest.toList (m : RotCaveatManifest) : List ℤ :=
  m.count :: (m.e0.toList ++ m.e1.toList ++ m.e2.toList ++ m.e3.toList)

/-- The manifest width: 29 felts (1 + 4 × 7). -/
theorem RotCaveatManifest.toList_length (m : RotCaveatManifest) : m.toList.length = 29 := by
  cases m; rfl

/-- Positional binding for the whole manifest: equal 29-felt packings force equal manifests
(count, every entry's type tag, DOMAIN TAG, KEY, and params). -/
theorem RotCaveatManifest.toList_injective {m m' : RotCaveatManifest}
    (h : m.toList = m'.toList) : m = m' := by
  cases m; cases m'
  simp only [toList, List.cons.injEq] at h
  obtain ⟨hc, hrest⟩ := h
  have h1 := List.append_inj hrest (by simp [RotCaveatEntry.toList])
  have h2 := List.append_inj h1.1 (by simp [RotCaveatEntry.toList])
  have h3 := List.append_inj h2.1 (by simp [RotCaveatEntry.toList])
  simp only [mk.injEq]
  exact ⟨hc, RotCaveatEntry.toList_injective h3.1, RotCaveatEntry.toList_injective h3.2,
    RotCaveatEntry.toList_injective h2.2, RotCaveatEntry.toList_injective h1.2⟩

#assert_axioms caveatOperand_wire_injective
#assert_axioms caveat_operand_no_aliasing
#assert_axioms RotCaveatManifest.toList_injective

/-! ## §3 — the chained caveat commitment (the same arity-{2,4} chip discipline). -/

/-- The chained chip commitment over an arbitrary limb list: 4-wide head, `chunk31` body
(3-wide groups while ≥ 3 remain, then singletons — arity ∈ {2,4}, NEVER 3). This is
`wireCommitR` minus the iroot tail: the caveat manifest has no "literally last" obligation. -/
def chainCommit (hash : List ℤ → ℤ) (l : List ℤ) : ℤ :=
  chainFrom hash (hash (l.take 4)) (chunk31 (l.drop 4))

/-- The chained commitment binds equal-length limb lists (the `wireCommitR_binds` argument,
without the snoc'd tail): equal commits force equal lists under the ONE CR floor. -/
theorem chainCommit_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {l l' : List ℤ} (hlen : l.length = l'.length)
    (h : chainCommit hash l = chainCommit hash l') : l = l' := by
  unfold chainCommit at h
  obtain ⟨hhead, hchunks⟩ := chainFrom_inj hash hCR
    (by rw [chunk31_length, chunk31_length, List.length_drop, List.length_drop, hlen]) h
  have htake : l.take 4 = l'.take 4 := hCR _ _ hhead
  have hdrop : l.drop 4 = l'.drop 4 := by
    have := congrArg List.flatten hchunks
    rwa [chunk31_flatten, chunk31_flatten] at this
  rw [← List.take_append_drop 4 l, ← List.take_append_drop 4 l', htake, hdrop]

/-- **`caveatCommit`** — the chained chip commitment of the caveat manifest: 29 limbs =
4-wide head + 8 × (digest+3) + 1 × (digest+1) = 10 chip sites, arity ∈ {2,4}. -/
def caveatCommit (hash : List ℤ → ℤ) (m : RotCaveatManifest) : ℤ :=
  chainCommit hash m.toList

/-- **THE CAVEAT BINDING KEYSTONE** — equal caveat commits force equal manifests: every
entry's type tag, DOMAIN TAG, KEY (slot index or heap felt), params, and the count are
bound. A forged domain tag or a tampered heap key MOVES the commit. -/
theorem caveatCommit_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {m m' : RotCaveatManifest}
    (h : caveatCommit hash m = caveatCommit hash m') : m = m' :=
  RotCaveatManifest.toList_injective
    (chainCommit_binds hash hCR
      ((m.toList_length).trans (m'.toList_length).symm) h)

/-- The operand tooth: equal commits force equal DECODED operands per entry (the composition
`caveatCommit_binds` ∘ `operand?` — what the SDK's attenuation check consumes). -/
theorem caveatCommit_binds_operand (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {m m' : RotCaveatManifest}
    (h : caveatCommit hash m = caveatCommit hash m') (i : Fin MAX_CAVEATS) :
    (m.entry i).operand? = (m'.entry i).operand? := by
  rw [caveatCommit_binds hash hCR h]

#assert_axioms chainCommit_binds
#assert_axioms caveatCommit_binds
#assert_axioms caveatCommit_binds_operand

/-- The all-zero entry ("no caveat"). -/
def zeroEntry : RotCaveatEntry := ⟨0, 0, 0, 0, 0, 0, 0⟩

/-- A concrete demo manifest: entry 0 caveats REGISTER 3 (monotonic, tag 6); entry 1
caveats HEAP KEY 123456789 (≥ 50, tag 2) — a key no u8 could carry. -/
def demoManifest : RotCaveatManifest :=
  { count := 2
  , e0 := ⟨6, domainCode .registers, 3, 0, 0, 0, 0⟩
  , e1 := ⟨2, domainCode .heap, 123456789, 50, 0, 0, 0⟩
  , e2 := zeroEntry
  , e3 := zeroEntry }

-- NON-VACUITY, both polarities (Horner toy sponge; deployment = audited p3 Poseidon2 under
-- the same CR floor). Forging the DOMAIN TAG (heap → registers: the aliasing attack the u8
-- operand could not even express) moves the commit...
#guard caveatCommit refSponge demoManifest
  != caveatCommit refSponge { demoManifest with e1 := { demoManifest.e1 with domainTag := 0 } }
-- ...tampering the HEAP KEY moves it (the key is commitment-carried, not metadata)...
#guard caveatCommit refSponge demoManifest
  != caveatCommit refSponge { demoManifest with e1 := { demoManifest.e1 with key := 123456790 } }
-- ...tampering the type tag, a param, and the count each move it...
#guard caveatCommit refSponge demoManifest
  != caveatCommit refSponge { demoManifest with e0 := { demoManifest.e0 with typeTag := 7 } }
#guard caveatCommit refSponge demoManifest
  != caveatCommit refSponge { demoManifest with e1 := { demoManifest.e1 with p0 := 51 } }
#guard caveatCommit refSponge demoManifest
  != caveatCommit refSponge { demoManifest with count := 1 }
-- ...and the honest recompute is stable (the positive polarity).
#guard caveatCommit refSponge demoManifest == caveatCommit refSponge demoManifest
-- The decode teeth, executable: both demo operands decode; a forged tag refuses.
#guard demoManifest.e0.operand? == some ⟨.registers, 3⟩
#guard demoManifest.e1.operand? == some ⟨.heap, 123456789⟩
#guard (RotCaveatEntry.mk 2 7 123456789 50 0 0 0).operand? == none

/-! ## §4 — the staged probe at the CONFIRMED R=24: the rotated block + the caveat manifest.

Column layout (the Rust twin is `columns.rs::rotation::caveat`):
  `0..30`   the R=24 pre-iroot limbs · `31` iroot · `32` state_commit ·
  `33..42`  the rotation chain carriers (= `probeWidth 24 = 43` ends the rotation part) ·
  `43`      caveat count · `44 + 7i .. 50 + 7i` entry `i` (i < 4) — the block is `43..71` ·
  `72..80`  the caveat chain carriers (9) · `81` CAVEAT_COMMIT · width **82**. -/

/-- The caveat manifest block base (= `probeWidth 24` — right after the rotation probe). -/
def CAVEAT_BASE : Nat := 43
/-- The caveat count column. -/
def CAVEAT_COUNT_COL : Nat := 43
/-- Entry `i`'s base column: `44 + 7i`. -/
def caveatEntryBase (i : Fin MAX_CAVEATS) : Nat := 44 + 7 * i.val
/-- The caveat chain carriers (9 — sites 0..8 of the 10-site caveat chain). -/
def CAVEAT_CHAIN_BASE : Nat := 72
/-- The caveat-commitment carrier (the chain's final digest). -/
def CAVEAT_COMMIT : Nat := 81
/-- The caveat probe trace width: 43 (rotation R=24) + 29 (manifest) + 9 (chain) + 1. -/
def CAVEAT_PROBE_WIDTH : Nat := 82
/-- The published-caveat-commit PI slot (after `PUB_COMMIT`, `PUB_HEIGHT`). -/
def PUB_CAVEAT : Nat := 2

/-- Read the caveat manifest block off a row (columns `43..71`, positional). -/
def blockManifest (a : Assignment) : RotCaveatManifest :=
  { count := a 43
  , e0 := ⟨a 44, a 45, a 46, a 47, a 48, a 49, a 50⟩
  , e1 := ⟨a 51, a 52, a 53, a 54, a 55, a 56, a 57⟩
  , e2 := ⟨a 58, a 59, a 60, a 61, a 62, a 63, a 64⟩
  , e3 := ⟨a 65, a 66, a 67, a 68, a 69, a 70, a 71⟩ }

/-- The caveat chain as ordered hash sites, GLOBAL site indices 11..20 (after the 11
rotation sites at R=24): the 4-wide head over `[count, e0.tag, e0.dom, e0.key]`, eight
(carrier+3) body sites, the (carrier+1) tail — arity ∈ {2,4}, never 3. Chaining is by the
CARRIER COLUMNS (`.col`), which graduates to the SAME wire bytes as a `.digest` reference
(`HashInput.toExpr` resolves `.digest k` to site `k`'s `digestCol` — `DescriptorIR2.lean`),
while keeping the v1 denotation local per site (each carrier is pinned by its own site, so
the chain still composes — `rotationCaveatSites_pin_caveat`). -/
def caveatSites : List VmHashSite :=
  [ ⟨72, [.col 43, .col 44, .col 45, .col 46], 4⟩
  , ⟨73, [.col 72, .col 47, .col 48, .col 49], 4⟩
  , ⟨74, [.col 73, .col 50, .col 51, .col 52], 4⟩
  , ⟨75, [.col 74, .col 53, .col 54, .col 55], 4⟩
  , ⟨76, [.col 75, .col 56, .col 57, .col 58], 4⟩
  , ⟨77, [.col 76, .col 59, .col 60, .col 61], 4⟩
  , ⟨78, [.col 77, .col 62, .col 63, .col 64], 4⟩
  , ⟨79, [.col 78, .col 65, .col 66, .col 67], 4⟩
  , ⟨80, [.col 79, .col 68, .col 69, .col 70], 4⟩
  , ⟨CAVEAT_COMMIT, [.col 80, .col 71], 2⟩ ]

/-- The probe's full ordered site list: the R=24 rotation chain, then the caveat chain. -/
def rotationCaveatSites : List VmHashSite := rotationSitesR 24 ++ caveatSites

-- The arity discipline holds across the whole walk (the chip refuses arity 3).
#guard rotationCaveatSites.all fun s => s.arity == 4 || s.arity == 2
#guard rotationCaveatSites.length == 21

/-- The v1-grammar caveat probe: 21 chained sites + the three last-row PI pins. -/
def rotationCaveatProbeVmDescriptor : EffectVmDescriptor :=
  { name        := "dregg-effectvm-rotation-caveat-v3-staged-r24"
  , traceWidth  := CAVEAT_PROBE_WIDTH
  , piCount     := 3
  , constraints :=
      [ .piBinding .last (stateCommitCol 24) PUB_COMMIT
      , .piBinding .last (committedHeightCol 24) PUB_HEIGHT
      , .piBinding .last CAVEAT_COMMIT PUB_CAVEAT ]
  , hashSites   := rotationCaveatSites
  , ranges      := [] }

/-- The graduated IR-v2 caveat probe (chip lookups, the five EPOCH tables) — the descriptor
`EmitRotationV3.lean` emits for the staged Rust path. -/
def rotationCaveatProbeVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 rotationCaveatProbeVmDescriptor

#guard graduable rotationCaveatProbeVmDescriptor
#guard rotationCaveatProbeVmDescriptor2.constraints.length == 3 + 21
#guard rotationCaveatProbeVmDescriptor2.tables.length == 5
#guard rotationCaveatProbeVmDescriptor2.hashSites.length == 0
#guard (emitVmJson2 rotationCaveatProbeVmDescriptor2).startsWith "{\"name\":\""

/-- The rotation leg of the walk still pins the state commitment (the R=24 site chain is a
prefix of the combined walk, so its accumulator is untouched by the caveat sites). -/
theorem rotationCaveatSites_pin_state (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env rotationCaveatSites) :
    env.loc (stateCommitCol 24)
      = wireCommitR hash (preLimbs 24 env.loc) (env.loc (irootCol 24)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := h
  exact h11

set_option maxHeartbeats 6400000 in
/-- The caveat leg pins the caveat commitment: a row satisfying the walk carries
`CAVEAT_COMMIT = caveatCommit` of its OWN manifest block — the ten per-site carrier
equations compose into the chained commitment. -/
theorem rotationCaveatSites_pin_caveat (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env rotationCaveatSites) :
    env.loc CAVEAT_COMMIT = caveatCommit hash (blockManifest env.loc) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h21, -⟩ := h
  simp only [VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil]
    at h11 h12 h13 h14 h15 h16 h17 h18 h19 h21
  rw [h21, h19, h18, h17, h16, h15, h14, h13, h12, h11]
  rfl

#assert_axioms rotationCaveatSites_pin_state
#assert_axioms rotationCaveatSites_pin_caveat

/-- The probe pins BOTH commitments on EVERY row of a `Satisfied2` witness. -/
theorem rotationCaveatProbe_pins (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hrange : t.tf .range = rangeRows BAL_LIMB_BITS)
    (hsat : Satisfied2 hash rotationCaveatProbeVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    (envAt t i).loc (stateCommitCol 24)
        = wireCommitR hash (preLimbs 24 (envAt t i).loc) ((envAt t i).loc (irootCol 24))
    ∧ (envAt t i).loc CAVEAT_COMMIT = caveatCommit hash (blockManifest (envAt t i).loc) := by
  have h := graduateV1_sound hash rotationCaveatProbeVmDescriptor minit mfin maddrs t
    hchip hrange (by decide) hsat i hi
  exact ⟨rotationCaveatSites_pin_state hash _ h.2.1,
    rotationCaveatSites_pin_caveat hash _ h.2.1⟩

/-- The probe PUBLISHES: last row, PI 0 = the state commit, PI 1 = the height limb,
PI 2 = the caveat commit. -/
theorem rotationCaveatProbe_publishes (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hrange : t.tf .range = rangeRows BAL_LIMB_BITS)
    (hsat : Satisfied2 hash rotationCaveatProbeVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 = t.rows.length) :
    (envAt t i).loc (stateCommitCol 24) = (envAt t i).pub PUB_COMMIT
    ∧ (envAt t i).loc (committedHeightCol 24) = (envAt t i).pub PUB_HEIGHT
    ∧ (envAt t i).loc CAVEAT_COMMIT = (envAt t i).pub PUB_CAVEAT := by
  have h := graduateV1_sound hash rotationCaveatProbeVmDescriptor minit mfin maddrs t
    hchip hrange (by decide) hsat i hi
  have h1 := h.1 (.piBinding .last (stateCommitCol 24) PUB_COMMIT)
    (by simp [rotationCaveatProbeVmDescriptor])
  have h2 := h.1 (.piBinding .last (committedHeightCol 24) PUB_HEIGHT)
    (by simp [rotationCaveatProbeVmDescriptor])
  have h3 := h.1 (.piBinding .last CAVEAT_COMMIT PUB_CAVEAT)
    (by simp [rotationCaveatProbeVmDescriptor])
  simp only [VmConstraint.holdsVm] at h1 h2 h3
  exact ⟨h1 (by simp [hlast]), h2 (by simp [hlast]), h3 (by simp [hlast])⟩

/-- **THE END-TO-END STAGED KEYSTONE** — two `Satisfied2` witnesses publishing the SAME
state commit and the SAME caveat commit agree on the WHOLE rotated block (all 24 registers,
every map root, lifecycle/epoch/height), the iroot, the published height, AND the WHOLE
caveat manifest — every entry's type tag, DOMAIN TAG, KEY, and params. A forged domain tag
or a tampered heap key in the manifest moves PI 2: REFUSED. Under the ONE CR floor. -/
theorem rotationCaveatProbe_binds_published (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hrange : t.tf .range = rangeRows BAL_LIMB_BITS)
    (hchip' : ChipTableSound hash (t'.tf .poseidon2))
    (hrange' : t'.tf .range = rangeRows BAL_LIMB_BITS)
    (hsat : Satisfied2 hash rotationCaveatProbeVmDescriptor2 minit mfin maddrs t)
    (hsat' : Satisfied2 hash rotationCaveatProbeVmDescriptor2 minit' mfin' maddrs' t')
    (i j : Nat) (hi : i < t.rows.length) (hj : j < t'.rows.length)
    (hlast : i + 1 = t.rows.length) (hlast' : j + 1 = t'.rows.length)
    (hpub : (envAt t i).pub PUB_COMMIT = (envAt t' j).pub PUB_COMMIT)
    (hcav : (envAt t i).pub PUB_CAVEAT = (envAt t' j).pub PUB_CAVEAT) :
    preLimbs 24 (envAt t i).loc = preLimbs 24 (envAt t' j).loc
    ∧ (envAt t i).loc (irootCol 24) = (envAt t' j).loc (irootCol 24)
    ∧ (envAt t i).pub PUB_HEIGHT = (envAt t' j).pub PUB_HEIGHT
    ∧ blockManifest (envAt t i).loc = blockManifest (envAt t' j).loc := by
  obtain ⟨hc, hh, hk⟩ := rotationCaveatProbe_publishes hash minit mfin maddrs t
    hchip hrange hsat i hi hlast
  obtain ⟨hc', hh', hk'⟩ := rotationCaveatProbe_publishes hash minit' mfin' maddrs' t'
    hchip' hrange' hsat' j hj hlast'
  obtain ⟨hp, hq⟩ := rotationCaveatProbe_pins hash minit mfin maddrs t hchip hrange hsat i hi
  obtain ⟨hp', hq'⟩ := rotationCaveatProbe_pins hash minit' mfin' maddrs' t'
    hchip' hrange' hsat' j hj
  have hwire : wireCommitR hash (preLimbs 24 (envAt t i).loc) ((envAt t i).loc (irootCol 24))
      = wireCommitR hash (preLimbs 24 (envAt t' j).loc) ((envAt t' j).loc (irootCol 24)) := by
    rw [← hp, ← hp', hc, hc', hpub]
  obtain ⟨hpre, hir⟩ := wireCommitR_binds hash hCR
    (by rw [preLimbs_length, preLimbs_length]) hwire
  have hcc : caveatCommit hash (blockManifest (envAt t i).loc)
      = caveatCommit hash (blockManifest (envAt t' j).loc) := by
    rw [← hq, ← hq', hk, hk', hcav]
  refine ⟨hpre, hir, ?_, caveatCommit_binds hash hCR hcc⟩
  rw [← hh, ← hh']
  exact congrArg (fun L => L.getD (committedHeightCol 24) 0) hpre

#assert_axioms rotationCaveatProbe_pins
#assert_axioms rotationCaveatProbe_publishes
#assert_axioms rotationCaveatProbe_binds_published

/-! ## §5 — the semantics bridge: a heap-domain entry means a `HeapAtom` (statement-level).

The landed heap-constraint lift (`Exec/Program.lean` §heap, `5e0558fdc`) gives the runtime
vocabulary: a heap-keyed constraint IS the name-keyed atom at `heapKey k`. The staged wire
entry decodes into that vocabulary; the type tags are the live `pi::SLOT_CAVEAT_TAG_*`
numbers, so the slot and heap planes share ONE tag space. PROVEN here: the decode is
well-defined and meets the landed heap-admit characterizations. NAMED PREMISE: the executor
does not yet DISCHARGE heap-keyed caveats at run time (the slot manifest's
`populate`/`verify` pair is the template; HORIZONLOG'd follow-up). -/

/-- Decode a wire type tag (+ first param) into the landed `HeapAtom` vocabulary. Tags are
the live `pi::SLOT_CAVEAT_TAG_*` numbers (FIELD_EQUALS 1 · FIELD_GTE 2 · FIELD_LTE 3 ·
WRITE_ONCE 4 · IMMUTABLE 5 · MONOTONIC 6 · STRICT_MONOTONIC 7 · FIELD_DELTA 8). Tags 9..12
(monotonic-sequence, temporal-gate, sender-authorized, allowed-transitions) are slot-shaped
or multi-input and are NOT heap-liftable single-key atoms — they decode `none` on the heap
plane, matching the landed single-key lift (`5e0558fdc`'s named tail). FAIL CLOSED. -/
def tagHeapAtom (tag p0 : ℤ) : Option HeapAtom :=
  if tag = 1 then some (.equals p0)
  else if tag = 2 then some (.ge p0)
  else if tag = 3 then some (.le p0)
  else if tag = 4 then some .writeOnce
  else if tag = 5 then some .immutable
  else if tag = 6 then some .monotonic
  else if tag = 7 then some .strictMono
  else if tag = 8 then some (.deltaBounded p0)
  else none

/-- **The runtime meaning of a heap-domain entry**: every atom its tag decodes to admits
the `(old, new)` heap transition — `evalHeap` at the entry's key, i.e. the EXISTING
name-keyed evaluator at `heapKey k` (the landed lift; absence fails closed BY THEOREM
there). This is what the executor's heap-caveat discharge must establish. -/
def RotCaveatEntry.heapAdmits (e : RotCaveatEntry) (k : Nat) (o n : Value) : Prop :=
  ∀ a, tagHeapAtom e.typeTag e.p0 = some a → evalHeap k a o n = true

/-- PROVEN where cheap — the decode meets the landed characterizations: a heap-domain
STRICT_MONOTONIC entry (tag 7) admits exactly when both sides are PRESENT at `heapKey k`
and strictly increase (`evalHeap_strictMono_iff`, transported verbatim). The wire tag, the
landed atom, and the record substrate's absence semantics meet in one statement. -/
theorem heapAdmits_strictMono_iff (k : Nat) (key p1 p2 p3 : ℤ) (o n : Value) :
    (RotCaveatEntry.mk 7 (domainCode .heap) key 0 p1 p2 p3).heapAdmits k o n ↔
      ∃ a b, o.scalar (heapKey k) = some a ∧ n.scalar (heapKey k) = some b ∧ a < b := by
  constructor
  · intro h
    exact (evalHeap_strictMono_iff k o n).mp (h .strictMono rfl)
  · intro h a ha
    have ha' : HeapAtom.strictMono = a := Option.some.inj ha
    cases ha'
    exact (evalHeap_strictMono_iff k o n).mpr h

/-- **NAMED PREMISE — `HeapCaveatRuntimeDischarge` (the executor leg DOES NOT exist yet).**
An executor admission relation `admitsTurn` discharges heap-keyed caveats iff every
admitted `(manifest, old, new)` satisfies each heap-domain entry's decoded meaning at its
committed key. The slot-caveat manifest already has this shape at run time
(`populate_slot_caveat_manifest` / `verify_slot_caveat_manifest`); the HEAP leg is the
HORIZONLOG'd follow-up — until it lands, this `Prop` is the honest boundary: the staged
wire BINDS the operand (§4), the runtime DISCHARGE is named, not claimed. -/
def HeapCaveatRuntimeDischarge
    (admitsTurn : RotCaveatManifest → Value → Value → Prop) : Prop :=
  ∀ (m : RotCaveatManifest) (o n : Value), admitsTurn m o n →
    ∀ (i : Fin MAX_CAVEATS) (k : Nat),
      (m.entry i).domainTag = domainCode .heap →
      (m.entry i).key = (k : ℤ) →
      (m.entry i).heapAdmits k o n

/-- The bridge, assembled: under the named discharge premise, a wire-bound heap-domain
entry's committed key really was constrained `HeapAtom`-wise on the admitted transition —
the staged operand's (domain, key, tag) triple and the heap `StateConstraint` semantics
connect end-to-end the moment the executor leg lands. -/
theorem staged_heap_caveat_bridge
    (admitsTurn : RotCaveatManifest → Value → Value → Prop)
    (hdis : HeapCaveatRuntimeDischarge admitsTurn)
    {m : RotCaveatManifest} {o n : Value} (h : admitsTurn m o n)
    (i : Fin MAX_CAVEATS) (k : Nat)
    (hd : (m.entry i).domainTag = domainCode .heap)
    (hk : (m.entry i).key = (k : ℤ)) :
    (m.entry i).heapAdmits k o n :=
  hdis m o n h i k hd hk

#assert_axioms heapAdmits_strictMono_iff
#assert_axioms staged_heap_caveat_bridge

-- The decode-tag alignment, executable (the Rust `SLOT_CAVEAT_TAG_*` numbers).
#guard tagHeapAtom 6 0 == some .monotonic
#guard tagHeapAtom 2 50 == some (.ge 50)
#guard tagHeapAtom 0 0 == none      -- "no caveat" decodes to nothing
#guard tagHeapAtom 10 0 == none     -- TEMPORAL_GATE is not a single-key heap atom
#guard tagHeapAtom 12 0 == none     -- ALLOWED_TRANSITIONS is not a single-key heap atom

/-! ## §6 — the staged wire artifacts (manifest + probe JSON). -/

/-- **The caveat-operand layout manifest** — built FROM the defs (it cannot drift from the
constants this module proves about). The Rust twin (`rotation_caveat_layout_matches_lean`
in `effect_vm_descriptors.rs`) rebuilds the SAME bytes from `columns.rs::rotation::caveat`
and compares against the committed `rotation-caveat-layout-v3-staged.json` — both sides
pin, neither parses. -/
def rotationCaveatLayoutManifest : String :=
  s!"\{\"v\":\"dregg-rotation-caveat-layout-v3-staged\",\"r\":24" ++
  s!",\"caveat_base\":{CAVEAT_BASE},\"count_col\":{CAVEAT_COUNT_COL}" ++
  s!",\"entry_base\":{caveatEntryBase ⟨0, by decide⟩},\"entry_size\":7" ++
  s!",\"max_caveats\":{MAX_CAVEATS},\"manifest_size\":29" ++
  s!",\"chain_base\":{CAVEAT_CHAIN_BASE},\"num_chain\":9,\"caveat_commit\":{CAVEAT_COMMIT}" ++
  s!",\"probe_width\":{CAVEAT_PROBE_WIDTH}" ++
  s!",\"domain_registers\":{domainCode .registers},\"domain_heap\":{domainCode .heap}" ++
  s!",\"pub_commit\":{PUB_COMMIT},\"pub_height\":{PUB_HEIGHT},\"pub_caveat\":{PUB_CAVEAT}}"

-- The byte pin (the golden the committed `rotation-caveat-layout-v3-staged.json` equals).
#guard rotationCaveatLayoutManifest ==
  "{\"v\":\"dregg-rotation-caveat-layout-v3-staged\",\"r\":24,\"caveat_base\":43,\"count_col\":43,\"entry_base\":44,\"entry_size\":7,\"max_caveats\":4,\"manifest_size\":29,\"chain_base\":72,\"num_chain\":9,\"caveat_commit\":81,\"probe_width\":82,\"domain_registers\":0,\"domain_heap\":1,\"pub_commit\":0,\"pub_height\":1,\"pub_caveat\":2}"

end Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat
