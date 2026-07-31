/-
# Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat — the WIDENED CAVEAT OPERAND (staged).

The live in-circuit caveat operand is `SlotCaveatEntry { type_tag, slot_index: u8, params }`
(`circuit/src/effect_vm/trace.rs`) — SLOT-ONLY. The rotation makes the heap the app-state
lane (heap-keyed `StateConstraint`s landed `5e0558fdc`: `heapKey k = FieldsMap.userKey` by
`rfl`, `HeapAtom.lift`), so capability attenuation must reach HEAP KEYS before the cutover
freezes the wire (`HORIZONLOG.md` "HEAP-KEYED CAVEATS — rotation-URGENT"). THIS module is the
Lean-first design + staged emission of the widened operand, at the CONFIRMED register count
R=24 (`.docs-history-noclaude/ROTATION-CUTOVER.md` §2b, ember 2026-06-12):

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
`Poseidon2SpongeCR` hypothesis. STAGED: nothing here rides
the live v1 wire (the live `SlotCaveatEntry` manifest at PI 101..126 is untouched); the
Rust consumers are the recursion-gated IR-v2 tests + the drift guards.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationR
import Dregg2.Exec.Program
import Dregg2.Exec.RelationalCaveat

namespace Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotation (PUB_COMMIT PUB_HEIGHT canon_eq_of_modEq)
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Crypto
open Dregg2.Substrate.Heap (refSponge)
open Dregg2.Exec (HeapAtom evalHeap heapKey Value evalHeap_strictMono_iff
  evalHeap_deltaEquals_iff evalHeap_deltaBounded_iff)
open Dregg2.Exec.EffectsState (fieldOf)
open Dregg2.Exec.RelationalCaveat (RelCaveat heapFieldLteOther evalHeapRel_fieldLteOther_iff heapName)

set_option autoImplicit false

deriving instance BEq for Dregg2.Exec.HeapAtom
deriving instance BEq for Dregg2.Exec.RelationalCaveat.RelCaveat

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

/-! ## §3b — the caveat commitment EXTENDED over the DFA route-commitment carrier.

The deployed caveat region carries, past the 29 manifest felts, a 4-felt **DFA route-commitment**
(`EffectVmEmitRotationV3.C_RC_OFF` — `custom_proof_pi_commitment(DfaProofWire.public_inputs)` on a
`Witnessed{Dfa}`-gated turn, the zero sentinel otherwise). It used to ride BESIDE the commitment:
the `caveatCommit` fold stopped at the manifest, so no equation of the descriptor related the rc
columns to anything and the `withDfaRcPins` pins were `local[c] == pi[k]` with the prover choosing
BOTH sides. `UnforcedPiPins.dropUnforcedPins` correctly deleted them (they were four of the 159),
and the `CarrierWitness::Dsl` fold — which locates its slot BY that pin — then refused every
deployed leg. Restoring the pins by exempting them from the subtraction would re-add the lie; the
fix is to make the columns **actually forced**, which is what this section does.

`caveatCommitRc` extends the chain by the rc felts under the SAME `chunk31` arity-{2,4}
discipline: 4 fresh limbs chunk to `[[rc0, rc1, rc2], [rc3]]`, i.e. one (digest+3) site and one
(digest+1) site — never arity 3. So the rc carrier is read by two CHIP SITES, which graduate to
lookup constraints; the columns are then in `UnforcedPiPins.forcedCols` because a NON-pin
constraint with a row denotation reads them, not because something declared them.

⚑ `caveatCommit` and `caveatCommit_binds` are UNCHANGED. Every downstream carrier gadget whose
premise is `caveatCommit hash rowManifest = caveatCommit hash committedManifest`
(`Deos.CarrierBoundFloorGadget`, `Deos.CapacityCarrier`, `Deos.BareCohortFloorRefuse*`,
`Emit.AvailWire/WideMembers`) keeps its statement verbatim; the deployed PI pin now discharges it
through `caveatCommitRc_binds`'s FIRST leg instead of directly. -/

/-- **`caveatCommitRc`** — the caveat commitment the deployed region actually pins: the 29-limb
manifest fold, then the DFA route-commitment felts absorbed by the same `chunk31` chunking. -/
def caveatCommitRc (hash : List ℤ → ℤ) (m : RotCaveatManifest) (rc : List ℤ) : ℤ :=
  chainFrom hash (caveatCommit hash m) (chunk31 rc)

/-- **THE rc BINDING KEYSTONE** — equal extended caveat commits force equal manifests AND equal
route-commitment carriers. This is the tooth the bare `withDfaRcPins` never had: an adversary who
moves the rc carrier AND its published PIs together (the move-both attack the pin-only emit could
not catch) moves THIS commitment, so the leg no longer matches the caveat-commit PI a verifier
reconstructs from the turn's own witnessed predicates ⇒ UNSAT. Under the ONE CR floor. -/
theorem caveatCommitRc_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {m m' : RotCaveatManifest} {rc rc' : List ℤ} (hlen : rc.length = rc'.length)
    (h : caveatCommitRc hash m rc = caveatCommitRc hash m' rc') : m = m' ∧ rc = rc' := by
  unfold caveatCommitRc at h
  obtain ⟨hhead, hchunks⟩ := chainFrom_inj hash hCR
    (by rw [chunk31_length, chunk31_length, hlen]) h
  refine ⟨caveatCommit_binds hash hCR hhead, ?_⟩
  have := congrArg List.flatten hchunks
  rwa [chunk31_flatten, chunk31_flatten] at this

/-- The manifest leg alone (what every landed carrier gadget's `hbind` premise wants). -/
theorem caveatCommitRc_binds_manifest (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {m m' : RotCaveatManifest} {rc rc' : List ℤ} (hlen : rc.length = rc'.length)
    (h : caveatCommitRc hash m rc = caveatCommitRc hash m' rc') : m = m' :=
  (caveatCommitRc_binds hash hCR hlen h).1

/-- The rc leg alone — the DSL/Dfa fold's half: the published route commitment is the trace's. -/
theorem caveatCommitRc_binds_rc (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {m m' : RotCaveatManifest} {rc rc' : List ℤ} (hlen : rc.length = rc'.length)
    (h : caveatCommitRc hash m rc = caveatCommitRc hash m' rc') : rc = rc' :=
  (caveatCommitRc_binds hash hCR hlen h).2

/-- The 4-felt carrier chunks to ONE (digest+3) site and ONE (digest+1) site — arity ∈ {2,4},
never the chip-refused 3. This is the site count the emitted region grows by. -/
theorem chunk31_rc_arities (a b c d : ℤ) : chunk31 [a, b, c, d] = [[a, b, c], [d]] := rfl

#assert_axioms caveatCommitRc_binds
#assert_axioms caveatCommitRc_binds_manifest
#assert_axioms caveatCommitRc_binds_rc

-- NON-VACUITY of the rc leg, both polarities (Horner toy sponge; deployment = the audited p3
-- Poseidon2 under the same CR floor). ⚑ THE MOVE-BOTH ADVERSARY, executable: perturbing the
-- route-commitment carrier — with the manifest held FIXED, which is exactly what "move the
-- carrier and its PIs together" does — MOVES the pinned commitment. Under the bare pin-only emit
-- this pair was INDISTINGUISHABLE (the fold stopped at the manifest, so both sides were the same
-- felt); that indistinguishability was the hole.
#guard caveatCommitRc refSponge demoManifest [1, 2, 3, 4]
  != caveatCommitRc refSponge demoManifest [2, 2, 3, 4]
#guard caveatCommitRc refSponge demoManifest [1, 2, 3, 4]
  != caveatCommitRc refSponge demoManifest [1, 2, 3, 5]
-- The ZERO SENTINEL (a turn with no Dfa caveat) is distinguishable from every real rc...
#guard caveatCommitRc refSponge demoManifest [0, 0, 0, 0]
  != caveatCommitRc refSponge demoManifest [1, 2, 3, 4]
-- ...the manifest is still bound with the rc held fixed...
#guard caveatCommitRc refSponge demoManifest [1, 2, 3, 4]
  != caveatCommitRc refSponge { demoManifest with count := 1 } [1, 2, 3, 4]
-- ...and the honest recompute is stable (the positive polarity).
#guard caveatCommitRc refSponge demoManifest [1, 2, 3, 4]
  == caveatCommitRc refSponge demoManifest [1, 2, 3, 4]
-- The extension is a genuine EXTENSION: it is NOT the manifest commit wearing a new name.
#guard caveatCommitRc refSponge demoManifest [0, 0, 0, 0]
  != caveatCommit refSponge demoManifest

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
theorem rotationCaveatProbe_pins (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2Faithful permOut hash rotationCaveatProbeVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    (envAt t i).loc (stateCommitCol 24)
        = wireCommitR hash (preLimbs 24 (envAt t i).loc) ((envAt t i).loc (irootCol 24))
    ∧ (envAt t i).loc CAVEAT_COMMIT = caveatCommit hash (blockManifest (envAt t i).loc) := by
  have h := satisfied2Faithful_satisfiedVm permOut hash rotationCaveatProbeVmDescriptor
    minit mfin maddrs t (by decide) hf i hi
  exact ⟨rotationCaveatSites_pin_state hash _ h.2.1,
    rotationCaveatSites_pin_caveat hash _ h.2.1⟩

/-- The probe PUBLISHES: last row, PI 0 = the state commit, PI 1 = the height limb,
PI 2 = the caveat commit. -/
theorem rotationCaveatProbe_publishes (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2Faithful permOut hash rotationCaveatProbeVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 = t.rows.length) :
    (envAt t i).loc (stateCommitCol 24) ≡ (envAt t i).pub PUB_COMMIT [ZMOD 2013265921]
    ∧ (envAt t i).loc (committedHeightCol 24) ≡ (envAt t i).pub PUB_HEIGHT [ZMOD 2013265921]
    ∧ (envAt t i).loc CAVEAT_COMMIT ≡ (envAt t i).pub PUB_CAVEAT [ZMOD 2013265921] := by
  have h := satisfied2Faithful_satisfiedVm permOut hash rotationCaveatProbeVmDescriptor
    minit mfin maddrs t (by decide) hf i hi
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
theorem rotationCaveatProbe_binds_published (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hf : Satisfied2Faithful permOut hash rotationCaveatProbeVmDescriptor2 minit mfin maddrs t)
    (hf' : Satisfied2Faithful permOut hash rotationCaveatProbeVmDescriptor2 minit' mfin' maddrs' t')
    (i j : Nat) (hi : i < t.rows.length) (hj : j < t'.rows.length)
    (hlast : i + 1 = t.rows.length) (hlast' : j + 1 = t'.rows.length)
    (hcCanon : 0 ≤ (envAt t i).loc (stateCommitCol 24)
      ∧ (envAt t i).loc (stateCommitCol 24) < 2013265921)
    (hcCanon' : 0 ≤ (envAt t' j).loc (stateCommitCol 24)
      ∧ (envAt t' j).loc (stateCommitCol 24) < 2013265921)
    (hhCanon : 0 ≤ (envAt t i).pub PUB_HEIGHT ∧ (envAt t i).pub PUB_HEIGHT < 2013265921)
    (hhCanon' : 0 ≤ (envAt t' j).pub PUB_HEIGHT ∧ (envAt t' j).pub PUB_HEIGHT < 2013265921)
    (hkCanon : 0 ≤ (envAt t i).loc CAVEAT_COMMIT ∧ (envAt t i).loc CAVEAT_COMMIT < 2013265921)
    (hkCanon' : 0 ≤ (envAt t' j).loc CAVEAT_COMMIT ∧ (envAt t' j).loc CAVEAT_COMMIT < 2013265921)
    (hpub : (envAt t i).pub PUB_COMMIT = (envAt t' j).pub PUB_COMMIT)
    (hcav : (envAt t i).pub PUB_CAVEAT = (envAt t' j).pub PUB_CAVEAT) :
    preLimbs 24 (envAt t i).loc = preLimbs 24 (envAt t' j).loc
    ∧ (envAt t i).loc (irootCol 24) = (envAt t' j).loc (irootCol 24)
    ∧ (envAt t i).pub PUB_HEIGHT = (envAt t' j).pub PUB_HEIGHT
    ∧ blockManifest (envAt t i).loc = blockManifest (envAt t' j).loc := by
  obtain ⟨hc, hh, hk⟩ := rotationCaveatProbe_publishes permOut hash minit mfin maddrs t
    hf i hi hlast
  obtain ⟨hc', hh', hk'⟩ := rotationCaveatProbe_publishes permOut hash minit' mfin' maddrs' t'
    hf' j hj hlast'
  obtain ⟨hp, hq⟩ := rotationCaveatProbe_pins permOut hash minit mfin maddrs t hf i hi
  obtain ⟨hp', hq'⟩ := rotationCaveatProbe_pins permOut hash minit' mfin' maddrs' t'
    hf' j hj
  -- Lift the two state-commit pins to a genuine ℤ equality of the digest columns via canonicality.
  have hcCong : (envAt t i).loc (stateCommitCol 24)
      ≡ (envAt t' j).loc (stateCommitCol 24) [ZMOD 2013265921] :=
    calc (envAt t i).loc (stateCommitCol 24)
        ≡ (envAt t i).pub PUB_COMMIT [ZMOD 2013265921] := hc
      _ = (envAt t' j).pub PUB_COMMIT := hpub
      _ ≡ (envAt t' j).loc (stateCommitCol 24) [ZMOD 2013265921] := hc'.symm
  have hcEq : (envAt t i).loc (stateCommitCol 24) = (envAt t' j).loc (stateCommitCol 24) :=
    canon_eq_of_modEq hcCanon hcCanon' hcCong
  have hwire : wireCommitR hash (preLimbs 24 (envAt t i).loc) ((envAt t i).loc (irootCol 24))
      = wireCommitR hash (preLimbs 24 (envAt t' j).loc) ((envAt t' j).loc (irootCol 24)) := by
    rw [← hp, ← hp', hcEq]
  obtain ⟨hpre, hir⟩ := wireCommitR_binds hash hCR
    (by rw [preLimbs_length, preLimbs_length]) hwire
  -- Lift the two caveat-commit pins to a genuine ℤ equality via canonicality.
  have hkCong : (envAt t i).loc CAVEAT_COMMIT
      ≡ (envAt t' j).loc CAVEAT_COMMIT [ZMOD 2013265921] :=
    calc (envAt t i).loc CAVEAT_COMMIT
        ≡ (envAt t i).pub PUB_CAVEAT [ZMOD 2013265921] := hk
      _ = (envAt t' j).pub PUB_CAVEAT := hcav
      _ ≡ (envAt t' j).loc CAVEAT_COMMIT [ZMOD 2013265921] := hk'.symm
  have hkEq : (envAt t i).loc CAVEAT_COMMIT = (envAt t' j).loc CAVEAT_COMMIT :=
    canon_eq_of_modEq hkCanon hkCanon' hkCong
  have hcc : caveatCommit hash (blockManifest (envAt t i).loc)
      = caveatCommit hash (blockManifest (envAt t' j).loc) := by
    rw [← hq, ← hq', hkEq]
  refine ⟨hpre, hir, ?_, caveatCommit_binds hash hCR hcc⟩
  have hHtEq : (envAt t i).loc (committedHeightCol 24)
      = (envAt t' j).loc (committedHeightCol 24) :=
    congrArg (fun L => L.getD (committedHeightCol 24) 0) hpre
  have hHtCong : (envAt t i).pub PUB_HEIGHT ≡ (envAt t' j).pub PUB_HEIGHT [ZMOD 2013265921] :=
    calc (envAt t i).pub PUB_HEIGHT
        ≡ (envAt t i).loc (committedHeightCol 24) [ZMOD 2013265921] := hh.symm
      _ = (envAt t' j).loc (committedHeightCol 24) := hHtEq
      _ ≡ (envAt t' j).pub PUB_HEIGHT [ZMOD 2013265921] := hh'
  exact canon_eq_of_modEq hhCanon hhCanon' hHtCong

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
WRITE_ONCE 4 · IMMUTABLE 5 · MONOTONIC 6 · STRICT_MONOTONIC 7 · FIELD_DELTA 8 ·
FIELD_DELTA_BOUNDED 20). **Tag 8 (FIELD_DELTA) decodes to the EXACT `deltaEquals`** — the live
Rust re-eval is `new == old + p0` (`verify.rs` `SLOT_CAVEAT_TAG_FIELD_DELTA`, an EXACT signed
delta, not a `|Δ| ≤ p0` bound), which is exactly what `HeapAtom.deltaEquals` lifts to
(`.fieldDelta`, `Exec/Program.lean`). The prior decode named `.deltaBounded`, a SEMANTIC
MISMATCH with the tag's runtime meaning; it is corrected here. The `|Δ| ≤ p0` bounded twin
(`deltaBounded`) takes its own fresh tag FIELD_DELTA_BOUNDED 20 (`pi::SLOT_CAVEAT_TAG_FIELD_DELTA_BOUNDED`).
Tags 9..12 (monotonic-sequence, temporal-gate, sender-authorized, allowed-transitions) are
slot-shaped or multi-input and are NOT heap-liftable single-key atoms — they decode `none` on
the heap plane, matching the landed single-key lift (`5e0558fdc`'s named tail). FAIL CLOSED. -/
def tagHeapAtom (tag p0 : ℤ) : Option HeapAtom :=
  if tag = 1 then some (.equals p0)
  else if tag = 2 then some (.ge p0)
  else if tag = 3 then some (.le p0)
  else if tag = 4 then some .writeOnce
  else if tag = 5 then some .immutable
  else if tag = 6 then some .monotonic
  else if tag = 7 then some .strictMono
  else if tag = 8 then some (.deltaEquals p0)
  else if tag = 20 then some (.deltaBounded p0)
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

/-- The tag-8 (FIELD_DELTA) decode meets the landed EXACT-delta characterization: a heap-domain
FIELD_DELTA entry admits exactly when both sides are PRESENT at `heapKey k` and `new = old + d`
(`evalHeap_deltaEquals_iff`, transported verbatim). THIS is the corrected meaning — the tag's
live Rust re-eval is the exact `new == old + p0`, so the heap-plane decode is `deltaEquals`,
NOT the `|Δ| ≤ d` bounded twin. -/
theorem heapAdmits_deltaEquals_iff (k : Nat) (key d p1 p2 p3 : ℤ) (o n : Value) :
    (RotCaveatEntry.mk 8 (domainCode .heap) key d p1 p2 p3).heapAdmits k o n ↔
      ∃ a b, o.scalar (heapKey k) = some a ∧ n.scalar (heapKey k) = some b ∧ b = a + d := by
  constructor
  · intro h
    exact (evalHeap_deltaEquals_iff k d o n).mp (h (.deltaEquals d) rfl)
  · intro h a ha
    have ha' : HeapAtom.deltaEquals d = a := Option.some.inj ha
    cases ha'
    exact (evalHeap_deltaEquals_iff k d o n).mpr h

/-- The fresh tag-20 (FIELD_DELTA_BOUNDED) decode meets the landed BOUNDED-delta characterization:
a heap-domain FIELD_DELTA_BOUNDED entry admits exactly when both sides are present and
`-d ≤ new − old ≤ d` (`evalHeap_deltaBounded_iff`, transported verbatim). The `|Δ| ≤ d` twin the
tag-8 correction displaced now has its own wire home (`pi::SLOT_CAVEAT_TAG_FIELD_DELTA_BOUNDED`),
so BOTH the exact and the bounded delta remain heap-expressible — no atom is lost. -/
theorem heapAdmits_deltaBounded_iff (k : Nat) (key d p1 p2 p3 : ℤ) (o n : Value) :
    (RotCaveatEntry.mk 20 (domainCode .heap) key d p1 p2 p3).heapAdmits k o n ↔
      ∃ a b, o.scalar (heapKey k) = some a ∧ n.scalar (heapKey k) = some b ∧
        -d ≤ b - a ∧ b - a ≤ d := by
  constructor
  · intro h
    exact (evalHeap_deltaBounded_iff k d o n).mp (h (.deltaBounded d) rfl)
  · intro h a ha
    have ha' : HeapAtom.deltaBounded d = a := Option.some.inj ha
    cases ha'
    exact (evalHeap_deltaBounded_iff k d o n).mpr h

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
#assert_axioms heapAdmits_deltaEquals_iff
#assert_axioms heapAdmits_deltaBounded_iff
#assert_axioms staged_heap_caveat_bridge

-- The decode-tag alignment, executable (the Rust `SLOT_CAVEAT_TAG_*` numbers).
#guard tagHeapAtom 6 0 == some .monotonic
#guard tagHeapAtom 2 50 == some (.ge 50)
#guard tagHeapAtom 8 4 == some (.deltaEquals 4)   -- FIELD_DELTA 8 = EXACT delta (the tag-8 fix)
#guard tagHeapAtom 20 5 == some (.deltaBounded 5) -- FIELD_DELTA_BOUNDED 20 = the |Δ| ≤ d twin
#guard tagHeapAtom 0 0 == none      -- "no caveat" decodes to nothing
#guard tagHeapAtom 10 0 == none     -- TEMPORAL_GATE is not a single-key heap atom
#guard tagHeapAtom 12 0 == none     -- ALLOWED_TRANSITIONS is not a single-key heap atom

/-! ## §5b — the CROSS-KEY heap relation bridge (a `RelCaveat`, NOT a single-key `HeapAtom`).

The per-key `HeapAtom` vocabulary above reads ONE key; the cross-key relation
`record[heap key] ≤ record[heap other_key] + delta` cannot be a `HeapAtom` (each atom reads only
ITS own key). It is the landed `RelationalCaveat.heapFieldLteOther` (`Exec/RelationalCaveat.lean`
§8, `evalHeapRel_fieldLteOther_iff`), the atom that lets a Bazaar purse keep BOTH operands in the
openable heap. Its wire tag is the live `pi::SLOT_CAVEAT_TAG_HEAP_FIELD_LTE_OTHER` number (21); a
heap-domain entry carrying it packs `key = key`, `p0 = other_key`, `p1 = delta`. SAME posture as
the per-key bridge: the decode is well-defined and meets the landed admit-char; the runtime
discharge is the NAMED premise `HeapRelCaveatRuntimeDischarge` (host/scalar-evaluated, exactly like
the per-key heap caveats — the executor leg is the HORIZONLOG'd follow-up). -/

/-- Decode a heap-domain entry carrying the cross-key tag (21 = `HEAP_FIELD_LTE_OTHER`) into the
landed `RelationalCaveat.heapFieldLteOther` vocabulary: `key = e.key`, `other_key = e.p0`,
`delta = e.p1`. Any other tag decodes `none` (this is the cross-key plane; the single-key atoms
live in `tagHeapAtom`). FAIL CLOSED. Heap keys are `Nat` names (`heapName`); the wire felts are
cast via `Int.toNat` (caveat heap keys are non-negative indices). -/
def RotCaveatEntry.relCaveat? (e : RotCaveatEntry) : Option RelCaveat :=
  if e.typeTag = 21 then some (heapFieldLteOther e.key.toNat e.p0.toNat e.p1)
  else none

/-- **The runtime meaning of a cross-key heap-domain entry**: the decoded cross-key relation admits
the post-write `record` — `RelCaveat.eval` at the entry's two heap-key names (the landed
`heapFieldLteOther`). This is what the executor's heap-caveat discharge must establish for the
cross-key plane (the `RelCaveat` analog of `heapAdmits`). -/
def RotCaveatEntry.heapRelAdmits (e : RotCaveatEntry) (rec : Value) : Prop :=
  ∀ c, e.relCaveat? = some c → c.eval rec = true

/-- PROVEN — the cross-key decode meets the landed characterization: a heap-domain
HEAP_FIELD_LTE_OTHER entry (tag 21) admits exactly when `record[heap key] ≤ record[heap other_key]
+ delta` (`evalHeapRel_fieldLteOther_iff`, transported verbatim). The wire tag, the landed
cross-key atom, and the record substrate's `fieldOf` semantics meet in one statement. -/
theorem heapRelAdmits_fieldLteOther_iff (key other delta p2 p3 : ℤ) (rec : Value) :
    (RotCaveatEntry.mk 21 (domainCode .heap) key other delta p2 p3).heapRelAdmits rec ↔
      fieldOf (heapName key.toNat) rec ≤ fieldOf (heapName other.toNat) rec + delta := by
  constructor
  · intro h
    exact (evalHeapRel_fieldLteOther_iff key.toNat other.toNat delta rec).mp (h _ rfl)
  · intro h c hc
    have hc' : heapFieldLteOther key.toNat other.toNat delta = c := Option.some.inj hc
    cases hc'
    exact (evalHeapRel_fieldLteOther_iff key.toNat other.toNat delta rec).mpr h

/-- **NAMED PREMISE — `HeapRelCaveatRuntimeDischarge`** (the cross-key executor leg does not exist
yet, the SAME honest boundary as `HeapCaveatRuntimeDischarge`). An executor admission relation
`admitsTurn` discharges cross-key heap caveats iff every admitted `(manifest, record)` satisfies
each heap-domain entry's decoded cross-key relation on the post-write `record`. Host/scalar-
evaluated, like the per-key heap caveats; the HEAP cross-key leg is the HORIZONLOG'd follow-up —
until it lands, this `Prop` is the honest boundary. -/
def HeapRelCaveatRuntimeDischarge
    (admitsTurn : RotCaveatManifest → Value → Prop) : Prop :=
  ∀ (m : RotCaveatManifest) (rec : Value), admitsTurn m rec →
    ∀ (i : Fin MAX_CAVEATS),
      (m.entry i).domainTag = domainCode .heap →
      (m.entry i).heapRelAdmits rec

/-- The cross-key bridge, assembled: under the named discharge premise, a wire-bound heap-domain
entry's cross-key relation really was enforced on the admitted post-write record — the staged
operand's (domain, key, other_key, delta) and the heap cross-key `StateConstraint` semantics
connect end-to-end the moment the executor leg lands. -/
theorem staged_heap_rel_caveat_bridge
    (admitsTurn : RotCaveatManifest → Value → Prop)
    (hdis : HeapRelCaveatRuntimeDischarge admitsTurn)
    {m : RotCaveatManifest} {rec : Value} (h : admitsTurn m rec)
    (i : Fin MAX_CAVEATS)
    (hd : (m.entry i).domainTag = domainCode .heap) :
    (m.entry i).heapRelAdmits rec :=
  hdis m rec h i hd

#assert_axioms heapRelAdmits_fieldLteOther_iff
#assert_axioms staged_heap_rel_caveat_bridge

-- The cross-key decode-tag alignment (Rust `SLOT_CAVEAT_TAG_HEAP_FIELD_LTE_OTHER` = 21).
#guard (RotCaveatEntry.mk 21 (domainCode .heap) 130 131 2 0 0).relCaveat?
  == some (heapFieldLteOther 130 131 2)
#guard (RotCaveatEntry.mk 3 (domainCode .heap) 130 131 2 0 0).relCaveat? == none -- a single-key tag: no cross-key decode
-- Both polarities on a concrete record (mirror of `RelationalCaveat.lean` §8):
-- capacity `new[130] ≤ new[131] + 2`: 5 ≤ 3+2 ADMITS, 6 ≤ 3+2 REFUSES.
#guard ((heapFieldLteOther 130 131 2).eval (.record [(heapName 130, .int 5), (heapName 131, .int 3)]))
#guard ((heapFieldLteOther 130 131 2).eval (.record [(heapName 130, .int 6), (heapName 131, .int 3)])) == false
-- no-underflow `new[130] ≤ new[131]` (delta 0): equal ADMITS, over REFUSES.
#guard ((heapFieldLteOther 130 131 0).eval (.record [(heapName 130, .int 4), (heapName 131, .int 4)]))
#guard ((heapFieldLteOther 130 131 0).eval (.record [(heapName 130, .int 5), (heapName 131, .int 4)])) == false

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
