/-
# Dregg2.Circuit.Emit.EffectVmEmitUMemCohort — the per-effect COHORT descriptors in
UMEM-FORM (`UMemOp` reconciliations), EMITTED + proven + byte-pinned, STAGED.

The rotation-flip plan's deployed-plumbing piece #1 (the flag-day audit's named missing seam).
`circuit/tests/effect_vm_umem_cohort.rs` (`a2217919`) demonstrated the umem-form SHAPE in
isolation — a Rust test that BUILDS the descriptor at run time, not a verified emitter. THIS
module is the verified Lean EMITTER: each deployed cohort effect's state TOUCH is emitted as a
`UMemOp` read/write against the universal `Domain × κ` boundary table — the per-cell `(domain,
key) → value` cells the Rank-1 codecs (`Dregg2.Crypto.UMemCodec`) address — REPLACING the
per-map `MapOp` reconciliation against a Merkle root.

The descriptor shape is the faithful Lean twin of the Rust `build_umem_form`: base columns
`0 key · 1 present · 2 value · 3 prev_present · 4 prev_value · 5 prev_serial`, the `umemOp`
guarded by the per-domain indicator column `6`, against the touched domain. The grammar is the
deployed `DescriptorIR2.umemOp` (the same one `demoU` byte-pins); the staged emit just instances
it per cohort effect.

  * **§1 the cohort** — `setFieldUMem` · `setHeapUMem` · `grantUMem` · `attenuateUMem` ·
    `transferBalanceUMem` · `mintBalanceUMem` · `burnBalanceUMem` (the heap-domain economic
    scalar lane — transfer/mint/burn, distinct selectors over the same `Balance` register) ·
    `revokeUMem` (the caps-plane DELETE write — a revoked slot's removal, its ghost ZERO leaf
    kept by the canonical `cap_root` per the cell-side tombstone reconciliation) ·
    `nullifierFreshUMem` (the absent-cell `none`-read freshness leg). The per-cell domain map
    matches `turn/src/umem.rs`: Field/Heap/Balance/Nonce → `heap` (1), CapSlot → `caps` (2),
    nullifiers → `nullifiers` (3). The §2 survival + §3 injectivity keystones are PARAMETRIC over
    `umemCohortDesc nm dom k`, so they fire verbatim at every cohort member — the supply lane and
    the revoke delete included.

  * **§2 rotV3-style SURVIVAL** — the emitted descriptor BINDS THE PUBLISHED STATE. For each
    cohort member, a `Satisfied2U` witness's claimed final image is FORCED to the genuine fold of
    the gathered universal-memory log (`satisfied2U_pins_final` — the post-state is not
    prover-chosen), and the touched map domain's committed boundary root EQUALS the derived
    boundary root at BOTH endpoints (`satisfied2U_boundary_root` / `satisfied2U_init_root`). This
    is the umem-form analogue of the rotation probe's `rotationProbe_commit_binds_published`:
    publishing forces the whole state. Grounded NON-VACUOUSLY by a concrete worked witness
    (`setFieldUMem_satisfied`) on which the keystone fires end-to-end.

  * **§3 the UMemCodec INJECTIVITY** — the umem addresses are FAITHFUL. The heap/field-plane
    address codec `uaddrEnc = hash[domainTag d, coll, key]` is injective under the one named CR
    floor (`umemCohort_addr_faithful` = `UMemCodec.uaddrEnc_injective`); the caps-plane boundary
    root binds its cap cells (`umemCohort_cap_root_binds` = `UMemCodec.capRoot_injective`) — a
    prover cannot keep the published cap root while tampering any granted/attenuated cap edge.

  * **§4 the staged wire artifacts** — every cohort descriptor's `emitVmJson2` is byte-pinned
    (`#guard`, the committed-descriptor discipline) and gathered into `umemCohortRegistry`. The
    driver (`EmitUMemCohort.lean`) writes the staged set
    `circuit/descriptors/umem-cohort-v1-staged-registry.tsv` — a NEW staged set BESIDE the
    deployed v1, NOT a replacement.

## A STAGED v1-COHORT LANE (distinct from the deployed WIDE+UMEM weld)

This module emits the v1-cohort `umem-cohort-v1-staged-registry.tsv` — a STAGED alternative set,
distinct from the deployed `rotation-wide-umem-welded-registry-staged.tsv` that the umem VK EPOCH
(G4) made the deployed default. The G4 flip welds the universal-memory leg onto the WIDE rotated
cohort and the deployed executor now REQUIRES it for a single-cohort sovereign turn; THIS v1-cohort
registry is a separate emit lane whose own routing flip is NOT done here. The grammar these emit is
the already-deployed `umemOp` shape (`demoU`'s wire golden), so the Rust IR-2 interpreter ALREADY
parses them — only the registry routing (which descriptor a selector resolves to) would be its flip.
`umem_witness_enabled` (the executor-state OBSERVATION bridge) is a separate toggle, untouched here.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; crypto enters only as the named
`Poseidon2SpongeCR` hypothesis (via `UMemCodec`), never as an axiom.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Crypto.UMemCodec

namespace Dregg2.Circuit.Emit.EffectVmEmitUMemCohort

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto.UniversalMemory (Domain UAddr)
open Dregg2.Crypto.MemoryChecking (Kind step)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

set_option autoImplicit false

/-! ## §1 — the cohort descriptors (umem-form, the Rust `build_umem_form` twin). -/

/-- One umem-form cohort descriptor: a single `UMemOp` against `dom` with kind `k`, over the
base columns `0 key · 1 present · 2 value · 3 prev_present · 4 prev_value · 5 prev_serial`,
guarded by the per-domain indicator column `6`. Width 7; the umemory + umem_boundary tables
declared (the deployed umem grammar). -/
def umemCohortDesc (nm : String) (dom : Domain) (k : Kind) : EffectVmDescriptor2 :=
  { name        := nm
  , traceWidth  := 7
  , piCount     := 0
  , tables      := [mainTableDef 7, umemTableDef, umemBoundaryTableDef]
  , constraints := [ .umemOp ⟨.var 6, dom, .var 0, .var 1, .var 2, .var 3, .var 4, .var 5, k⟩ ]
  , hashSites   := []
  , ranges      := [] }

/-- SET-FIELD on the committed user-field map (slot ≥ 16) → a `heap`-domain write (the per-map
form is the `fields_root` map-write). -/
def setFieldUMem : EffectVmDescriptor2 :=
  umemCohortDesc "dregg-effectvm-umem-set-field-v1-staged" .heap .write

/-- SET-HEAP on the committed `(collection, key) → value` heap → a `heap`-domain write (the
per-map form is the `heap_root` map-write). -/
def setHeapUMem : EffectVmDescriptor2 :=
  umemCohortDesc "dregg-effectvm-umem-set-heap-v1-staged" .heap .write

/-- GRANT a capability → a `caps`-domain write (a fresh-key insert; the per-map form is the
`cap_root` sorted-insert). -/
def grantUMem : EffectVmDescriptor2 :=
  umemCohortDesc "dregg-effectvm-umem-grant-v1-staged" .caps .write

/-- ATTENUATE an existing capability in place → a `caps`-domain write (an existing-key update;
the per-map form is the `cap_root` value-update). -/
def attenuateUMem : EffectVmDescriptor2 :=
  umemCohortDesc "dregg-effectvm-umem-attenuate-v1-staged" .caps .write

/-- TRANSFER's economic touch is the scalar `Balance` register, which lives in the `heap` domain
(`turn/src/umem.rs`: Balance/Nonce → `heap`) — a `heap`-domain scalar write. -/
def transferBalanceUMem : EffectVmDescriptor2 :=
  umemCohortDesc "dregg-effectvm-umem-transfer-balance-v1-staged" .heap .write

/-- MINT's economic touch is the SAME scalar `Balance` register (`heap` domain) — a credit is a
`heap`-domain scalar write, the cohort-form twin of the deployed `Effect::Mint` per-asset-well
supply credit. A DISTINCT selector from `transferBalanceUMem`: same balance-lane shape, its own
descriptor name (the supply lane is not a transfer). -/
def mintBalanceUMem : EffectVmDescriptor2 :=
  umemCohortDesc "dregg-effectvm-umem-mint-balance-v1-staged" .heap .write

/-- BURN's economic touch is the SAME scalar `Balance` register (`heap` domain) — a debit is a
`heap`-domain scalar write (the supply DELETE on the scalar lane; the balance moves DOWN, the
cell record stays). A DISTINCT selector from `mint`/`transfer`: the supply lane's own descriptor
name. -/
def burnBalanceUMem : EffectVmDescriptor2 :=
  umemCohortDesc "dregg-effectvm-umem-burn-balance-v1-staged" .heap .write

/-- REVOKE a capability → the caps-plane DELETE write: the revoked slot's live cell is removed
(its ghost ZERO leaf kept by the canonical `cap_root`; the cell-side tombstone reconciliation,
`turn/src/umem.rs`'s `CapTombstone` plane). At the umem grammar a delete is a `write` of the
absent/zero cell over the claimed prior — still a single `caps`-domain `umemOp .write` over the
base columns, distinct from `grant` (fresh insert) and `attenuate` (in-place narrow) by its own
selector. -/
def revokeUMem : EffectVmDescriptor2 :=
  umemCohortDesc "dregg-effectvm-umem-revoke-v1-staged" .caps .write

/-- The `absent` map-op → umem `none`-read: a `nullifiers`-domain READ returning `none` against
an absent boundary cell — Merkle-path-free freshness (`nullifier_fresh_sound`). -/
def nullifierFreshUMem : EffectVmDescriptor2 :=
  umemCohortDesc "dregg-effectvm-umem-nullifier-fresh-v1-staged" .nullifiers .read

/-- The staged umem-form cohort registry: `(lean_def_name, descriptor)`, the source of the
staged TSV the driver emits. NEW staged set — beside the deployed v1, not a replacement. -/
def umemCohortRegistry : List (String × EffectVmDescriptor2) :=
  [ ("setFieldUMem",        setFieldUMem)
  , ("setHeapUMem",         setHeapUMem)
  , ("grantUMem",           grantUMem)
  , ("attenuateUMem",       attenuateUMem)
  , ("transferBalanceUMem", transferBalanceUMem)
  , ("mintBalanceUMem",     mintBalanceUMem)
  , ("burnBalanceUMem",     burnBalanceUMem)
  , ("revokeUMem",          revokeUMem)
  , ("nullifierFreshUMem",  nullifierFreshUMem) ]

-- STRUCTURAL pins: each cohort descriptor declares EXACTLY its one umemOp, in the named domain,
-- over width 7. The umem-form gather collects exactly this cohort touch.
#guard (umemOpsOf setFieldUMem).length == 1
#guard (umemOpsOf grantUMem).length == 1
#guard (umemOpsOf mintBalanceUMem).length == 1
#guard (umemOpsOf burnBalanceUMem).length == 1
#guard (umemOpsOf revokeUMem).length == 1
#guard (umemOpsOf nullifierFreshUMem).length == 1
#guard umemCohortRegistry.length == 9
#guard setFieldUMem.traceWidth == 7
-- The staged set is DISTINCT from the deployed v1 (no name collides with the per-map registry):
-- every staged name carries the `umem`/`-staged` markers the v1 names never carry.
#guard umemCohortRegistry.all (fun e => "dregg-effectvm-umem-".isPrefixOf e.2.name)
#guard umemCohortRegistry.all (fun e => e.2.name.endsWith "-v1-staged")

/-! ## §2 — rotV3-style SURVIVAL: the emitted descriptor BINDS THE PUBLISHED STATE.

For each cohort member, a `Satisfied2U` witness forces its claimed final image to the genuine
fold of the gathered universal-memory log, and derives the touched map domain's committed
boundary root from that forced column — the umem-form analogue of the rotation probe's
`rotationProbe_commit_binds_published`. These are thin specializations of the deployed
`DescriptorIR2` keystones at each staged descriptor; the descriptor-specific content is the
single guarded umemOp whose gather these keystones range over. Grounded non-vacuously in §2b. -/

/-- **SURVIVAL (the final image is FORCED).** Every declared universal address's claimed final
value equals the genuine fold of the gathered log — the published post-state is not
prover-chosen. (`satisfied2U_pins_final` at the cohort descriptor.) -/
theorem umemCohort_pins_final (nm : String) (dom : Domain) (k : Kind)
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {uinit : UAddr ℤ → Option ℤ} {ufin : UAddr ℤ → Option ℤ × Nat}
    {uaddrs : List (UAddr ℤ)} {t : VmTrace}
    (h : Satisfied2U hash (umemCohortDesc nm dom k) minit mfin maddrs uinit ufin uaddrs t) :
    ∀ a ∈ uaddrs, (ufin a).1
      = ((umemLog (umemCohortDesc nm dom k) t).foldl step uinit) a :=
  satisfied2U_pins_final hash (umemCohortDesc nm dom k) h

/-- **SURVIVAL (the committed POST root is the derived boundary root).** For the touched map
domain `dm`: the deployed per-map root EQUALS the sorted-Poseidon2 root of the boundary view
derived from the forced final column. The umem reconciliation moves exactly what the per-map
`MapOp` reconciliation moves. (`satisfied2U_boundary_root` at the cohort descriptor.) -/
theorem umemCohort_post_root (nm : String) (dom : Domain) (k : Kind)
    (hash : List ℤ → ℤ) (dm : Domain)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {uinit : UAddr ℤ → Option ℤ} {ufin : UAddr ℤ → Option ℤ × Nat}
    {uaddrs : List (UAddr ℤ)} {t : VmTrace}
    {hmap : Dregg2.Substrate.Heap.FeltHeap} {as : List ℤ}
    (h : Satisfied2U hash (umemCohortDesc nm dom k) minit mfin maddrs uinit ufin uaddrs t)
    (hs : Dregg2.Substrate.Heap.SortedKeys hmap) (has : as.Pairwise (· < ·))
    (hda : ∀ a ∈ as, (dm, a) ∈ uaddrs)
    (hsem : ∀ a : ℤ, Dregg2.Substrate.Heap.get hmap a
      = if a ∈ as then ((umemLog (umemCohortDesc nm dom k) t).foldl step uinit) (dm, a)
        else none) :
    Dregg2.Substrate.Heap.root hash hmap
      = Dregg2.Substrate.Heap.root hash
          (Dregg2.Crypto.UniversalMemory.boundaryCells (fun a => (ufin (dm, a)).1) as) :=
  satisfied2U_boundary_root hash (umemCohortDesc nm dom k) dm h hs has hda hsem

/-- **SURVIVAL (the committed PRE root is bound to the declared init image).** The companion at
the *init* column: the committed pre-state root EQUALS the derived boundary root of the declared
init image — pinning that root forces the init image to BE the committed pre-state (a tampered
init cannot keep the published root). The umem reconciliation's init anchor.
(`satisfied2U_init_root` at the cohort descriptor.) -/
theorem umemCohort_pre_root (nm : String) (dom : Domain) (k : Kind)
    (hash : List ℤ → ℤ) (dm : Domain)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {uinit : UAddr ℤ → Option ℤ} {ufin : UAddr ℤ → Option ℤ × Nat}
    {uaddrs : List (UAddr ℤ)} {t : VmTrace}
    {hpre : Dregg2.Substrate.Heap.FeltHeap} {as : List ℤ}
    (h : Satisfied2U hash (umemCohortDesc nm dom k) minit mfin maddrs uinit ufin uaddrs t)
    (hs : Dregg2.Substrate.Heap.SortedKeys hpre) (has : as.Pairwise (· < ·))
    (hsem : ∀ a : ℤ, Dregg2.Substrate.Heap.get hpre a
      = if a ∈ as then uinit (dm, a) else none) :
    Dregg2.Substrate.Heap.root hash hpre
      = Dregg2.Substrate.Heap.root hash
          (Dregg2.Crypto.UniversalMemory.boundaryCells (fun a => uinit (dm, a)) as) :=
  satisfied2U_init_root hash (umemCohortDesc nm dom k) dm h hs has hsem

/-! ### §2b — the SURVIVAL keystone fired end-to-end (non-vacuity).

A concrete worked `Satisfied2U` witness for `setFieldUMem`: one main row writing field key 7 ←
42 (prev absent) in the `heap` domain, the universal boundary starting absent. The survival
keystone fires on it — the forced final image carries `some 42` at `(heap, 7)`, no Merkle path,
every leg discharged concretely. Nothing in §2 is vacuous. -/

/-- The worked main row: key 7 (col 0), present 1 (col 1), value 42 (col 2), prev absent
(cols 3/4/5 = 0), guard on (col 6). -/
def sfRow : Assignment := fun i =>
  if i = 0 then 7 else if i = 1 then 1 else if i = 2 then 42 else if i = 6 then 1 else 0

/-- The worked witness: one main row; the umem table carries exactly the gathered log's row. -/
def sfTrace : VmTrace :=
  { rows := [sfRow], pub := zeroAsg
  , tf := fun tid => match tid with
      | .custom 1 => [[1, 7, 1, 42, 0, 0, 0, 1]]
      | _ => [] }

/-- The worked universal boundary: everything starts absent. -/
def sfUinit : UAddr ℤ → Option ℤ := fun _ => none

/-- The worked final claims: field `(heap, 7)` ← `some 42` at serial 1. -/
def sfUfin : UAddr ℤ → Option ℤ × Nat := fun a =>
  if a = (Domain.heap, 7) then (some 42, 1) else (none, 0)

/-- The worked declared universal addresses. -/
def sfUaddrs : List (UAddr ℤ) := [(Domain.heap, 7)]

-- The gathered umem log balances (ONE check), is disciplined, and is consistent (the executable
-- shadow of the survival keystone, AT the IR — the umem-form touch reconciles).
#guard decide (Dregg2.Crypto.MemoryChecking.Disciplined (umemLog setFieldUMem sfTrace))
#guard decide (Dregg2.Crypto.MemoryChecking.MemCheck sfUinit sfUfin sfUaddrs
  (umemLog setFieldUMem sfTrace))
#guard decide (Dregg2.Crypto.MemoryChecking.Consistent sfUinit (umemLog setFieldUMem sfTrace))
-- The forced fold carries the published value at the touched address (the survival payoff).
#guard ((umemLog setFieldUMem sfTrace).foldl step sfUinit) (Domain.heap, 7) == some 42

/-- The worked `Satisfied2U` witness, fully constructed (the row constraint is the global-content
umemOp ⇒ row-locally `True`; the multiset legs are `decide`-level; the tables are faithful by
`rfl`). -/
theorem setFieldUMem_satisfied :
    Satisfied2U (fun _ => 0) setFieldUMem (fun _ => 0) (fun _ => ((0 : ℤ), 0)) []
      sfUinit sfUfin sfUaddrs sfTrace := by
  refine ⟨⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints: the one constraint is the umemOp (global content ⇒ row-locally True)
    intro i hi c hc
    simp only [setFieldUMem, umemCohortDesc, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc; trivial
  · intro i hi; trivial          -- rowHashes: none
  · intro i hi r hr; simp [setFieldUMem, umemCohortDesc] at hr   -- rowRanges: none
  · intro op hop                  -- memClosed: the flat memory log is empty
    rw [show memLog setFieldUMem sfTrace = [] from rfl] at hop; cases hop
  · rw [show memLog setFieldUMem sfTrace = [] from rfl]; exact by decide   -- memDisciplined
  · rw [show memLog setFieldUMem sfTrace = [] from rfl]; exact memCheck_nil _ _  -- memBalanced
  · rfl                           -- memTableFaithful
  · rfl                           -- mapTableFaithful
  · exact by decide               -- umemAddrsNodup
  · exact by decide               -- umemClosed
  · exact by decide               -- umemDisciplined
  · exact by decide               -- umemBalanced
  · exact by decide               -- umemNullifierInsertOnly (heap domain ⇒ vacuous)
  · rfl                           -- umemTableFaithful

/-- **THE SURVIVAL KEYSTONE, FIRED.** On the worked witness the claimed final image is FORCED to
the genuine fold — `setFieldUMem` binds the published field value (`some 42` at `(heap, 7)`),
end-to-end, concretely. The umem-form descriptor binds the published state. -/
theorem setFieldUMem_survives_concrete :
    ∀ a ∈ sfUaddrs, (sfUfin a).1 = ((umemLog setFieldUMem sfTrace).foldl step sfUinit) a :=
  satisfied2U_pins_final (fun _ => 0) setFieldUMem setFieldUMem_satisfied

/-! ## §3 — the UMemCodec INJECTIVITY: the umem addresses / cap cells are FAITHFUL. -/

/-- **The heap/field-plane address codec is FAITHFUL.** Under the one named CR floor, equal
encoded `uaddrEnc` addresses force the same domain, collection, and key — the umem-form's
`(domain, key)` address realizes the abstract triple injectively (the planes the cohort touches
do not alias). (`UMemCodec.uaddrEnc_injective`.) -/
theorem umemCohort_addr_faithful (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {d d' : Domain} {coll key coll' key' : ℤ}
    (h : Dregg2.Crypto.UMemCodec.uaddrEnc hash d coll key
      = Dregg2.Crypto.UMemCodec.uaddrEnc hash d' coll' key') :
    d = d' ∧ coll = coll' ∧ key = key' :=
  Dregg2.Crypto.UMemCodec.uaddrEnc_injective hash hCR h

/-- **The caps-plane boundary root BINDS its cap cells.** Under the one named CR floor, two cap
cell lists with equal boundary roots are equal — a prover cannot keep the published cap root
(the `caps`-domain boundary commitment the `grantUMem` / `attenuateUMem` touches reconcile
against) while tampering ANY granted/attenuated cap edge. (`UMemCodec.capRoot_injective`.) -/
theorem umemCohort_cap_root_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {l₁ l₂ : List Dregg2.Crypto.UMemCodec.CapEdge}
    (h : Dregg2.Crypto.UMemCodec.rootWith (Dregg2.Crypto.UMemCodec.capLeafOf hash) hash l₁
      = Dregg2.Crypto.UMemCodec.rootWith (Dregg2.Crypto.UMemCodec.capLeafOf hash) hash l₂) :
    l₁ = l₂ :=
  Dregg2.Crypto.UMemCodec.capRoot_injective hash hCR h

/-! ## §4 — the staged wire artifacts (byte-pinned descriptor JSON).

Each `#guard` is the committed-descriptor discipline (the sha-pinned twin): the emitted JSON
CANNOT drift from the verified descriptor. The driver `EmitUMemCohort.lean` writes these exact
bytes to `circuit/descriptors/umem-cohort-v1-staged-registry.tsv`. -/

#guard emitVmJson2 setFieldUMem ==
  "{\"name\":\"dregg-effectvm-umem-set-field-v1-staged\",\"ir\":2,\"trace_width\":7,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":7,\"sem\":\"main\"},{\"id\":6,\"name\":\"umemory\",\"arity\":8,\"sem\":\"umemory\"},{\"id\":7,\"name\":\"umem_boundary\",\"arity\":7,\"sem\":\"umem_boundary\"}],\"constraints\":[{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":1,\"guard\":{\"t\":\"var\",\"v\":6},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":2},\"prev_present\":{\"t\":\"var\",\"v\":3},\"prev_value\":{\"t\":\"var\",\"v\":4},\"prev_serial\":{\"t\":\"var\",\"v\":5}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 setHeapUMem ==
  "{\"name\":\"dregg-effectvm-umem-set-heap-v1-staged\",\"ir\":2,\"trace_width\":7,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":7,\"sem\":\"main\"},{\"id\":6,\"name\":\"umemory\",\"arity\":8,\"sem\":\"umemory\"},{\"id\":7,\"name\":\"umem_boundary\",\"arity\":7,\"sem\":\"umem_boundary\"}],\"constraints\":[{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":1,\"guard\":{\"t\":\"var\",\"v\":6},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":2},\"prev_present\":{\"t\":\"var\",\"v\":3},\"prev_value\":{\"t\":\"var\",\"v\":4},\"prev_serial\":{\"t\":\"var\",\"v\":5}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 grantUMem ==
  "{\"name\":\"dregg-effectvm-umem-grant-v1-staged\",\"ir\":2,\"trace_width\":7,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":7,\"sem\":\"main\"},{\"id\":6,\"name\":\"umemory\",\"arity\":8,\"sem\":\"umemory\"},{\"id\":7,\"name\":\"umem_boundary\",\"arity\":7,\"sem\":\"umem_boundary\"}],\"constraints\":[{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":2,\"guard\":{\"t\":\"var\",\"v\":6},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":2},\"prev_present\":{\"t\":\"var\",\"v\":3},\"prev_value\":{\"t\":\"var\",\"v\":4},\"prev_serial\":{\"t\":\"var\",\"v\":5}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 attenuateUMem ==
  "{\"name\":\"dregg-effectvm-umem-attenuate-v1-staged\",\"ir\":2,\"trace_width\":7,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":7,\"sem\":\"main\"},{\"id\":6,\"name\":\"umemory\",\"arity\":8,\"sem\":\"umemory\"},{\"id\":7,\"name\":\"umem_boundary\",\"arity\":7,\"sem\":\"umem_boundary\"}],\"constraints\":[{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":2,\"guard\":{\"t\":\"var\",\"v\":6},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":2},\"prev_present\":{\"t\":\"var\",\"v\":3},\"prev_value\":{\"t\":\"var\",\"v\":4},\"prev_serial\":{\"t\":\"var\",\"v\":5}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 transferBalanceUMem ==
  "{\"name\":\"dregg-effectvm-umem-transfer-balance-v1-staged\",\"ir\":2,\"trace_width\":7,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":7,\"sem\":\"main\"},{\"id\":6,\"name\":\"umemory\",\"arity\":8,\"sem\":\"umemory\"},{\"id\":7,\"name\":\"umem_boundary\",\"arity\":7,\"sem\":\"umem_boundary\"}],\"constraints\":[{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":1,\"guard\":{\"t\":\"var\",\"v\":6},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":2},\"prev_present\":{\"t\":\"var\",\"v\":3},\"prev_value\":{\"t\":\"var\",\"v\":4},\"prev_serial\":{\"t\":\"var\",\"v\":5}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 mintBalanceUMem ==
  "{\"name\":\"dregg-effectvm-umem-mint-balance-v1-staged\",\"ir\":2,\"trace_width\":7,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":7,\"sem\":\"main\"},{\"id\":6,\"name\":\"umemory\",\"arity\":8,\"sem\":\"umemory\"},{\"id\":7,\"name\":\"umem_boundary\",\"arity\":7,\"sem\":\"umem_boundary\"}],\"constraints\":[{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":1,\"guard\":{\"t\":\"var\",\"v\":6},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":2},\"prev_present\":{\"t\":\"var\",\"v\":3},\"prev_value\":{\"t\":\"var\",\"v\":4},\"prev_serial\":{\"t\":\"var\",\"v\":5}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 burnBalanceUMem ==
  "{\"name\":\"dregg-effectvm-umem-burn-balance-v1-staged\",\"ir\":2,\"trace_width\":7,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":7,\"sem\":\"main\"},{\"id\":6,\"name\":\"umemory\",\"arity\":8,\"sem\":\"umemory\"},{\"id\":7,\"name\":\"umem_boundary\",\"arity\":7,\"sem\":\"umem_boundary\"}],\"constraints\":[{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":1,\"guard\":{\"t\":\"var\",\"v\":6},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":2},\"prev_present\":{\"t\":\"var\",\"v\":3},\"prev_value\":{\"t\":\"var\",\"v\":4},\"prev_serial\":{\"t\":\"var\",\"v\":5}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 revokeUMem ==
  "{\"name\":\"dregg-effectvm-umem-revoke-v1-staged\",\"ir\":2,\"trace_width\":7,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":7,\"sem\":\"main\"},{\"id\":6,\"name\":\"umemory\",\"arity\":8,\"sem\":\"umemory\"},{\"id\":7,\"name\":\"umem_boundary\",\"arity\":7,\"sem\":\"umem_boundary\"}],\"constraints\":[{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":2,\"guard\":{\"t\":\"var\",\"v\":6},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":2},\"prev_present\":{\"t\":\"var\",\"v\":3},\"prev_value\":{\"t\":\"var\",\"v\":4},\"prev_serial\":{\"t\":\"var\",\"v\":5}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 nullifierFreshUMem ==
  "{\"name\":\"dregg-effectvm-umem-nullifier-fresh-v1-staged\",\"ir\":2,\"trace_width\":7,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":7,\"sem\":\"main\"},{\"id\":6,\"name\":\"umemory\",\"arity\":8,\"sem\":\"umemory\"},{\"id\":7,\"name\":\"umem_boundary\",\"arity\":7,\"sem\":\"umem_boundary\"}],\"constraints\":[{\"t\":\"umem_op\",\"kind\":\"read\",\"domain\":3,\"guard\":{\"t\":\"var\",\"v\":6},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":2},\"prev_present\":{\"t\":\"var\",\"v\":3},\"prev_value\":{\"t\":\"var\",\"v\":4},\"prev_serial\":{\"t\":\"var\",\"v\":5}}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## Axiom-hygiene pins. -/

#assert_axioms umemCohort_pins_final
#assert_axioms umemCohort_post_root
#assert_axioms umemCohort_pre_root
#assert_axioms setFieldUMem_satisfied
#assert_axioms setFieldUMem_survives_concrete
#assert_axioms umemCohort_addr_faithful
#assert_axioms umemCohort_cap_root_binds

end Dregg2.Circuit.Emit.EffectVmEmitUMemCohort
