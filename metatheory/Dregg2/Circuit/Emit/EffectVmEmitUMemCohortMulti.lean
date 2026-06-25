/-
# Dregg2.Circuit.Emit.EffectVmEmitUMemCohortMulti — the MULTI-DOMAIN per-effect COHORT descriptors
in UMEM-FORM (`UMemOp` reconciliations, one op per touched domain), EMITTED + proven + byte-pinned,
STAGED.

The completion of the umem cohort to the FULL effect set. The single-domain cohort
(`EffectVmEmitUMemCohort.lean`, width-7, ONE `umemOp`) covers every effect whose state touch lives
in ONE domain; but some deployed effects touch MORE THAN ONE domain in a single effect — the
NOTE/BRIDGE economic verbs combine a `nullifiers`-domain insert (the spend/mint freshness gate)
with a `heap`-domain balance write (the credit). The single-domain cohort FAILS CLOSED on such a
leg (`turn/src/umem.rs::umem_cohort_proving_inputs_from`, the named `c67796d8` seam: "multi-domain
within an effect → fails closed, stays on per-map until its own cohort design"). THIS module is
that cohort design: a FIXED per-effect descriptor with ONE guarded `umemOp` PER touched domain.

The shape is the faithful Lean twin of the deployed producer's variable-width form
(`turn/src/umem.rs::umem_proving_inputs_from`, width `6 + #domains`, guard column `6 + i` for the
`i`-th domain in sorted-domain-code order) — but with the domain SET BAKED IN per effect, so it is
a FIXED descriptor that can back ONE committed VK (the variable producer form cannot — `c67796d8`).
The production prover ALREADY proves this exact multi-domain shape
(`circuit/tests/effect_vm_umem_real_turn.rs` proves a real turn touching heap·caps·nullifiers·index
through `prove_vm_descriptor2_umem`); this module emits the FIXED, byte-pinned, proven twin.

  * **§1 the multi-domain cohort** — `umemCohortDesc2 nm d₀ k₀ d₁ k₁` = the width-8 two-domain
    shape (base columns `0 key · 1 present · 2 value · 3 prev_present · 4 prev_value · 5 prev_serial`
    shared, guard column `6` for domain `d₀`, guard column `7` for domain `d₁`, ONE `umemOp` each).
    The deployed multi-domain members are `noteSpendUMem` and `bridgeMintUMem`, BOTH touching
    `{heap (balance credit), nullifiers (freshness insert)}` — the producer sorts domain codes
    (`heap`=1 < `nullifiers`=3), so `heap` rides guard column 6 and `nullifiers` guard column 7,
    each a `write` (a fresh nullifier insert is a write of the present cell over an absent prior;
    the `umemNullifierInsertOnly` leg is satisfied — the inserted value is never `none`). The
    construction generalizes to N domains (one guarded `umemOp` per domain at column `6 + i`); the
    deployed reality is exactly the width-8 two-domain case.

  * **§2 rotV3-style SURVIVAL — PER DOMAIN** — the emitted descriptor BINDS THE PUBLISHED STATE in
    EACH touched domain. `noteSpend_pins_final` forces the claimed final image of EVERY declared
    universal address (across both domains) to the genuine fold of the gathered log; and
    `noteSpend_post_root` / `noteSpend_pre_root` are PARAMETRIC over the touched domain `dm`, so
    they fire SEPARATELY at the `heap` plane (the balance) AND the `nullifiers` plane (the
    freshness leg) — each domain's committed boundary root equals its derived boundary root. These
    are thin specializations of the descriptor-general `Satisfied2U` keystones, which already range
    over the whole gathered umem log regardless of the constraint count. Grounded NON-VACUOUSLY by
    a concrete two-row worked witness (§2b).

  * **§2b cross-domain binding — THE HONEST SCOPE.** The multi-domain cohort leg reconciles each
    touched domain's boundary FAITHFULLY and INDEPENDENTLY (per-domain survival above). It does NOT
    by itself bind the CROSS-domain economic invariant (e.g. balance-credit == spent-note-value) —
    that linkage is NOT a memory-reconciliation property; it rides the effect's own AIR gates in
    the rotated descriptor (the weld, `926124e6`, preserves the WHOLE rotated constraint set
    alongside the umem leg). So the multi-domain extension is exactly as sound as the single-domain
    one PER DOMAIN; the economic cross-binding is a separate, already-deployed concern carried by
    the welded rotated gates — the cohort leg neither weakens nor claims it. This is the same
    division as the single-domain cohort, made explicit because two domains now ride one descriptor.

  * **§3 the UMemCodec INJECTIVITY** — the multi-domain addresses are FAITHFUL across planes. The
    heap/nullifier-plane address codec is injective under the one named CR floor
    (`noteSpend_addr_faithful` = `UMemCodec.uaddrEnc_injective`), so the `heap` balance cell and the
    `nullifiers` freshness cell can never alias — the two domains the multi-domain descriptor
    reconciles are genuinely disjoint.

  * **§4 the staged wire artifacts** — every multi-domain cohort descriptor's `emitVmJson2` is
    byte-pinned (`#guard`) and gathered into `umemCohortMultiRegistry`. The driver
    (`EmitUMemCohortMulti.lean`) writes the staged set
    `circuit/descriptors/umem-cohort-multidomain-v1-staged-registry.tsv` — a NEW staged set BESIDE
    the single-domain `umem-cohort-v1-staged-registry.tsv` and the deployed per-map v1.

## VK-RISK-FREE

STAGED beside the deployed + single-domain-staged registries: a new registry constant, NO VK bump,
nothing on the live wire. `umem_witness_enabled` is untouched. The grammar is the already-deployed
`umemOp` shape (`demoU`'s wire golden), so the Rust IR-2 interpreter ALREADY parses these; only the
registry routing is the flip, and that flip is NOT done here.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; crypto enters only as the named
`Poseidon2SpongeCR` hypothesis (via `UMemCodec`), never as an axiom.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Crypto.UMemCodec

namespace Dregg2.Circuit.Emit.EffectVmEmitUMemCohortMulti

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto.UniversalMemory (Domain UAddr)
open Dregg2.Crypto.MemoryChecking (Kind step)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

set_option autoImplicit false

/-! ## §1 — the multi-domain cohort descriptors (umem-form, the producer's fixed twin). -/

/-- A TWO-domain umem-form cohort descriptor: TWO `UMemOp`s sharing the base columns
`0 key · 1 present · 2 value · 3 prev_present · 4 prev_value · 5 prev_serial`, the first guarded by
column `6` against domain `d₀` with kind `k₀`, the second guarded by column `7` against domain `d₁`
with kind `k₁`. Width 8; the umemory + umem_boundary tables declared. This is the producer's
sorted-domain form (`turn/src/umem.rs`) with the domain set BAKED IN — a FIXED shape that backs one
committed VK. (The N-domain generalization is one guarded `umemOp` per domain at column `6 + i`; the
deployed multi-domain effects are all two-domain, so this is the deployed instance.) -/
def umemCohortDesc2 (nm : String) (d₀ : Domain) (k₀ : Kind) (d₁ : Domain) (k₁ : Kind) :
    EffectVmDescriptor2 :=
  { name        := nm
  , traceWidth  := 8
  , piCount     := 0
  , tables      := [mainTableDef 8, umemTableDef, umemBoundaryTableDef]
  , constraints :=
      [ .umemOp ⟨.var 6, d₀, .var 0, .var 1, .var 2, .var 3, .var 4, .var 5, k₀⟩
      , .umemOp ⟨.var 7, d₁, .var 0, .var 1, .var 2, .var 3, .var 4, .var 5, k₁⟩ ]
  , hashSites   := []
  , ranges      := [] }

/-- NOTE-SPEND: reveal a nullifier (the `nullifiers`-domain freshness insert — the double-spend
gate) AND credit the balance (the `heap`-domain scalar write). The producer sorts domain codes, so
`heap`(1) rides guard column 6 and `nullifiers`(3) guard column 7, each a `write`. -/
def noteSpendUMem : EffectVmDescriptor2 :=
  umemCohortDesc2 "dregg-effectvm-umem-note-spend-v1-staged"
    Domain.heap Kind.write Domain.nullifiers Kind.write

/-- BRIDGE-MINT: insert an inbound bridged nullifier (the `nullifiers`-domain freshness insert) AND
credit the balance (the `heap`-domain scalar write) — the SAME two-domain shape as `noteSpendUMem`
(`heap` col 6 · `nullifiers` col 7, both `write`), its own descriptor name (the bridge lane is not
a note-spend). -/
def bridgeMintUMem : EffectVmDescriptor2 :=
  umemCohortDesc2 "dregg-effectvm-umem-bridge-mint-v1-staged"
    Domain.heap Kind.write Domain.nullifiers Kind.write

/-- The staged MULTI-DOMAIN umem-form cohort registry: `(lean_def_name, descriptor)`, the source of
the staged TSV the driver emits. NEW staged set — beside the single-domain staged registry and the
deployed per-map v1, not a replacement. -/
def umemCohortMultiRegistry : List (String × EffectVmDescriptor2) :=
  [ ("noteSpendUMem",  noteSpendUMem)
  , ("bridgeMintUMem", bridgeMintUMem) ]

-- STRUCTURAL pins: each multi-domain descriptor declares EXACTLY two umemOps, in the named domains,
-- over width 8 (the two guarded operand lanes the producer's two-domain form yields).
#guard (umemOpsOf noteSpendUMem).length == 2
#guard (umemOpsOf bridgeMintUMem).length == 2
#guard noteSpendUMem.traceWidth == 8
#guard umemCohortMultiRegistry.length == 2
-- domain assignment matches the producer's sorted-code order (heap col 6, nullifiers col 7):
#guard (umemOpsOf noteSpendUMem).map (fun m => domainCode m.domain) == [1, 3]
#guard (umemOpsOf bridgeMintUMem).map (fun m => domainCode m.domain) == [1, 3]
-- DISTINCT from the single-domain + deployed sets: every name carries the umem/-staged markers.
#guard umemCohortMultiRegistry.all (fun e => "dregg-effectvm-umem-".isPrefixOf e.2.name)
#guard umemCohortMultiRegistry.all (fun e => e.2.name.endsWith "-v1-staged")

/-! ## §2 — rotV3-style SURVIVAL, PER DOMAIN: the emitted descriptor BINDS THE PUBLISHED STATE.

The descriptor-general `Satisfied2U` keystones (`satisfied2U_pins_final` / `_boundary_root` /
`_init_root`) range over the WHOLE gathered umem log, independent of the constraint count, so they
fire at the multi-domain descriptor verbatim. `_pins_final` forces every declared address (across
BOTH domains); `_boundary_root` / `_init_root` are parametric over the touched domain `dm`, so they
fire separately at `heap` and at `nullifiers`. -/

/-- **SURVIVAL (the final image is FORCED, across both domains).** Every declared universal
address's claimed final value equals the genuine fold of the gathered log — the published
post-state is not prover-chosen, in EITHER touched domain. -/
theorem noteSpend_pins_final (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {uinit : UAddr ℤ → Option ℤ} {ufin : UAddr ℤ → Option ℤ × Nat}
    {uaddrs : List (UAddr ℤ)} {t : VmTrace}
    (h : Satisfied2U hash noteSpendUMem minit mfin maddrs uinit ufin uaddrs t) :
    ∀ a ∈ uaddrs, (ufin a).1 = ((umemLog noteSpendUMem t).foldl step uinit) a :=
  satisfied2U_pins_final hash noteSpendUMem h

/-- **SURVIVAL (the committed POST root is the derived boundary root) — PER DOMAIN.** For the
touched domain `dm` (instantiate at `heap` for the balance plane, `nullifiers` for the freshness
plane): the deployed per-map root EQUALS the sorted-Poseidon2 root of the boundary view derived
from the forced final column. The multi-domain reconciliation moves exactly what the per-map
`MapOp` reconciliations move in EACH plane. -/
theorem noteSpend_post_root (hash : List ℤ → ℤ) (dm : Domain)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {uinit : UAddr ℤ → Option ℤ} {ufin : UAddr ℤ → Option ℤ × Nat}
    {uaddrs : List (UAddr ℤ)} {t : VmTrace}
    {hmap : Dregg2.Substrate.Heap.FeltHeap} {as : List ℤ}
    (h : Satisfied2U hash noteSpendUMem minit mfin maddrs uinit ufin uaddrs t)
    (hs : Dregg2.Substrate.Heap.SortedKeys hmap) (has : as.Pairwise (· < ·))
    (hda : ∀ a ∈ as, (dm, a) ∈ uaddrs)
    (hsem : ∀ a : ℤ, Dregg2.Substrate.Heap.get hmap a
      = if a ∈ as then ((umemLog noteSpendUMem t).foldl step uinit) (dm, a) else none) :
    Dregg2.Substrate.Heap.root hash hmap
      = Dregg2.Substrate.Heap.root hash
          (Dregg2.Crypto.UniversalMemory.boundaryCells (fun a => (ufin (dm, a)).1) as) :=
  satisfied2U_boundary_root hash noteSpendUMem dm h hs has hda hsem

/-- **SURVIVAL (the committed PRE root is bound to the declared init image) — PER DOMAIN.** The
companion at the *init* column for any touched domain `dm`: the committed pre-state root EQUALS the
derived boundary root of the declared init image, so a tampered init cannot keep the published root
in EITHER plane. -/
theorem noteSpend_pre_root (hash : List ℤ → ℤ) (dm : Domain)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {uinit : UAddr ℤ → Option ℤ} {ufin : UAddr ℤ → Option ℤ × Nat}
    {uaddrs : List (UAddr ℤ)} {t : VmTrace}
    {hpre : Dregg2.Substrate.Heap.FeltHeap} {as : List ℤ}
    (h : Satisfied2U hash noteSpendUMem minit mfin maddrs uinit ufin uaddrs t)
    (hs : Dregg2.Substrate.Heap.SortedKeys hpre) (has : as.Pairwise (· < ·))
    (hsem : ∀ a : ℤ, Dregg2.Substrate.Heap.get hpre a = if a ∈ as then uinit (dm, a) else none) :
    Dregg2.Substrate.Heap.root hash hpre
      = Dregg2.Substrate.Heap.root hash
          (Dregg2.Crypto.UniversalMemory.boundaryCells (fun a => uinit (dm, a)) as) :=
  satisfied2U_init_root hash noteSpendUMem dm h hs has hsem

/-! ### §2b — the SURVIVAL keystone fired end-to-end on a TWO-domain witness (non-vacuity).

A concrete worked `Satisfied2U` witness for `noteSpendUMem`: one `heap`-domain row crediting the
balance (key 10 ← 5, prev absent) AND one `nullifiers`-domain row inserting a fresh nullifier (key
20 ← present, prev absent). The survival keystone fires on it — the forced final image carries the
credited balance at `(heap, 10)` AND the inserted nullifier at `(nullifiers, 20)`, no Merkle path,
every leg discharged concretely (including `umemNullifierInsertOnly`: the nullifier write's value is
present, not `none`). Nothing in §2 is vacuous. -/

/-- The worked `heap` row: key 10 (col 0), present 1 (col 1), value 5 (col 2), prev absent
(cols 3/4/5 = 0), `heap` guard on (col 6). -/
def nsHeapRow : Assignment := fun i =>
  if i = 0 then 10 else if i = 1 then 1 else if i = 2 then 5 else if i = 6 then 1 else 0

/-- The worked `nullifiers` row: key 20 (col 0), present 1 (col 1), value 1 (col 2), prev absent
(cols 3/4/5 = 0), `nullifiers` guard on (col 7). -/
def nsNullRow : Assignment := fun i =>
  if i = 0 then 20 else if i = 1 then 1 else if i = 2 then 1 else if i = 7 then 1 else 0

/-- The worked witness: the heap row then the nullifier row; the umem table carries exactly the
gathered log's two rows (`uopRow` of each). -/
def nsTrace : VmTrace :=
  { rows := [nsHeapRow, nsNullRow], pub := zeroAsg
  , tf := fun tid => match tid with
      | .custom 1 => [[1, 10, 1, 5, 0, 0, 0, 1], [3, 20, 1, 1, 0, 0, 0, 1]]
      | _ => [] }

/-- The worked universal boundary: everything starts absent. -/
def nsUinit : UAddr ℤ → Option ℤ := fun _ => none

/-- The worked final claims: `(heap, 10)` ← `some 5` at serial 1, `(nullifiers, 20)` ← `some 1` at
serial 2 (the positional fold serials). -/
def nsUfin : UAddr ℤ → Option ℤ × Nat := fun a =>
  if a = (Domain.heap, 10) then (some 5, 1)
  else if a = (Domain.nullifiers, 20) then (some 1, 2)
  else (none, 0)

/-- The worked declared universal addresses (both touched planes). -/
def nsUaddrs : List (UAddr ℤ) := [(Domain.heap, 10), (Domain.nullifiers, 20)]

-- The gathered umem log balances, is disciplined, and is consistent (the executable shadow of the
-- survival keystone, AT the IR — the two-domain touch reconciles).
#guard decide (Dregg2.Crypto.MemoryChecking.Disciplined (umemLog noteSpendUMem nsTrace))
#guard decide (Dregg2.Crypto.MemoryChecking.MemCheck nsUinit nsUfin nsUaddrs
  (umemLog noteSpendUMem nsTrace))
#guard decide (Dregg2.Crypto.MemoryChecking.Consistent nsUinit (umemLog noteSpendUMem nsTrace))
-- The forced fold carries the published value at BOTH touched addresses (the survival payoff).
#guard ((umemLog noteSpendUMem nsTrace).foldl step nsUinit) (Domain.heap, 10) == some 5
#guard ((umemLog noteSpendUMem nsTrace).foldl step nsUinit) (Domain.nullifiers, 20) == some 1

/-- The worked `Satisfied2U` witness, fully constructed (the row constraints are the two
global-content umemOps ⇒ row-locally `True`; the multiset legs are `decide`-level; the tables are
faithful by `rfl`). -/
theorem noteSpendUMem_satisfied :
    Satisfied2U (fun _ => 0) noteSpendUMem (fun _ => 0) (fun _ => ((0 : ℤ), 0)) []
      nsUinit nsUfin nsUaddrs nsTrace := by
  refine ⟨⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints: each of the two constraints is a umemOp (global content ⇒ row-locally True)
    intro i hi c hc
    simp only [noteSpendUMem, umemCohortDesc2, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc <;> subst hc <;> trivial
  · intro i hi; trivial          -- rowHashes: none
  · intro i hi r hr; simp [noteSpendUMem, umemCohortDesc2] at hr   -- rowRanges: none
  · intro op hop                  -- memClosed: the flat memory log is empty
    rw [show memLog noteSpendUMem nsTrace = [] from rfl] at hop; cases hop
  · rw [show memLog noteSpendUMem nsTrace = [] from rfl]; exact by decide   -- memDisciplined
  · rw [show memLog noteSpendUMem nsTrace = [] from rfl]; exact memCheck_nil _ _  -- memBalanced
  · rfl                           -- memTableFaithful
  · rfl                           -- mapTableFaithful
  · exact by decide               -- umemAddrsNodup
  · exact by decide               -- umemClosed
  · exact by decide               -- umemDisciplined
  · exact by decide               -- umemBalanced
  · exact by decide               -- umemNullifierInsertOnly (the nullifier write's value ≠ none)
  · rfl                           -- umemTableFaithful

/-- **THE SURVIVAL KEYSTONE, FIRED ON TWO DOMAINS.** On the worked witness the claimed final image
is FORCED to the genuine fold at BOTH planes — `noteSpendUMem` binds the published balance (`some 5`
at `(heap, 10)`) AND the published nullifier (`some 1` at `(nullifiers, 20)`), end-to-end,
concretely. The multi-domain umem-form descriptor binds the published state in every touched
domain. -/
theorem noteSpendUMem_survives_concrete :
    ∀ a ∈ nsUaddrs, (nsUfin a).1 = ((umemLog noteSpendUMem nsTrace).foldl step nsUinit) a :=
  satisfied2U_pins_final (fun _ => 0) noteSpendUMem noteSpendUMem_satisfied

/-! ## §3 — the UMemCodec INJECTIVITY: the multi-domain addresses are FAITHFUL across planes. -/

/-- **The address codec is FAITHFUL across the touched planes.** Under the one named CR floor, equal
encoded `uaddrEnc` addresses force the same domain, collection, and key — so the `heap` balance cell
and the `nullifiers` freshness cell of a multi-domain effect can NEVER alias (the two planes the
multi-domain descriptor reconciles are genuinely disjoint). (`UMemCodec.uaddrEnc_injective`.) -/
theorem noteSpend_addr_faithful (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {d d' : Domain} {coll key coll' key' : ℤ}
    (h : Dregg2.Crypto.UMemCodec.uaddrEnc hash d coll key
      = Dregg2.Crypto.UMemCodec.uaddrEnc hash d' coll' key') :
    d = d' ∧ coll = coll' ∧ key = key' :=
  Dregg2.Crypto.UMemCodec.uaddrEnc_injective hash hCR h

/-! ## §4 — the staged wire artifacts (byte-pinned descriptor JSON).

Each `#guard` is the committed-descriptor discipline (the sha-pinned twin): the emitted JSON CANNOT
drift from the verified descriptor. The driver `EmitUMemCohortMulti.lean` writes these exact bytes
to `circuit/descriptors/umem-cohort-multidomain-v1-staged-registry.tsv`. -/

#guard emitVmJson2 noteSpendUMem ==
  "{\"name\":\"dregg-effectvm-umem-note-spend-v1-staged\",\"ir\":2,\"trace_width\":8,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":8,\"sem\":\"main\"},{\"id\":6,\"name\":\"umemory\",\"arity\":8,\"sem\":\"umemory\"},{\"id\":7,\"name\":\"umem_boundary\",\"arity\":7,\"sem\":\"umem_boundary\"}],\"constraints\":[{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":1,\"guard\":{\"t\":\"var\",\"v\":6},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":2},\"prev_present\":{\"t\":\"var\",\"v\":3},\"prev_value\":{\"t\":\"var\",\"v\":4},\"prev_serial\":{\"t\":\"var\",\"v\":5}},{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":3,\"guard\":{\"t\":\"var\",\"v\":7},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":2},\"prev_present\":{\"t\":\"var\",\"v\":3},\"prev_value\":{\"t\":\"var\",\"v\":4},\"prev_serial\":{\"t\":\"var\",\"v\":5}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 bridgeMintUMem ==
  "{\"name\":\"dregg-effectvm-umem-bridge-mint-v1-staged\",\"ir\":2,\"trace_width\":8,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":8,\"sem\":\"main\"},{\"id\":6,\"name\":\"umemory\",\"arity\":8,\"sem\":\"umemory\"},{\"id\":7,\"name\":\"umem_boundary\",\"arity\":7,\"sem\":\"umem_boundary\"}],\"constraints\":[{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":1,\"guard\":{\"t\":\"var\",\"v\":6},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":2},\"prev_present\":{\"t\":\"var\",\"v\":3},\"prev_value\":{\"t\":\"var\",\"v\":4},\"prev_serial\":{\"t\":\"var\",\"v\":5}},{\"t\":\"umem_op\",\"kind\":\"write\",\"domain\":3,\"guard\":{\"t\":\"var\",\"v\":7},\"key\":{\"t\":\"var\",\"v\":0},\"present\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"var\",\"v\":2},\"prev_present\":{\"t\":\"var\",\"v\":3},\"prev_value\":{\"t\":\"var\",\"v\":4},\"prev_serial\":{\"t\":\"var\",\"v\":5}}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## Axiom-hygiene pins. -/

#assert_axioms noteSpend_pins_final
#assert_axioms noteSpend_post_root
#assert_axioms noteSpend_pre_root
#assert_axioms noteSpendUMem_satisfied
#assert_axioms noteSpendUMem_survives_concrete
#assert_axioms noteSpend_addr_faithful

end Dregg2.Circuit.Emit.EffectVmEmitUMemCohortMulti
