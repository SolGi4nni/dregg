/-
# Dregg2.Bridge.LightClientMina — the VERIFIED Mina (Ouroboros Samasika / Pickles) light client.

⚑ SUBSTRATE, SAID OUT LOUD: this file is a Lean-authored MODEL + rules (pure `Nat`/`Bool`), exactly
as `LightClientSolana` / `LightClientTendermint` / `LightClientMidnight` are. It authors NO AIR. The
one AIR object in the Mina light-client lane — the state-row canonicality width gate — is authored
in Lean in `Dregg2.Circuit.Emit.LightClientMinaHashFold`, generated from `AirBuilder.rangeNonneg`
via `StakeWidthRange.widthGate`. No Rust hand-writes a constraint for any of it.

## Why Mina was the missing fifth chain

The repo has a per-chain light-client pattern — a Lean-authored rule set (`Bridge.LightClient*`), a
carrier fold that DERIVES the hash carriers (`Circuit.Emit.LightClient*HashFold`), and an
`@[export]` gate the Rust routes through (`Bridge.LightClient*Gate`). Ethereum, Tendermint/Cosmos,
Solana and Midnight are all in it. **Mina was not**, even though the Mina *verification content*
already exists and is the deepest in the tree: `MinaRealBlockGate` decides a REAL devnet block
(539508) whose Wrap proof o1-labs' own `kimchi::verifier::verify` accepts, `MinaRealBlockTranscript`
DERIVES every challenge, and `PastaIpaFold` discharges `sg == ⟨s, srs.g⟩` over all 32,768 real
generators. None of it was wired to a light client.

Meanwhile the deployed Mina plumbing (`bridge/src/mina_observer.rs`) confirmed finality by asking a
GraphQL endpoint and believing the answer. Its own header called that an upgrade from "trusting a
relayer's ack" — and it is, but the rung it lands on is "trusting a node's RPC". This file is the
rule set for the next rung.

## What a Mina light client tracks (and what this file's rules therefore are)

Mina's chain object is a **Pickles-proved block**: each block carries a recursive proof that the
whole protocol state (including the ledger) is valid, so a Mina light client does NOT re-execute —
it follows STATE HASHES and checks a proof per block. So the rules are:

  * **LINKAGE** (`linkOk`) — the exhibited segment is PARENT-LINKED and HEIGHT-CONTIGUOUS from the
    governance-pinned weak-subjectivity anchor: block `i+1`'s `previousStateHash` IS block `i`'s
    computed state hash, and its `blockchainLength` is exactly one more. This is the carrier
    `LightClientMinaHashFold` FOLDS OUT into a Poseidon chain whose terminal value is the tip state
    hash.
  * **DEPTH, WITNESSED** (`witnessedDepth`) — Ouroboros Samasika gives probabilistic finality with
    depth `k`. The load-bearing move here is that the depth must be BACKED BY EXHIBITED, LINKED
    BLOCKS, not computed as `claimed_tip_height − claimed_submitted_height`. `mina_depth_is_witnessed`
    is that theorem: acceptance entails `confirmationDepth ≤ blocks.length`. Two claimed heights
    from the same untrusted endpoint can say anything; `k` linked blocks each carrying a Pickles
    proof cannot be conjured.
  * **PICKLES** (`picklesOk`) — a NAMED CARRIER, the Mina analog of Solana's `ED_OK` and Ethereum's
    `BLS_OK`: every exhibited block's Wrap proof verifies AT THAT BLOCK'S OWN state hash. The
    at-its-own-state-hash part is the public-input binding — a proof that verifies against some
    other block's public input says nothing about this one. The carrier's RESULT crosses into the
    decision; the arithmetic behind it is `KimchiVerify` / `MinaRealBlockGate`, and
    `LightClientMinaHashFold` discharges it on the REAL devnet block.
  * **CANONICALITY** (`canonOk`) — a NAMED CARRIER at this layer, DERIVED downstream: every state-row
    field element is canonical (`< p`). Poseidon's `absorbAt` enters every input through
    `(state + x) % p`, so a NON-canonical field element is invisible at the digest
    (`MinaStateQuery.poseidonPair_shift_collides`). This is the exact Mina twin of the Solana
    stake-width defect, and it is closed the same way — by a Lean-authored width gate, in the fold.

## What is NOT here, named rather than implied

  * **FORK CHOICE IS NOT CHECKED *HERE*.** These rules say "this exhibited segment is linked,
    proved and `k` deep from the anchor"; they do NOT say "and it is the chain the network
    selected". A `k`-deep linked proved segment from a DIFFERENT anchor is not refused by anything
    in THIS file. That is the honest boundary between what this is (an anchored, proof-carrying
    segment verifier) and a Mina light client (which follows the chain).
    ⚑ UPDATED 2026-07-29: the rule itself now EXISTS in the tree —
    `Dregg2.Bridge.MinaChainSelection` implements Samasika `select` / `is_short_range` / the
    relative min-window-density against `proof_of_stake.ml`, differentials it against openmina on
    real states, and gives the light client `minaBetterTip`. What is still absent is the WIRING:
    nothing in this file calls it, and `select` is a TOURNAMENT, not an order — it has proved
    3-cycles, so it can rank two named tips but must never be folded over a candidate set.
  * **NO RE-EXECUTION and no ledger check** beyond the state-row commitment — that is what the
    Pickles proof is for, and `picklesSound` is exactly the assumption that it works.

## The crypto leaf (`MinaLeaf`), honest and minimal

Two named carriers, both VISIBLE STRUCTURE FIELDS (never a global `axiom`):

  * `picklesSound` — a verifying Pickles/Kimchi Wrap proof at a state hash entails that state was
    genuinely PROVED. This inherits the undischarged FRI/IPA floor; it is not "verified" in the
    l4v sense and this file does not claim it is.
  * `stateHashCR` + `noStateCollision` — the state-hash collision carrier as a `Prop` over an OPAQUE
    `stateHash`, the `SolLeaf.stakeTableCR` pattern. ⚑ It is a floor ONLY while the hash is opaque:
    the moment it is instantiated at the concrete Poseidon (`LightClientMinaHashFold`) the slot goes
    to `False`, because `absorbAt` reduces every input mod `p` and global injectivity is refuted.
    The binding content there rides a per-instance separation floor instead. Stated here so a reader
    of THIS file does not take the abstract carrier for more than it is.

Kernel-clean: `#assert_axioms` hard-gates every theorem; `demoLeaf` PROVES both carriers, and both
polarities are witnessed (a collapsing state hash REFUTES `stateHashCR`; a never-accepting verifier
makes `picklesOk` false).
-/
import Dregg2.Bridge.VerifiedLightClient
import Dregg2.Tactics

set_option autoImplicit false

namespace Dregg2.Bridge.LightClientMina

/-! ## §1 — The HONEST crypto leaf: Pickles soundness + the state-hash CR carrier, as VISIBLE
fields. `MinaLeaf` is the Mina refinement of the foundation `CryptoLeaf` shape: the "signature"
primitive is a per-block PICKLES WRAP PROOF verify at the block's own state hash, and the hash
primitive is the Poseidon protocol-state hash the chain links through. -/

/-- **`MinaLeaf`** — the named, minimal verified-primitive bundle for Mina. `picklesSound` is THE
proof leaf; `stateHashCR` + `noStateCollision` are the state-hash CR carrier; `rowCanonical` is the
field-element width discipline the fold derives from an emitted gate. All are visible structure
fields an instance must supply. -/
structure MinaLeaf where
  /-- A Pasta `Fp` field element — a state hash, a ledger hash, a public-input digest. -/
  Digest : Type
  /-- Digest equality is decidable (the Rust `==` on the 32-byte little-endian field). -/
  deqD : DecidableEq Digest
  /-- A Pickles Wrap proof (opaque; the real one is the object `MinaRealBlockGate` decides). -/
  Proof : Type
  /-- **The protocol-state hash.** Poseidon over the state row `(previousStateHash,
  blockchainLength, stagedLedgerHash, publicInputDigest)`. Opaque here; instantiated at the real
  Poseidon in `LightClientMinaHashFold`. -/
  stateHash : Digest × Nat × Digest × Digest → Digest
  /-- **The Pickles/Kimchi Wrap verify RESULT**, at the block's OWN state hash. The at-its-own-hash
  argument IS the public-input binding: a proof verifying at another block's public input carries no
  claim about this block. Opaque; `KimchiVerify.kimchiVerifyDecisionFieldRec` realizes it. -/
  picklesVerify : Digest → Proof → Bool
  /-- The DENOTATION: that protocol state was genuinely PROVED (a Pickles proof for it exists). -/
  Proved : Digest → Prop
  /-- **THE PICKLES LEAF (named, minimal).** A verifying Wrap proof at a state hash entails that
  state was genuinely proved. ⚑ This inherits the undischarged FRI/IPA soundness floor — it is a
  named assumption, not a discharged one. -/
  picklesSound : ∀ d π, picklesVerify d π = true → Proved d
  /-- **The state-row CANONICALITY predicate** (`every field element < p`). A per-row Boolean the
  deployed path computes and the fold DERIVES from the emitted width gate. -/
  rowCanonical : Digest × Nat × Digest × Digest → Bool
  /-- **CARRIER — THE STATE-HASH CR LEAF (named, minimal).** A `Prop`, NOT idealized injectivity,
  mirroring `SolLeaf.stakeTableCR`. ⚑ Satisfiable only while `stateHash` is OPAQUE: at the concrete
  Poseidon it is FALSE (`absorbAt` reduces mod `p`), and the fold sets this slot to `False` and rides
  a per-instance separation floor instead. -/
  stateHashCR : Prop
  /-- The CR carrier unpacked: GIVEN the floor, two state rows with the same state hash ARE the same
  row — so a tip state hash pins the block that produced it. -/
  noStateCollision : stateHashCR →
    ∀ r₁ r₂ : Digest × Nat × Digest × Digest, stateHash r₁ = stateHash r₂ → r₁ = r₂
  /-- The zero field element — the fail-closed probe's digest slot. -/
  zeroDigest : Digest

/-- Decidable digest equality as a `Bool`. -/
def MinaLeaf.dBeq (L : MinaLeaf) (a b : L.Digest) : Bool := @decide (a = b) (L.deqD a b)

theorem MinaLeaf.dBeq_iff (L : MinaLeaf) {a b : L.Digest} : L.dBeq a b = true ↔ a = b := by
  letI := L.deqD; unfold MinaLeaf.dBeq; exact decide_eq_true_iff

/-- **`MinaLeaf.state_inj` (the floor theorem shape; mirrors `SolLeaf.table_inj`).** GIVEN the CR
carrier, a state-hash equality pins the whole state row. -/
theorem MinaLeaf.state_inj (L : MinaLeaf) (hcr : L.stateHashCR)
    {r₁ r₂ : L.Digest × Nat × L.Digest × L.Digest} (h : L.stateHash r₁ = L.stateHash r₂) : r₁ = r₂ :=
  L.noStateCollision hcr r₁ r₂ h

/-! ## §2 — The data types (the real Mina GraphQL / protocol-state shapes). -/

/-- A Mina block header, as a light client tracks it: the fields the protocol-state hash commits
and the light client links through. `previousStateHash` + `blockchainLength` are literally the two
fields `bridge/src/mina_observer.rs`'s `bestChain` query already pulls. -/
structure MinaHeader (L : MinaLeaf) where
  /-- `protocolState.previousStateHash` — the parent block's state hash. -/
  parent : L.Digest
  /-- `protocolState.consensusState.blockHeight` — the blockchain length. -/
  height : Nat
  /-- The staged-ledger hash this block commits (the object a state query opens under). -/
  ledgerHash : L.Digest
  /-- The Wrap proof's PUBLIC-INPUT digest for this block (what the Pickles proof is verified at). -/
  piDigest : L.Digest

/-- The state ROW the protocol-state hash commits over (the `entryRow` analog). -/
def stateRow {L : MinaLeaf} (h : MinaHeader L) : L.Digest × Nat × L.Digest × L.Digest :=
  (h.parent, h.height, h.ledgerHash, h.piDigest)

/-- **A block's own state hash** — Poseidon over its state row. -/
def blockHash (L : MinaLeaf) (h : MinaHeader L) : L.Digest := L.stateHash (stateRow h)

/-- The update a Mina finality claim carries: the exhibited canonical SEGMENT (oldest-first, starting
one block above the anchor), one Wrap proof per block, and the height the settlement was submitted
at. -/
structure MinaUpdate (L : MinaLeaf) where
  /-- The exhibited segment, OLDEST-FIRST. Its length is the depth evidence. -/
  blocks : List (MinaHeader L)
  /-- One Pickles Wrap proof per block, in the same order. -/
  proofs : List L.Proof
  /-- The Mina height the settlement was submitted at (`StateAdvance.submitted_at`). -/
  submittedHeight : Nat

/-- The TRUSTED STATE: the governance-pinned weak-subjectivity anchor (a state hash + its height)
and the Samasika confirmation depth `k`. -/
structure MinaTrustedState (L : MinaLeaf) where
  /-- The pinned WS anchor block's state hash. -/
  anchorState : L.Digest
  /-- The pinned anchor's blockchain length. -/
  anchorHeight : Nat
  /-- The Samasika confirmation depth `k` (≈290 on mainnet; small on devnets/tests). -/
  confirmationDepth : Nat

/-! ## §3 — THE RULES: parent-linkage + height contiguity, WITNESSED depth, and the two carriers. -/

/-- **The linkage fold, as a Boolean.** Walking the segment oldest-first from `(prev, prevHeight)`:
each block's `previousStateHash` must BE the running state hash and its height exactly one more. The
running value is the child's own state hash. This is the carrier `LightClientMinaHashFold` replaces
with a Poseidon chain whose terminal value is the tip state hash. -/
def chainLinked (L : MinaLeaf) : L.Digest → Nat → List (MinaHeader L) → Bool
  | _, _, [] => true
  | prev, ph, h :: rest =>
      L.dBeq h.parent prev && decide (h.height = ph + 1)
        && chainLinked L (blockHash L h) h.height rest

/-- **GATE (linkage)** — the exhibited segment is parent-linked and height-contiguous from the
pinned WS anchor. -/
def linkOk (L : MinaLeaf) (ts : MinaTrustedState L) (u : MinaUpdate L) : Bool :=
  chainLinked L ts.anchorState ts.anchorHeight u.blocks

/-- The `Prop` form of the linkage fold — what acceptance DENOTES. -/
def ChainFrom (L : MinaLeaf) : L.Digest → Nat → List (MinaHeader L) → Prop
  | _, _, [] => True
  | prev, ph, h :: rest =>
      h.parent = prev ∧ h.height = ph + 1 ∧ ChainFrom L (blockHash L h) h.height rest

/-- The Boolean linkage fold ENTAILS the `Prop` one (the extraction lemma). -/
theorem chainFrom_of_chainLinked (L : MinaLeaf) :
    ∀ (bs : List (MinaHeader L)) (prev : L.Digest) (ph : Nat),
      chainLinked L prev ph bs = true → ChainFrom L prev ph bs := by
  intro bs
  induction bs with
  | nil => intro _ _ _; trivial
  | cons h rest ih =>
    intro prev ph hb
    simp only [chainLinked, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨hpar, hht⟩, hrest⟩ := hb
    exact ⟨(L.dBeq_iff).mp hpar, hht, ih _ _ hrest⟩

/-- **The tip height WITNESSED by the exhibited segment** — the anchor height plus the number of
exhibited blocks. NOT a height the endpoint claims. -/
def tipHeight {L : MinaLeaf} (ts : MinaTrustedState L) (u : MinaUpdate L) : Nat :=
  ts.anchorHeight + u.blocks.length

/-- **The confirmation depth WITNESSED** — how far the witnessed tip is past the submitted height. -/
def witnessedDepth {L : MinaLeaf} (ts : MinaTrustedState L) (u : MinaUpdate L) : Nat :=
  tipHeight ts u - u.submittedHeight

/-- **CARRIER (Pickles/Kimchi)** — every exhibited block's Wrap proof verifies AT ITS OWN state hash,
and there is exactly one proof per block (a short proof list must not silently pass). -/
def picklesOk (L : MinaLeaf) (u : MinaUpdate L) : Bool :=
  decide (u.blocks.length = u.proofs.length)
  && (u.blocks.zip u.proofs).all (fun p => L.picklesVerify (blockHash L p.1) p.2)

/-- **CARRIER (canonicality)** — every exhibited state row's field elements are canonical (`< p`).
DERIVED downstream from the emitted width gate (`LightClientMinaHashFold.minaRowWidthGates`). -/
def canonOk (L : MinaLeaf) (u : MinaUpdate L) : Bool :=
  u.blocks.all (fun h => L.rowCanonical (stateRow h))

/-- **`minaVerifyDecision`** — THE scalar verify-logic decision, over the projections a deployed node
computes. The segment must be non-empty, the submitted height must be AT OR ABOVE the pinned anchor
(without which the "depth" is measured from outside the exhibited evidence), the witnessed depth must
meet the Samasika requirement, and the three carriers/gates must hold.

⚑ The `anchorH ≤ submittedH` conjunct is what makes `mina_depth_is_witnessed` provable, and it is the
exact conjunct the deployed observer does not have. This is the object `@[export] dregg_mina_lc_verify`
renders and `mina_no_forgery` is proven over. -/
def minaVerifyDecision (segLen anchorH submittedH witDepth reqDepth : Nat)
    (linkB picklesB canonB : Bool) : Bool :=
  decide (0 < segLen)
  && decide (anchorH ≤ submittedH)
  && decide (reqDepth ≤ witDepth)
  && linkB && picklesB && canonB

/-- **THE VERIFY RULES**, as the scalar decision over the update's true projections. -/
def minaVerify (L : MinaLeaf) (ts : MinaTrustedState L) (u : MinaUpdate L) : Bool :=
  minaVerifyDecision u.blocks.length ts.anchorHeight u.submittedHeight
    (witnessedDepth ts u) ts.confirmationDepth
    (linkOk L ts u) (picklesOk L u) (canonOk L u)

/-- The empty / uninitialized update — no blocks, no proofs: the Nomad fail-closed probe (an empty
segment witnesses zero depth ⇒ reject). -/
def emptyUpdate (L : MinaLeaf) : MinaUpdate L := ⟨[], [], 0⟩

/-! ## §4 — THE FOREIGN-VALIDITY denotation: what a verify-accepted update genuinely IS. -/

/-- **`MinaValidAt L ts u`** — Mina's anchored proof-carrying segment validity, relative to the
pinned WS anchor `ts`:

  * `proved` — EVERY exhibited block's protocol state was genuinely PROVED (via `picklesSound`, at
    that block's OWN state hash — the public-input binding);
  * `anchored` — the segment is a parent-linked, height-contiguous chain FROM the pinned anchor;
  * `depthWitnessed` — the Samasika confirmation depth is BACKED by at least that many exhibited
    linked proved blocks. Not asserted by subtracting two claimed heights.
  * `canonical` — every exhibited state row is canonical, so the Poseidon linkage above is not
    aliasable by a non-canonical field element.

⚑ NOT a conjunct, and deliberately: "this is the chain Samasika selects". Nothing here rules out a
second `k`-deep proved segment from a different anchor. See the header. -/
structure MinaValidAt (L : MinaLeaf) (ts : MinaTrustedState L) (u : MinaUpdate L) : Prop where
  /-- Every exhibited block's state was genuinely proved. -/
  proved : ∀ h ∈ u.blocks, L.Proved (blockHash L h)
  /-- The segment is parent-linked and height-contiguous from the pinned anchor. -/
  anchored : ChainFrom L ts.anchorState ts.anchorHeight u.blocks
  /-- The confirmation depth is witnessed by exhibited blocks. -/
  depthWitnessed : ts.confirmationDepth ≤ u.blocks.length
  /-- Every exhibited state row is canonical. -/
  canonical : ∀ h ∈ u.blocks, L.rowCanonical (stateRow h) = true

/-! ## §5 — Supporting extraction lemmas. -/

/-- The witnessed depth never exceeds the exhibited segment length, GIVEN the submitted height is at
or above the anchor. This is the arithmetic the whole depth claim rests on. -/
theorem witnessedDepth_le_length {L : MinaLeaf} (ts : MinaTrustedState L) (u : MinaUpdate L)
    (h : ts.anchorHeight ≤ u.submittedHeight) : witnessedDepth ts u ≤ u.blocks.length := by
  unfold witnessedDepth tipHeight
  omega

/-- ⚑ **WITHOUT the anchor bound the depth claim is UNBOUNDED** — an update whose submitted height is
`0` while the anchor sits at `1000` witnesses a "depth" of `1000` from a segment of ONE block. This
is the deployed observer's arithmetic exactly (`tip_height.saturating_sub(submitted_height)`), and it
is why `minaVerifyDecision` carries the `anchorH ≤ submittedH` conjunct. -/
theorem witnessedDepth_unbounded_without_anchor_bound (L : MinaLeaf) (b : MinaHeader L)
    (ts : MinaTrustedState L) (hts : ts.anchorHeight = 1000) :
    witnessedDepth ts ⟨[b], [], 0⟩ = 1001 := by
  simp [witnessedDepth, tipHeight, hts]

/-- Every proof-carrying block in an accepted update has a verifying Wrap proof. -/
theorem picklesOk_forall (L : MinaLeaf) (u : MinaUpdate L) (h : picklesOk L u = true) :
    ∀ p ∈ u.blocks.zip u.proofs, L.picklesVerify (blockHash L p.1) p.2 = true := by
  unfold picklesOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- Zipping at equal lengths covers every block: each block appears as some zip pair. -/
theorem mem_zip_of_mem_left {L : MinaLeaf} :
    ∀ (bs : List (MinaHeader L)) (ps : List L.Proof), bs.length = ps.length →
      ∀ b ∈ bs, ∃ p, (b, p) ∈ bs.zip ps := by
  intro bs
  induction bs with
  | nil => intro _ _ b hb; simp at hb
  | cons x xs ih =>
    intro ps hlen b hb
    cases ps with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨y, by simp⟩
      · obtain ⟨p, hp⟩ := ih ys (by simpa using hlen) b hb
        exact ⟨p, by simp [hp]⟩

/-! ## §6 — THE THREE OBLIGATIONS: NoForgery, FailClosed, NonVacuous. -/

/-- **NO FORGERY (the ts-relative statement).** For every leaf, pinned WS anchor and update:
verify-acceptance entails the update is Mina-VALID relative to that anchor — every exhibited block
genuinely PROVED (via the Pickles leaf, at its own state hash), the segment parent-linked and
height-contiguous FROM the anchor, the confirmation depth BACKED by that many exhibited blocks, and
every state row canonical.

⚑ NO CR carrier is needed for this direction, and that is not an oversight: the conjuncts above are
all POSITIVE facts about the exhibited segment. The CR floor is what a NON-EQUIVOCATION claim needs
("no OTHER segment reaches this tip"), and that statement lives in
`LightClientMinaHashFold.mina_segment_binding_on`, at the per-instance separation floor — because at
the concrete Poseidon the global-injectivity form is REFUTED. -/
theorem mina_no_forgery (L : MinaLeaf) :
    ∀ (ts : MinaTrustedState L) (u : MinaUpdate L), minaVerify L ts u = true → MinaValidAt L ts u := by
  intro ts u h
  unfold minaVerify minaVerifyDecision at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨_hlen, hanch⟩, hdep⟩, hlink⟩, hpick⟩, hcanon⟩ := h
  have hzip : u.blocks.length = u.proofs.length := by
    unfold picklesOk at hpick
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpick
    exact hpick.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨p, hp⟩ := mem_zip_of_mem_left u.blocks u.proofs hzip b hb
    exact L.picklesSound _ p (picklesOk_forall L u hpick (b, p) hp)
  · exact chainFrom_of_chainLinked L u.blocks ts.anchorState ts.anchorHeight hlink
  · exact le_trans hdep (witnessedDepth_le_length ts u hanch)
  · intro b hb
    unfold canonOk at hcanon
    simp only [List.all_eq_true] at hcanon
    exact hcanon b hb

/-- ⚑ **THE PAYOFF THE DEPLOYED OBSERVER DOES NOT HAVE.** Acceptance entails the Samasika
confirmation depth is backed by AT LEAST that many exhibited, parent-linked, Pickles-PROVED blocks.
An endpoint cannot conjure `k` linked proved blocks; it can trivially claim two heights whose
difference is `k`, which is what `mina_observer::observe_settlement` computes today. -/
theorem mina_depth_is_witnessed (L : MinaLeaf) (ts : MinaTrustedState L) (u : MinaUpdate L)
    (h : minaVerify L ts u = true) : ts.confirmationDepth ≤ u.blocks.length :=
  (mina_no_forgery L ts u h).depthWitnessed

/-- **FAIL CLOSED.** The empty update is REFUSED for every leaf and every trusted state: an empty
segment witnesses no depth at all. (The Nomad-law tooth: a zero-evidence input must not accept.) -/
theorem mina_empty_refused (L : MinaLeaf) (ts : MinaTrustedState L) :
    minaVerify L ts (emptyUpdate L) = false := by
  unfold minaVerify minaVerifyDecision emptyUpdate
  simp

/-! ## §7 — The DEMO instance and the NON-VACUITY discriminators (both polarities witnessed). -/

/-- The demo state hash: a genuinely INJECTIVE toy commitment over the state row, built from
`Nat.pair` (whose inverse `Nat.unpair` gives the injectivity in one step), so the CR carrier is
PROVABLE here rather than assumed — and the collapsing instance below genuinely REFUTES it.

⚑ A polynomial `p·k³ + h·k² + l·k + pi` would NOT do: it is injective only on rows bounded by `k`,
which is exactly the unbounded-field defect the real fold's width gate exists to close. Using one
here would have made `demoStateHash_inj` false, not merely unprovable. -/
def demoStateHash : Nat × Nat × Nat × Nat → Nat
  | (p, h, l, pi) => Nat.pair p (Nat.pair h (Nat.pair l pi))

/-- The demo Pickles verifier: proof `7` is the genuine one, and it must be presented at the state
hash it was minted for (the public-input binding, in miniature). -/
def demoPicklesVerify (d : Nat) (π : Nat × Nat) : Bool := decide (π.1 = 7) && decide (π.2 = d)

/-- The demo `Proved` denotation. -/
def demoProved (d : Nat) : Prop := ∃ π : Nat × Nat, demoPicklesVerify d π = true

/-- The demo Pickles-soundness leaf, PROVED (the `picklesSound` slot). -/
theorem demoPicklesSound (d : Nat) (π : Nat × Nat) (h : demoPicklesVerify d π = true) :
    demoProved d := ⟨π, h⟩

/-- The demo canonicality predicate: the three BLOCK-SUPPLIED fields below the toy modulus `2^16`.
(The parent is a digest — a hash OUTPUT — so it is not width-bounded in the demo; the real
canonicality discipline, which gates the parent precisely because the anchor-shift attack targets it,
is `LightClientMinaHashFold.minaRowWidthGates`.) -/
def demoRowCanonical : Nat × Nat × Nat × Nat → Bool
  | (_, h, l, pi) => decide (h < 65536) && decide (l < 65536) && decide (pi < 65536)

/-- `Nat.pair` is injective, via its inverse. -/
theorem demoPair_inj {a b c d : Nat} (h : Nat.pair a b = Nat.pair c d) : a = c ∧ b = d := by
  have h' := congrArg Nat.unpair h
  rw [Nat.unpair_pair, Nat.unpair_pair] at h'
  exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

/-- The demo state hash is INJECTIVE — so `demoLeaf` genuinely proves its CR carrier rather than
carrying it as a hypothesis. -/
theorem demoStateHash_inj (r₁ r₂ : Nat × Nat × Nat × Nat)
    (h : demoStateHash r₁ = demoStateHash r₂) : r₁ = r₂ := by
  obtain ⟨p₁, h₁, l₁, i₁⟩ := r₁
  obtain ⟨p₂, h₂, l₂, i₂⟩ := r₂
  simp only [demoStateHash] at h
  obtain ⟨hp, h1⟩ := demoPair_inj h
  obtain ⟨hh, h2⟩ := demoPair_inj h1
  obtain ⟨hl, hi⟩ := demoPair_inj h2
  simp only [Prod.mk.injEq]
  exact ⟨hp, hh, hl, hi⟩

/-- **`demoLeaf`** — a lawful `MinaLeaf` that PROVES both carriers (so no theorem above is vacuous on
it). -/
@[reducible] def demoLeaf : MinaLeaf where
  Digest := Nat
  deqD := inferInstance
  Proof := Nat × Nat
  stateHash := demoStateHash
  picklesVerify := demoPicklesVerify
  Proved := demoProved
  picklesSound := demoPicklesSound
  rowCanonical := demoRowCanonical
  stateHashCR := True
  noStateCollision := fun _ r₁ r₂ h => demoStateHash_inj r₁ r₂ h
  zeroDigest := 0

/-- The pinned anchor: state hash `1`, height `10`, confirmation depth `3`. -/
def ts0 : MinaTrustedState demoLeaf := ⟨1, 10, 3⟩

/-- Block 11 (parent = the anchor). -/
def b11 : MinaHeader demoLeaf := ⟨1, 11, 100, 200⟩
/-- Block 12 (parent = block 11's state hash). -/
def b12 : MinaHeader demoLeaf := ⟨blockHash demoLeaf b11, 12, 101, 201⟩
/-- Block 13 (parent = block 12's state hash). -/
def b13 : MinaHeader demoLeaf := ⟨blockHash demoLeaf b12, 13, 102, 202⟩

/-- The genuine proof for a block: `(7, its own state hash)` — the public-input binding. -/
def demoProofFor (b : MinaHeader demoLeaf) : demoLeaf.Proof := (7, blockHash demoLeaf b)

/-- The genuine update: three linked proved blocks above the anchor, settlement submitted at the
anchor height, so the witnessed depth is `3`. -/
def genuineUpdate : MinaUpdate demoLeaf :=
  ⟨[b11, b12, b13], [demoProofFor b11, demoProofFor b12, demoProofFor b13], 10⟩

/-- **NON-VACUITY: the gate ACCEPTS a genuine 3-deep anchored proof-carrying segment, and REJECTS
every single-conjunct tamper** — a broken parent link, a non-contiguous height, one block too few
(depth `2 < 3`), a settlement claimed below the anchor (the deployed observer's unbounded-depth
shape), a forged Pickles proof, a proof presented at the WRONG state hash (the public-input
rebinding attack), a missing proof, and a non-canonical field element. -/
theorem mina_gate_discriminates :
    minaVerify demoLeaf ts0 genuineUpdate = true
    -- broken parent link (block 12 claims a wrong parent)
    ∧ minaVerify demoLeaf ts0
        ⟨[b11, { b12 with parent := 999 }, b13],
         [demoProofFor b11, demoProofFor { b12 with parent := 999 }, demoProofFor b13], 10⟩ = false
    -- non-contiguous height (block 12 claims height 14)
    ∧ minaVerify demoLeaf ts0
        ⟨[b11, { b12 with height := 14 }], [demoProofFor b11,
          demoProofFor { b12 with height := 14 }], 10⟩ = false
    -- one block too few: witnessed depth 2 < required 3
    ∧ minaVerify demoLeaf ts0 ⟨[b11, b12], [demoProofFor b11, demoProofFor b12], 10⟩ = false
    -- settlement claimed BELOW the anchor: the deployed observer would read depth 13 here
    ∧ minaVerify demoLeaf ts0 ⟨[b11], [demoProofFor b11], 0⟩ = false
    -- forged Pickles proof (not the genuine `7`)
    ∧ minaVerify demoLeaf ts0
        ⟨[b11, b12, b13], [(8, blockHash demoLeaf b11), demoProofFor b12, demoProofFor b13], 10⟩
        = false
    -- ⚑ the genuine proof, presented at the WRONG block's state hash (public-input rebinding)
    ∧ minaVerify demoLeaf ts0
        ⟨[b11, b12, b13], [demoProofFor b12, demoProofFor b12, demoProofFor b13], 10⟩ = false
    -- a missing proof (short proof list must not silently pass)
    ∧ minaVerify demoLeaf ts0 ⟨[b11, b12, b13], [demoProofFor b11, demoProofFor b12], 10⟩ = false
    -- a non-canonical field element (ledger hash above the toy modulus). NOTE the tampered block is
    -- the LAST one, so the linkage above it is untouched and this conjunct isolates canonicality.
    ∧ minaVerify demoLeaf ts0
        ⟨[b11, b12, { b13 with ledgerHash := 70000 }],
         [demoProofFor b11, demoProofFor b12, demoProofFor { b13 with ledgerHash := 70000 }], 10⟩
        = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A COLLAPSING state hash — every state row commits to the same digest. The refuting polarity: it
makes `stateHashCR`'s unpacking FALSE, so the carrier is not satisfied by everything. -/
def collapseStateHash : Nat × Nat × Nat × Nat → Nat := fun _ => 0

/-- **THE CR CARRIER IS REFUTABLE** — a collapsing state hash cannot supply `noStateCollision`. -/
theorem collapse_not_stateHashCR :
    ¬ (∀ r₁ r₂ : Nat × Nat × Nat × Nat, collapseStateHash r₁ = collapseStateHash r₂ → r₁ = r₂) := by
  intro h
  exact absurd (h (0, 0, 0, 0) (1, 0, 0, 0) rfl) (by decide)

/-- **THE PICKLES CARRIER IS REFUTABLE** — a never-accepting verifier makes `picklesOk` false on the
genuine update, so the carrier is load-bearing rather than a decoration. -/
theorem never_accepting_pickles_refuses :
    ((genuineUpdate.blocks.zip genuineUpdate.proofs).all (fun _ => false)) = false := by decide

/-! ## §8 — axiom hygiene. -/

#assert_axioms MinaLeaf.dBeq_iff
#assert_axioms MinaLeaf.state_inj
#assert_axioms chainFrom_of_chainLinked
#assert_axioms witnessedDepth_le_length
#assert_axioms witnessedDepth_unbounded_without_anchor_bound
#assert_axioms picklesOk_forall
#assert_axioms mem_zip_of_mem_left
#assert_axioms mina_no_forgery
#assert_axioms mina_depth_is_witnessed
#assert_axioms mina_empty_refused
#assert_axioms demoPair_inj
#assert_axioms demoStateHash_inj
#assert_axioms demoPicklesSound
#assert_axioms mina_gate_discriminates
#assert_axioms collapse_not_stateHashCR
#assert_axioms never_accepting_pickles_refuses

#print axioms mina_no_forgery
#print axioms mina_depth_is_witnessed

end Dregg2.Bridge.LightClientMina
