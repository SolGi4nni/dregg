/-
# Dregg2.Apps.QueueRoot — the queue `message_root` EVOLUTION modeled: dequeue-proof semantics.

THE GAP, CLOSED HERE (the one-disease instance the #173 dequeue-verifier fix exposed): the queue
keystones (`Dregg2.Apps.QueueFactory.queueEnqueue/queueDequeue`) model `message_root` as an OPAQUE
`Int` parameter (`newRoot`) — seq monotonicity / capacity / no-underflow / owner-gating /
fail-closed are PROVED, but root EVOLUTION was entirely out-of-model. The Rust commitment scheme
(`storage/src/queue.rs` `verify_dequeue_proof` / `verify_dequeue_proof_against` over
`storage/src/commitment.rs` `blake3_binary_root`) was load-bearing for dequeue-proof soundness
with no Lean backing. THIS module models the root function and proves the dequeue-proof
keystones, then WELDS them to the factory model so the admitted root pair IS the modeled root
transition.

## The Rust scheme being modeled (storage/src/queue.rs, storage/src/commitment.rs)

* leaf  = `hash_entry(entry)` — domain-tagged BLAKE3 (`TAG_QUEUE_ENTRY`, derive-key) over the
  canonical 88-byte entry preimage (`content_hash ‖ sender ‖ deposit ‖ enqueued_at ‖ size`).
* root  = `blake3_binary_root(pending_leaves)` over the PENDING WINDOW (head..tail), zero-padded
  to the next power of two; single-leaf = that leaf unchanged; empty = the all-zeros sentinel.
* `verify_dequeue_proof(p)`  ⟺  `merkle_root([hash_entry(p.entry)] ++ p.remaining_leaves)
  == p.old_root  ∧  merkle_root(p.remaining_leaves) == p.new_root`.
* `verify_dequeue_proof_against(p, expected)`  ⟺  `p.old_root == expected ∧
  verify_dequeue_proof(p)` (refuses replayed/stale proofs).
* `position` is carried METADATA, explicitly NOT bound by the roots (the Rust doc says do not
  trust it cryptographically) — the model omits it, matching its non-cryptographic status.

## FAITHFUL vs ABSTRACTED — read this before trusting any keystone

FAITHFUL (mirrors the Rust verifier exactly):
  * the two-check conjunction shape of `verifyDequeue` (old-root opens to head-leaf :: remaining;
    new-root is exactly remaining), boolean and fail-closed on any mismatch;
  * the `_against` form (`old_root == expected && structural`) and its replay refusal;
  * the leaf function as an injective-under-CR, never-zero function of the entry (`LeafCR` +
    `LeafNonzero` — domain-tagged BLAKE3 CR + preimage resistance: no entry hashes to the
    all-zeros padding/sentinel value);
  * the emptying dequeue (`remaining = []`) goes through the SAME code path (no special case).

ABSTRACTED (the `RootCR` carrier, and EXACTLY what it bundles): `root : List Int → Int` is
abstract; digests are `Int` (repo convention). `RootCR` asserts injectivity of `root` on
ZERO-FREE leaf lists. Discharging it at the deployed `blake3_binary_root` requires THREE
computational facts, all named here because NONE is structural in the Rust tree:
  (1) BLAKE3 collision resistance (the named §8 floor, `Crypto/PortalFloor.lean Blake3Kernel`);
  (2) NO LEAF/NODE DOMAIN SEPARATION IS PRESENT in Rust: internal nodes are UNtagged
      `blake3(left ‖ right)` while leaves are derive-key-tagged — their non-collision (incl. the
      single-leaf passthrough `root [l] = l` never equaling another tree's internal node) is a
      computational, not structural, property. A 0x00/0x01 level prefix in Rust would make it
      structural;
  (3) ZERO-FREEDOM: the zero-pad-to-pow2 mechanism makes FULL injectivity FALSE — trailing zero
      leaves alias the padding (`root [a,b,c] = root [a,b,c,0]`, PROVED below on a reference
      padded scheme: `refRoot_pad_alias` / `padded_root_not_fully_injective`). Injectivity holds
      only on lists with no zero leaf; honest leaves are never zero by (1)-preimage-resistance.

⚠ THE RESIDUE THE RESTRICTION EXPOSES (a real Rust finding, reported loudly): the Rust verifier
does NOT check that the claimed `remaining_leaves` are zero-free. A prover holding a valid
dequeue can append zero leaves to the claim (e.g. real window `[l1,l2,l3]`, claimed remaining
`[l2,l3,0]`): check (1) passes (`root [l1,l2,l3,0] = root [l1,l2,l3]`, the padding alias) and
check (2) then ADMITS `new_root = root [l2,l3,0] ≠ root [l2,l3]` — a NON-CANONICAL post-root for
the same head-dequeue, diverging the verifier's tracked root from the live queue (subsequent
honest proofs against it fail: a poisoning/DoS lever, not a theft lever). The soundness keystones
below therefore carry an explicit `ZeroFree p.remaining` hypothesis, and `verifyDequeueStrict`
models the ONE-LINE Rust hardening (`remaining_leaves` all-nonzero check) under which the pins
are unconditional in the claim (`strict_dequeue_proof_pins`). Until Rust adopts it, the gap is
the named hypothesis — never silent.

## The keystones

  * `dequeue_proof_pins` — VERIFIER SOUNDNESS: an admitted proof against a root committing to
    `head :: rest` PINS the transition: claimed entry = head, claimed remaining = rest, and
    new_root = root rest. Any other claim would BE a hash collision.
  * `dequeue_forgery_refused` — the `rotate_compromise_resistant` shape: under CR, a proof
    claiming a different entry / post-list / post-root is REFUSED (`= false`).
  * `honest_dequeue_verifies` (+ `_against`) — COMPLETENESS: the real head + the real remaining
    list always verifies (and against the live root).
  * `stale_proof_refused` — REPLAY: a structurally-valid proof does NOT verify against any root
    committing to a DIFFERENT pending list (the `verify_dequeue_proof_against` form).
  * `dequeue_proof_unique` — two admitted proofs against the same old-root pin the SAME
    entry/remaining/new-root.
  * THE WELD (§4): `dequeue_root_written` constrains the EXISTING `queueDequeue` (the committed
    post-state's `message_root` IS the `newRoot` argument — the opaque parameter now has read-back
    semantics), and `queueDequeueProven` is the GUARDED form (proof-checked against the live
    `message_root` field, then the existing `queueDequeue`): tighten-only
    (`queueDequeueProven_eq`, so every QueueFactory keystone lifts), and
    `queueDequeueProven_pins_root_transition` — the admitted root pair is EXACTLY the modeled
    root transition `root (leafHash head :: rest) → root rest`.

Existing keystones are NOT touched: `QueueFactory.queueDequeue` keeps its statement; this module
only ADDS theorems over it and a guarded form on top of it.

## §7 — THE HARDENING UPGRADE, PROVED (level tags + length binding ⇒ NO zero-free restriction)

§7 models the LEVEL-TAGGED variant of `blake3_binary_root` — leaf nodes hashed under a leaf
prefix (`tagLeaf` = blake3(0x00 ‖ leaf)), internal nodes under a node prefix (`combine` =
blake3(0x01 ‖ l ‖ r)), and the root bound to the LIST LENGTH (`bindLen` = blake3(0x02 ‖ len ‖
root)) — and PROVES the strengthened carrier needs NO zero-free restriction:
`taggedRoot_injective` (injective on ALL leaf lists) under only the three per-domain CR carriers,
with NO `ZeroFree` and NO `LeafNonzero` hypothesis anywhere (`tagged_dequeue_proof_pins`). The
padding alias is killed by the length binding (`tagged_kills_pad_alias`; the prefix-free tags are
what make the three carriers jointly dischargeable at ONE BLAKE3 instance — `TagSep` kills the
single-leaf-passthrough/internal-node confusion the header item (2) names). The interim
`verifyDequeueStrict` zero-check becomes unnecessary under the upgraded scheme.

⚠ RUST ADOPTION IS A WIRE-AFFECTING CHANGE: switching `blake3_binary_root` to the tagged scheme
changes EVERY queue `message_root` on the wire (and any stored roots) — it needs a coordinated
root-format migration, NOT a drop-in patch. The Rust leg is HORIZONLOG'd (metatheory section),
deliberately not done here.

l4v bar: `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every keystone; crypto
enters ONLY as the named `RootCR`/`LeafCR`/`LeafNonzero` hypotheses (witnessed TRUE on a
reference injective root and FALSE on a colliding one — never `True`-shaped); no `sorry`, no
`:= True`, no `native_decide`. Non-vacuity both polarities, `#guard`-EXECUTED: honest proofs
verify and commit; forged entry / tampered post-root / dropped leaf / stale root / zero-padded
claim (strict) / non-owner all REFUSE.
-/
import Dregg2.Apps.QueueFactory
import Dregg2.Tactics

namespace Dregg2.Apps.QueueRoot

open Dregg2.Exec
open Dregg2.Exec.EffectsState (fieldOf)
open Dregg2.Apps.QueueFactory

variable {Entry : Type}

/-! ## §1 — the named CR carriers (the crypto floor, as hypotheses — never `True`). -/

/-- A leaf list with no zero leaf. Zero is BOTH the padding value and the empty-root sentinel in
the Rust scheme (`blake3_binary_root` pads with `[0u8;32]`; `MerkleRoot::empty()` is all-zeros),
so zero-freedom is exactly the precondition under which the padded root is a binding commitment
to the list. Honest leaves are never zero (`LeafNonzero`). -/
abbrev ZeroFree (ls : List Int) : Prop := ∀ l ∈ ls, l ≠ 0

/-- Cons preserves zero-freedom. -/
theorem ZeroFree.cons {l : Int} {ls : List Int} (hl : l ≠ 0) (hls : ZeroFree ls) :
    ZeroFree (l :: ls) := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · exact h ▸ hl
  · exact hls x h

/-- **`RootCR root` — the NAMED pending-window-root CR carrier**: equal roots of ZERO-FREE leaf
lists force equal lists. The `KeySetCR` shape (`Apps/PreRotation.lean`). At the deployed
`blake3_binary_root` this discharges to BLAKE3 CR (+ the leaf/node-separation and zero-freedom
facts itemized in the header — the zero-free restriction is LOAD-BEARING: full injectivity is
FALSE for the padded scheme, `padded_root_not_fully_injective`). -/
def RootCR (root : List Int → Int) : Prop :=
  ∀ ls₁ ls₂ : List Int, ZeroFree ls₁ → ZeroFree ls₂ → root ls₁ = root ls₂ → ls₁ = ls₂

/-- **`LeafCR leafHash` — the NAMED entry-leaf CR carrier**: equal leaf commitments force equal
entries. Models `hash_entry` (domain-tagged BLAKE3 over the canonical 88-byte entry preimage,
`TAG_QUEUE_ENTRY`); discharges to the BLAKE3 floor. -/
def LeafCR (leafHash : Entry → Int) : Prop :=
  ∀ a b : Entry, leafHash a = leafHash b → a = b

/-- **`LeafNonzero leafHash`** — no entry's leaf commitment is the zero padding/sentinel value
(BLAKE3 preimage resistance: producing an entry with `hash_entry = [0u8;32]` is infeasible).
This is what keeps HONEST pending windows zero-free. -/
def LeafNonzero (leafHash : Entry → Int) : Prop := ∀ e : Entry, leafHash e ≠ 0

/-- An honest pending window (an image of `leafHash`) is zero-free. -/
theorem leafImage_zero_free {leafHash : Entry → Int} (hLZ : LeafNonzero leafHash)
    (es : List Entry) : ZeroFree (es.map leafHash) := by
  intro l hl
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hl
  exact hLZ e

/-! ## §2 — the dequeue proof + the verifier (mirrors `storage/src/queue.rs` exactly). -/

/-- **The dequeue proof** (`queue.rs DequeueProof`, minus the explicitly-untrusted `position`
metadata): the claimed head entry, the pre/post roots, and the leaf commitments of the pending
entries remaining AFTER the head, in FIFO order. -/
structure DequeueProof (Entry : Type) where
  /-- The claimed dequeued head entry (the verifier recomputes its leaf). -/
  entry : Entry
  /-- The claimed pre-state pending-window root. -/
  oldRoot : Int
  /-- The claimed post-state pending-window root. -/
  newRoot : Int
  /-- Leaf commitments of the pending entries remaining after the head, FIFO order. -/
  remaining : List Int

/-- **`verifyDequeue` — `verify_dequeue_proof`, verbatim**: (1) `old_root` commits to
`[hash_entry(entry)] ++ remaining`; (2) `new_root` is exactly `remaining`. Fail-closed boolean
conjunction. (`merkle_root([]) = empty sentinel` in Rust is just `root []` here, so emptying
dequeues check through the same path.) -/
def verifyDequeue (root : List Int → Int) (leafHash : Entry → Int)
    (p : DequeueProof Entry) : Bool :=
  (root (leafHash p.entry :: p.remaining) == p.oldRoot) && (root p.remaining == p.newRoot)

/-- **`verifyDequeueAgainst` — `verify_dequeue_proof_against`, verbatim**: the structural check
PLUS `old_root == expected` (the verifier's tracked live root) — refuses replayed/stale proofs. -/
def verifyDequeueAgainst (root : List Int → Int) (leafHash : Entry → Int)
    (p : DequeueProof Entry) (expected : Int) : Bool :=
  (p.oldRoot == expected) && verifyDequeue root leafHash p

/-- **`verifyDequeueStrict` — the ONE-LINE HARDENING Rust should adopt** (see header ⚠): also
refuse any claimed remaining leaf equal to the zero padding value, closing the
non-canonical-post-root alias. Under THIS verifier the soundness pins are unconditional in the
claim (`strict_dequeue_proof_pins`). -/
def verifyDequeueStrict (root : List Int → Int) (leafHash : Entry → Int)
    (p : DequeueProof Entry) : Bool :=
  p.remaining.all (fun l => l != 0) && verifyDequeue root leafHash p

/-- The honest proof for dequeuing `head` off the window `leafHash head :: rest` — exactly what
`MerkleQueue::dequeue` emits (`old_root` from the pre-window, `new_root`/`remaining` from the
post-window). -/
def honestDequeueProof (root : List Int → Int) (leafHash : Entry → Int)
    (head : Entry) (rest : List Int) : DequeueProof Entry :=
  { entry := head
    oldRoot := root (leafHash head :: rest)
    newRoot := root rest
    remaining := rest }

/-! ## §3 — the dequeue-proof keystones. -/

/-- **`verifyDequeue_factors`.** An admitted proof factors into the two root equations — the
bridge every keystone reuses. -/
theorem verifyDequeue_factors {root : List Int → Int} {leafHash : Entry → Int}
    {p : DequeueProof Entry} (h : verifyDequeue root leafHash p = true) :
    root (leafHash p.entry :: p.remaining) = p.oldRoot ∧ root p.remaining = p.newRoot := by
  unfold verifyDequeue at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

/-- The `_against` form factors into the live-root pin plus the structural check. -/
theorem verifyDequeueAgainst_factors {root : List Int → Int} {leafHash : Entry → Int}
    {p : DequeueProof Entry} {expected : Int}
    (h : verifyDequeueAgainst root leafHash p expected = true) :
    p.oldRoot = expected ∧ verifyDequeue root leafHash p = true := by
  unfold verifyDequeueAgainst at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

/-- **VERIFIER SOUNDNESS (`dequeue_proof_pins`) — KEYSTONE.** If the checks pass under the named
CR carriers and the pre-root commits to the (zero-free) window `leafHash head :: rest`, then the
admitted proof PINS the transition: the claimed entry IS `head`, the claimed remaining IS `rest`,
and the post-root commits to EXACTLY `rest`. Any other claimed entry or post-list implies a hash
collision. (`hzfClaim` is the named residue of the Rust zero-pad gap — see header ⚠; the strict
verifier discharges it, `strict_dequeue_proof_pins`.) -/
theorem dequeue_proof_pins {root : List Int → Int} {leafHash : Entry → Int}
    (hRC : RootCR root) (hLC : LeafCR leafHash) (hLZ : LeafNonzero leafHash)
    {p : DequeueProof Entry} {head : Entry} {rest : List Int}
    (hzfClaim : ZeroFree p.remaining) (hzfReal : ZeroFree rest)
    (hpre : p.oldRoot = root (leafHash head :: rest))
    (hv : verifyDequeue root leafHash p = true) :
    p.entry = head ∧ p.remaining = rest ∧ p.newRoot = root rest := by
  obtain ⟨h1, h2⟩ := verifyDequeue_factors hv
  have hlist : leafHash p.entry :: p.remaining = leafHash head :: rest :=
    hRC _ _ (ZeroFree.cons (hLZ p.entry) hzfClaim) (ZeroFree.cons (hLZ head) hzfReal)
      (h1.trans hpre)
  injection hlist with hl hr
  refine ⟨hLC _ _ hl, hr, ?_⟩
  rw [← h2, hr]

/-- **FORGERY REFUSED (`dequeue_forgery_refused`) — the `rotate_compromise_resistant` shape.**
Under the named CR, a proof claiming ANY other entry, post-list, or post-root than the real
head-dequeue transition is REFUSED — an admitted forgery would BE a hash collision. -/
theorem dequeue_forgery_refused {root : List Int → Int} {leafHash : Entry → Int}
    (hRC : RootCR root) (hLC : LeafCR leafHash) (hLZ : LeafNonzero leafHash)
    {p : DequeueProof Entry} {head : Entry} {rest : List Int}
    (hzfClaim : ZeroFree p.remaining) (hzfReal : ZeroFree rest)
    (hpre : p.oldRoot = root (leafHash head :: rest))
    (hne : p.entry ≠ head ∨ p.remaining ≠ rest ∨ p.newRoot ≠ root rest) :
    verifyDequeue root leafHash p = false := by
  cases hv : verifyDequeue root leafHash p with
  | false => rfl
  | true =>
      obtain ⟨he, hr, hn⟩ := dequeue_proof_pins hRC hLC hLZ hzfClaim hzfReal hpre hv
      rcases hne with h | h | h
      · exact absurd he h
      · exact absurd hr h
      · exact absurd hn h

/-- **COMPLETENESS (`honest_dequeue_verifies`).** An honest dequeue — the real head, the real
remaining list — ALWAYS verifies. No crypto hypothesis needed (the verifier recomputes the same
function the producer used). -/
theorem honest_dequeue_verifies (root : List Int → Int) (leafHash : Entry → Int)
    (head : Entry) (rest : List Int) :
    verifyDequeue root leafHash (honestDequeueProof root leafHash head rest) = true := by
  simp [verifyDequeue, honestDequeueProof]

/-- **COMPLETENESS, `_against` form.** The honest proof verifies against the live pre-root. -/
theorem honest_dequeue_verifies_against (root : List Int → Int) (leafHash : Entry → Int)
    (head : Entry) (rest : List Int) :
    verifyDequeueAgainst root leafHash (honestDequeueProof root leafHash head rest)
      (root (leafHash head :: rest)) = true := by
  unfold verifyDequeueAgainst
  rw [honest_dequeue_verifies]
  simp [honestDequeueProof]

/-- **REPLAY REFUSED (`stale_proof_refused`) — the `verify_dequeue_proof_against` keystone.** A
structurally-valid proof does NOT verify against any root committing to a DIFFERENT (zero-free)
pending list: the live-root pin would force a collision. So a once-valid proof cannot be replayed
after the queue advances. -/
theorem stale_proof_refused {root : List Int → Int} {leafHash : Entry → Int}
    (hRC : RootCR root) (hLZ : LeafNonzero leafHash) {p : DequeueProof Entry}
    (hzfClaim : ZeroFree p.remaining) {ls : List Int} (hzf : ZeroFree ls)
    (hne : leafHash p.entry :: p.remaining ≠ ls)
    (hv : verifyDequeue root leafHash p = true) :
    verifyDequeueAgainst root leafHash p (root ls) = false := by
  unfold verifyDequeueAgainst
  have h1 := (verifyDequeue_factors hv).1
  have hbeq : (p.oldRoot == root ls) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    exact hne (hRC _ _ (ZeroFree.cons (hLZ p.entry) hzfClaim) hzf (h1.trans heq))
  rw [hbeq, Bool.false_and]

/-- **UNIQUENESS (`dequeue_proof_unique`).** Two admitted proofs against the same pre-root pin
the SAME entry, remaining list, and post-root — the pre-root leaves a prover no freedom at all. -/
theorem dequeue_proof_unique {root : List Int → Int} {leafHash : Entry → Int}
    (hRC : RootCR root) (hLC : LeafCR leafHash) (hLZ : LeafNonzero leafHash)
    {p₁ p₂ : DequeueProof Entry}
    (hz₁ : ZeroFree p₁.remaining) (hz₂ : ZeroFree p₂.remaining)
    (hold : p₁.oldRoot = p₂.oldRoot)
    (h₁ : verifyDequeue root leafHash p₁ = true) (h₂ : verifyDequeue root leafHash p₂ = true) :
    p₁.entry = p₂.entry ∧ p₁.remaining = p₂.remaining ∧ p₁.newRoot = p₂.newRoot := by
  obtain ⟨a1, b1⟩ := verifyDequeue_factors h₁
  obtain ⟨a2, b2⟩ := verifyDequeue_factors h₂
  have hlist : leafHash p₁.entry :: p₁.remaining = leafHash p₂.entry :: p₂.remaining :=
    hRC _ _ (ZeroFree.cons (hLZ p₁.entry) hz₁) (ZeroFree.cons (hLZ p₂.entry) hz₂)
      (a1.trans (hold.trans a2.symm))
  injection hlist with hl hr
  exact ⟨hLC _ _ hl, hr, by rw [← b1, ← b2, hr]⟩

/-! ### §3s — the STRICT verifier: the pins with NO hypothesis on the claim. -/

/-- The strict check makes the claimed remaining list zero-free — the hypothesis the plain Rust
verifier leaves open becomes a CHECKED fact. -/
theorem strict_claim_zero_free {root : List Int → Int} {leafHash : Entry → Int}
    {p : DequeueProof Entry} (h : verifyDequeueStrict root leafHash p = true) :
    ZeroFree p.remaining := by
  unfold verifyDequeueStrict at h
  simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at h
  exact fun l hl => h.1 l hl

/-- A strictly-admitted proof is plainly admitted (strict only tightens). -/
theorem verifyDequeueStrict_sound {root : List Int → Int} {leafHash : Entry → Int}
    {p : DequeueProof Entry} (h : verifyDequeueStrict root leafHash p = true) :
    verifyDequeue root leafHash p = true := by
  unfold verifyDequeueStrict at h
  exact (Bool.and_eq_true _ _ |>.mp h).2

/-- **`strict_dequeue_proof_pins`.** Under the hardened verifier the soundness pins hold with NO
zero-freedom hypothesis on the claim — the check supplies it. This is the precise payoff of the
recommended one-line Rust hardening. -/
theorem strict_dequeue_proof_pins {root : List Int → Int} {leafHash : Entry → Int}
    (hRC : RootCR root) (hLC : LeafCR leafHash) (hLZ : LeafNonzero leafHash)
    {p : DequeueProof Entry} {head : Entry} {rest : List Int} (hzfReal : ZeroFree rest)
    (hpre : p.oldRoot = root (leafHash head :: rest))
    (hv : verifyDequeueStrict root leafHash p = true) :
    p.entry = head ∧ p.remaining = rest ∧ p.newRoot = root rest :=
  dequeue_proof_pins hRC hLC hLZ (strict_claim_zero_free hv) hzfReal hpre
    (verifyDequeueStrict_sound hv)

/-! ## §3b — WHY the carrier is zero-free-restricted: the padding alias, EXHIBITED.

A reference padded binary root with the SAME zero-padding mechanism as `blake3_binary_root`
(layer-wise zero-pad of odd layers; for the 3-vs-4 witness below this coincides exactly with
Rust's pre-pad-to-pow2). The node hash is a stand-in — the alias is STRUCTURAL: padding is
indistinguishable from a zero leaf, so FULL injectivity is FALSE for any such scheme and the
`RootCR` restriction to zero-free lists is forced, not a convenience. -/

/-- Stand-in node combiner (structure only — the alias below holds for ANY combiner). -/
def refCombine (a b : Int) : Int := a * 37 + b + 1

/-- One tree layer: pair up, zero-padding the odd tail (the Rust padding mechanism). -/
def refLayer : List Int → List Int
  | [] => []
  | [a] => [refCombine a 0]
  | a :: b :: rest => refCombine a b :: refLayer rest

/-- Fuel-indexed layer fold (fuel = list length always suffices: layers halve). -/
def refRootAux : Nat → List Int → Int
  | _, [] => 0
  | _, [x] => x
  | 0, _ => 0
  | Nat.succ f, ls => refRootAux f (refLayer ls)

/-- The reference padded binary root: empty = 0 sentinel, single leaf = passthrough, else fold
layers — the `blake3_binary_root` shape. -/
def refRoot (ls : List Int) : Int := refRootAux ls.length ls

/-- **THE PADDING ALIAS.** A trailing zero leaf is indistinguishable from padding:
`refRoot [1,2,3] = refRoot [1,2,3,0]` — two DIFFERENT lists, ONE root, no hash collision
anywhere. Exactly the `blake3_binary_root([a,b,c]) = blake3_binary_root([a,b,c,0])` fact. -/
theorem refRoot_pad_alias : refRoot [1, 2, 3] = refRoot [1, 2, 3, 0] := by decide

/-- **FULL injectivity is FALSE for the padded scheme** — the witness that the `RootCR`
zero-free restriction is load-bearing (an unrestricted carrier could NEVER be discharged at the
deployed hash). -/
theorem padded_root_not_fully_injective :
    ¬ (∀ ls₁ ls₂ : List Int, refRoot ls₁ = refRoot ls₂ → ls₁ = ls₂) := fun h =>
  absurd (h [1, 2, 3] [1, 2, 3, 0] refRoot_pad_alias) (by decide)

/-! ## §4 — THE WELD: constrain `QueueFactory`'s opaque `newRoot`.

`queueDequeue`'s statement is UNCHANGED (every existing keystone intact); we ADD (i) read-back
semantics for the opaque parameter (`dequeue_root_written` / `enqueue_root_written`), and (ii)
the guarded form `queueDequeueProven` — the dequeue proof checked against the LIVE
`message_root` field (the `_against` form, so stale proofs refuse), then the existing
`queueDequeue` with the proof's own `newRoot`. Tighten-only, so owner-gating / no-underflow /
fail-closed-empty all lift verbatim. -/

/-- **`dequeue_root_written` — the EXISTING keystone surface, constrained.** A committed
`queueDequeue` writes EXACTLY its `newRoot` argument into `message_root` — the formerly-opaque
parameter now has proved read-back semantics, so pinning `newRoot` pins the committed field. -/
theorem dequeue_root_written {k k' : RecordKernelState} {e actor : CellId} {newRoot : Int}
    (h : queueDequeue k e actor newRoot = some k') :
    fieldOf messageRootField (k'.cell e) = newRoot := by
  unfold queueDequeue at h
  by_cases hg : actor = fieldOf ownerField (k.cell e) ∧ 0 < qOccupancy k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h; subst h
    exact qWriteField_same _ e messageRootField newRoot
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- The enqueue twin: a committed `queueEnqueue` writes exactly its `newRoot` argument. -/
theorem enqueue_root_written {k k' : RecordKernelState} {e actor : CellId}
    {senders : List CellId} {newRoot : Int}
    (h : queueEnqueue k e actor senders newRoot = some k') :
    fieldOf messageRootField (k'.cell e) = newRoot := by
  unfold queueEnqueue at h
  by_cases hg : senders.contains actor ∧ qOccupancy k e < qCap k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h; subst h
    exact qWriteField_same _ e messageRootField newRoot
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`queueDequeueProven` — the GUARDED dequeue.** Verify the proof against the cell's LIVE
`message_root` (the `_against` form: structural + live-root pin), then run the EXISTING
`queueDequeue` installing the proof's `newRoot`. Fail-closed on either gate. -/
def queueDequeueProven (root : List Int → Int) (leafHash : Entry → Int)
    (k : RecordKernelState) (e actor : CellId) (p : DequeueProof Entry) :
    Option RecordKernelState :=
  if verifyDequeueAgainst root leafHash p (fieldOf messageRootField (k.cell e)) = true then
    queueDequeue k e actor p.newRoot
  else none

/-- A committed proven dequeue factors: the proof verified against the live root AND the
underlying `queueDequeue` committed. -/
theorem queueDequeueProven_factors {root : List Int → Int} {leafHash : Entry → Int}
    {k k' : RecordKernelState} {e actor : CellId} {p : DequeueProof Entry}
    (h : queueDequeueProven root leafHash k e actor p = some k') :
    verifyDequeueAgainst root leafHash p (fieldOf messageRootField (k.cell e)) = true ∧
      queueDequeue k e actor p.newRoot = some k' := by
  unfold queueDequeueProven at h
  by_cases hg : verifyDequeueAgainst root leafHash p (fieldOf messageRootField (k.cell e)) = true
  · rw [if_pos hg] at h; exact ⟨hg, h⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **TIGHTEN-ONLY.** A committed proven dequeue IS the existing `queueDequeue` — so every
QueueFactory keystone (owner gate, no-underflow, fail-closed empty, bal-neutrality) lifts. -/
theorem queueDequeueProven_eq {root : List Int → Int} {leafHash : Entry → Int}
    {k k' : RecordKernelState} {e actor : CellId} {p : DequeueProof Entry}
    (h : queueDequeueProven root leafHash k e actor p = some k') :
    queueDequeue k e actor p.newRoot = some k' :=
  (queueDequeueProven_factors h).2

/-- The lift, witnessed: a committed proven dequeue preserves the no-underflow invariant
(KEYSTONE (b) of QueueFactory, verbatim through the new gate). -/
theorem queueDequeueProven_preserves_no_underflow {root : List Int → Int}
    {leafHash : Entry → Int} {k k' : RecordKernelState} {e actor : CellId}
    {p : DequeueProof Entry}
    (h : queueDequeueProven root leafHash k e actor p = some k') (hpre : qNoUnderflow k e) :
    qNoUnderflow k' e :=
  dequeue_preserves_no_underflow (queueDequeueProven_eq h) hpre

/-- **THE WELD KEYSTONE (`queueDequeueProven_pins_root_transition`).** If the cell's live
`message_root` commits to the (zero-free) pending window `leafHash head :: rest`, then a
COMMITTED proven dequeue's root pair is EXACTLY the modeled root transition: the claimed entry
IS `head`, the claimed remaining IS `rest`, and the committed post-state's `message_root` IS
`root rest`. The opaque-`newRoot` disease instance, closed. -/
theorem queueDequeueProven_pins_root_transition {root : List Int → Int}
    {leafHash : Entry → Int} (hRC : RootCR root) (hLC : LeafCR leafHash)
    (hLZ : LeafNonzero leafHash) {k k' : RecordKernelState} {e actor : CellId}
    {p : DequeueProof Entry} {head : Entry} {rest : List Int}
    (hzfClaim : ZeroFree p.remaining) (hzfReal : ZeroFree rest)
    (hpre : fieldOf messageRootField (k.cell e) = root (leafHash head :: rest))
    (h : queueDequeueProven root leafHash k e actor p = some k') :
    p.entry = head ∧ p.remaining = rest ∧
      fieldOf messageRootField (k'.cell e) = root rest := by
  obtain ⟨hv, hd⟩ := queueDequeueProven_factors h
  obtain ⟨hold, hver⟩ := verifyDequeueAgainst_factors hv
  obtain ⟨he, hr, hn⟩ := dequeue_proof_pins hRC hLC hLZ hzfClaim hzfReal
    (hold.trans hpre) hver
  exact ⟨he, hr, by rw [dequeue_root_written hd, hn]⟩

/-- **FORGERY FAIL-CLOSED on the weld.** Under the named CR, a proof claiming any entry other
than the real head NEVER commits — refused before the state is touched. -/
theorem queueDequeueProven_refuses_forgery {root : List Int → Int} {leafHash : Entry → Int}
    (hRC : RootCR root) (hLC : LeafCR leafHash) (hLZ : LeafNonzero leafHash)
    {k : RecordKernelState} {e actor : CellId} {p : DequeueProof Entry}
    {head : Entry} {rest : List Int}
    (hzfClaim : ZeroFree p.remaining) (hzfReal : ZeroFree rest)
    (hpre : fieldOf messageRootField (k.cell e) = root (leafHash head :: rest))
    (hne : p.entry ≠ head) :
    queueDequeueProven root leafHash k e actor p = none := by
  unfold queueDequeueProven
  rw [if_neg (fun hg => by
    obtain ⟨hold, hver⟩ := verifyDequeueAgainst_factors hg
    obtain ⟨he, _, _⟩ := dequeue_proof_pins hRC hLC hLZ hzfClaim hzfReal
      (hold.trans hpre) hver
    exact hne he)]

/-- **REPLAY/STALE FAIL-CLOSED on the weld.** A proof whose claimed window differs from what the
LIVE `message_root` commits to never commits — once the queue advances, old proofs are dead. -/
theorem queueDequeueProven_refuses_stale {root : List Int → Int} {leafHash : Entry → Int}
    (hRC : RootCR root) (hLZ : LeafNonzero leafHash)
    {k : RecordKernelState} {e actor : CellId} {p : DequeueProof Entry}
    (hzfClaim : ZeroFree p.remaining) {ls : List Int} (hzf : ZeroFree ls)
    (hpre : fieldOf messageRootField (k.cell e) = root ls)
    (hne : leafHash p.entry :: p.remaining ≠ ls) :
    queueDequeueProven root leafHash k e actor p = none := by
  unfold queueDequeueProven
  rw [if_neg (fun hg => by
    obtain ⟨hold, hver⟩ := verifyDequeueAgainst_factors hg
    have h1 := (verifyDequeue_factors hver).1
    exact hne (hRC _ _ (ZeroFree.cons (hLZ p.entry) hzfClaim) hzf
      (h1.trans (hold.trans hpre))))]

/-- **COMPLETENESS on the weld.** The owner, holding the honest proof for the live window,
ALWAYS commits when the queue is non-empty — the proof gate never blocks the honest dequeue. -/
theorem queueDequeueProven_commits_honest {root : List Int → Int} {leafHash : Entry → Int}
    {k : RecordKernelState} {e actor : CellId} (head : Entry) (rest : List Int)
    (hpre : fieldOf messageRootField (k.cell e) = root (leafHash head :: rest))
    (howner : (actor : Int) = fieldOf ownerField (k.cell e)) (hne : 0 < qOccupancy k e) :
    (queueDequeueProven root leafHash k e actor
        (honestDequeueProof root leafHash head rest)).isSome := by
  have hv := honest_dequeue_verifies_against root leafHash head rest
  simp only [queueDequeueProven, hpre]
  rw [if_pos hv]
  exact nonempty_queue_dequeues k e actor _ howner hne

/-! ## §5 — NON-VACUITY, both polarities, EXECUTED.

The CR carriers witnessed TRUE (an injective reference root/leaf, so the CR-consuming keystones
FIRE) and FALSE (a colliding root falsifies `RootCR`; the padded `refRoot` falsifies FULL
injectivity — §3b); fast executable instances + a concrete queue world for `#guard`s: honest
proofs verify and commit; forged entry / tampered post-root / dropped leaf / stale root /
zero-padded claim (strict) / non-owner all refuse. -/

/-- Injective `Int → Nat` (sign interleaving) — the building block for the reference CR root. -/
def intCode (i : Int) : Nat := if 0 ≤ i then 2 * i.toNat else 2 * (-i).toNat + 1

theorem intCode_injective : Function.Injective intCode := by
  intro a b h
  unfold intCode at h
  split at h <;> split at h <;> omega

/-- A reference CR root: the injective `Encodable` encoding of the sign-interleaved list (the
`PreRotation.demoHash` pattern). -/
def demoRoot (ls : List Int) : Int := ((Encodable.encode (ls.map intCode) : ℕ) : ℤ)

/-- The reference root IS collision-resistant (even unrestricted) — `RootCR` witnessed TRUE. -/
theorem demoRoot_CR : RootCR demoRoot := by
  intro ls₁ ls₂ _ _ h
  unfold demoRoot at h
  exact List.map_injective_iff.mpr intCode_injective
    (Encodable.encode_injective (by exact_mod_cast h))

/-- A COLLIDING root (constant) FALSIFIES `RootCR` — the carrier is not `True`-shaped. -/
def badRoot (_ : List Int) : Int := 0

theorem badRoot_not_CR : ¬ RootCR badRoot := fun hbad =>
  absurd (hbad [1] [2] (by decide) (by decide) rfl) (by decide)

/-- A reference CR + nonzero leaf hash over `Nat` entries. -/
def demoLeaf (n : Nat) : Int := (n : Int) + 1

theorem demoLeaf_CR : LeafCR demoLeaf := by
  intro a b h; unfold demoLeaf at h; omega

theorem demoLeaf_nonzero : LeafNonzero demoLeaf := by
  intro e; unfold demoLeaf; omega

/-- The CR-consuming soundness keystone FIRES on the reference instances: a forged head entry
(`9` against a window headed by `4`) is refused. -/
example :
    verifyDequeue demoRoot demoLeaf
      { entry := 9, oldRoot := demoRoot [demoLeaf 4, demoLeaf 5],
        newRoot := demoRoot [demoLeaf 5], remaining := [demoLeaf 5] } = false :=
  dequeue_forgery_refused demoRoot_CR demoLeaf_CR demoLeaf_nonzero
    (by decide) (by decide) rfl (Or.inl (by decide))

/-- Fast executable instances for the `#guard` demos (the keystones use `demoRoot`/`demoLeaf`). -/
def tinyLeaf (n : Nat) : Int := (n : Int) * 7 + 3
def tinyRoot (ls : List Int) : Int := ls.foldl (fun a x => a * 1000 + x + 1) 0

-- (i) COMPLETENESS, executed: the honest dequeue proof verifies (incl. the emptying dequeue):
#guard verifyDequeue tinyRoot tinyLeaf (honestDequeueProof tinyRoot tinyLeaf 4 [tinyLeaf 5, tinyLeaf 6])
#guard verifyDequeue tinyRoot tinyLeaf (honestDequeueProof tinyRoot tinyLeaf 4 [])
#guard verifyDequeueAgainst tinyRoot tinyLeaf (honestDequeueProof tinyRoot tinyLeaf 4 [tinyLeaf 5])
        (tinyRoot [tinyLeaf 4, tinyLeaf 5])

-- (ii) FORGED ENTRY refused (the claimed head is not the committed head):
#guard verifyDequeue tinyRoot tinyLeaf
        { entry := 9, oldRoot := tinyRoot [tinyLeaf 4, tinyLeaf 5],
          newRoot := tinyRoot [tinyLeaf 5], remaining := [tinyLeaf 5] } == false

-- (iii) TAMPERED POST-ROOT refused (right head, wrong new_root):
#guard verifyDequeue tinyRoot tinyLeaf
        { entry := 4, oldRoot := tinyRoot [tinyLeaf 4, tinyLeaf 5],
          newRoot := tinyRoot [tinyLeaf 5] + 1, remaining := [tinyLeaf 5] } == false

-- (iv) DROPPED LEAF refused (claimed remaining omits a pending entry):
#guard verifyDequeue tinyRoot tinyLeaf
        { entry := 4, oldRoot := tinyRoot [tinyLeaf 4, tinyLeaf 5, tinyLeaf 6],
          newRoot := tinyRoot [tinyLeaf 5], remaining := [tinyLeaf 5] } == false

-- (v) REPLAY refused: the honest proof does NOT verify against the ADVANCED root:
#guard verifyDequeueAgainst tinyRoot tinyLeaf (honestDequeueProof tinyRoot tinyLeaf 4 [tinyLeaf 5])
        (tinyRoot [tinyLeaf 5]) == false

-- (vi) THE ZERO-PAD GAP, executed: a zero-leaf claim passes the PLAIN verifier shape but the
-- STRICT verifier refuses it (the one-line hardening's tooth):
#guard verifyDequeue tinyRoot tinyLeaf
        { entry := 4, oldRoot := tinyRoot [tinyLeaf 4, 0], newRoot := tinyRoot [0], remaining := [0] }
#guard verifyDequeueStrict tinyRoot tinyLeaf
        { entry := 4, oldRoot := tinyRoot [tinyLeaf 4, 0], newRoot := tinyRoot [0], remaining := [0] }
        == false
#guard verifyDequeueStrict tinyRoot tinyLeaf (honestDequeueProof tinyRoot tinyLeaf 4 [tinyLeaf 5])

-- (vii) THE PADDING ALIAS, executed (§3b): one root, two lists — and a sanity non-collision:
#guard refRoot [1, 2, 3] == refRoot [1, 2, 3, 0]
#guard (refRoot [1, 2, 3] == refRoot [1, 2, 4]) == false

/-- The WELD world: cell 0 is a queue (capacity 3, owner 1, head_seq 2, tail_seq 0 — occupancy 2)
whose `message_root` is the MODELED root of the pending window `[tinyLeaf 4, tinyLeaf 5]`. -/
def qrWorld : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun c =>
      if c = 0 then .record
        [ (headSeqField, .int 2), (tailSeqField, .int 0), (capacityField, .int 3)
        , (ownerField, .int 1), (senderSetField, .int 0)
        , (messageRootField, .int (tinyRoot [tinyLeaf 4, tinyLeaf 5])) ]
      else .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun _ _ => 0 }

-- (viii) the owner's honest proven dequeue COMMITS...
#guard (queueDequeueProven tinyRoot tinyLeaf qrWorld 0 1
          (honestDequeueProof tinyRoot tinyLeaf 4 [tinyLeaf 5])).isSome
-- ...the post message_root IS the modeled root of the remaining window (the pinned transition):
#guard ((queueDequeueProven tinyRoot tinyLeaf qrWorld 0 1
          (honestDequeueProof tinyRoot tinyLeaf 4 [tinyLeaf 5])).map
            (fun s => fieldOf messageRootField (s.cell 0))) == some (tinyRoot [tinyLeaf 5])
-- ...and the tail advanced (the existing QueueFactory semantics, lifted through the gate):
#guard ((queueDequeueProven tinyRoot tinyLeaf qrWorld 0 1
          (honestDequeueProof tinyRoot tinyLeaf 4 [tinyLeaf 5])).map
            (fun s => qTail s 0)) == some 1

-- (ix) FORGED ENTRY refused on the weld (wrong claimed head — wrong old_root recomputation):
#guard (queueDequeueProven tinyRoot tinyLeaf qrWorld 0 1
          { entry := 9, oldRoot := tinyRoot [tinyLeaf 4, tinyLeaf 5],
            newRoot := tinyRoot [tinyLeaf 5], remaining := [tinyLeaf 5] }).isNone

-- (x) TAMPERED POST-ROOT refused on the weld:
#guard (queueDequeueProven tinyRoot tinyLeaf qrWorld 0 1
          { entry := 4, oldRoot := tinyRoot [tinyLeaf 4, tinyLeaf 5],
            newRoot := 999, remaining := [tinyLeaf 5] }).isNone

-- (xi) STALE PROOF refused on the weld (old_root ≠ the live message_root):
#guard (queueDequeueProven tinyRoot tinyLeaf qrWorld 0 1
          (honestDequeueProof tinyRoot tinyLeaf 5 [])).isNone

-- (xii) the OWNER GATE composes: a non-owner with the HONEST proof still cannot dequeue:
#guard (queueDequeueProven tinyRoot tinyLeaf qrWorld 0 0
          (honestDequeueProof tinyRoot tinyLeaf 4 [tinyLeaf 5])).isNone

/-! ## §7 — THE HARDENING UPGRADE: level-tagged + length-bound root is injective on ALL lists.

The model of the recommended `blake3_binary_root` replacement (header §7): leaves enter through
`tagLeaf` (the 0x00-prefixed leaf hash), internal nodes through `combine` (the 0x01-prefixed
node hash), and the final root is bound to the list length through `bindLen` (the 0x02-prefixed
length wrap). The tree mechanism is the SAME layer-wise zero-padded fold as the deployed scheme
(`tLayer`/`tRoot` mirror §3b's `refLayer`/`refRoot` shape) — ONLY the tagging and the length
binding are added, so the theorem isolates exactly what the hardening buys. -/

/-- **`PairCR combine` — the node-domain CR carrier**: the 2-to-1 node hash is pairwise
injective (`blake3(0x01 ‖ l ‖ r)` collision resistance). -/
def PairCR (combine : Int → Int → Int) : Prop :=
  ∀ a b a' b', combine a b = combine a' b' → a = a' ∧ b = b'

/-- **`LenBindCR bindLen` — the length-binding CR carrier**: the root wrap is injective in BOTH
the length and the tree root (`blake3(0x02 ‖ len ‖ root)` collision resistance). -/
def LenBindCR (bindLen : Nat → Int → Int) : Prop :=
  ∀ n x m y, bindLen n x = bindLen m y → n = m ∧ x = y

/-- **`TagSep tagLeaf combine` — the leaf/node DOMAIN SEPARATION** the 0x00/0x01 prefixes give:
no leaf hash is ever an internal-node hash. This is what makes the per-domain carriers jointly
dischargeable at ONE BLAKE3 instance, and it kills the single-leaf-passthrough confusion
(`tag_separation_kills_passthrough`). -/
def TagSep (tagLeaf : Int → Int) (combine : Int → Int → Int) : Prop :=
  ∀ x a b, tagLeaf x ≠ combine a b

/-- One tree layer: pair up with the node hash, zero-padding the odd tail (the SAME padding
mechanism as the deployed `blake3_binary_root` / §3b `refLayer`). -/
def tLayer (combine : Int → Int → Int) : List Int → List Int
  | [] => []
  | [a] => [combine a 0]
  | a :: b :: rest => combine a b :: tLayer combine rest

/-- A layer halves (rounding up): the shape is a function of the LENGTH alone — which is why
binding the length pins the whole tree shape. -/
theorem tLayer_length (combine : Int → Int → Int) :
    ∀ ls : List Int, (tLayer combine ls).length = (ls.length + 1) / 2
  | [] => by simp [tLayer]
  | [_] => by simp [tLayer]
  | _ :: _ :: rest => by
      show (tLayer combine rest).length + 1 = _
      rw [tLayer_length combine rest]
      simp only [List.length_cons]
      omega

/-- The layered binary fold (the `blake3_binary_root` mechanism: empty = 0 sentinel, single =
passthrough, else fold a layer and recurse). -/
def tRoot (combine : Int → Int → Int) : List Int → Int
  | [] => 0
  | [x] => x
  | a :: b :: rest => tRoot combine (combine a b :: tLayer combine rest)
  termination_by ls => ls.length
  decreasing_by
    simp only [List.length_cons, tLayer_length]
    omega

/-- The single-leaf passthrough, named (the WF equation surfaced for rewriting). -/
theorem tRoot_singleton (combine : Int → Int → Int) (x : Int) : tRoot combine [x] = x := by
  simp [tRoot]

/-- **The tagged, length-bound root** — the hardened `blake3_binary_root`: tag every leaf, fold
the layers with the node hash, bind the length. -/
def taggedRoot (tagLeaf : Int → Int) (combine : Int → Int → Int) (bindLen : Nat → Int → Int)
    (ls : List Int) : Int :=
  bindLen ls.length (tRoot combine (ls.map tagLeaf))

/-- A layer is injective on SAME-LENGTH lists under the node-domain carrier (pairwise peeling;
the odd tail peels against the shared pad). -/
theorem tLayer_inj {combine : Int → Int → Int} (hC : PairCR combine) :
    ∀ ls₁ ls₂ : List Int, ls₁.length = ls₂.length →
      tLayer combine ls₁ = tLayer combine ls₂ → ls₁ = ls₂
  | [], [], _, _ => rfl
  | [], [_], hlen, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; omega
  | [], _ :: _ :: _, hlen, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; omega
  | [_], [], hlen, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; omega
  | _ :: _ :: _, [], hlen, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; omega
  | [_], _ :: _ :: _, hlen, _ => by
      simp only [List.length_cons, List.length_nil] at hlen; omega
  | _ :: _ :: _, [_], hlen, _ => by
      simp only [List.length_cons, List.length_nil] at hlen; omega
  | [a], [b], _, h => by
      simp only [tLayer, List.cons.injEq, and_true] at h
      rw [(hC _ _ _ _ h).1]
  | a :: b :: r₁, c :: d :: r₂, hlen, h => by
      simp only [tLayer, List.cons.injEq] at h
      obtain ⟨hac, hbd⟩ := hC _ _ _ _ h.1
      have hlen' : r₁.length = r₂.length := by
        simp only [List.length_cons] at hlen; omega
      rw [hac, hbd, tLayer_inj hC r₁ r₂ hlen' h.2]

/-- **The layered fold is injective on SAME-LENGTH lists** under the node-domain carrier alone
(equal lengths ⇒ equal tree SHAPES ⇒ the pairwise node hash peels to the leaves). The length
binding supplies the same-length premise on all lists — that composition is the headline. -/
theorem tRoot_inj {combine : Int → Int → Int} (hC : PairCR combine) :
    ∀ ls₁ ls₂ : List Int, ls₁.length = ls₂.length →
      tRoot combine ls₁ = tRoot combine ls₂ → ls₁ = ls₂
  | [], [], _, _ => rfl
  | [], [_], hlen, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; omega
  | [], _ :: _ :: _, hlen, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; omega
  | [_], [], hlen, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; omega
  | _ :: _ :: _, [], hlen, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; omega
  | [_], _ :: _ :: _, hlen, _ => by
      simp only [List.length_cons, List.length_nil] at hlen; omega
  | _ :: _ :: _, [_], hlen, _ => by
      simp only [List.length_cons, List.length_nil] at hlen; omega
  | [a], [b], _, h => by
      rw [tRoot_singleton, tRoot_singleton] at h
      rw [h]
  | a :: b :: r₁, c :: d :: r₂, hlen, h => by
      have hlen' : r₁.length = r₂.length := by
        simp only [List.length_cons] at hlen; omega
      simp only [tRoot] at h
      have hlist : combine a b :: tLayer combine r₁ = combine c d :: tLayer combine r₂ :=
        tRoot_inj hC _ _
          (by simp only [List.length_cons, tLayer_length]; omega) h
      injection hlist with h1 h2
      obtain ⟨hac, hbd⟩ := hC _ _ _ _ h1
      rw [hac, hbd, tLayer_inj hC r₁ r₂ hlen' h2]
  termination_by ls₁ _ _ _ => ls₁.length
  decreasing_by
    simp only [List.length_cons, tLayer_length]
    omega

/-- **THE HEADLINE — `taggedRoot_injective`: the hardened root is injective on ALL leaf lists.**
NO zero-free restriction, NO leaf-nonzero carrier: under the three per-domain CR carriers
(realizable at one BLAKE3 via the 0x00/0x01/0x02 prefixes), equal tagged roots force equal lists
— different lengths die at the length binding; same lengths share the tree shape and peel by the
node hash to the tagged leaves. This is the theorem that justifies the Rust hardening upgrade:
the padded scheme's `RootCR`-on-zero-free-lists weakens to plain injectivity. -/
theorem taggedRoot_injective {tagLeaf : Int → Int} {combine : Int → Int → Int}
    {bindLen : Nat → Int → Int}
    (hT : Function.Injective tagLeaf) (hC : PairCR combine) (hB : LenBindCR bindLen) :
    ∀ ls₁ ls₂ : List Int,
      taggedRoot tagLeaf combine bindLen ls₁ = taggedRoot tagLeaf combine bindLen ls₂ →
        ls₁ = ls₂ := by
  intro ls₁ ls₂ h
  obtain ⟨hlen, hroot⟩ := hB _ _ _ _ h
  have hmap : ls₁.map tagLeaf = ls₂.map tagLeaf :=
    tRoot_inj hC _ _ (by simp [hlen]) hroot
  exact List.map_injective_iff.mpr hT hmap

/-- The hardened root discharges the §1 `RootCR` carrier WITHOUT using the zero-free premises —
every existing zero-free-keyed keystone lifts to it for free. -/
theorem taggedRoot_RootCR {tagLeaf : Int → Int} {combine : Int → Int → Int}
    {bindLen : Nat → Int → Int}
    (hT : Function.Injective tagLeaf) (hC : PairCR combine) (hB : LenBindCR bindLen) :
    RootCR (taggedRoot tagLeaf combine bindLen) :=
  fun ls₁ ls₂ _ _ h => taggedRoot_injective hT hC hB ls₁ ls₂ h

/-- **The upgrade payoff at the verifier — `tagged_dequeue_proof_pins`**: under the hardened
root, verifier soundness holds with NO `ZeroFree` hypothesis on the claim, NO `ZeroFree` on the
real window, and NO `LeafNonzero` carrier — the §3 pins, unconditional in the claim and free of
the interim `verifyDequeueStrict` check. -/
theorem tagged_dequeue_proof_pins {tagLeaf : Int → Int} {combine : Int → Int → Int}
    {bindLen : Nat → Int → Int} {leafHash : Entry → Int}
    (hT : Function.Injective tagLeaf) (hC : PairCR combine) (hB : LenBindCR bindLen)
    (hLC : LeafCR leafHash)
    {p : DequeueProof Entry} {head : Entry} {rest : List Int}
    (hpre : p.oldRoot = taggedRoot tagLeaf combine bindLen (leafHash head :: rest))
    (hv : verifyDequeue (taggedRoot tagLeaf combine bindLen) leafHash p = true) :
    p.entry = head ∧ p.remaining = rest
      ∧ p.newRoot = taggedRoot tagLeaf combine bindLen rest := by
  obtain ⟨h1, h2⟩ := verifyDequeue_factors hv
  have hlist : leafHash p.entry :: p.remaining = leafHash head :: rest :=
    taggedRoot_injective hT hC hB _ _ (h1.trans hpre)
  injection hlist with hl hr
  exact ⟨hLC _ _ hl, hr, by rw [← h2, hr]⟩

/-- **The padding alias DIES** (the §3b/`refRoot_pad_alias` attack, killed): a trailing zero leaf
changes the LENGTH, so the bound root differs — `[a,b,c]` and `[a,b,c,0]` can no longer share a
root. (Length binding does the killing; the proof needs only the carriers.) -/
theorem tagged_kills_pad_alias {tagLeaf : Int → Int} {combine : Int → Int → Int}
    {bindLen : Nat → Int → Int}
    (_hT : Function.Injective tagLeaf) (_hC : PairCR combine) (hB : LenBindCR bindLen) :
    taggedRoot tagLeaf combine bindLen [1, 2, 3]
      ≠ taggedRoot tagLeaf combine bindLen [1, 2, 3, 0] := by
  intro h
  obtain ⟨hlen, -⟩ := hB _ _ _ _ h
  simp at hlen

/-- **The padding alias is STRUCTURAL in the un-bound fold** (NEG companion, ANY combiner): the
bare layered fold still aliases `[1,2,3]` with `[1,2,3,0]` — tagging/CR alone cannot save the
deployed scheme; the length binding is load-bearing. -/
theorem tRoot_pad_alias (combine : Int → Int → Int) :
    tRoot combine [1, 2, 3] = tRoot combine [1, 2, 3, 0] := by
  simp [tRoot, tLayer]

/-- **`TagSep` kills the passthrough confusion** (header item (2)): a single-leaf root — which
the scheme passes through as the tagged leaf itself — can NEVER equal an internal-node value, so
no cross-level reinterpretation exists. In the deployed UNtagged Rust scheme this non-collision
is merely computational; the 0x00/0x01 prefixes make it structural. -/
theorem tag_separation_kills_passthrough {tagLeaf : Int → Int} {combine : Int → Int → Int}
    (hS : TagSep tagLeaf combine) (x a b : Int) :
    tRoot combine [tagLeaf x] ≠ combine a b := by
  rw [tRoot_singleton]
  exact hS x a b

/-! ### §7b — the carriers witnessed BOTH polarities + executable teeth. -/

/-- A reference node hash with PROVED pairwise injectivity (the `Encodable` pairing over the
sign-interleaved codes — the `demoRoot` pattern): `PairCR` witnessed TRUE. -/
def demoCombine (a b : Int) : Int := ((Encodable.encode (intCode a, intCode b) : ℕ) : ℤ)

theorem demoCombine_CR : PairCR demoCombine := by
  intro a b a' b' h
  unfold demoCombine at h
  have h' : Encodable.encode (intCode a, intCode b)
      = Encodable.encode (intCode a', intCode b') := by exact_mod_cast h
  have hp := Encodable.encode_injective h'
  exact ⟨intCode_injective (congrArg Prod.fst hp), intCode_injective (congrArg Prod.snd hp)⟩

/-- A reference leaf tag with proved injectivity. -/
def demoTagLeaf (x : Int) : Int := 2 * x + 1

theorem demoTagLeaf_inj : Function.Injective demoTagLeaf := by
  intro a b h
  unfold demoTagLeaf at h
  omega

/-- A reference length binding with PROVED `LenBindCR` (the same `Encodable` pairing). -/
def demoBind (n : Nat) (x : Int) : Int := ((Encodable.encode (n, intCode x) : ℕ) : ℤ)

theorem demoBind_CR : LenBindCR demoBind := by
  intro n x m y h
  unfold demoBind at h
  have h' : Encodable.encode (n, intCode x) = Encodable.encode (m, intCode y) := by
    exact_mod_cast h
  have hp := Encodable.encode_injective h'
  exact ⟨congrArg Prod.fst hp, intCode_injective (congrArg Prod.snd hp)⟩

/-- A binding that IGNORES the length FALSIFIES `LenBindCR` — the carrier is not `True`-shaped
(and exactly such a scheme is the deployed one). -/
def badBind (_ : Nat) (x : Int) : Int := x

theorem badBind_not_CR : ¬ LenBindCR badBind := fun hbad =>
  absurd (hbad 0 5 1 5 rfl).1 (by decide)

/-- The headline FIRES on the reference instances: the hardened root separates the §3b alias
pair on ALL-lists injectivity (no zero-freedom invoked anywhere). -/
theorem demo_tagged_separates_alias :
    taggedRoot demoTagLeaf demoCombine demoBind [1, 2, 3]
      ≠ taggedRoot demoTagLeaf demoCombine demoBind [1, 2, 3, 0] :=
  tagged_kills_pad_alias demoTagLeaf_inj demoCombine_CR demoBind_CR

/-- Fast executable tagged instance for the `#guard` teeth (cheap length binding suffices to
EXHIBIT the alias dying; the proved carriers above are the soundness side). -/
def tinyTagged (ls : List Int) : Int :=
  tRoot refCombine (ls.map demoTagLeaf) * 1000 + ls.length

-- (xiii) the UN-BOUND fold still aliases (the structural NEG, executed on the layered fold):
#guard tRoot refCombine [1, 2, 3] == tRoot refCombine [1, 2, 3, 0]
-- ...and the length-bound tagged scheme separates the same pair (the upgrade's tooth, executed):
#guard (tinyTagged [1, 2, 3] == tinyTagged [1, 2, 3, 0]) == false
-- (xiv) the §5 zero-pad ATTACK SHAPE dies wholesale: a window and its zero-extended forgery
-- no longer share a root (lengths differ under the binding):
#guard (tinyTagged [demoTagLeaf 4] == tinyTagged [demoTagLeaf 4, 0]) == false
-- (xv) completeness survives the upgrade: the honest dequeue proof verifies against the
-- tagged root (no crypto needed — the verifier recomputes the same function):
#guard verifyDequeue tinyTagged tinyLeaf (honestDequeueProof tinyTagged tinyLeaf 4 [tinyLeaf 5])
#guard verifyDequeue tinyTagged tinyLeaf (honestDequeueProof tinyTagged tinyLeaf 4 [])

/-! ## §6 — axiom hygiene: every keystone pins {propext, Classical.choice, Quot.sound}. -/

#assert_axioms ZeroFree.cons
#assert_axioms leafImage_zero_free
#assert_axioms verifyDequeue_factors
#assert_axioms verifyDequeueAgainst_factors
#assert_axioms dequeue_proof_pins
#assert_axioms dequeue_forgery_refused
#assert_axioms honest_dequeue_verifies
#assert_axioms honest_dequeue_verifies_against
#assert_axioms stale_proof_refused
#assert_axioms dequeue_proof_unique
#assert_axioms strict_claim_zero_free
#assert_axioms verifyDequeueStrict_sound
#assert_axioms strict_dequeue_proof_pins
#assert_axioms refRoot_pad_alias
#assert_axioms padded_root_not_fully_injective
#assert_axioms dequeue_root_written
#assert_axioms enqueue_root_written
#assert_axioms queueDequeueProven_factors
#assert_axioms queueDequeueProven_eq
#assert_axioms queueDequeueProven_preserves_no_underflow
#assert_axioms queueDequeueProven_pins_root_transition
#assert_axioms queueDequeueProven_refuses_forgery
#assert_axioms queueDequeueProven_refuses_stale
#assert_axioms queueDequeueProven_commits_honest
#assert_axioms intCode_injective
#assert_axioms demoRoot_CR
#assert_axioms badRoot_not_CR
#assert_axioms demoLeaf_CR
#assert_axioms demoLeaf_nonzero

-- §7 (the hardening upgrade):
#assert_axioms tLayer_length
#assert_axioms tLayer_inj
#assert_axioms tRoot_inj
#assert_axioms taggedRoot_injective
#assert_axioms taggedRoot_RootCR
#assert_axioms tagged_dequeue_proof_pins
#assert_axioms tagged_kills_pad_alias
#assert_axioms tRoot_pad_alias
#assert_axioms tag_separation_kills_passthrough
#assert_axioms demoCombine_CR
#assert_axioms demoBind_CR
#assert_axioms badBind_not_CR
#assert_axioms demo_tagged_separates_alias

end Dregg2.Apps.QueueRoot
