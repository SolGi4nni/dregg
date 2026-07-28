/-
# Dregg2.Circuit.Emit.EffectVmEmitRotationR — the rotated state block, PARAMETRIC in the
register count R (the 16-vs-24-vs-32 measurement probes).

`EffectVmEmitRotation.lean` pins the R=16 staged emission (the deployed reference; its
artifacts are byte-frozen). THIS module re-expresses that emission as a FUNCTION of the
register count R, so the register-count decision (`.docs-history-noclaude/ROTATION-CUTOVER.md` — registers are
ALWAYS-PAID limbs in every turn proof's commitment chain, heap fields are METERED umem rows)
can be settled by MEASUREMENT instead of vibes:

  * **§1 the layout, as functions of R** — every column index of the rotated block
    (`capRootCol R = R+1`, …, `irootCol R = R+7`, `stateCommitCol R = R+8`); the R=16
    instance `#guard`-pins to the deployed constants (the pins do not move).
  * **§2 the arity-{2,4} chunking** — `chunk31` groups the post-head limbs into 3-wide
    chip absorptions (digest + 3 = arity 4) with a singleton tail (digest + 1 = arity 2);
    the deployed chip AIR pins arity ∈ {2,4}, so an arity-3 tail REFUSES — the chunking
    NEVER produces one (`#guard`ed per R). The iroot rides its own arity-2 final site,
    LITERALLY LAST, at every R (the `CommitBindsMMR` last-limb discipline).
  * **§3 `wireCommitR`** — the chained commitment over an ARBITRARY pre-iroot limb list.
    `wireCommitR_eq_pinned`: at R=16 it IS the pinned `wireCommit`, by `rfl`. The keystone
    `wireCommitR_binds` holds PARAMETRICALLY in R (equal-length limb lists, equal chained
    commits ⇒ equal lists ∧ equal iroots, under the ONE `Poseidon2SpongeCR` floor) — no
    per-R axiom, no per-R re-proof: instantiating the list length at R+7 IS the R-register
    binding theorem.
  * **§4 the probe descriptors** — `rotationProbeVmDescriptorR R` (v1 grammar) and its
    graduated IR-v2 form; the R=16 instance graduates to BYTE-IDENTICAL wire JSON as the
    pinned `rotationProbeVmDescriptor2` (`#guard` on the emitted strings — the strongest
    possible no-drift statement). R=24 and R=32 are emitted for the Rust measurement
    harness (`circuit/src/descriptor_ir2.rs` — proof bytes / prove ms / verify ms /
    opened-values bytes / chip rows, plus tamper teeth per R).
  * **§5 per-R welds** — the site walks pin `STATE_COMMIT = wireCommitR` of the row's own
    limbs (R=24/R=32), and the end-to-end keystones (`rotationProbeR{24,32}_pins_commit`,
    `…_commit_binds_published`) re-prove the pinned module's §4 story at each measured R.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; crypto only as the named
`Poseidon2SpongeCR` hypothesis. STAGED: nothing here rides
the live wire; the R=24/R=32 artifacts exist to be MEASURED.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotation

namespace Dregg2.Circuit.Emit.EffectVmEmitRotationR

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotation
open Dregg2.Circuit.RotationLayout (RotatedLimbs)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Lightclient.MMR (mroot mroot_binds_or_collides)
open Dregg2.Substrate.Heap (refSponge)

set_option autoImplicit false

/-! ## §1 — the rotated layout as functions of the register count R. -/

/-- The cap-map root limb column at register count `R`. -/
def capRootCol (R : Nat) : Nat := R + 1
/-- The nullifier-map root limb column. -/
def nullifierRootCol (R : Nat) : Nat := R + 2
/-- The heap-map root limb column. -/
def heapRootCol (R : Nat) : Nat := R + 3
/-- The lifecycle scalar limb column. -/
def lifecycleCol (R : Nat) : Nat := R + 4
/-- The epoch scalar limb column. -/
def epochCol (R : Nat) : Nat := R + 5
/-- The committed-height scalar limb column. -/
def committedHeightCol (R : Nat) : Nat := R + 6
/-- The receipt-index MMR root carrier, absorbed literally LAST. -/
def irootCol (R : Nat) : Nat := R + 7
/-- The rotated state commitment carrier. -/
def stateCommitCol (R : Nat) : Nat := R + 8
/-- The rotated block width: 1 cells root + R registers + 3 map roots + 3 scalars + iroot
+ state_commit. -/
def blockSize (R : Nat) : Nat := R + 9
/-- The chain carriers start right after the block. -/
def chainBase (R : Nat) : Nat := R + 9

-- The R=16 instance IS the pinned layout (the deployed constants do not move).
#guard capRootCol 16 == CAP_ROOT
#guard nullifierRootCol 16 == NULLIFIER_ROOT
#guard heapRootCol 16 == HEAP_ROOT
#guard lifecycleCol 16 == LIFECYCLE
#guard epochCol 16 == EPOCH
#guard committedHeightCol 16 == COMMITTED_HEIGHT
#guard irootCol 16 == IROOT
#guard stateCommitCol 16 == STATE_COMMIT
#guard blockSize 16 == BLOCK_SIZE
#guard chainBase 16 == CHAIN_BASE

/-! ## §2 — the arity-{2,4} chunking (the chip pins arity ∈ {2,4}; arity 3 REFUSES). -/

/-- Group the post-head fresh inputs into chip absorptions: 3-wide groups while ≥ 3 remain
(digest + 3 = arity 4), then singletons (digest + 1 = arity 2). NEVER a pair (digest + 2 =
arity 3 — the deployed chip AIR refuses it). -/
def chunk31 {α : Type _} : List α → List (List α)
  | a :: b :: c :: rest => [a, b, c] :: chunk31 rest
  | [a, b] => [[a], [b]]
  | [a] => [[a]]
  | [] => []

/-- The chunk count as a function of the input LENGTH alone. -/
def chunkCount : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => chunkCount n + 1

theorem chunk31_length {α : Type _} : ∀ xs : List α, (chunk31 xs).length = chunkCount xs.length
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: rest => by
      simp only [chunk31, List.length_cons, chunkCount]
      exact congrArg (· + 1) (chunk31_length rest)

/-- The chunking loses nothing and reorders nothing: flattening recovers the input. -/
theorem chunk31_flatten {α : Type _} : ∀ xs : List α, (chunk31 xs).flatten = xs
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: c :: rest => by
      simp only [chunk31, List.flatten_cons, chunk31_flatten rest]
      rfl

/-- The per-site fresh-input column groups at register count `R`: the 4-wide head
(`cells_root, r0, r1, r2`), the `chunk31` body over columns `4..R+6`, the iroot ALONE last. -/
def siteChunks (R : Nat) : List (List Nat) :=
  [0, 1, 2, 3] :: (chunk31 ((List.range (R + 7)).drop 4) ++ [[irootCol R]])

/-- Number of chained-absorption sites. -/
def numSites (R : Nat) : Nat := (siteChunks R).length
/-- Number of intermediate chain carriers (every site but the final one). -/
def numChain (R : Nat) : Nat := numSites R - 1
/-- The probe trace width: the rotated block + the chain carriers. -/
def probeWidth (R : Nat) : Nat := blockSize R + numChain R

-- The three measured points: R=16 → 9 sites / width 33 (the pinned shape);
-- R=24 → 11 sites (EXACT 3-fill: no mid arity-2 site) / width 43; R=32 → 15 sites / width 55.
#guard numSites 16 == 9
#guard numChain 16 == NUM_CHAIN
#guard probeWidth 16 == PROBE_WIDTH
#guard numSites 24 == 11
#guard numChain 24 == 10
#guard probeWidth 24 == 43
#guard numSites 32 == 15
#guard numChain 32 == 14
#guard probeWidth 32 == 55

/-! ## §3 — `wireCommitR`: the chained commitment, parametric in the limb list. -/

/-- Fold the chained absorption: each later site hashes the running digest in front of its
fresh inputs. -/
def chainFrom (hash : List ℤ → ℤ) : ℤ → List (List ℤ) → ℤ
  | acc, [] => acc
  | acc, c :: cs => chainFrom hash (hash (acc :: c)) cs

theorem chainFrom_snoc (hash : List ℤ → ℤ) (acc : ℤ) (cs : List (List ℤ)) (c : List ℤ) :
    chainFrom hash acc (cs ++ [c]) = hash (chainFrom hash acc cs :: c) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons d ds ih => simp only [List.cons_append, chainFrom, ih]

/-- **`wireCommitR`** — the chained rotated commitment over an arbitrary pre-iroot limb list
`l` (length `R + 7` at register count R): the 4-wide head, the `chunk31` body, the iroot as
its own arity-2 final site, LITERALLY LAST. -/
def wireCommitR (hash : List ℤ → ℤ) (l : List ℤ) (ir : ℤ) : ℤ :=
  chainFrom hash (hash (l.take 4)) (chunk31 (l.drop 4) ++ [[ir]])

/-- **The R=16 instance IS the pinned `wireCommit`** — definitionally. The parametric
emission reproduces the deployed shape exactly; nothing moved. -/
theorem wireCommitR_eq_pinned (hash : List ℤ → ℤ) (s : RotatedLimbs) (ir : ℤ) :
    wireCommitR hash s.toList ir = wireCommit hash s ir := rfl

/-- The chained fold is injective under the CR floor, given equal CHUNK COUNTS: equal final
digests force equal seeds and equal chunk lists (peel from the outermost hash, rightward in). -/
theorem chainFrom_inj (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ∀ {cs cs' : List (List ℤ)} {acc acc' : ℤ}, cs.length = cs'.length →
      chainFrom hash acc cs = chainFrom hash acc' cs' → acc = acc' ∧ cs = cs' := by
  intro cs
  induction cs using List.reverseRecOn with
  | nil =>
    intro cs' acc acc' hlen h
    have hnil : cs' = [] := List.length_eq_zero_iff.mp hlen.symm
    subst hnil
    exact ⟨h, rfl⟩
  | append_singleton ds c ih =>
    intro cs' acc acc' hlen h
    rcases List.eq_nil_or_concat cs' with rfl | ⟨ds', c', rfl⟩
    · simp at hlen
    · simp only [List.concat_eq_append] at hlen h ⊢
      rw [chainFrom_snoc, chainFrom_snoc] at h
      have h2 := hCR _ _ h
      simp only [List.cons.injEq] at h2
      obtain ⟨hch, hcc⟩ := h2
      have hlen' : ds.length = ds'.length := by
        simpa using hlen
      obtain ⟨hacc, hds⟩ := ih hlen' hch
      exact ⟨hacc, by rw [hds, hcc]⟩

/-- **THE PARAMETRIC ANTI-GHOST KEYSTONE** (the `wireCommit_binds` shape, in R): for ANY
register count — any equal-length pre-iroot limb lists — equal chained wire commits force
equal limb lists AND equal iroots, under the ONE named CR floor. No per-R axiom, no per-R
re-proof: length `R + 7` IS the R-register binding theorem (R = 16 recovers the pinned
`wireCommit_binds` through `wireCommitR_eq_pinned`). -/
theorem wireCommitR_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {l l' : List ℤ} {ir ir' : ℤ} (hlen : l.length = l'.length)
    (h : wireCommitR hash l ir = wireCommitR hash l' ir') : l = l' ∧ ir = ir' := by
  unfold wireCommitR at h
  rw [chainFrom_snoc, chainFrom_snoc] at h
  have h1 := hCR _ _ h
  simp only [List.cons.injEq, and_true] at h1
  obtain ⟨hchain, hir⟩ := h1
  obtain ⟨hhead, hchunks⟩ := chainFrom_inj hash hCR
    (by rw [chunk31_length, chunk31_length, List.length_drop, List.length_drop, hlen]) hchain
  have htake : l.take 4 = l'.take 4 := hCR _ _ hhead
  have hdrop : l.drop 4 = l'.drop 4 := by
    have := congrArg List.flatten hchunks
    rwa [chunk31_flatten, chunk31_flatten] at this
  refine ⟨?_, hir⟩
  rw [← List.take_append_drop 4 l, ← List.take_append_drop 4 l', htake, hdrop]

/-- The log tooth, parametric: with `ir := mroot log`, equal chained commits force EQUAL
receipt logs at every R (tamper / truncate / extend / REORDER all refused). -/
theorem wireCommitR_binds_log (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {l l' : List ℤ} {L L' : List ℤ} (hlen : l.length = l'.length)
    (h : wireCommitR hash l (mroot hash L) = wireCommitR hash l' (mroot hash L')) :
    l = l' ∧ L = L' :=
  ⟨(wireCommitR_binds hash hCR hlen h).1,
   (mroot_binds_or_collides hash (wireCommitR_binds hash hCR hlen h).2).resolve_right
     (fun hc => hc.1 (hCR _ _ hc.2))⟩

#assert_axioms chainFrom_inj
#assert_axioms wireCommitR_binds
#assert_axioms wireCommitR_binds_log

/-! ## §3.8 — `wireCommitR8`: the FAITHFUL 8-FELT chained commitment (Phase B-ROTATION).

The 1-felt chain above (`chainFrom`/`wireCommitR`) threads a SINGLE ℤ accumulator — ~31-bit,
collision in seconds. The faithful commitment threads an 8-FELT carrier: each step is ONE wide
permutation `permW (acc ++ c)` exposing 8 output lanes (`acc : List ℤ`, length 8), so EVERY
intermediate carrier is 8 felts — there is NO 31-bit intermediate (the anti-laundering crux; a
1-felt-chain-with-wide-final-squeeze is the forbidden laundered version). The Rust twin is
`poseidon2::wire_commit_8` over `single_perm_compress`; the in-circuit faithfulness floor is the
wide chip lever `chip_lookup_sound_N` (the `permW`-parametric wide squeeze, CHIP_RATE = 16 ≥ the
11 inputs of a carrier‖3-limb step).

The binding keystone carries NO collision-resistance floor: it is stated as EXTRACTION (bind, or hand
back the colliding pair), so the chain logic is the same fold as the 1-felt proof with the carrier
widened from `ℤ` to `List ℤ`, and the crypto residual is priced separately rather than assumed. -/

/-! ### The wide binding, WITHOUT a floor.

⚑ There used to be a carrier here: `Poseidon2WideCR permW := ∀ xs ys, permW xs = permW ys → xs = ys`
— the "wide collision-resistance floor", doc-marked REALIZABLE. It was **FALSE at deployed
parameters** and it has been **DELETED** (VACUITY-SWEEP FINDING 2). The deployed
`single_perm_compress` squeezes 8 BOUNDED BabyBear lanes, so its range is FINITE while `List ℤ` is
infinite: collisions EXIST by pigeonhole (`VacuitySweepTeeth.widePerm_not_injective_babyBear`).
Collision-resistance means collisions are hard to FIND, never that they do not EXIST. Every consumer
conditioned on it — `chainFrom8_inj`, `wireCommitR8_binds`, and the nine hypothesis uses downstream —
was **VACUOUSLY TRUE at real parameters**, and `#assert_axioms` was blind to it: the proofs were
clean; the HYPOTHESIS was the flaw.

What replaces it, below, assumes NOTHING. The chain walk `chainCollFind` LOCATES the colliding step
as a total function, and `wireCommit8Find` resolves the head — so an equivocation on the faithful
8-felt commitment either forces the limbs equal or HANDS BACK the two distinct lists at which the
deployed permutation actually collides. That is a true theorem at deployed parameters, where the old
one was empty. The probabilistic residual is priced in `Circuit.InjectiveFloorRegrounded` §3
(`wireCommitR8_binds_advantage_bound`, a real collision game at an explicit adversary class `Eff`,
with the `Eff` obligation in the open). -/

/-- The wide permutation's output-width contract: every squeeze is exactly 8 felts (true of the
Rust `single_perm_compress`, which reads `state[0..8]`). This is what keeps the carrier 8-wide
THROUGHOUT — the anti-laundering invariant (no narrow intermediate). -/
def Poseidon2Width8 (permW : List ℤ → List ℤ) : Prop :=
  ∀ xs : List ℤ, (permW xs).length = 8

/-- Fold the 8-FELT chained absorption: each later site permutes the running 8-felt carrier IN
FRONT of its fresh inputs (`acc ++ c`), the 8-felt output becoming the next carrier. -/
def chainFrom8 (permW : List ℤ → List ℤ) : List ℤ → List (List ℤ) → List ℤ
  | acc, [] => acc
  | acc, c :: cs => chainFrom8 permW (permW (acc ++ c)) cs

theorem chainFrom8_snoc (permW : List ℤ → List ℤ) (acc : List ℤ) (cs : List (List ℤ))
    (c : List ℤ) :
    chainFrom8 permW acc (cs ++ [c]) = permW (chainFrom8 permW acc cs ++ c) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons d ds ih => simp only [List.cons_append, chainFrom8, ih]

/-- A `chainFrom8` over a non-empty chunk list lands length 8 (its last step is a `permW`, whose
output is width 8). The EMPTY case returns the seed, so a width-8 seed stays width 8. -/
theorem chainFrom8_len (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW) :
    ∀ {acc : List ℤ} {cs : List (List ℤ)}, acc.length = 8 → (chainFrom8 permW acc cs).length = 8 := by
  intro acc cs
  induction cs generalizing acc with
  | nil => intro hacc; simpa [chainFrom8] using hacc
  | cons d ds ih => intro _; exact ih (hW (acc ++ d))

/-- **`wireCommitR8`** — the chained 8-FELT commitment over an arbitrary pre-iroot limb list:
the 4-wide head (no carrier), the `chunk31` body (carrier ‖ 3 limbs = arity 11), the iroot as
its own final site, LITERALLY LAST. The final chunk is `[ir, 0, 0]` (carrier ‖ iroot ‖ 2 zero
pads = arity 11): `permW` is invariant to trailing zero inputs, so the two pads do NOT change the
digest value, but they land the EMITTED final chip lookup on the chip AIR's WIDE (arity-11) row
(the deployed Rust chip pins `in7..in10 == 0` for every arity != 11, refusing the arity-9 final
whose in7/in8 = carrier-lane-7/iroot are nonzero). Returns 8 felts. -/
def wireCommitR8 (permW : List ℤ → List ℤ) (l : List ℤ) (ir : ℤ) : List ℤ :=
  chainFrom8 permW (permW (l.take 4)) (chunk31 (l.drop 4) ++ [[ir, 0, 0]])

/-- `IsCollW permW p` — the pair `p` is a genuine collision of the wide permutation. A predicate about
SPECIFIC lists, never `∃ xs ys, …`: at deployed parameters an existence claim is unconditionally true
by pigeonhole and so carries no content (`InjectiveFloorRegrounded` §0). -/
def IsCollW (permW : List ℤ → List ℤ) (p : List ℤ × List ℤ) : Prop :=
  p.1 ≠ p.2 ∧ permW p.1 = permW p.2

/-- "Is this pair a genuine collision?" is DECIDABLE (equality of `List ℤ` is) — so the extractor may
branch on it and remain a total function, no `Classical.choice` in the reduction. -/
instance decidableIsCollW (permW : List ℤ → List ℤ) (p : List ℤ × List ℤ) :
    Decidable (IsCollW permW p) := by
  unfold IsCollW
  infer_instance

/-- **⚑ THE CHAIN WALK.** Step the two 8-felt chains together. At each step the two `permW` arguments
are `acc ++ c` and `acc' ++ c'`; if they COLLIDE (equal images, distinct arguments) return them, else
carry on with the two new carriers. If the walk runs out of chunks, return the two seeds — the caller
(`wireCommit8Find`) resolves that case at the head.

Note the third possibility the `else` silently absorbs and `chainCollFind_spec` handles: the two
arguments may have DIFFERENT `permW` images at this step and the chains still re-converge later. That
is why the walk continues rather than concluding, and it is exactly the case a "peel from the outside"
proof gets for free but a FUNCTION must be written to survive. -/
def chainCollFind (permW : List ℤ → List ℤ) :
    List ℤ → List (List ℤ) → List ℤ → List (List ℤ) → List ℤ × List ℤ
  | acc, c :: ds, acc', c' :: ds' =>
      if permW (acc ++ c) = permW (acc' ++ c') ∧ (acc ++ c) ≠ (acc' ++ c') then
        (acc ++ c, acc' ++ c')
      else
        chainCollFind permW (permW (acc ++ c)) ds (permW (acc' ++ c')) ds'
  | acc, _, acc', _ => (acc, acc')

/-- **⚑ THE WALK IS CORRECT — this REPLACES the deleted `chainFrom8_inj`.** For two chains of EQUAL
chunk count over width-8 carriers with EQUAL final digests: EITHER the seeds and the chunk lists agree
outright, OR the walk lands on a genuine `permW` collision. The old theorem's peel, restated so that
the failure branch produces a WITNESS instead of consuming an injectivity hypothesis that the deployed
permutation refutes. -/
theorem chainCollFind_spec (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW) :
    ∀ {cs cs' : List (List ℤ)} {acc acc' : List ℤ}, cs.length = cs'.length →
      acc.length = 8 → acc'.length = 8 →
      chainFrom8 permW acc cs = chainFrom8 permW acc' cs' →
      (acc = acc' ∧ cs = cs') ∨ IsCollW permW (chainCollFind permW acc cs acc' cs') := by
  intro cs
  induction cs with
  | nil =>
    intro cs' acc acc' hlen _ _ h
    have hnil : cs' = [] := List.length_eq_zero_iff.mp hlen.symm
    subst hnil
    exact Or.inl ⟨h, rfl⟩
  | cons c ds ih =>
    intro cs' acc acc' hlen hacc hacc' h
    cases cs' with
    | nil => simp at hlen
    | cons c' ds' =>
      simp only [chainFrom8] at h
      have hlen' : ds.length = ds'.length := by simpa using hlen
      by_cases hif : permW (acc ++ c) = permW (acc' ++ c') ∧ (acc ++ c) ≠ (acc' ++ c')
      · refine Or.inr ?_
        show IsCollW permW (chainCollFind permW acc (c :: ds) acc' (c' :: ds'))
        rw [chainCollFind, if_pos hif]
        exact ⟨hif.2, hif.1⟩
      · rcases ih hlen' (hW (acc ++ c)) (hW (acc' ++ c')) h with ⟨himg, hds⟩ | hcoll
        · -- the recursive carriers agree; with the failed test that forces the ARGUMENTS to agree.
          refine Or.inl ⟨?_, ?_⟩
          · have hargs : acc ++ c = acc' ++ c' := by
              by_contra hne
              exact hif ⟨himg, hne⟩
            exact (List.append_inj hargs (by rw [hacc, hacc'])).1
          · have hargs : acc ++ c = acc' ++ c' := by
              by_contra hne
              exact hif ⟨himg, hne⟩
            rw [(List.append_inj hargs (by rw [hacc, hacc'])).2, hds]
        · refine Or.inr ?_
          show IsCollW permW (chainCollFind permW acc (c :: ds) acc' (c' :: ds'))
          rw [chainCollFind, if_neg hif]
          exact hcoll

/-- **⚑ THE `wireCommitR8` EXTRACTOR.** Run the chain walk over the deployed commitment's chunk
decomposition (`head = permW (l.take 4)`, body `= chunk31 (l.drop 4)`, then the iroot site `[ir,0,0]`
LAST). If the walk found a genuine collision, that is the answer; otherwise the walk proved the seeds
and chunks agree, which — given the claims DIFFER — forces the collision to be at the HEAD, so return
the two 4-wide head blocks. -/
def wireCommit8Find (permW : List ℤ → List ℤ) (l : List ℤ) (ir : ℤ) (l' : List ℤ) (ir' : ℤ) :
    List ℤ × List ℤ :=
  let r := chainCollFind permW (permW (l.take 4)) (chunk31 (l.drop 4) ++ [[ir, 0, 0]])
    (permW (l'.take 4)) (chunk31 (l'.drop 4) ++ [[ir', 0, 0]])
  if IsCollW permW r then r else (l.take 4, l'.take 4)

/-- **`WireColl permW l ir l' ir'`** — the pair the extractor RETURNS on this equivocation is a genuine
collision of the deployed wide permutation. The named disjunct every consumer below carries instead of
the deleted floor. -/
def WireColl (permW : List ℤ → List ℤ) (l : List ℤ) (ir : ℤ) (l' : List ℤ) (ir' : ℤ) : Prop :=
  IsCollW permW (wireCommit8Find permW l ir l' ir')

/-- **⚑ THE EXTRACTOR IS CORRECT — a `wireCommitR8` equivocation always yields a REAL `permW`
collision.** Two DISTINCT `(limbs, iroot)` claims of EQUAL limb length with the SAME 8-felt chained
commitment produce two DISTINCT lists with the SAME `permW` image. -/
theorem wireCommit8Find_spec (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW)
    {l l' : List ℤ} {ir ir' : ℤ} (hlen : l.length = l'.length)
    (hne : ¬ (l = l' ∧ ir = ir'))
    (h : wireCommitR8 permW l ir = wireCommitR8 permW l' ir') :
    WireColl permW l ir l' ir' := by
  unfold wireCommitR8 at h
  by_cases hif : IsCollW permW (chainCollFind permW (permW (l.take 4))
      (chunk31 (l.drop 4) ++ [[ir, 0, 0]]) (permW (l'.take 4)) (chunk31 (l'.drop 4) ++ [[ir', 0, 0]]))
  · show IsCollW permW (wireCommit8Find permW l ir l' ir')
    rw [wireCommit8Find, if_pos hif]
    exact hif
  · show IsCollW permW (wireCommit8Find permW l ir l' ir')
    rw [wireCommit8Find, if_neg hif]
    have hclen : (chunk31 (l.drop 4) ++ [[ir, 0, 0]]).length
        = (chunk31 (l'.drop 4) ++ [[ir', 0, 0]]).length := by
      rw [List.length_append, List.length_append, chunk31_length, chunk31_length,
        List.length_drop, List.length_drop, hlen]
      simp
    rcases chainCollFind_spec permW hW hclen (hW (l.take 4)) (hW (l'.take 4)) h with
      ⟨hseed, hcs⟩ | hcoll
    · -- the walk found nothing: seeds AND chunk lists agree, so the break is at the HEAD.
      obtain ⟨hbody, hir⟩ := List.append_inj' hcs rfl
      have hir' : ir = ir' := by simpa using hir
      have hdrop : l.drop 4 = l'.drop 4 := by
        have := congrArg List.flatten hbody
        rwa [chunk31_flatten, chunk31_flatten] at this
      refine ⟨fun htake => hne ⟨?_, hir'⟩, hseed⟩
      replace htake : List.take 4 l = List.take 4 l' := htake
      rw [← List.take_append_drop 4 l, ← List.take_append_drop 4 l', htake, hdrop]
    · exact absurd hcoll hif

/-- **THE PARAMETRIC ANTI-GHOST KEYSTONE, 8-FELT — UNCONDITIONAL** (`wireCommitR_binds`, wide carrier,
with the false floor REMOVED): equal 8-felt chained wire commits over equal-length pre-iroot limb lists
EITHER force equal limb lists AND equal iroots, OR exhibit a genuine collision of the deployed wide
permutation at the two lists `wireCommit8Find` returns. The genuine ~124-bit binding the light client
trusts — now stated so that it says something about the REAL permutation.

⚑ **STRENGTH, stated honestly.** The old `wireCommitR8_binds` concluded a bare equality from
`Poseidon2WideCR permW`, which the deployed `single_perm_compress` REFUTES; at deployed parameters that
theorem was vacuous. This one is a disjunction — formally weaker, but it HOLDS of the deployed
permutation, which the old one did not. Nothing that was genuinely proved has been given up. -/
theorem wireCommitR8_binds_or_collides (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW)
    {l l' : List ℤ} {ir ir' : ℤ} (hlen : l.length = l'.length)
    (h : wireCommitR8 permW l ir = wireCommitR8 permW l' ir') :
    (l = l' ∧ ir = ir') ∨ WireColl permW l ir l' ir' := by
  by_cases hne : l = l' ∧ ir = ir'
  · exact Or.inl hne
  · exact Or.inr (wireCommit8Find_spec permW hW hlen hne h)

/-- **⚑ THE NO-STRENGTH-LOST TOOTH.** The deleted `wireCommitR8_binds` is EXACTLY the injective special
case of the unconditional keystone: assume the injectivity the old carrier asserted and the collision
disjunct is impossible, so the equality falls out. Nothing that was genuinely proved was given up by
the deletion — what was given up is the pretence that the deployed permutation satisfies the
hypothesis. Stated as a standalone bridge, deliberately NOT as a hypothesis on any deployed keystone:
`Function.Injective permW` is FALSE at deployed BabyBear parameters
(`VacuitySweepTeeth.widePerm_not_injective_babyBear`), so a keystone carrying it would be right back
where this sweep started. -/
theorem wireCommitR8_binds_of_injective (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW) (hinj : Function.Injective permW)
    {l l' : List ℤ} {ir ir' : ℤ} (hlen : l.length = l'.length)
    (h : wireCommitR8 permW l ir = wireCommitR8 permW l' ir') : l = l' ∧ ir = ir' := by
  rcases wireCommitR8_binds_or_collides permW hW hlen h with hEq | ⟨hne, himg⟩
  · exact hEq
  · exact absurd (hinj himg) hne

/-- **(CANARY — the collision disjunct is REFUTABLE, so the disjunction is not a free pass.)** At an
injective width-8 permutation the extractor's returned pair is NOT a collision, so
`wireCommitR8_binds_or_collides` cannot discharge itself by taking the right branch: the binding has to
do the work. A disjunction whose right side were always available would carry no more content than
`True`. -/
theorem wireColl_refutable_of_injective (permW : List ℤ → List ℤ)
    (hinj : Function.Injective permW) (l : List ℤ) (ir : ℤ) (l' : List ℤ) (ir' : ℤ) :
    ¬ WireColl permW l ir l' ir' := by
  rintro ⟨hne, himg⟩
  exact hne (hinj himg)

#assert_axioms chainCollFind_spec
#assert_axioms wireCommit8Find_spec
#assert_axioms wireCommitR8_binds_or_collides
#assert_axioms wireCommitR8_binds_of_injective
#assert_axioms wireColl_refutable_of_injective

-- NON-VACUITY at the measured widths, both polarities (Horner toy sponge): a low register,
-- a high register, the committed height, and the iroot each move the commit; the honest
-- recompute is stable.
/-- A concrete R=24 pre-iroot limb payload (31 distinct limbs). -/
def demoPre24 : List ℤ := (List.range 31).map (fun i => 100 + (i : ℤ))
/-- A concrete R=32 pre-iroot limb payload (39 distinct limbs). -/
def demoPre32 : List ℤ := (List.range 39).map (fun i => 200 + (i : ℤ))

#guard wireCommitR refSponge demoPre24 7 != wireCommitR refSponge (demoPre24.set 1 999) 7
#guard wireCommitR refSponge demoPre24 7 != wireCommitR refSponge (demoPre24.set 24 999) 7
#guard wireCommitR refSponge demoPre24 7 != wireCommitR refSponge (demoPre24.set 30 999) 7
#guard wireCommitR refSponge demoPre24 7 != wireCommitR refSponge demoPre24 8
#guard wireCommitR refSponge demoPre24 7 == wireCommitR refSponge demoPre24 7
#guard wireCommitR refSponge demoPre32 7 != wireCommitR refSponge (demoPre32.set 1 999) 7
#guard wireCommitR refSponge demoPre32 7 != wireCommitR refSponge (demoPre32.set 32 999) 7
#guard wireCommitR refSponge demoPre32 7 != wireCommitR refSponge (demoPre32.set 38 999) 7
#guard wireCommitR refSponge demoPre32 7 != wireCommitR refSponge demoPre32 8

-- NON-VACUITY for the 8-FELT chain (`wireCommitR8`): a width-8 Horner toy `refWide` (each lane =
-- `refSponge (tag :: xs)`, so all 8 lanes avalanche over the whole input). The wide commit
-- DISTINGUISHES a low-register flip, a HIGH-position flip (the fields-root sub-limb's place — the
-- collision-distinguishing tooth at the spec level), and the iroot, AND is stable on the honest
-- recompute — the same both-polarity discipline the 1-felt guards above carry, at full width.
def refWide : List ℤ → List ℤ := fun xs => (List.range 8).map (fun t => refSponge ((t : ℤ) :: xs))

#guard (refWide [1, 2, 3]).length == 8
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide (demoPre24.set 1 999) 7
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide (demoPre24.set 30 999) 7   -- HIGH limb
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide demoPre24 8                -- iroot bound
#guard wireCommitR8 refWide demoPre24 7 == wireCommitR8 refWide demoPre24 7                -- honest stable
-- the INTERMEDIATE-CARRIER tooth at the spec level: an EARLY limb (folded mid-chain) still moves
-- the published 8-felt commit (the carrier is 8-wide throughout, no narrow waist).
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide (demoPre24.set 5 999) 7

/-! ## §4 — the probe descriptors, parametric in R. -/

/-- A site's input list at walk index `k`: the previous digest (except at the head) followed
by the fresh columns. -/
def siteInputs (k : Nat) (c : List Nat) : List HashInput :=
  (if k == 0 then [] else [HashInput.digest (k - 1)]) ++ c.map .col

/-- Build the ordered chip sites from the chunk groups: site `k`'s digest rides chain carrier
`k`; the FINAL site's digest is the state commitment. -/
def sitesGo (R : Nat) : Nat → List (List Nat) → List VmHashSite
  | k, [c] =>
    [{ digestCol := stateCommitCol R, inputs := siteInputs k c, arity := (siteInputs k c).length }]
  | k, c :: cs =>
    { digestCol := chainBase R + k, inputs := siteInputs k c, arity := (siteInputs k c).length }
      :: sitesGo R (k + 1) cs
  | _, [] => []

/-- The rotated absorption as ordered hash sites, at register count `R`. -/
def rotationSitesR (R : Nat) : List VmHashSite := sitesGo R 0 (siteChunks R)

deriving instance DecidableEq for VmHashSite

/-- **The R=16 sites ARE the pinned `rotationSites`** — the parametric chunking reproduces
the deployed 9-site chain exactly (7 arity-4 + 2 arity-2, iroot literally last). -/
theorem rotationSitesR_16 : rotationSitesR 16 = rotationSites := by decide

-- The arity discipline holds at every measured R: arity ∈ {2, 4}, NEVER 3 (the chip refuses).
#guard (rotationSitesR 16).all fun s => s.arity == 4 || s.arity == 2
#guard (rotationSitesR 24).all fun s => s.arity == 4 || s.arity == 2
#guard (rotationSitesR 32).all fun s => s.arity == 4 || s.arity == 2
-- The iroot rides the FINAL arity-2 site at every measured R.
#guard match (rotationSitesR 24).getLast? with
  | some s => s.digestCol == stateCommitCol 24 && s.arity == 2
      && s.inputs == [.digest 9, .col (irootCol 24)]
  | none => false
#guard match (rotationSitesR 32).getLast? with
  | some s => s.digestCol == stateCommitCol 32 && s.arity == 2
      && s.inputs == [.digest 13, .col (irootCol 32)]
  | none => false

/-- The v1-grammar probe at register count `R`: the chained sites + the two last-row PI pins
(published commit, published committed height). -/
def rotationProbeVmDescriptorR (R : Nat) : EffectVmDescriptor :=
  { name        := s!"dregg-effectvm-rotation-state-v3-staged-r{R}"
  , traceWidth  := probeWidth R
  , piCount     := 2
  , constraints :=
      [ .piBinding .last (stateCommitCol R) PUB_COMMIT
      , .piBinding .last (committedHeightCol R) PUB_HEIGHT ]
  , hashSites   := rotationSitesR R
  , ranges      := [] }

/-- The graduated IR-v2 probe at register count `R` (chip lookups, the five EPOCH tables). -/
def rotationProbeVmDescriptorR2 (R : Nat) : EffectVmDescriptor2 :=
  graduateV1 (rotationProbeVmDescriptorR R)

#guard graduable (rotationProbeVmDescriptorR 16)
#guard graduable (rotationProbeVmDescriptorR 24)
#guard graduable (rotationProbeVmDescriptorR 32)
#guard (rotationProbeVmDescriptorR2 24).constraints.length == 2 + 11
#guard (rotationProbeVmDescriptorR2 32).constraints.length == 2 + 15

-- **BYTE IDENTITY at R=16**: the parametric emission, name-aligned, graduates to the
-- EXACT wire JSON of the pinned probe — the committed
-- `dregg-effectvm-rotation-state-v3-staged.json` cannot move.
#guard emitVmJson2 (graduateV1
    { rotationProbeVmDescriptorR 16 with name := "dregg-effectvm-rotation-state-v3-staged" })
  == emitVmJson2 rotationProbeVmDescriptor2

/-! ## §5 — the per-R welds: site walks pin `wireCommitR`; the end-to-end keystones. -/

/-- The pre-iroot limb values a row carries, in absorption order (columns `0..R+6`). -/
def preLimbs (R : Nat) (a : Assignment) : List ℤ := (List.range (R + 7)).map a

theorem preLimbs_length (R : Nat) (a : Assignment) : (preLimbs R a).length = R + 7 := by
  simp [preLimbs]

/-- The R=24 site walk pins the commitment carrier to the genuine chained absorption of the
row's OWN limbs and iroot (the `rotationSites_pin` shape at R=24). -/
theorem rotationSitesR24_pin (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env (rotationSitesR 24)) :
    env.loc (stateCommitCol 24)
      = wireCommitR hash (preLimbs 24 env.loc) (env.loc (irootCol 24)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h10, -⟩ := h
  exact h10

/-- The R=32 site walk pins the commitment carrier likewise. -/
theorem rotationSitesR32_pin (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env (rotationSitesR 32)) :
    env.loc (stateCommitCol 32)
      = wireCommitR hash (preLimbs 32 env.loc) (env.loc (irootCol 32)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h14, -⟩ := h
  exact h14

#assert_axioms rotationSitesR24_pin
#assert_axioms rotationSitesR32_pin

/-- The R=24 probe pins the rotated commitment on EVERY row of a `Satisfied2` witness. -/
theorem rotationProbeR24_pins_commit (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2Faithful permOut hash (rotationProbeVmDescriptorR2 24) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    (envAt t i).loc (stateCommitCol 24)
      = wireCommitR hash (preLimbs 24 (envAt t i).loc) ((envAt t i).loc (irootCol 24)) := by
  have h := satisfied2Faithful_satisfiedVm permOut hash (rotationProbeVmDescriptorR 24)
    minit mfin maddrs t (by decide) hf i hi
  exact rotationSitesR24_pin hash _ h.2.1

/-- The R=32 probe pins the rotated commitment on EVERY row likewise. -/
theorem rotationProbeR32_pins_commit (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2Faithful permOut hash (rotationProbeVmDescriptorR2 32) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    (envAt t i).loc (stateCommitCol 32)
      = wireCommitR hash (preLimbs 32 (envAt t i).loc) ((envAt t i).loc (irootCol 32)) := by
  have h := satisfied2Faithful_satisfiedVm permOut hash (rotationProbeVmDescriptorR 32)
    minit mfin maddrs t (by decide) hf i hi
  exact rotationSitesR32_pin hash _ h.2.1

/-- The R=24 probe PUBLISHES: last row, PI 0 = the commitment, PI 1 = the height limb. -/
theorem rotationProbeR24_publishes (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2Faithful permOut hash (rotationProbeVmDescriptorR2 24) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 = t.rows.length) :
    (envAt t i).loc (stateCommitCol 24) ≡ (envAt t i).pub PUB_COMMIT [ZMOD 2013265921]
    ∧ (envAt t i).loc (committedHeightCol 24) ≡ (envAt t i).pub PUB_HEIGHT [ZMOD 2013265921] := by
  have h := satisfied2Faithful_satisfiedVm permOut hash (rotationProbeVmDescriptorR 24)
    minit mfin maddrs t (by decide) hf i hi
  have h1 := h.1 (.piBinding .last (stateCommitCol 24) PUB_COMMIT)
    (by simp [rotationProbeVmDescriptorR])
  have h2 := h.1 (.piBinding .last (committedHeightCol 24) PUB_HEIGHT)
    (by simp [rotationProbeVmDescriptorR])
  simp only [VmConstraint.holdsVm] at h1 h2
  exact ⟨h1 (by simp [hlast]), h2 (by simp [hlast])⟩

/-- The R=32 probe PUBLISHES likewise. -/
theorem rotationProbeR32_publishes (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2Faithful permOut hash (rotationProbeVmDescriptorR2 32) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 = t.rows.length) :
    (envAt t i).loc (stateCommitCol 32) ≡ (envAt t i).pub PUB_COMMIT [ZMOD 2013265921]
    ∧ (envAt t i).loc (committedHeightCol 32) ≡ (envAt t i).pub PUB_HEIGHT [ZMOD 2013265921] := by
  have h := satisfied2Faithful_satisfiedVm permOut hash (rotationProbeVmDescriptorR 32)
    minit mfin maddrs t (by decide) hf i hi
  have h1 := h.1 (.piBinding .last (stateCommitCol 32) PUB_COMMIT)
    (by simp [rotationProbeVmDescriptorR])
  have h2 := h.1 (.piBinding .last (committedHeightCol 32) PUB_HEIGHT)
    (by simp [rotationProbeVmDescriptorR])
  simp only [VmConstraint.holdsVm] at h1 h2
  exact ⟨h1 (by simp [hlast]), h2 (by simp [hlast])⟩

/-- **THE R=24 END-TO-END KEYSTONE** (the pinned `rotationProbe_commit_binds_published`, at
the measured width): two `Satisfied2` witnesses publishing the SAME commit agree on the WHOLE
pre-iroot limb list (all 24 registers, every map root, lifecycle/epoch/height), the iroot,
and the published height — under the ONE CR floor, via the PARAMETRIC keystone. -/
theorem rotationProbeR24_commit_binds_published (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hf : Satisfied2Faithful permOut hash (rotationProbeVmDescriptorR2 24) minit mfin maddrs t)
    (hf' : Satisfied2Faithful permOut hash (rotationProbeVmDescriptorR2 24) minit' mfin' maddrs' t')
    (i j : Nat) (hi : i < t.rows.length) (hj : j < t'.rows.length)
    (hlast : i + 1 = t.rows.length) (hlast' : j + 1 = t'.rows.length)
    (hcCanon : 0 ≤ (envAt t i).loc (stateCommitCol 24)
      ∧ (envAt t i).loc (stateCommitCol 24) < 2013265921)
    (hcCanon' : 0 ≤ (envAt t' j).loc (stateCommitCol 24)
      ∧ (envAt t' j).loc (stateCommitCol 24) < 2013265921)
    (hhCanon : 0 ≤ (envAt t i).pub PUB_HEIGHT ∧ (envAt t i).pub PUB_HEIGHT < 2013265921)
    (hhCanon' : 0 ≤ (envAt t' j).pub PUB_HEIGHT ∧ (envAt t' j).pub PUB_HEIGHT < 2013265921)
    (hpub : (envAt t i).pub PUB_COMMIT = (envAt t' j).pub PUB_COMMIT) :
    preLimbs 24 (envAt t i).loc = preLimbs 24 (envAt t' j).loc
    ∧ (envAt t i).loc (irootCol 24) = (envAt t' j).loc (irootCol 24)
    ∧ (envAt t i).pub PUB_HEIGHT = (envAt t' j).pub PUB_HEIGHT := by
  obtain ⟨hc, hh⟩ := rotationProbeR24_publishes permOut hash minit mfin maddrs t
    hf i hi hlast
  obtain ⟨hc', hh'⟩ := rotationProbeR24_publishes permOut hash minit' mfin' maddrs' t'
    hf' j hj hlast'
  have hp := rotationProbeR24_pins_commit permOut hash minit mfin maddrs t hf i hi
  have hp' := rotationProbeR24_pins_commit permOut hash minit' mfin' maddrs' t' hf' j hj
  -- Lift the two commit pins to a genuine ℤ equality of the digest columns via canonicality.
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
  refine ⟨hpre, hir, ?_⟩
  have hHtEq : (envAt t i).loc (committedHeightCol 24) = (envAt t' j).loc (committedHeightCol 24) :=
    congrArg (fun L => L.getD (committedHeightCol 24) 0) hpre
  have hHtCong : (envAt t i).pub PUB_HEIGHT ≡ (envAt t' j).pub PUB_HEIGHT [ZMOD 2013265921] :=
    calc (envAt t i).pub PUB_HEIGHT
        ≡ (envAt t i).loc (committedHeightCol 24) [ZMOD 2013265921] := hh.symm
      _ = (envAt t' j).loc (committedHeightCol 24) := hHtEq
      _ ≡ (envAt t' j).pub PUB_HEIGHT [ZMOD 2013265921] := hh'
  exact canon_eq_of_modEq hhCanon hhCanon' hHtCong

/-- **THE R=32 END-TO-END KEYSTONE** likewise. -/
theorem rotationProbeR32_commit_binds_published (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hf : Satisfied2Faithful permOut hash (rotationProbeVmDescriptorR2 32) minit mfin maddrs t)
    (hf' : Satisfied2Faithful permOut hash (rotationProbeVmDescriptorR2 32) minit' mfin' maddrs' t')
    (i j : Nat) (hi : i < t.rows.length) (hj : j < t'.rows.length)
    (hlast : i + 1 = t.rows.length) (hlast' : j + 1 = t'.rows.length)
    (hcCanon : 0 ≤ (envAt t i).loc (stateCommitCol 32)
      ∧ (envAt t i).loc (stateCommitCol 32) < 2013265921)
    (hcCanon' : 0 ≤ (envAt t' j).loc (stateCommitCol 32)
      ∧ (envAt t' j).loc (stateCommitCol 32) < 2013265921)
    (hhCanon : 0 ≤ (envAt t i).pub PUB_HEIGHT ∧ (envAt t i).pub PUB_HEIGHT < 2013265921)
    (hhCanon' : 0 ≤ (envAt t' j).pub PUB_HEIGHT ∧ (envAt t' j).pub PUB_HEIGHT < 2013265921)
    (hpub : (envAt t i).pub PUB_COMMIT = (envAt t' j).pub PUB_COMMIT) :
    preLimbs 32 (envAt t i).loc = preLimbs 32 (envAt t' j).loc
    ∧ (envAt t i).loc (irootCol 32) = (envAt t' j).loc (irootCol 32)
    ∧ (envAt t i).pub PUB_HEIGHT = (envAt t' j).pub PUB_HEIGHT := by
  obtain ⟨hc, hh⟩ := rotationProbeR32_publishes permOut hash minit mfin maddrs t
    hf i hi hlast
  obtain ⟨hc', hh'⟩ := rotationProbeR32_publishes permOut hash minit' mfin' maddrs' t'
    hf' j hj hlast'
  have hp := rotationProbeR32_pins_commit permOut hash minit mfin maddrs t hf i hi
  have hp' := rotationProbeR32_pins_commit permOut hash minit' mfin' maddrs' t' hf' j hj
  -- Lift the two commit pins to a genuine ℤ equality of the digest columns via canonicality.
  have hcCong : (envAt t i).loc (stateCommitCol 32)
      ≡ (envAt t' j).loc (stateCommitCol 32) [ZMOD 2013265921] :=
    calc (envAt t i).loc (stateCommitCol 32)
        ≡ (envAt t i).pub PUB_COMMIT [ZMOD 2013265921] := hc
      _ = (envAt t' j).pub PUB_COMMIT := hpub
      _ ≡ (envAt t' j).loc (stateCommitCol 32) [ZMOD 2013265921] := hc'.symm
  have hcEq : (envAt t i).loc (stateCommitCol 32) = (envAt t' j).loc (stateCommitCol 32) :=
    canon_eq_of_modEq hcCanon hcCanon' hcCong
  have hwire : wireCommitR hash (preLimbs 32 (envAt t i).loc) ((envAt t i).loc (irootCol 32))
      = wireCommitR hash (preLimbs 32 (envAt t' j).loc) ((envAt t' j).loc (irootCol 32)) := by
    rw [← hp, ← hp', hcEq]
  obtain ⟨hpre, hir⟩ := wireCommitR_binds hash hCR
    (by rw [preLimbs_length, preLimbs_length]) hwire
  refine ⟨hpre, hir, ?_⟩
  have hHtEq : (envAt t i).loc (committedHeightCol 32) = (envAt t' j).loc (committedHeightCol 32) :=
    congrArg (fun L => L.getD (committedHeightCol 32) 0) hpre
  have hHtCong : (envAt t i).pub PUB_HEIGHT ≡ (envAt t' j).pub PUB_HEIGHT [ZMOD 2013265921] :=
    calc (envAt t i).pub PUB_HEIGHT
        ≡ (envAt t i).loc (committedHeightCol 32) [ZMOD 2013265921] := hh.symm
      _ = (envAt t' j).loc (committedHeightCol 32) := hHtEq
      _ ≡ (envAt t' j).pub PUB_HEIGHT [ZMOD 2013265921] := hh'
  exact canon_eq_of_modEq hhCanon hhCanon' hHtCong

#assert_axioms rotationProbeR24_pins_commit
#assert_axioms rotationProbeR32_pins_commit
#assert_axioms rotationProbeR24_commit_binds_published
#assert_axioms rotationProbeR32_commit_binds_published

end Dregg2.Circuit.Emit.EffectVmEmitRotationR
