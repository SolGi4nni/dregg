/-
# Market.WideCommitBoundary — the faithful eight-lane light-client boundary.

The generic circuit apex historically collapsed a deployed state commitment to one `ℤ`.
This module keeps the deployed shape: the commitment is the eight-felt result of the
`wireCommitR8` chain over a 178-limb kernel payload, with the receipt-log root absorbed
last.  The payload's first limb is the already-proved `CommitSurface.commit`; the
remaining 177 lanes are domain-separated headroom for the deployed layout.  Thus the
wide chain adds no new trust: `wireCommitR8_binds` recovers the entire payload and receipt
root, then `CommitSurface.commit_binds` recovers the kernel.

No axiom, `sorry`, `admit`, or native decision procedure.
-/
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Circuit.Emit.EffectVmEmitRotationR
import Dregg2.Tactics

namespace Market.WideCommitBoundary

open Dregg2.Exec
open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
  (Poseidon2WideCR Poseidon2Width8 chainFrom8_len chainFrom8_snoc wireCommitR8
   wireCommitR8_binds)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

set_option autoImplicit false

/-- The deployed endpoint payload width. -/
def kernelPayloadWidth : Nat := 178

/-- A full-width kernel payload.  Limb zero is the binding full-kernel commitment;
the remaining positions are explicit zero headroom in this abstract boundary codec.
The deployed descriptor refines this codec by replacing those zeroes with its named
rotated lanes; binding of the endpoint needs only the already-binding first limb. -/
def kernelPayload (S : CommitSurface) (k : RecordKernelState) (t : BoundaryTurn) : List ℤ :=
  S.commit k t :: List.replicate (kernelPayloadWidth - 1) 0

set_option maxRecDepth 1000 in
theorem kernelPayload_length (S : CommitSurface) (k : RecordKernelState) (t : BoundaryTurn) :
    (kernelPayload S k t).length = kernelPayloadWidth := by
  change 1 + (List.replicate 177 (0 : ℤ)).length = 178
  rw [List.length_replicate]

/-- The variable preimage of the deployed `hash_fact` chip.  Its fixed namespace
and padding words do not affect the injectivity argument, so the boundary keeps
only the predicate followed by its terms. -/
def factHash (hash : List ℤ → ℤ) (pred : ℤ) (terms : List ℤ) : ℤ :=
  hash (pred :: terms)

/-- One truthful balance receipt.  Ring actions have `actor = src`, but both
fields remain in the digest because both belong to `Turn`. -/
def turnDigest (hash : List ℤ → ℤ) (t : Turn) : ℤ :=
  factHash hash t.actor [t.src, t.dst, t.amt]

theorem turnDigest_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {a b : Turn} (h : turnDigest hash a = turnDigest hash b) : a = b := by
  have hp := hCR _ _ h
  cases a
  cases b
  simp only [turnDigest, factHash, List.cons.injEq, Nat.cast_inj] at hp
  simp_all

/-- Receipt-index root with the executor's prepend update.  The empty root has a
one-word preimage; every action step has a two-word preimage, so log length is
also bound by collision resistance. -/
def receiptRoot (hash : List ℤ → ℤ) : List Turn → ℤ
  | [] => factHash hash 0 []
  | t :: ts => factHash hash (receiptRoot hash ts) [turnDigest hash t]

theorem receiptRoot_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    Function.Injective (receiptRoot hash) := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hp := hCR _ _ h
          simp [receiptRoot, factHash] at hp
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil =>
          have hp := hCR _ _ h
          simp [receiptRoot, factHash] at hp
      | cons y ys =>
          have hp := hCR _ _ h
          simp only [receiptRoot, factHash, List.cons.injEq] at hp
          obtain ⟨hroot, hdigest, _⟩ := hp
          have htail : xs = ys := ih hroot
          have hhead : x = y := turnDigest_binds hash hCR hdigest
          subst ys
          subst y
          rfl

/-- Exactly eight felts, with width carried by the type rather than a side premise. -/
structure Felt8 where
  vals : List ℤ
  width : vals.length = 8

@[ext] theorem Felt8.ext {a b : Felt8} (h : a.vals = b.vals) : a = b := by
  cases a
  cases b
  simp_all

/-- `wireCommitR8` always returns the deployed eight-lane width. -/
theorem wireCommitR8_length (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW)
    (limbs : List ℤ) (iroot : ℤ) : (wireCommitR8 permW limbs iroot).length = 8 := by
  unfold wireCommitR8
  rw [chainFrom8_snoc]
  exact hW _

/-- The faithful eight-lane commitment of one chained kernel state. -/
def commit8 (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW)
    (hash : List ℤ → ℤ) (S : CommitSurface) (s : RecChainedState)
    (t : BoundaryTurn) : Felt8 :=
  ⟨wireCommitR8 permW (kernelPayload S s.kernel t) (receiptRoot hash s.log),
    wireCommitR8_length permW hW _ _⟩

/-- Published endpoint surface for the shielded-ring batch. -/
structure PublishedCommit8 where
  pubPre : Felt8
  pubPost : Felt8
  turn : BoundaryTurn
  creators : Fin 2 → CellId
  turnCount : Nat
  preReceiptRoot : ℤ
  postReceiptRoot : ℤ

/-- Faithful decode of the eight-lane endpoint, including its receipt-chain roots. -/
structure StateDecode8 (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW)
    (hash : List ℤ → ℤ) (S : CommitSurface) (pc : PublishedCommit8)
    (pre post : RecChainedState) : Prop where
  preBinds : pc.pubPre = commit8 permW hW hash S pre pc.turn
  postBinds : pc.pubPost = commit8 permW hW hash S post pc.turn
  preReceiptBinds : pc.preReceiptRoot = receiptRoot hash pre.log
  postReceiptBinds : pc.postReceiptRoot = receiptRoot hash post.log
  preWF : Dregg2.Circuit.StateCommit.AccountsWF pre.kernel
  postWF : Dregg2.Circuit.StateCommit.AccountsWF post.kernel

/-- Equal faithful pre endpoints determine the entire chained pre-state. -/
theorem stateDecode8_pre_faithful (permW : List ℤ → List ℤ)
    (hWideCR : Poseidon2WideCR permW) (hW : Poseidon2Width8 permW)
    (hash : List ℤ → ℤ) (hReceiptCR : Poseidon2SpongeCR hash)
    (S : CommitSurface) (pc : PublishedCommit8)
    {pre post pre' post' : RecChainedState}
    (h : StateDecode8 permW hW hash S pc pre post)
    (h' : StateDecode8 permW hW hash S pc pre' post') : pre = pre' := by
  have hwide :
      wireCommitR8 permW (kernelPayload S pre.kernel pc.turn) (receiptRoot hash pre.log) =
        wireCommitR8 permW (kernelPayload S pre'.kernel pc.turn) (receiptRoot hash pre'.log) := by
    have := congrArg Felt8.vals (h.preBinds.symm.trans h'.preBinds)
    simpa [commit8] using this
  obtain ⟨hpayload, hroot⟩ := wireCommitR8_binds permW hWideCR hW
    (by rw [kernelPayload_length, kernelPayload_length]) hwide
  have hkcommit : S.commit pre.kernel pc.turn = S.commit pre'.kernel pc.turn := by
    simpa [kernelPayload] using congrArg List.head? hpayload
  have hk : pre.kernel = pre'.kernel :=
    S.commit_binds pre.kernel pre'.kernel pc.turn h.preWF h'.preWF hkcommit
  have hlog : pre.log = pre'.log := receiptRoot_binds hash hReceiptCR hroot
  cases pre
  cases pre'
  simp_all

/-- Equal faithful post endpoints determine the entire chained post-state. -/
theorem stateDecode8_post_faithful (permW : List ℤ → List ℤ)
    (hWideCR : Poseidon2WideCR permW) (hW : Poseidon2Width8 permW)
    (hash : List ℤ → ℤ) (hReceiptCR : Poseidon2SpongeCR hash)
    (S : CommitSurface) (pc : PublishedCommit8)
    {pre post pre' post' : RecChainedState}
    (h : StateDecode8 permW hW hash S pc pre post)
    (h' : StateDecode8 permW hW hash S pc pre' post') : post = post' := by
  have hwide :
      wireCommitR8 permW (kernelPayload S post.kernel pc.turn) (receiptRoot hash post.log) =
        wireCommitR8 permW (kernelPayload S post'.kernel pc.turn) (receiptRoot hash post'.log) := by
    have := congrArg Felt8.vals (h.postBinds.symm.trans h'.postBinds)
    simpa [commit8] using this
  obtain ⟨hpayload, hroot⟩ := wireCommitR8_binds permW hWideCR hW
    (by rw [kernelPayload_length, kernelPayload_length]) hwide
  have hkcommit : S.commit post.kernel pc.turn = S.commit post'.kernel pc.turn := by
    simpa [kernelPayload] using congrArg List.head? hpayload
  have hk : post.kernel = post'.kernel :=
    S.commit_binds post.kernel post'.kernel pc.turn h.postWF h'.postWF hkcommit
  have hlog : post.log = post'.log := receiptRoot_binds hash hReceiptCR hroot
  cases post
  cases post'
  simp_all

/-- A one-lane endpoint forgery cannot equal an honest eight-lane publication. -/
theorem Felt8.set_ne (x : Felt8) (i : Fin 8) (v : ℤ)
    (hne : some v ≠ x.vals[i.val]?) :
    x.vals.set i v ≠ x.vals := by
  have hi : i.val < x.vals.length := by simpa [x.width] using i.isLt
  intro h
  have this := congrArg (fun ys => ys[i.val]?) h
  simp [List.getElem?_set, hi] at this
  apply hne
  simpa [hi] using congrArg some this

#guard kernelPayloadWidth == 178
#guard receiptRoot (fun xs => xs.sum)
  [{ actor := 1, src := 1, dst := 2, amt := 3 }] == 7

#assert_axioms kernelPayload_length
#assert_axioms turnDigest_binds
#assert_axioms receiptRoot_binds
#assert_axioms wireCommitR8_length
#assert_axioms stateDecode8_pre_faithful
#assert_axioms stateDecode8_post_faithful
#assert_axioms Felt8.set_ne

end Market.WideCommitBoundary
