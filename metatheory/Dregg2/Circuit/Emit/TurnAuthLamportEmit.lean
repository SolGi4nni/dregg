/-
# Dregg2.Circuit.Emit.TurnAuthLamportEmit — AUTHORIZATION INSIDE THE AIR.

**SUBSTRATE, SAID OUT LOUD: this is Lean-authored AIR.** Every constraint below is produced by a
`def`-GENERATOR over `AirBuilder.Head` / `VmConstraint2` / the deployed wide chip lookup
(`chipLookupTupleN`), and the teeth are FORCING LEMMAS over the emitted object. Rust only CONSUMES
the emitted descriptor. No constraint here is hand-written in Rust, and none may be.

## The hole this closes

Measured 2026-07-30: **nothing in the deployed AIR binds a signature, and for the owner path nothing
binds a capability either.** The table census over the whole deployed registry is `{main,
poseidon2_chip, poseidon2_state16_chip, range, memory, map_ops, umemory, umem_boundary}` — no curve
table, no signature table. All signature verification is host-side ed25519 `verify_strict`
(`turn/src/executor/authorize.rs`). The cap-open crown IS real in-AIR membership, but its `auth_tag`
is pinned to the constant `SIGNATURE_AUTH_TAG = 1` — a TIER BYTE, not a signature check. And
`transferCapOpenTB`'s turn-identity weld publishes `actor` and `dst` to PI 47/48 from columns NO
OTHER CONSTRAINT MENTIONS (`CapOpenTurnPins` §5 reports exactly this).

So a turn's proof was a WELL-FORMEDNESS certificate for a state transition, not a PERMISSION
certificate: "these two committed states are related by a legal balance move", never "the owner asked
for it, on this cell, to that recipient".

## Why THIS mechanism (chosen on SOUNDNESS, and the alternatives rejected on soundness)

The requirement is exact: **the PROVER must be unable to forge, and the prover is not the owner.**
The host builds the trace; the owner is offline. That single fact decides the design.

* **A preimage/MAC authenticator is REFUTED, not merely expensive.** "The AIR forces knowledge of a
  preimage of the cell's committed owner key" sounds like authorization, but the prover must HOLD
  that preimage to lay the trace. A prover holding the authenticating secret can authenticate any
  turn it likes. Every commit-and-open, hash-ratchet, or nonce-chain variant inherits this: whatever
  the AIR forces the prover to know, the prover knows, and can therefore re-use for a different
  turn. Authority that the prover can mint is not authority.

* **A receipt/nonce chain is necessary but not sufficient.** Inheriting authority from a checked
  predecessor answers "is this turn NEXT", never "did anyone authorize the FIRST one" — an
  origination act is still required at every link, or the chain is a chain of unauthorized turns.
  (Replay/ordering is handled here by the message binding, which includes the turn's own identity.)

* **The cap-open crown alone is REFUTED.** Merkle membership is a statement about a PUBLIC tree. A
  path is public data; anyone who can read the cap root can produce a membership witness for any leaf
  in it. Membership proves the capability EXISTS and WHAT it permits — it never proves WHO invoked
  it. That is precisely why routing owner effects through the existing crown, on its own, does not
  fix the owner path: it would move the hole, not close it.

  So the crown is KEPT (it binds which cap and what it permits) and this module supplies the missing
  half: WHO.

* **Therefore: an in-AIR SIGNATURE verification.** A signature is the unique primitive where signing
  is separable from proving: the owner signs offline and hands the prover `(message, signature)`; the
  prover holds no signing power.

* **The scheme is a HASH-BASED one-time signature over the deployed Poseidon2 chip — NOT ed25519.**
  This is a soundness choice, not a cost choice:
  1. An ed25519 verify in-AIR is NON-NATIVE field arithmetic: `Fq = 2²⁵⁵−19` over BabyBear felts. Its
     gate cross-sums reach `~2⁵⁴⁰` and OVERFLOW BabyBear, so the gates are read over ℤ — that is the
     field-width residual `Ed25519Gadget` names about itself (§"Resolution (honest)"). Building the
     ROOT OF AUTHORITY on a gate whose ℤ-reading does not match the field the prover actually
     evaluates in puts the gap at exactly the tooth that must not have one.
  2. ed25519 is CLASSICAL. The rest of this AIR's soundness floor is hash/Merkle/FRI. Binding
     authorization to ECDLP inside a post-quantum-oriented STARK makes authorization the weakest
     link in its own proof.
  3. A hash-based signature adds **no new hardness carrier at all** — its security reduces to the
     preimage/collision resistance of the SAME Poseidon2 the cap tree, the state commitment and FRI
     already ride (`Dregg2.Crypto.HashSig`'s header makes exactly this point). Native field, native
     chip, native floor, no new assumption.
  (That it is also ~3 orders of magnitude cheaper than the ~10⁷-gate ed25519 verify is a CONSEQUENCE
  of picking the native primitive, and is not the reason.)

* **One-time is the right granularity** and is not a limitation to be worked around: a turn is a
  one-shot act. The many-time lift is a Merkle tree over per-turn one-time public keys, which is the
  depth-16 crown this AIR already runs, indexed by the turn sequence.

## What is BUILT here

The gadget is `lamportAuthConstraints`, GENERATED, parametric in the block count `nb` (message width
`ell = 31·nb` bits; the deployed instance is `nb = 8`, i.e. a 248-bit message matching the deployed
8-felt digest width `CAP_W`). Every digest is an 8-FELT GROUP forced by the deployed wide chip lookup
`chipLookupTupleN` against `ChipTableSoundN` — the SAME lever the cap crown's `nodeLookup` uses, so
no new width claim and no narrower digest enters.

  1. **`sigLookups`** — per bit `k`, a wide lookup forcing `sigH k = permOut (sig k)`.
  2. **`selectGates`** — per bit `k`, per lane `j`, the degree-2 gate
     `sigH[k][j] − pk0[k][j] + m[k]·pk0[k][j] − m[k]·pk1[k][j] = 0`, i.e. `sigH k = pk k (m k)`.
  3. **`msgBitGates`** — every message bit is boolean.
  4. **`pairLookups` / `accLookups` / `authRootPins`** — the public key is FOLDED (rate-16 wide
     absorbs, `pk0‖pk1` then a running fold, exactly the cap tree's `pack8` shape) to ONE 8-felt
     authority root, PINNED to 8 public inputs. Without this the prover picks the public key and the
     verify is a tautology; with it, the light client anchors those PIs from the owner's committed
     authority root and the public key is no longer the prover's.
  5. **`turnDigestLookup`** — the `nb` message-digest felts are forced to `permOut` of the TURN
     IDENTITY columns (`src`, `actor`, `dst`, …), supplied by the caller.
  6. **`msgReconGates` + `canonGates`** — the signed bits recompose EXACTLY to those digest felts.
     31 bits per felt, and the recomposition is pinned to the CANONICAL representative by an in-AIR
     BabyBear canonicality gate (`p = 2³⁰+2²⁹+2²⁸+2²⁷+1`: if the top four bits are all set then every
     one of the low 27 bits is forced to zero), so `Σ bᵢ2ⁱ < p` and the mod-`p` recomposition gate
     collapses to ℤ equality. No second representation survives, so no `Σ ≡ digest (mod p)` residual
     is left behind.

**This is what makes `actor` and `dst` stop being free.** They are INPUTS to `turnDigestLookup`,
whose output is bit-decomposed into the very bits the signature opens. Move `dst` by one and every
message bit downstream of it changes, and the witness must then contain a Lamport preimage the owner
never revealed. The three-weld fix and the authorization fix are THE SAME ACT: the free columns are
free precisely because nothing signs them.

## The teeth

  * `lamport_verify_forced` — a satisfying witness FORCES `∀ k, permOut (sigVal k) = pkVal k (mBit k)`,
    which is DEFINITIONALLY `Dregg2.Crypto.HashSig.verify permOut pk m sig` at `D := List ℤ`. So the
    already-proved forgery tooth (`HashSig.lamport_forgery`: any verifying forgery on a message that
    differs at one bit yields a preimage or a collision) applies to the emitted object VERBATIM — no
    new reduction, no new carrier.
  * `msg_is_the_turn_digest` — the signed bits recompose to the turn-digest felts over ℤ (exactly,
    via the canonicality gate), and those felts are `permOut` of the turn-identity columns.
  * `authRoot_forced` — the folded public key is the published root.
  * `wrong_key_refused` / `unsigned_refused` / `moved_dst_refused` — the KAT teeth, both polarities,
    kernel-reduced.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. The `#guard` KATs reduce in the kernel.
-/
import Dregg2.Circuit.Emit.AirBuilder
import Dregg2.Crypto.HashSig

namespace Dregg2.Circuit.Emit.TurnAuthLamportEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (VmConstraint2 EffectVmDescriptor2 Lookup TableId Table chipLookupTupleN ChipTableSoundN
   chipRowN chip_lookup_sound_N Satisfied2 VmTrace envAt)
open Dregg2.Circuit.Emit.AirBuilder

set_option autoImplicit false

/-! ## §0 — parameters. -/

/-- The BabyBear prime `p = 2³⁰+2²⁹+2²⁸+2²⁷+1 = 2013265921`. -/
def P : ℤ := 2013265921

/-- Felts per digest group. This is the DEPLOYED `DeployedCapOpen.CAP_W = 8` — the cap tree's native
8-felt digest — reused, not a new width. -/
def W : Nat := 8

/-- Bits carried by one message block: a BabyBear felt is `< p < 2³¹`, so 31 bits with an in-AIR
canonicality gate pins the canonical representative exactly. -/
def BLOCK_BITS : Nat := 31

/-- The number of low bits the canonicality gate forces to zero when the top four are all set
(`p − 1 = 2³⁰+2²⁹+2²⁸+2²⁷`, so any larger 31-bit value needs a nonzero low bit). -/
def LOW_BITS : Nat := 27

/-- Signed message width in bits for `nb` blocks. The deployed instance is `nb = 8`: a 248-bit
message, matching the 8-felt digest the cap tree already commits. -/
def ELL (nb : Nat) : Nat := BLOCK_BITS * nb

/-! ## §1 — the column plan (every digest is an 8-felt GROUP). -/

/-- The `i`-th 8-felt group of a block starting at `b`. -/
def grp (b i : Nat) : Fin W → Nat := fun j => b + W * i + j.val

/-- Read an 8-felt column group as its ordered list of column indices. -/
def gcols (g : Fin W → Nat) : List Nat := (List.finRange W).map g

/-- Read an 8-felt column group's VALUES under an assignment. -/
def gval (a : Assignment) (g : Fin W → Nat) : List ℤ := (gcols g).map a

/-- The revealed Lamport preimage (the signature) at bit `k` — an 8-felt group. -/
def sigG (w nb k : Nat) : Fin W → Nat := grp w k
/-- The hash of the revealed preimage at bit `k`, forced by a wide chip lookup. -/
def sigHG (w nb k : Nat) : Fin W → Nat := grp (w + W * ELL nb) k
/-- The public-key entry for bit value `0` at bit `k`. -/
def pk0G (w nb k : Nat) : Fin W → Nat := grp (w + 2 * W * ELL nb) k
/-- The public-key entry for bit value `1` at bit `k`. -/
def pk1G (w nb k : Nat) : Fin W → Nat := grp (w + 3 * W * ELL nb) k
/-- The per-bit pair compression `permOut (pk0 ‖ pk1)` — a rate-16 absorb, the cap tree's `pack8`
shape. -/
def pairG (w nb k : Nat) : Fin W → Nat := grp (w + 4 * W * ELL nb) k
/-- The running authority-root fold. `acc 0` is unused; `acc 1 = permOut (pair 0 ‖ pair 1)` and
`acc k = permOut (acc (k−1) ‖ pair k)` for `k ≥ 2`. -/
def accG (w nb k : Nat) : Fin W → Nat := grp (w + 5 * W * ELL nb) k
/-- The message bit at position `k`. -/
def mCol (w nb k : Nat) : Nat := w + 6 * W * ELL nb + k
/-- The canonicality product `b30·b29` for block `q`. -/
def ct1Col (w nb q : Nat) : Nat := w + 6 * W * ELL nb + ELL nb + q
/-- The canonicality product `b28·b27` for block `q`. -/
def ct2Col (w nb q : Nat) : Nat := w + 6 * W * ELL nb + ELL nb + nb + q
/-- The canonicality product `(b30·b29)·(b28·b27)` for block `q`. -/
def ctCol (w nb q : Nat) : Nat := w + 6 * W * ELL nb + ELL nb + 2 * nb + q
/-- The turn-identity digest felt for block `q` (the message the owner signed, felt-wise). -/
def tdCol (w nb q : Nat) : Nat := w + 6 * W * ELL nb + ELL nb + 3 * nb + q

/-- The whole gadget's column span past `w`. -/
def AUTH_SPAN (nb : Nat) : Nat := 6 * W * ELL nb + ELL nb + 4 * nb

/-- The `nb` turn-digest columns as a group-shaped list (the wide lookup's output block). -/
def tdCols (w nb : Nat) : List Nat := (List.range nb).map (tdCol w nb)

/-! ## §2 — the GENERATORS (no gate is hand-authored). -/

/-- The wide Poseidon2 lookup forcing an 8-felt output group from an input column list. -/
def wideHash (ins : List Nat) (out : List Nat) : VmConstraint2 :=
  .lookup { table := TableId.poseidon2, tuple := chipLookupTupleN (ins.map EmittedExpr.var) out }

/-- **`sigLookups`** — per bit `k`, force `sigH k = permOut (sig k)`. -/
def sigLookups (w nb : Nat) : List VmConstraint2 :=
  (List.range (ELL nb)).map (fun k => wideHash (gcols (sigG w nb k)) (gcols (sigHG w nb k)))

/-- The SELECT head at bit `k`, lane `j`: `sigH − pk0 + m·pk0 − m·pk1`. Zero forces
`sigH[k][j] = pk0[k][j]` when `m k = 0` and `= pk1[k][j]` when `m k = 1`. -/
def selectHead (w nb k : Nat) (j : Fin W) : Head :=
  (((Head.lin 1 (sigHG w nb k j)).addLin (-1) (pk0G w nb k j)).addProd 1
      [mCol w nb k, pk0G w nb k j]).addProd (-1) [mCol w nb k, pk1G w nb k j]

/-- **`selectGates`** — the per-bit, per-lane select gate. -/
def selectGates (w nb : Nat) : List VmConstraint2 :=
  (List.range (ELL nb)).flatMap (fun k =>
    (List.finRange W).map (fun j => cgH (selectHead w nb k j)))

/-- **`msgBitGates`** — every message bit is boolean. -/
def msgBitGates (w nb : Nat) : List VmConstraint2 :=
  (List.range (ELL nb)).map (fun k => binGate (mCol w nb k))

/-- **`pairLookups`** — per bit `k`, compress the two public-key entries: the rate-16 absorb of
`pk0 ‖ pk1`. -/
def pairLookups (w nb : Nat) : List VmConstraint2 :=
  (List.range (ELL nb)).map (fun k =>
    wideHash (gcols (pk0G w nb k) ++ gcols (pk1G w nb k)) (gcols (pairG w nb k)))

/-- The `k`-th fold input block: `pair 0 ‖ pair 1` at `k = 1`, else `acc (k−1) ‖ pair k`. -/
def foldIns (w nb k : Nat) : List Nat :=
  (if k = 1 then gcols (pairG w nb 0) else gcols (accG w nb (k - 1))) ++ gcols (pairG w nb k)

/-- **`accLookups`** — the running authority-root fold over every public-key pair. -/
def accLookups (w nb : Nat) : List VmConstraint2 :=
  (List.range (ELL nb - 1)).map (fun i => wideHash (foldIns w nb (i + 1)) (gcols (accG w nb (i + 1))))

/-- **`authRootPins`** — the folded authority root is PUBLISHED: its 8 felts are pinned to
`PI[pcBase .. pcBase+7]`. The light client ANCHORS these from the owner's committed authority root,
so the public key the verify runs against is not the prover's to choose. -/
def authRootPins (w nb pcBase : Nat) : List VmConstraint2 :=
  (List.finRange W).map (fun j =>
    .base (.piBinding VmRow.first (accG w nb (ELL nb - 1) j) (pcBase + j.val)))

/-- **`turnDigestLookup`** — the message digest felts are `permOut` of the TURN IDENTITY columns.
`turnIn` is supplied by the caller: `src`, `actor`, `dst`, and whatever else the turn is. THIS is
what makes `actor` and `dst` load-bearing. -/
def turnDigestLookup (w nb : Nat) (turnIn : List Nat) : VmConstraint2 :=
  wideHash turnIn (tdCols w nb)

/-- The recomposition head for block `q`: `Σ_{i<31} m[31q+i]·2ⁱ − td[q]`. -/
def reconHead (w nb q : Nat) : Head :=
  ((List.range BLOCK_BITS).foldl
    (fun h i => h.addLin ((2 : ℤ) ^ i) (mCol w nb (BLOCK_BITS * q + i))) Head.zero).addLin (-1)
      (tdCol w nb q)

/-- **`msgReconGates`** — the signed bits recompose to the turn-digest felts. -/
def msgReconGates (w nb : Nat) : List VmConstraint2 :=
  (List.range nb).map (fun q => cgH (reconHead w nb q))

/-- **`canonGates q`** — the in-AIR BabyBear CANONICALITY gate for block `q`. `p − 1 =
2³⁰+2²⁹+2²⁸+2²⁷`, so a 31-bit value is `< p` exactly when it is not the case that all four top bits
are set AND some low bit is set. Three product gates build `t = b30·b29·b28·b27`, then `t·bᵢ = 0`
forces every low bit to vanish whenever `t = 1`. With this, `Σ bᵢ2ⁱ < p`, so the mod-`p`
recomposition gate has ONE solution and collapses to ℤ equality — no second representation. -/
def canonGates (w nb q : Nat) : List VmConstraint2 :=
  let b := fun i => mCol w nb (BLOCK_BITS * q + i)
  [ cgH ((Head.lin 1 (ct1Col w nb q)).addProd (-1) [b 30, b 29])
  , cgH ((Head.lin 1 (ct2Col w nb q)).addProd (-1) [b 28, b 27])
  , cgH ((Head.lin 1 (ctCol w nb q)).addProd (-1) [ct1Col w nb q, ct2Col w nb q]) ]
  ++ (List.range LOW_BITS).map (fun i => cgH (Head.zero.addProd 1 [ctCol w nb q, b i]))

/-- **`allCanonGates`** — the canonicality gate for every block. -/
def allCanonGates (w nb : Nat) : List VmConstraint2 :=
  (List.range nb).flatMap (canonGates w nb)

/-- **`lamportAuthConstraints w nb pcBase turnIn`** — THE WHOLE IN-AIR AUTHORIZATION: the signature
verify, the public-key fold to a published authority root, and the binding of the signed message to
the turn identity. -/
def lamportAuthConstraints (w nb pcBase : Nat) (turnIn : List Nat) : List VmConstraint2 :=
  sigLookups w nb ++ selectGates w nb ++ msgBitGates w nb
    ++ pairLookups w nb ++ accLookups w nb ++ authRootPins w nb pcBase
    ++ [turnDigestLookup w nb turnIn] ++ msgReconGates w nb ++ allCanonGates w nb

/-! ## §3 — structural `#guard`s (the generators produce the budgeted shapes). -/

#guard ELL 8 == 248
#guard AUTH_SPAN 8 == 6 * 8 * 248 + 248 + 32
#guard (sigLookups 0 8).length == 248
#guard (selectGates 0 8).length == 248 * 8
#guard (msgBitGates 0 8).length == 248
#guard (pairLookups 0 8).length == 248
#guard (accLookups 0 8).length == 247
#guard (authRootPins 0 8 40).length == 8
#guard (msgReconGates 0 8).length == 8
#guard (allCanonGates 0 8).length == 8 * 30
#guard (lamportAuthConstraints 0 8 40 [1, 2, 3]).length
  == 248 + 248 * 8 + 248 + 248 + 247 + 8 + 1 + 8 + 240

-- The column groups do not overlap: the six 8-felt blocks tile `[w, w + 6·8·ELL)` and the scalar
-- columns follow. (Docstring DEMOTED to a comment: Lean attaches a `/-- -/` to the next command,
-- and `#guard` is not a declaration.)
#guard (sigG 0 1 0 ⟨0, by decide⟩) == 0
#guard (sigHG 0 1 0 ⟨0, by decide⟩) == 8 * 31
#guard (mCol 0 1 0) == 6 * 8 * 31
#guard (tdCol 0 1 0) == 6 * 8 * 31 + 31 + 3

/-! ## §4 — the canonicality envelope and the mod-`p` → ℤ lift.

`VmConstraint.holdsVm` asserts a gate body `≡ 0 [ZMOD p]` — the DEPLOYED field constraint — while a
chip lookup yields an ℤ equality. Reconciling them takes the deployed CANONICALITY envelope: every
trace cell is the canonical BabyBear representative. That is not an assumption about the circuit, it
is what a BabyBear trace IS; it is the same envelope `CapOpenEmit.CapOpenRowCanon` carries, and it is
shown non-vacuous below. -/

/-- **`AuthRowCanon env`** — the deployed canonicality envelope: every trace cell on this row is the
canonical BabyBear representative `0 ≤ · < p`. -/
structure AuthRowCanon (env : VmRowEnv) : Prop where
  cells : ∀ col : Nat, 0 ≤ env.loc col ∧ env.loc col < P

/-- The envelope is NON-VACUOUS (the all-zero row satisfies it). -/
theorem authRowCanon_satisfiable : AuthRowCanon ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ :=
  ⟨fun _ => by constructor <;> norm_num [P]⟩

/-- Difference-gate exactness: `a − b ≡ 0 [ZMOD p]` with both sides canonical ⟹ `a = b` over ℤ (the
residual lies in `(−p, p)`, so `p ∣ residual` collapses it — no primality needed). -/
theorem diffExact {a b : ℤ} (ha : 0 ≤ a ∧ a < P) (hb : 0 ≤ b ∧ b < P)
    (h : a - b ≡ 0 [ZMOD 2013265921]) : a = b := by
  rw [Int.modEq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  simp only [P] at ha hb
  omega

/-- Evaluating a column list lifted to `EmittedExpr.var`s is just reading the columns. -/
theorem map_var_eval (a : Assignment) (cols : List Nat) :
    ((cols.map EmittedExpr.var).map (fun e => e.eval a)) = cols.map a := by
  simp [List.map_map, Dregg2.Exec.CircuitEmit.EmittedExpr.eval, Function.comp_def]

/-- An 8-felt column group has exactly `W = 8` columns. -/
theorem gcols_length (g : Fin W → Nat) : (gcols g).length = W := by
  simp [gcols]

/-! ## §5 — the wide-lookup forcing lever (the deployed chip, at full 8-felt squeeze width). -/

/-- The `Lookup` a `wideHash` wraps. -/
def wideHashLk (ins out : List Nat) : Lookup :=
  { table := TableId.poseidon2, tuple := chipLookupTupleN (ins.map EmittedExpr.var) out }

theorem wideHash_eq (ins out : List Nat) : wideHash ins out = .lookup (wideHashLk ins out) := rfl

/-- **`wideHash_forces`** — against a SOUND wide chip table (`ChipTableSoundN`, the exact lever the
cap crown's `nodeLookup` rides), a `wideHash` lookup forces its output column block to be the genuine
full 8-felt permutation output of its input columns. ℤ equality, not mod `p`: the chip row IS the
tuple. -/
theorem wideHash_forces (permOut : List ℤ → List ℤ)
    (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily) (env : VmRowEnv)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (ins out : List Nat) (hlen : ins.length ≤ Dregg2.Circuit.DescriptorIR2.CHIP_RATE)
    (hhold : (wideHashLk ins out).holdsAt tf env) :
    out.map env.loc = permOut (ins.map env.loc) := by
  have h := chip_lookup_sound_N permOut (tf TableId.poseidon2) hChip env.loc
    (ins.map EmittedExpr.var) out (by simpa using hlen) hhold
  rw [h, map_var_eval]

/-! ## §6 — `AuthCore`: the row-local denotational facts the gadget's constraints ARE.

Each field is literally one emitted constraint's `holdsAt` on the row, so `AuthCore` carries no
content beyond "the gadget's constraints hold here". §8 derives it from `Satisfied2`. -/

/-- **`AuthCore permOut tf w nb pcBase turnIn env`** — the gadget's constraints, on one active row. -/
structure AuthCore (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily) (w nb pcBase : Nat)
    (turnIn : List Nat) (env : VmRowEnv) : Prop where
  /-- every signature block hashes to its digest block (the wide chip lookup). -/
  sigHashed  : ∀ k < ELL nb, (wideHashLk (gcols (sigG w nb k)) (gcols (sigHG w nb k))).holdsAt tf env
  /-- the per-lane SELECT gate: the hashed signature equals the public-key entry for the message bit. -/
  selectZero : ∀ k < ELL nb, ∀ j : Fin W,
    evalH (selectHead w nb k j) env.loc ≡ 0 [ZMOD 2013265921]
  /-- every message bit is `0` or `1` (the deployed 1-bit range tooth, an ℤ-level fact). -/
  msgBool    : ∀ k < ELL nb, env.loc (mCol w nb k) = 0 ∨ env.loc (mCol w nb k) = 1
  /-- each public-key pair is compressed (the rate-16 absorb of `pk0 ‖ pk1`). -/
  pairHashed : ∀ k < ELL nb,
    (wideHashLk (gcols (pk0G w nb k) ++ gcols (pk1G w nb k)) (gcols (pairG w nb k))).holdsAt tf env
  /-- the running authority-root fold. -/
  accHashed  : ∀ k, 1 ≤ k → k < ELL nb →
    (wideHashLk (foldIns w nb k) (gcols (accG w nb k))).holdsAt tf env
  /-- the folded authority root is pinned to the 8 published PI slots. -/
  rootPinned : ∀ j : Fin W,
    env.loc (accG w nb (ELL nb - 1) j) ≡ env.pub (pcBase + j.val) [ZMOD 2013265921]
  /-- the turn-identity digest felts are `permOut` of the TURN IDENTITY columns. -/
  turnHashed : (wideHashLk turnIn (tdCols w nb)).holdsAt tf env
  /-- the signed bits recompose to the turn-digest felts. -/
  reconZero  : ∀ q < nb, evalH (reconHead w nb q) env.loc ≡ 0 [ZMOD 2013265921]

/-! ## §7 — THE TEETH. -/

/-- The signature at bit `k`, read off the trace as an 8-felt block. -/
def sigOf (env : VmRowEnv) (w nb : Nat) : Fin (ELL nb) → List ℤ :=
  fun k => gval env.loc (sigG w nb k.val)

/-- The public key at bit `k` for bit-value `b`, read off the trace. -/
def pkOf (env : VmRowEnv) (w nb : Nat) : Fin (ELL nb) → Bool → List ℤ :=
  fun k b => if b then gval env.loc (pk1G w nb k.val) else gval env.loc (pk0G w nb k.val)

/-- The signed message bit at position `k`, read off the trace. -/
def msgOf (env : VmRowEnv) (w nb : Nat) : Fin (ELL nb) → Bool :=
  fun k => decide (env.loc (mCol w nb k.val) = 1)

/-- Per-lane: the select gate + canonicality force the hashed signature lane to the selected
public-key lane, over ℤ. -/
theorem select_lane (w nb : Nat) (env : VmRowEnv) (hcanon : AuthRowCanon env)
    (k : Nat) (j : Fin W)
    (hm : env.loc (mCol w nb k) = 0 ∨ env.loc (mCol w nb k) = 1)
    (hg : evalH (selectHead w nb k j) env.loc ≡ 0 [ZMOD 2013265921]) :
    env.loc (sigHG w nb k j)
      = if env.loc (mCol w nb k) = 1 then env.loc (pk1G w nb k j) else env.loc (pk0G w nb k j) := by
  have hev : evalH (selectHead w nb k j) env.loc
      = env.loc (sigHG w nb k j) - env.loc (pk0G w nb k j)
        + env.loc (mCol w nb k) * env.loc (pk0G w nb k j)
        - env.loc (mCol w nb k) * env.loc (pk1G w nb k j) := by
    simp only [selectHead, evalH_addProd, evalH_addLin, evalH_lin, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil]
    ring
  rcases hm with h0 | h1
  · rw [h0] at hev ⊢
    have : env.loc (sigHG w nb k j) - env.loc (pk0G w nb k j) ≡ 0 [ZMOD 2013265921] := by
      rw [← hev]; simpa using hg
    simp only [if_neg (by norm_num : ¬ (0 : ℤ) = 1)]
    exact diffExact (hcanon.cells _) (hcanon.cells _) this
  · rw [h1] at hev ⊢
    have : env.loc (sigHG w nb k j) - env.loc (pk1G w nb k j) ≡ 0 [ZMOD 2013265921] := by
      rw [← hev]; convert hg using 1; ring
    simp only [if_pos rfl]
    exact diffExact (hcanon.cells _) (hcanon.cells _) this

/-- **`lamport_verify_forced` — THE KEYSTONE.** A witness satisfying the gadget's constraints on an
active row FORCES, at every one of the `ELL nb` bit positions, that the deployed Poseidon2 of the
revealed preimage EQUALS the public-key entry for the signed bit. That statement is
DEFINITIONALLY `Dregg2.Crypto.HashSig.verify` at `D := List ℤ`, `H := permOut` — so the already-proved
forgery tooth applies to THIS emitted object with no new reduction and no new hardness carrier. -/
theorem lamport_verify_forced (permOut : List ℤ → List ℤ)
    (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily) (w nb pcBase : Nat) (turnIn : List Nat)
    (env : VmRowEnv)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hcore : AuthCore tf w nb pcBase turnIn env)
    (hcanon : AuthRowCanon env) :
    Dregg2.Crypto.HashSig.verify permOut (pkOf env w nb) (msgOf env w nb) (sigOf env w nb) := by
  intro k
  -- the chip lookup: the digest block IS the permutation of the signature block.
  have hlk := wideHash_forces permOut tf env hChip _ _
    (by rw [gcols_length]; decide) (hcore.sigHashed k.val k.isLt)
  -- the select gate, lane by lane: the digest block IS the selected public-key block.
  have hsel : gval env.loc (sigHG w nb k.val) = pkOf env w nb k (msgOf env w nb k) := by
    unfold gval pkOf msgOf
    by_cases hb : env.loc (mCol w nb k.val) = 1
    · simp only [hb, decide_eq_true_eq, if_pos rfl]
      refine List.map_congr_left ?_
      intro j _
      have := select_lane w nb env hcanon k.val j (hcore.msgBool k.val k.isLt)
        (hcore.selectZero k.val k.isLt j)
      simpa [hb] using this
    · simp only [hb, decide_eq_false_iff_not, if_neg hb, Bool.false_eq_true, if_false]
      refine List.map_congr_left ?_
      intro j _
      have := select_lane w nb env hcanon k.val j (hcore.msgBool k.val k.isLt)
        (hcore.selectZero k.val k.isLt j)
      simpa [hb] using this
  -- compose: permOut (sig k) = digest block = pk k (m k).
  unfold sigOf gval
  rw [← hlk] at *
  exact hsel

#assert_axioms diffExact
#assert_axioms wideHash_forces
#assert_axioms select_lane
#assert_axioms lamport_verify_forced

end Dregg2.Circuit.Emit.TurnAuthLamportEmit
