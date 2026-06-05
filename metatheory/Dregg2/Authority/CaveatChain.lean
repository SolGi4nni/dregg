/-
# Dregg2.Authority.CaveatChain — the macaroon as a real HMAC-authenticated append-only caveat chain.

`Authority/Caveat.lean` reduces a caveat to a bare `Ctx → Bool` and a token to a list of those
checks. That captures the narrowing algebra (`attenuate_narrows`) but cannot express the macaroon's
reason to exist: chain integrity. A `Ctx → Bool` list cannot say "you cannot remove, reorder, or
forge a caveat" — the whole point of the running HMAC tag.

This module carries the real Rust semantics of `macaroon/src/macaroon.rs`:

```text
//! macaroon/src/macaroon.rs:7-21
//!   T₀ = HMAC(root_key, nonce_bytes)
//!   Tᵢ = HMAC(Tᵢ₋₁, encode(Cᵢ))
```

- **`Macaroon::new`** seeds `T₀ = HMAC(root_key, nonce_bytes)` (`macaroon.rs:118-129`). Here: `seedTag root nonce = mac root nonce`.
- **`add_first_party`** = append-only attenuation; `new_tail = HMAC(old_tail, encode(caveat))` (`macaroon.rs:146-156`). Here: `Chain.append`.
- **`verify`** replays the chain from root and does a constant-time final-tail compare (`macaroon.rs:204-262`). Here: `Chain.replayTag` + `Chain.verify`.
- Integrity tests — tamper (`macaroon.rs:464-484`), removal (`macaroon.rs:486-506`), wrong key (`macaroon.rs:455-462`) — are the negative theorems below via the unforgeability portal.

Real semantics here: the fold structure of the tag, append-only attenuation, conjunction admit-semantics
(`Token.admits` = `List.all`, `token/src/dregg_caveats.rs:388`), and the replay-and-compare verifier.

§8 PORTAL (honest carried crypto assumption, NEVER faked as proved — mirroring `Dregg2.CryptoKernel`):
the keyed-hash `mac : Key → Bytes → Tag` itself. Its security — that an adversary lacking the root key
or any running tag cannot produce a tag for a forged chain — is the `MacUnforgeable` Prop-carrier. The
integrity theorems are stated relative to it: we do NOT prove HMAC secure; we prove the reduction.

Builds on `Dregg2.Authority.Caveat` (reusing its `Caveat`/`Token.admits` narrowing layer); a verified
chain yields a `Ctx → Bool` admit-gate (`verifiedChainGate`).

Pure, computable, `#eval`-able. No `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Dregg2.Authority.Caveat

namespace Dregg2.Authority.CaveatChain

open Dregg2.Authority

/-! ## §8 portal — the abstract keyed-hash (HMAC). -/

/- A **tag** = the 32-byte HMAC-SHA256 chain tail (`macaroon.rs:104` `tail : [u8; 32]`). Abstract.
`DecidableEq` because the Rust does an equality compare (constant-time, `macaroon.rs:257`); the
constant-time-ness is an operational side-channel property below the semantic layer, not a
correctness property, so it is *not* modeled here (it does not change the accept/reject relation). -/
variable {Tag : Type} [DecidableEq Tag]

/-- A **key** for the keyed hash: either the issuer root key (`macaroon.rs:118`) or, after the first
step, a previous tag used *as* the key (`macaroon.rs:154` `hmac_sha256(&self.tail, …)`). In the real
HMAC chain a tag IS reused as a key, so we identify the two: `Key := Tag`. The root key is just the
first key in the chain. -/
abbrev Key (Tag : Type) := Tag

/- The **encoded bytes** of a caveat fed to the HMAC (`WireCaveat::encode`, `macaroon.rs:153`).
Abstract; the only thing the chain semantics needs is that distinct caveats encode distinctly enough
to be hashed — collision-freedom of `encode∘C` is folded into the `mac` portal's unforgeability. -/
variable {Bytes : Type}

/-- **`MacKernel`** — the §8 keyed-hash portal. `mac key bytes` is HMAC-SHA256 (`macaroon.rs`'s
`crypto::hmac_sha256`). Uninterpreted (like `Dregg2.Crypto.CryptoKernel.hash`); its security is the
`unforgeable` Prop-carrier, the obligation the Rust HMAC discharges, never a Lean law. -/
class MacKernel (Key Bytes Tag : Type) where
  /-- HMAC-SHA256: `mac key msg` (`crypto::hmac_sha256(key, msg)`). -/
  mac : Key → Bytes → Tag
  /-- **CARRIER — keyed-hash unforgeability** (`Prop`, the correct KIND of assumption, exactly as
  `CryptoKernel.collisionHard` is a `Prop`). Informally: "no PPT adversary, lacking `key`, produces
  any `(msg, t)` with `mac key msg = t`." We expose it as the precise *reduction premise* the
  integrity proofs consume: a function turning any forged-but-accepted chain into a witnessed MAC
  collision (defined precisely once the chain type is in scope, below). It is `True`-dischargeable
  only by the toy reference kernel; the real kernel leaves it as the standing §8 obligation. -/
  unforgeable : Prop

variable [MacKernel (Key Tag) Bytes Tag]

open MacKernel

/-! ## The chain (the macaroon body), modeled exactly as the Rust computes the tail. -/

/-- A **link** in the caveat chain = one caveat together with the bytes that were HMAC'd for it.
In Rust the bytes ARE `WireCaveat::encode(caveat)` (`macaroon.rs:153`); we keep them as a paired
field so the *semantic* caveat (a `Ctx → Bool` gate / 3P gateway, from `Authority.Caveat`) and the
*hashed* representation are both present and their correspondence is explicit. -/
structure Link (Ctx Gateway Bytes : Type) where
  /-- the semantic caveat (reused from `Authority.Caveat`) — the narrowing gate. -/
  caveat : Caveat Ctx Gateway
  /-- its wire encoding `encode(Cᵢ)` fed to the HMAC (`macaroon.rs:153`). -/
  encoded : Bytes

/-- A **caveat chain** = the macaroon body: a root key (held secret by the issuer, `macaroon.rs:118`),
a nonce-seed (the `Nonce::encode` bytes, `macaroon.rs:71-74,120`), the ordered links, and the stored
tail (`macaroon.rs:104`). Append-only attenuation only ever extends `links` (and recomputes `tail`).

NOTE the `tail` is stored, *as in the Rust* (`Macaroon.tail`), and is exactly what the adversary may
try to forge: `verify` recomputes from the root and compares against this stored field. -/
structure Chain (Ctx Gateway Key Bytes Tag : Type) where
  /-- root key — secret, never on the wire (`macaroon.rs:117` "must be kept secret by the issuer"). -/
  root  : Key
  /-- nonce-seed bytes (`Nonce::encode`, `macaroon.rs:71`); seeds `T₀`. -/
  nonce : Bytes
  /-- the ordered, append-only caveat links `[C₁ … Cₙ]` (`macaroon.rs:101`). -/
  links : List (Link Ctx Gateway Bytes)
  /-- the stored HMAC chain tail `Tₙ` (`macaroon.rs:104`). -/
  tail  : Tag

/-- **`seedTag root nonce = T₀`** — the chain seed (`macaroon.rs:121` `hmac_sha256(root_key,
nonce_bytes)`). -/
def seedTag (root : Key Tag) (nonce : Bytes) : Tag := mac root nonce

/-- **`foldTag t₀ links`** — replay the HMAC chain from a starting tag over the link encodings:
`Tᵢ = HMAC(Tᵢ₋₁, encode(Cᵢ))` (`macaroon.rs:154`, the header invariant `macaroon.rs:16-20`). A
left fold, *exactly* the Rust `for wire_caveat … current_tail = hmac_sha256(&current_tail, &encoded)`
loop (`macaroon.rs:215-254`). -/
def foldTag (t0 : Tag) (links : List (Link Ctx Gateway Bytes)) : Tag :=
  links.foldl (fun t link => mac t link.encoded) t0

/-- **`replayTag c`** — recompute the chain tail from the ROOT key (`macaroon.rs:213-254`). This is
what `verify` derives; it does NOT consult the stored `c.tail`. -/
def replayTag (c : Chain Ctx Gateway (Key Tag) Bytes Tag) : Tag :=
  foldTag (seedTag c.root c.nonce) c.links

/-- **`Chain.wellTagged c`** — the honest-construction invariant: the stored tail equals the replayed
tail. Every chain produced by `seed`/`append` (below) satisfies this by construction; an *adversary*
fabricates a `Chain` whose stored `tail` and `links` need NOT satisfy it. -/
def Chain.wellTagged (c : Chain Ctx Gateway (Key Tag) Bytes Tag) : Prop :=
  c.tail = replayTag c

/-! ## Construction = `Macaroon::new` + `add_first_party` (append-only attenuation). -/

/-- **`seed root nonce` = `Macaroon::new`** (`macaroon.rs:118-129`): an empty caveat chain whose tail
is `T₀ = mac root nonce`. -/
def seed (root : Key Tag) (nonce : Bytes) : Chain Ctx Gateway (Key Tag) Bytes Tag :=
  { root := root, nonce := nonce, links := [], tail := seedTag root nonce }

/-- **`Chain.append c link` = `add_first_party`** (`macaroon.rs:151-156`): the ONE attenuation op —
append a caveat link and advance the tail `new_tail = mac old_tail link.encoded`. Append-only by
construction (it can only push onto `links`, never remove/reorder). -/
def Chain.append (c : Chain Ctx Gateway (Key Tag) Bytes Tag) (link : Link Ctx Gateway Bytes) :
    Chain Ctx Gateway (Key Tag) Bytes Tag :=
  { c with links := c.links ++ [link], tail := mac c.tail link.encoded }

/-- **Verification** = replay-and-compare (`macaroon.rs:204-262`). Recompute the tail from the root
and accept iff it matches the stored tail (the constant-time compare at `macaroon.rs:257`). Returns
`Bool` — the runnable golden oracle. -/
def Chain.verify (c : Chain Ctx Gateway (Key Tag) Bytes Tag) : Bool :=
  decide (replayTag c = c.tail)

/-! ## (c) Verification recomputes the chain tag and accepts iff it matches. -/

/-- **`verify_iff_wellTagged`** — `verify` accepts exactly when the stored tail equals the replayed
tail: `verify = true ↔ wellTagged`. The Rust constant-time compare (`macaroon.rs:257-259`):
accept iff `current_tail == self.tail`. -/
theorem verify_iff_wellTagged (c : Chain Ctx Gateway (Key Tag) Bytes Tag) :
    c.verify = true ↔ c.wellTagged := by
  unfold Chain.verify Chain.wellTagged
  rw [decide_eq_true_iff]
  exact eq_comm

/-! ## Honest construction always verifies (the chain Rust actually builds is well-tagged). -/

/-- **`replayTag_seed`** — a freshly `seed`ed chain replays to its own tail (`T₀`). -/
theorem replayTag_seed (Ctx Gateway : Type) (root : Key Tag) (nonce : Bytes) :
    replayTag (seed (Ctx := Ctx) (Gateway := Gateway) root nonce)
      = (seed (Ctx := Ctx) (Gateway := Gateway) root nonce).tail := by
  simp [replayTag, seed, foldTag]

/-- **`replayTag_append`** — appending a link advances the replayed tail by one HMAC step over
the old replayed tail: the fold's defining recurrence (`Tᵢ = mac Tᵢ₋₁ encode(Cᵢ)`). -/
theorem replayTag_append (c : Chain Ctx Gateway (Key Tag) Bytes Tag) (link : Link Ctx Gateway Bytes) :
    replayTag (c.append link) = mac (replayTag c) link.encoded := by
  simp [replayTag, Chain.append, foldTag, List.foldl_append]

/-- **`wellTagged_seed`** — `Macaroon::new` produces a well-tagged chain. -/
theorem wellTagged_seed (Ctx Gateway : Type) (root : Key Tag) (nonce : Bytes) :
    (seed (Ctx := Ctx) (Gateway := Gateway) root nonce).wellTagged :=
  (replayTag_seed Ctx Gateway root nonce).symm

/-- **`wellTagged_append`** — `add_first_party` preserves well-taggedness: if the parent was
well-tagged, the attenuated child is too. Every chain built by `seed` then any number of `append`s
verifies (`macaroon.rs:434-453` `test_attenuation_and_verify`). -/
theorem wellTagged_append (c : Chain Ctx Gateway (Key Tag) Bytes Tag) (link : Link Ctx Gateway Bytes)
    (h : c.wellTagged) : (c.append link).wellTagged := by
  unfold Chain.wellTagged at h ⊢
  rw [replayTag_append, ← h]
  rfl

/-- **`honest_chain_verifies`** — a `seed` then `append`s always `verify`s. Positive companion to
the negative integrity theorems. -/
theorem honest_chain_verifies (Ctx Gateway : Type) (root : Key Tag) (nonce : Bytes)
    (link : Link Ctx Gateway Bytes) :
    ((seed (Ctx := Ctx) (Gateway := Gateway) root nonce).append link).verify = true :=
  (verify_iff_wellTagged _).mpr (wellTagged_append _ _ (wellTagged_seed Ctx Gateway root nonce))

/-! ## (a) Append-only attenuation NARROWS — bridged to `Authority.Caveat`. -/

/-- The semantic admit-set of a chain (the `Ctx → Bool` face): the conjunction of all link caveats,
reusing `Caveat.ok` from `Authority.Caveat` (so the meet-semantics `token/src/dregg_caveats.rs:388`
is shared with `Token.admits`, not re-derived). -/
def Chain.admits (c : Chain Ctx Gateway (Key Tag) Bytes Tag) (ctx : Ctx) (d : Discharges Gateway) :
    Bool :=
  c.links.all (fun l => l.caveat.ok ctx d)

/-- **`append_narrows`** — append-only attenuation can only restrict. Anything the attenuated chain
admits, the parent already admitted: appending a caveat never grows authority. "A key may only
narrow" (`caveat.rs:2-9,47-49`, `macaroon.rs:146-150`), now stated on the real HMAC chain. -/
theorem append_narrows (c : Chain Ctx Gateway (Key Tag) Bytes Tag) (link : Link Ctx Gateway Bytes)
    (ctx : Ctx) (d : Discharges Gateway) :
    (c.append link).admits ctx d = true → c.admits ctx d = true := by
  unfold Chain.admits Chain.append
  simp only [List.all_append, Bool.and_eq_true]
  intro h; exact h.1

/-- **`append_subset`** — set form: the attenuated chain's admissible-request set is a subset of
the parent's. Authority strictly shrinks as caveats are appended. -/
theorem append_subset (c : Chain Ctx Gateway (Key Tag) Bytes Tag) (link : Link Ctx Gateway Bytes)
    (d : Discharges Gateway) :
    {ctx | (c.append link).admits ctx d = true} ⊆ {ctx | c.admits ctx d = true} :=
  fun ctx h => append_narrows c link ctx d h

/-! ## Bridge to `Authority.Caveat`: a verified chain yields a `Ctx → Bool` admit-gate / a `Token`. -/

/-- **`verifiedChainGate`** — a verified chain projects to the `Authority.Caveat` abstraction: its
admit decision as a `Ctx → Bool` gate (with discharges fixed). Everything proved about `Token.admits`
in `Authority/Caveat.lean` applies to a chain that has passed `verify`. -/
def verifiedChainGate (c : Chain Ctx Gateway (Key Tag) Bytes Tag) (d : Discharges Gateway) :
    Ctx → Bool :=
  fun ctx => c.verify && c.admits ctx d

/-- **`chainToken`** — a chain's links project to an `Authority.Token` (dropping the HMAC tail):
the narrowing algebra carries over verbatim. The chain adds integrity on top of the token's
admit-semantics; this map shows the chain is a faithful refinement, not a parallel object. -/
def chainToken (c : Chain Ctx Gateway (Key Tag) Bytes Tag) : Token Ctx Gateway :=
  { kind := .macaroon, caveats := c.links.map (·.caveat) }

/-- **`chainToken_admits`** — the projection preserves admit-semantics: the chain's `admits`
equals its projected token's `Token.admits`. The bridge is meaning-preserving. -/
theorem chainToken_admits (c : Chain Ctx Gateway (Key Tag) Bytes Tag) (ctx : Ctx)
    (d : Discharges Gateway) :
    c.admits ctx d = (chainToken c).admits ctx d := by
  unfold Chain.admits chainToken Token.admits
  rw [List.all_map]
  rfl

/-! ## (b) Tail-binding / chain-integrity — stated relative to keyed-hash unforgeability.

We do NOT prove HMAC secure. We expose the §8 unforgeability assumption as a precise reduction
premise — "if a chain verifies, its stored tail was produced by the legitimate fold from the root" —
and prove the integrity laws as consequences of that premise plus the proved fold structure. The real
HMAC discharges the premise (assumed); the toy reference kernel discharges it trivially. -/

/-- **The unforgeability premise, specialized to chains (the §8 reduction hook).** "Any chain that
`verify`s is well-tagged." Note this is *definitionally* `verify_iff_wellTagged` — so it is, in this
abstract setting, PROVED, NOT assumed. The §8 content is hidden one level down: it is the assertion
that the adversary *could not have produced the stored `tail`* for forged `links` WITHOUT it equalling
the legitimate fold — i.e. that `replayTag c = c.tail` is not satisfiable by a forged `c` except by a
MAC collision. That last clause is what `MacKernel.unforgeable` carries; the theorems below phrase
integrity so that the only escape hatch is exactly such a collision. -/
def ChainIntegrityPremise (Ctx Gateway : Type) : Prop :=
  ∀ c : Chain Ctx Gateway (Key Tag) Bytes Tag, c.verify = true → c.wellTagged

theorem chainIntegrityPremise_holds (Ctx Gateway : Type) :
    ChainIntegrityPremise (Tag := Tag) (Bytes := Bytes) Ctx Gateway :=
  fun c h => (verify_iff_wellTagged c).mp h

/-- **`integrity_tail_binds`** — positive form: if a chain verifies, its stored tail is the
legitimate fold of its links from its root. No accepted chain has a tail detached from its caveat
list — the tail binds the entire ordered caveat sequence (`macaroon.rs:257`). -/
theorem integrity_tail_binds (c : Chain Ctx Gateway (Key Tag) Bytes Tag) (h : c.verify = true) :
    c.tail = foldTag (seedTag c.root c.nonce) c.links :=
  (verify_iff_wellTagged c).mp h

/-- **`forgery_requires_mac_query`** — the integrity reduction. If a forged chain `cForged` (different
links) `verify`s against the same stored tail as an honest chain `cHonest` over the same root+nonce,
the adversary has exhibited a MAC collision at the tail: the fold over forged links equals the fold
over honest links, despite differing link lists. Producing this without the root key is what
`MacKernel.unforgeable` forbids — the reduction "forge ⇒ break HMAC", with HMAC security left as
the §8 portal. -/
theorem forgery_requires_mac_query
    (cHonest cForged : Chain Ctx Gateway (Key Tag) Bytes Tag)
    (hroot : cForged.root = cHonest.root) (hnonce : cForged.nonce = cHonest.nonce)
    (hsameTail : cForged.tail = cHonest.tail)
    (hH : cHonest.verify = true) (hF : cForged.verify = true)
    (hdiffer : cForged.links ≠ cHonest.links) :
    -- the forged fold collides with the honest fold at the tail, over DIFFERING link lists:
    foldTag (seedTag cForged.root cForged.nonce) cForged.links
      = foldTag (seedTag cHonest.root cHonest.nonce) cHonest.links
    ∧ cForged.links ≠ cHonest.links := by
  refine ⟨?_, hdiffer⟩
  have eH : cHonest.tail = foldTag (seedTag cHonest.root cHonest.nonce) cHonest.links :=
    integrity_tail_binds cHonest hH
  have eF : cForged.tail = foldTag (seedTag cForged.root cForged.nonce) cForged.links :=
    integrity_tail_binds cForged hF
  rw [← eF, ← eH]; exact hsameTail

/-- **`removal_breaks_tail`** — the dropped-caveat law (`macaroon.rs:486-506`
`test_removed_caveat_fails`). If a verifying chain has its last caveat dropped (reverting `links`
to the parent's) without recomputing the tail, the result fails `verify` unless the parent's fold
collided with the child's tail — a MAC no-op, exactly what the unforgeability portal rules out.
Stated as: the stripped chain verifies → a MAC step was a no-op (the collision witness). -/
theorem removal_breaks_tail
    (c : Chain Ctx Gateway (Key Tag) Bytes Tag) (link : Link Ctx Gateway Bytes)
    -- `child` = c.append link (a verifying attenuated chain); `stripped` reverts links to `c.links`
    -- but keeps the CHILD's tail (the adversary drops a caveat without re-signing):
    (stripped : Chain Ctx Gateway (Key Tag) Bytes Tag)
    (hsl : stripped.links = c.links) (hsr : stripped.root = c.root) (hsn : stripped.nonce = c.nonce)
    (hst : stripped.tail = (c.append link).tail)
    (hc : c.wellTagged)
    (hverif : stripped.verify = true) :
    -- the only way removal slips past verify: the dropped HMAC step was a no-op (a collision):
    mac (replayTag c) link.encoded = replayTag c := by
  have hwt : stripped.wellTagged := (verify_iff_wellTagged stripped).mp hverif
  unfold Chain.wellTagged at hwt
  -- stripped.tail = replayTag stripped = foldTag over c.links from c.root = replayTag c (since wellTagged c)
  have hreplay_stripped : replayTag stripped = replayTag c := by
    unfold replayTag seedTag
    rw [hsl, hsr, hsn]
  -- stripped.tail = child.tail = mac (replayTag c) link.encoded  (child well-tagged via append)
  have hchild : (c.append link).tail = mac (replayTag c) link.encoded := by
    show mac c.tail link.encoded = mac (replayTag c) link.encoded
    unfold Chain.wellTagged at hc; rw [hc]
  -- combine: mac (replayTag c) link.encoded = child.tail = stripped.tail = replayTag stripped = replayTag c
  rw [hst, hchild] at hwt
  rw [hwt, hreplay_stripped]

/-! ## It runs (`#eval`) — a toy `MacKernel` over `Nat` exhibiting build/verify and a forgery rejection. -/

namespace Demo

/-- A toy keyed hash over `Nat`: `mac k m = 31*k + 7*m + 1` (a TEST stand-in for HMAC; injective in
each argument, enough to demonstrate the chain mechanics — NOT collision-resistant, NOT the real
crypto). The reference kernel's `unforgeable` carrier is `True` (toy-discharged), exactly as
`CryptoKernel.Reference.collisionHard := True`. -/
instance : MacKernel Nat Nat Nat where
  mac k m := 31 * k + 7 * m + 1
  unforgeable := True

/-- A toy request context: a block height (matching `Authority/Caveat.lean`'s `Height`). -/
abbrev H := Nat

/-- Root macaroon: `seed root=5 nonce=9`, no caveats (`Macaroon::new`). -/
def root5 : Chain H Unit Nat Nat Nat := seed (Ctx := H) (Gateway := Unit) 5 9

/-- Attenuate with "height ≥ 100" (encoded as bytes `100`) then "height ≤ 200" (bytes `200`). -/
def windowed : Chain H Unit Nat Nat Nat :=
  (root5.append { caveat := .local (fun h => decide (100 ≤ h)), encoded := 100 }).append
        { caveat := .local (fun h => decide (h ≤ 200)),  encoded := 200 }

def noD : Discharges Unit := fun _ => false

#guard root5.verify                       -- Macaroon::new is well-tagged
#guard windowed.verify                    -- honest attenuation chain verifies
#guard windowed.admits 150 noD            -- 150 ∈ [100,200]
#guard windowed.admits 50  noD == false   -- a caveat narrowed it out
#guard (verifiedChainGate (Ctx := H) windowed noD) 150            -- gate: verified ∧ admits
#guard (verifiedChainGate (Ctx := H) windowed noD) 50 == false

/-- A FORGED chain: take `windowed`'s tail but drop the last caveat (the `test_removed_caveat_fails`
attack) without re-signing. -/
def forgedDropped : Chain H Unit Nat Nat Nat :=
  { windowed with links := windowed.links.dropLast }

#guard forgedDropped.verify == false     -- tail no longer binds the truncated link list

/-- A FORGED chain: tamper the encoded bytes of a caveat (the `test_tampered_caveat_fails` attack). -/
def forgedTampered : Chain H Unit Nat Nat Nat :=
  { windowed with links := [{ caveat := .local (fun _ => true), encoded := 999 }] ++ windowed.links.tail }

#guard forgedTampered.verify == false    -- replayed tail diverges from stored tail

end Demo

end Dregg2.Authority.CaveatChain
