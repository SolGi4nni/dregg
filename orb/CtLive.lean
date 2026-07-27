/-
# CtLive — driving the PROVEN RFC 6962 CT verifier over the byte level

`Pki.Ct` and `Ct.Inclusion` model Certificate Transparency (RFC 6962) as
sans-IO, proven Lean:

  * the **SCT verifier** (`Pki.Ct.verifySct`): reconstruct the RFC 6962 §3.2
    `digitally-signed` input (`signedData`) from the log entry + the SCT's own
    timestamp/extensions and check the log's signature over it — the Ed25519 lane
    routes to the F*-verified `Crypto.ed25519Verify` (EverCrypt), with
    `sct_verify_correct` (accept the honest log's SCT) and `sct_verify_reject`
    (reject a tampered one under log authenticity);
  * the **log id** (`Pki.Ct.logId`): `SHA-256(log public key)`, over the real
    `Crypto.sha256`, pinned 32 bytes wide by `log_id_correct`;
  * the **Merkle inclusion (audit-path) verifier** (`Ct.verifyInclusion` /
    `rootFromPath` / `auditPath` / `mth`): recompute a size-`n` tree head from a
    leaf hash, its index, and the sibling path, with `inclusion_iff`
    (verify iff genuine leaf) — RFC 6962 §2.1;
  * the concrete leaf/node hashes those consume (`Pki.Ct.mtlHash` = `SHA-256(0x00
    ‖ leaf)`, `nodeHash` = `SHA-256(0x01 ‖ l ‖ r)`), the RFC 6962 §2.1
    domain-separated forms.

None of that logic was wired into a running binary. This executable is that
wiring: a `selftest` that drives the PROVEN pipeline over real bytes:

  1. **SCT lane (real Ed25519).** Sign a certificate entry's RFC 6962 §3.2
     signed-data with a log key (RFC 8032 §7.1 test key — the same vector
     `crypto-selftest` verifies), then run the PROVEN `verifySct` under that log's
     public key: it ACCEPTS. Flip one certificate byte and `verifySct` REJECTS —
     the real EverCrypt Ed25519 sign/verify roundtrip, realizing
     `sct_verify_correct` / `sct_verify_reject`. The log id is `SHA-256` of the
     log key (real hash, 32 bytes), realizing `log_id_correct`.
  2. **Inclusion lane (proven verifier, executed).** Build a log, run the PROVEN
     `Ct.mth` / `auditPath` / `verifyInclusion` over a concrete collision-free
     hash scheme: the honest audit path for the genuine leaf VERIFIES; a wrong
     claimed leaf and a wrong root are REJECTED — realizing `ct_inclusion_faithful`.
  3. **Inclusion lane (real SHA-256 bytes).** Recompute a 4-leaf tree head with
     the concrete RFC 6962 §2.1 `mtlHash`/`nodeHash` (real EverCrypt SHA-256, the
     0x00/0x01 domain-separation prefixes) and check an audit-path recomputation
     against it: the byte-level realization of the same recomputation the proven
     `rootFromPath` performs.

## Honesty / realization boundary

This is **drorb-native**: the SCT is signed by our own test log key and the log
is our own leaf list — NOT a fetch of real SCTs from a public CT log, nor parsing
of the X.509 SCT extension (OID 1.3.6.1.4.1.11129.2.4.2) / OCSP-stapled or
TLS-extension SCTs off a live handshake. Those are pure I/O (an HTTPS GET of a
log's `get-sth` / `get-proof-by-hash`, or DER extension extraction); the
cryptographic/structural core they feed is exactly the proven Lean exercised
here. That real-log ingestion is the named residual — no server socket is
missing, CT verification is a client-side check over bytes already in hand.

The inclusion lane's proven verifier runs over an injective (collision-free) hash
scheme so its interface obligations hold by construction; that real SHA-256
instantiates that collision-resistant, domain-separated interface is the standard
idealized-hash assumption (the design of `Ct.Basic`, where the digest is a
parameter never realized), witnessed byte-for-byte by lane 3 — not re-proven.

Usage:
  ct-live selftest
-/
import Pki.Ct

namespace CtLive

open Ct (HashScheme auditPath rootFromPath verifyInclusion mth inclusion_iff inclusion_complete)
open Pki.Ct

/-! ## The Phase-0 faithfulness theorems

The running selftest applies EXACTLY the proven decision. Two headline
obligations, both composing existing round-trip lemmas (never a `P → P`). -/

/-- **ct_inclusion_faithful.** For the genuine `i`-th appended leaf, the honest
audit path recomputes PRECISELY the model tree head (`rootFromPath … = some (mth
HS xs)` — the wire recomputation equals the signed tree head), and the proven
`verifyInclusion` therefore ACCEPTS. Composes `inclusion_complete` (the honest
recomputation, RFC 6962 §2.1) and `inclusion_iff` (verify-iff-genuine, whose `→`
spends `hnode_inj`/`hleaf_inj` collision resistance). Non-vacuous: the hypotheses
are `i < xs.length` and `xs[i]? = some y`; the conclusion is a concrete equality
about the recomputed head and a `= true`, not a tautology. -/
theorem ct_inclusion_faithful {Leaf H : Type} (HS : HashScheme Leaf H) [DecidableEq H]
    {xs : List Leaf} {i : Nat} {y : Leaf} (hi : i < xs.length) (hy : xs[i]? = some y) :
    rootFromPath HS (HS.hleaf y) i xs.length (auditPath HS xs i) = some (mth HS xs)
    ∧ verifyInclusion HS (HS.hleaf y) i xs.length (auditPath HS xs i) (mth HS xs) = true :=
  ⟨inclusion_complete HS xs.length xs i y rfl hy, (inclusion_iff HS hi).mpr hy⟩

/-- **ct_sct_faithful.** An SCT the log produced by Ed25519-signing the RFC 6962
§3.2 signed-data of a certificate entry VERIFIES under the log's public key — the
real EverCrypt sign/verify roundtrip. A genuine, honestly-logged certificate
always presents an SCT the proven `verifySct` accepts. Composes
`sct_verify_correct`; axioms include only the named `Crypto.Assumptions` Ed25519
seam. Non-vacuous: the hypothesis is that `signSctEd` actually produced this SCT
(inhabited — the selftest below produces one). -/
theorem ct_sct_faithful (sk : ByteArray) (ts : UInt64) (entry : LogEntryType)
    (leafEntry ext : Bytes) (logPub : ByteArray) (sct : Sct)
    (h : signSctEd sk ts entry leafEntry ext logPub = some sct) :
    verifySct Crypto.ed25519Verify sct entry leafEntry (Crypto.Assumptions.ed25519_pubOf sk) = true :=
  sct_verify_correct sk ts entry leafEntry ext logPub sct h

/-- **ct_sct_reject_faithful.** Under log authenticity for the log's public key
(the EUF-CMA functional shadow, an explicit hypothesis — never a Lean axiom), an
SCT reconstructing signed-data the log never signed — a tampered timestamp,
certificate, entry type, or extensions — is REJECTED by the proven `verifySct`
over the real `Crypto.ed25519Verify`. Composes `sct_verify_reject`; core axioms
only. Non-vacuous: the hypotheses (`LogAuthentic` and that the reconstructed
signed-data lies outside the log's signing history) are the satisfiable
conditions the selftest witnesses on a flipped certificate byte. -/
theorem ct_sct_reject_faithful (pub : ByteArray) (signed : ByteArray → Prop)
    (sct : Sct) (entry : LogEntryType) (leafEntry : Bytes)
    (hauth : LogAuthentic Crypto.ed25519Verify pub signed)
    (htamper :
      ¬ signed (toBA (signedData sct.version sct.timestamp entry leafEntry sct.extensions))) :
    verifySct Crypto.ed25519Verify sct entry leafEntry pub = false :=
  sct_verify_reject Crypto.ed25519Verify pub signed sct entry leafEntry hauth htamper

#print axioms ct_inclusion_faithful
#print axioms ct_sct_faithful
#print axioms ct_sct_reject_faithful

/-! ## A concrete collision-free hash scheme — so the PROVEN verifier RUNS

`Ct.HashScheme` bundles the hash forms with their collision-resistance /
domain-separation obligations. Over a free (structural) digest those obligations
hold by construction (`injection` / constructor disjointness), so we can EXECUTE
the proven `mth` / `auditPath` / `verifyInclusion` on real inputs. This realizes
the abstract verifier without introducing any axiom; that real SHA-256 also
inhabits this interface is the idealized-hash assumption (witnessed on bytes by
lane 3), not a Lean claim. -/

/-- A free structural Merkle digest over byte-string leaves. -/
inductive HDig where
  | empty
  | leaf (b : Bytes)
  | node (l r : HDig)
  deriving DecidableEq, Repr

/-- The collision-free scheme: leaves/nodes are distinct constructors, so the
`HashScheme` obligations are discharged with no axiom. -/
def freeScheme : HashScheme Bytes HDig where
  hempty := .empty
  hleaf := .leaf
  hnode := .node
  hleaf_inj := by intro x y h; exact HDig.leaf.inj h
  hnode_inj := by intro a b c d h; exact HDig.node.inj h
  leaf_ne_node := by intro x a b h; exact HDig.noConfusion h
  empty_ne_leaf := by intro x h; exact HDig.noConfusion h
  empty_ne_node := by intro a b h; exact HDig.noConfusion h

/-! ## Byte + hex helpers (mirror ControlLive/DerpLive) -/

def ofHex (s : String) : ByteArray := Id.run do
  let cs := s.toList.filter (fun c => c ≠ ' ' ∧ c ≠ '\n')
  let hexVal : Char → Option UInt8 := fun c =>
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
    else none
  let rec go : List Char → ByteArray → ByteArray
    | hi :: lo :: rest, acc =>
      match hexVal hi, hexVal lo with
      | some h, some l => go rest (acc.push (h * 16 + l))
      | _, _ => acc
    | _, acc => acc
  go cs (ByteArray.mk #[])

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-- Hex of a byte list (`Bytes` / a `Dig`). -/
def hx (l : Bytes) : String := toHex (toBA l)

/-- A digest is a byte list (the concrete RFC 6962 §2.1 SHA-256 output). -/
abbrev Dig := List UInt8

/-- Fold an audit path (leaf-to-root) into a recomputed head, over the concrete
RFC 6962 §2.1 node hash. Each step `(siblingOnRight, sib)`: when the sibling is on
the right we are the left child (`nodeHash acc sib`), else the right
(`nodeHash sib acc`). This is exactly the recomputation the proven `rootFromPath`
performs, on real SHA-256 bytes. -/
def ctFold (lh : Dig) (path : List (Bool × Dig)) : Dig :=
  path.foldl (fun acc step =>
    if step.1 then (nodeHash acc step.2).toList else (nodeHash step.2 acc).toList) lh

/-! ## The selftest -/

def selftest : IO UInt32 := do
  IO.println "== ct-live selftest : RFC 6962 Certificate Transparency, byte-level, proven verifier =="

  -- ── 1. SCT lane : real Ed25519 (RFC 8032 §7.1 test key) ─────────────────────
  IO.println "\n-- SCT (RFC 6962 §3.2), real EverCrypt Ed25519 --"
  let logSeed := ofHex "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
  let logPub  := ofHex "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
  let leaf    : Bytes := [0x30, 0x82, 0x01, 0x0a, 0xde, 0xad, 0xbe, 0xef]  -- stand-in DER cert entry
  let leafBad : Bytes := [0x30, 0x82, 0x01, 0x0a, 0xde, 0xad, 0xbe, 0xff]  -- one flipped byte
  let ext     : Bytes := []
  let ts      : UInt64 := 1709000000000

  let lid := logId logPub                        -- SHA-256(log public key), real hash
  IO.println s!"log id (SHA-256 of log key)   : {toHex lid}  ({lid.size}B)"
  if lid.size ≠ 32 then do IO.eprintln "log id not 32 bytes"; return 1

  let some sct := signSctEd logSeed ts .x509 leaf ext logPub
    | do IO.eprintln "signSctEd failed (EverCrypt Ed25519 sign)"; return 1
  IO.println s!"log signed the cert's §3.2 signed-data; SCT sig ({sct.signature.signature.size}B)"

  let accept := verifySct Crypto.ed25519Verify sct .x509 leaf    logPub
  let reject := verifySct Crypto.ed25519Verify sct .x509 leafBad logPub
  IO.println s!"verifySct(genuine cert)  ACCEPT : {accept}"
  IO.println s!"verifySct(flipped cert)  REJECT : {!reject}  (verify returned {reject})"
  if !accept then do IO.eprintln "genuine SCT did not verify"; return 1
  if reject  then do IO.eprintln "tampered SCT verified — MUST NOT happen"; return 1

  -- ── 2. Inclusion lane : the PROVEN verifier, executed ───────────────────────
  IO.println "\n-- Merkle inclusion (RFC 6962 §2.1), proven Ct.verifyInclusion executed --"
  let leaves : List Bytes := [[0x0a], [0x0b], [0x0c], [0x0d], [0x0e]]
  let i := 2
  let some y := leaves[i]?
    | do IO.eprintln "bad leaf index"; return 1
  let root := mth freeScheme leaves                       -- proven Merkle Tree Hash
  let path := auditPath freeScheme leaves i               -- proven honest audit path
  let lh   := freeScheme.hleaf y
  let ok       := verifyInclusion freeScheme lh i leaves.length path root
  let rejLeaf  := verifyInclusion freeScheme (freeScheme.hleaf ([0xff] : Bytes)) i leaves.length path root
  let rejRoot  := verifyInclusion freeScheme lh i leaves.length path (freeScheme.hleaf ([0x00] : Bytes))
  IO.println s!"log of {leaves.length} leaves, audit path for leaf #{i} has {path.length} sibling(s)"
  IO.println s!"verifyInclusion(genuine leaf)     ACCEPT : {ok}"
  IO.println s!"verifyInclusion(wrong leaf)       REJECT : {!rejLeaf}"
  IO.println s!"verifyInclusion(wrong root)       REJECT : {!rejRoot}"
  if !ok then do IO.eprintln "genuine inclusion did not verify"; return 1
  if rejLeaf || rejRoot then do IO.eprintln "a bad inclusion verified — MUST NOT happen"; return 1

  -- ── 3. Inclusion lane : real SHA-256 byte hashing (mtlHash/nodeHash) ────────
  IO.println "\n-- Merkle inclusion over REAL SHA-256 (RFC 6962 §2.1 0x00/0x01 domain sep) --"
  let a : Bytes := [0x01, 0x02, 0x03]
  let b : Bytes := [0x04, 0x05]
  let c : Bytes := [0x06]
  let d : Bytes := [0x07, 0x08, 0x09, 0x0a]
  let la := (mtlHash a).toList                     -- SHA-256(0x00 ‖ a)
  let lb := (mtlHash b).toList
  let lc := (mtlHash c).toList
  let ld := (mtlHash d).toList
  let nAB := (nodeHash la lb).toList               -- SHA-256(0x01 ‖ la ‖ lb)
  let nCD := (nodeHash lc ld).toList
  let head := (nodeHash nAB nCD).toList            -- the signed tree head
  IO.println s!"tree head (4 leaves, real SHA-256) : {hx head}"
  -- inclusion of leaf c (index 2): leaf-to-root sibling path [(right: ld), (left-subtree: nAB)]
  let recompC := ctFold lc [(true, ld), (false, nAB)]
  let inclC := recompC == head
  let recompBad := ctFold lc [(true, la), (false, nAB)]   -- wrong sibling
  let inclBad := recompBad == head
  IO.println s!"audit-path recompute(leaf c)  MATCHES head : {inclC}"
  IO.println s!"audit-path recompute(bad sib) MISMATCH     : {!inclBad}"
  if !inclC then do IO.eprintln "real-SHA256 inclusion recomputation did not match head"; return 1
  if inclBad then do IO.eprintln "a bad SHA-256 audit path matched — MUST NOT happen"; return 1

  -- ── cross-check summary ─────────────────────────────────────────────────────
  if accept && !reject && ok && !rejLeaf && !rejRoot && inclC && !inclBad then do
    IO.println "\nPASS — SCT verifies (real Ed25519) and rejects a tampered cert;"
    IO.println "       the proven Merkle inclusion verifier accepts the genuine leaf and rejects forgeries;"
    IO.println "       the RFC 6962 §2.1 audit-path recomputation over real SHA-256 reproduces the tree head."
    IO.println "CT VERIFICATION PIPELINE EXERCISED (drorb-native, byte-level, verified crypto)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the CT pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: ct-live selftest"
    return 1

end CtLive

def main (args : List String) : IO UInt32 := CtLive.main args
