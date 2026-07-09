/-
# Dregg2.Deos.AnchoredQuote — the COMMITTEE-ANCHORED quote verifier, discharged to the crypto floor.

Foundation piece **F3** of `docs/DREGG-DOCUMENT-FOUNDATION.md`. `Deos/Transclusion.lean` names Xanadu's
quote and proves its four properties — but its anti-forge keystones (`transclusion_provenance_faithful`,
`transclusion_forge_refused`) rest on `SourceHistory.stateAt : Receipt → Value` being an **abstract total
function** (a receipt determines a value BY MODEL CONSTRUCTION). They REFUSE "a different value for the
same cited receipt", but say NOTHING about an adversary who **fabricates the attestation itself** — signs
a root with keys the client does not trust. The collision-resistance hypotheses `HInj`/`HFresh`
(`Exec/Receipt.chain_tamper_evident`) exist but are **never invoked** by any transclusion keystone. So the
non-forgeable quote is asserted by the model, not proven.

This module closes that gap. The Rust hole is exact: `TranscludedField::include()` gated on
`AttestedResource::verify()` — content-hash + receipt-stream reconstruction + a **structural quorum
count** — NOT the cryptographic `verify_anchored(committee)`. "It cannot tell a fabricated root by a
committee it does not trust." Here we model the committee-anchored gate and PROVE that a quote it accepts
CANNOT be fabricated — the anti-forge **discharges to the crypto floor** via TWO named carriers, both
ACTUALLY USED in the proof of `anchored_quote_unforgeable`:

  1. **signature unforgeability (EUF-CMA)** — `SigUnforgeable Verify Signed`: a signature that VERIFIES
     under a public key was legitimately SIGNED by that key's holder. This is what turns the structural
     check `Verify signer msg sig` (a predicate an adversary can *claim*) into the cryptographic fact
     `Signed signer msg` (a fact only the key-holder can produce). It is the EUF-CMA carrier shape of
     `Crypto.HybridQuorum.Unforgeable` / `Crypto.ThresholdReduction.Unforgeable`, named at this boundary.

  2. **receipt-chain tamper-evidence** — `HInj`/`HFresh` threaded through
     `CrossCellImport.importProvenance_tamper_evident` (→ `Exec/Receipt.chain_tamper_evident`): a valid
     provenance cannot be denied by any OTHER well-linked history presenting the same head, so the cited
     receipt (and hence the committed value) is pinned. This closes "fabricate a different chain".

`anchored_quote_unforgeable` (the headline): if the committee-anchored gate ACCEPTS a quote AND the
provenance is re-presented against any well-linked history with the same head, then the quoted value IS
the source's genuinely-committed value at the cited receipt — no fabrication survives. NON-VACUOUS: an
honest quote ADMITS and the headline fires on it under a genuinely injective digest (§Witnesses); a quote
carrying a signature that does not verify under a trusted committee key, a quote of a value the source
never committed, and a genuine quote checked against the WRONG committee are each REFUSED — exactly where
the old structural `verify()` path would have accepted them.

NEW file only. Touches neither `Transclusion.lean` nor the core. Every keystone `#assert_all_clean`
(⊆ `{propext, Classical.choice, Quot.sound}`); the crypto floor is the NAMED hypotheses
(`SigUnforgeable`, `HInj`, `HFresh`), never a Lean axiom.
-/
import Dregg2.Authority.CrossCellImport
import Dregg2.Tactics
import Mathlib.Data.Nat.Pairing

namespace Dregg2.Deos.AnchoredQuote

open Dregg2.Exec (Value FieldName)
open Dregg2.Exec.Receipts
  (Receipt ReceiptChain wellLinked genesisSentinel)
open Dregg2.Authority.CrossCellImport
  (Import SourceHistory importValid readAt importProvenance_tamper_evident)

universe u v

/-! ## §1 — The signed message + the abstract signature scheme.

A committee attests a finalized cross-cell read by signing a canonical message that BINDS the claimed
value, the cited source receipt (the provenance), and the source field. Binding all three is what makes
the signature a witness that "the committee saw THIS value at THIS receipt", so neither the value nor the
provenance can be swapped after the fact. (`localField` — the LOCAL document field the quote lands in — is
deliberately NOT in the message: it is the quoter's choice, not the source's attestation.) -/

/-- **`QuoteMsg`** — the canonical committee-signed message of an anchored quote: the quoted value, the
cited source receipt (provenance), and the source field, bound together. -/
abbrev QuoteMsg := Int × Receipt × FieldName

/-- The canonical message an import's quote is signed over. -/
def quoteMsg (imp : Import) : QuoteMsg := (imp.value, imp.provenance, imp.sourceField)

/-- **`SigUnforgeable Verify Signed` (THE EUF-CMA CARRIER).** Every signature that VERIFIES under a
public key `pk` on a message `m` was legitimately SIGNED by the holder of `pk` — no verifying signature on
an un-signed message exists. This is the boundary at which the signature scheme's unforgeability (ed25519
EUF-CMA / the ML-DSA MLWE-MSIS carrier for the PQ half) is named; it is the `Crypto.HybridQuorum.Unforgeable`
shape. It is the hinge that upgrades a STRUCTURAL check (`Verify`, which an adversary can *present*) to a
CRYPTOGRAPHIC fact (`Signed`, which only the key-holder can produce). -/
def SigUnforgeable {PK : Type u} {Sig : Type v}
    (Verify : PK → QuoteMsg → Sig → Prop) (Signed : PK → QuoteMsg → Prop) : Prop :=
  ∀ pk m σ, Verify pk m σ → Signed pk m

/-! ## §2 — The anchored quote + the two acceptance gates (the cryptographic one and the old structural one). -/

/-- **`AnchoredQuote`** — a peer's quote as it arrives on the wire: the cited cross-cell `Import` (value +
provenance + fields), the claimed `signer` (a committee public key), and the `sig` over `quoteMsg imp`. -/
structure AnchoredQuote (PK : Type u) (Sig : Type v) where
  /-- The cited cross-cell import (source receipt + the value its field held there). -/
  imp    : Import
  /-- The public key the quote claims signed it. -/
  signer : PK
  /-- The signature over the canonical `quoteMsg imp`. -/
  sig    : Sig

/-- **`anchoredAccept committee Verify q` (THE COMMITTEE-ANCHORED GATE — Rust `verify_anchored`).** The
quote is accepted iff its `signer` is a key IN the client's TRUSTED committee AND its signature VERIFIES
on the canonical message under that key. This is the cryptographic gate: an attacker's own-key signature is
refused (the key is not in the committee), and a bogus signature under a committee key is refused (it does
not verify). Mirrors `AttestedResource::verify_anchored`'s `is_valid(committee)` — a check on the SIGNERS,
never a count. -/
def anchoredAccept {PK : Type u} {Sig : Type v}
    (committee : List PK) (Verify : PK → QuoteMsg → Sig → Prop)
    (q : AnchoredQuote PK Sig) : Prop :=
  q.signer ∈ committee ∧ Verify q.signer (quoteMsg q.imp) q.sig

/-- **`structuralAccept h q` (THE OLD STRUCTURAL GATE — Rust `verify`).** The content-chain check ONLY:
the cited receipt is in the source's chain. No committee, no signature crypto — exactly the weaker path
`include()` used to take (content-hash + receipt-stream reconstruction + a structural quorum COUNT). A
fabricated attestation with attacker-chosen keys passes THIS but not `anchoredAccept`. -/
def structuralAccept {PK : Type u} {Sig : Type v}
    (h : SourceHistory) (q : AnchoredQuote PK Sig) : Prop :=
  q.imp.provenance ∈ h.chain

/-! ## §3 — THE HEADLINE: an anchored quote cannot be forged (reduction to the crypto floor).

The anti-forge that `Transclusion.lean` asserted by model construction, here PROVEN by discharging to the
two named carriers. Both are ACTUALLY USED below: `hunforge` (EUF-CMA) upgrades the accepted `Verify` to
`Signed`; `HInj`/`HFresh` (through `importProvenance_tamper_evident`) pin the provenance against any rival
well-linked history. -/

/-- **`anchored_quote_unforgeable` (THE VERIFIER KEYSTONE).** Suppose the committee-anchored gate ACCEPTS
the quote `q` (`haccept`), the committee only ever signs valid finalized reads against its attested source
history `h` (`hpolicy` — the honest-committee semantics), the signature scheme is unforgeable (`hunforge`),
and the digest is collision-resistant (`HInj`/`HFresh`). Then for ANY well-linked history `h'` that
presents the same head as `h` (an adversary's attempt to re-present the source), the quote's cited receipt
lives in `h'` AND the quoted value is the value the source GENUINELY committed at that receipt. A
fabrication — a root signed by untrusted keys, or a value the source never committed, or a swapped chain —
cannot pass this gate. The anti-forge DISCHARGES to signature-unforgeability + hash collision-resistance;
it is not a model artifact.

Proof obligations actually invoked:
* `hunforge` — from the accepted `Verify q.signer …` (a structural predicate) to `Signed q.signer …`
  (the cryptographic fact); this is where "attacker keys" is refused.
* `HInj`/`HFresh` (via `importProvenance_tamper_evident`) — the provenance is pinned in `h'`; this is
  where "a fabricated chain" is refused. -/
theorem anchored_quote_unforgeable
    {PK : Type u} {Sig : Type v}
    {H : Receipt → Nat} {committee : List PK}
    {Verify : PK → QuoteMsg → Sig → Prop} {Signed : PK → QuoteMsg → Prop}
    {h h' : SourceHistory} {q : AnchoredQuote PK Sig}
    (HInj : Function.Injective H) (HFresh : ∀ p, H p ≠ genesisSentinel)
    (hunforge : SigUnforgeable Verify Signed)
    (hpolicy : ∀ pk imp, pk ∈ committee → Signed pk (quoteMsg imp) → importValid H h imp)
    (haccept : anchoredAccept committee Verify q)
    (hwl' : wellLinked H h'.chain)
    (hhead : h.chain.head? = h'.chain.head?) :
    q.imp.provenance ∈ h'.chain
      ∧ readAt h q.imp.provenance q.imp.sourceField = q.imp.value := by
  obtain ⟨hmem, hver⟩ := haccept
  -- (crypto floor #1) EUF-CMA: the ACCEPTED signature witnesses a genuine committee signature.
  have hsigned : Signed q.signer (quoteMsg q.imp) := hunforge _ _ _ hver
  -- the honest committee only signs valid finalized reads ⇒ the quote's import IS valid against `h`.
  have hvalid : importValid H h q.imp := hpolicy _ _ hmem hsigned
  refine ⟨?_, hvalid.2.2⟩
  -- (crypto floor #2) tamper-evidence: the provenance is pinned in ANY same-head well-linked history.
  exact importProvenance_tamper_evident HInj HFresh hvalid hwl' hhead

/-- **`anchored_quote_refuses_untrusted_signer` (the negative tooth, generic).** If the quote's claimed
signer is NOT in the client's trusted committee, the anchored gate REFUSES it — no matter what signature it
carries. A fabricated root by attacker-chosen keys never passes. (The other refusal — a bogus signature
under a committee key — is `¬ Verify`, discharged concretely in §Witnesses.) -/
theorem anchored_quote_refuses_untrusted_signer
    {PK : Type u} {Sig : Type v}
    {committee : List PK} {Verify : PK → QuoteMsg → Sig → Prop} {q : AnchoredQuote PK Sig}
    (huntrusted : q.signer ∉ committee) :
    ¬ anchoredAccept committee Verify q := by
  intro ⟨hmem, _⟩; exact huntrusted hmem

/-! ## §4 — NON-VACUITY: a concrete committee, a genuinely injective digest, both polarities BITE.

The digest `injH` is a REAL injective collision-resistant stand-in (a `Nat.pair` encoding of the receipt's
four commitments, `+1` so no real receipt hashes to the reserved genesis sentinel) — so `HInj`/`HFresh` are
DISCHARGED, not assumed, and the headline `anchored_quote_unforgeable` genuinely FIRES on the honest quote.
The toy signature scheme accepts exactly the honest committee key `7`'s genuine signature (`42`) on a valid
finalized read; a wrong signer, a bogus signature, a fabricated value, and the wrong committee are each
refused where `structuralAccept` (the old path) would accept. -/

section Witnesses

open Dregg2.Exec.Receipts (mkReceipt)

/-- A genuinely INJECTIVE receipt digest: a `Nat.pair` encoding of the four commitments, offset by one so
its image avoids the reserved genesis sentinel (`0`). This DISCHARGES the `HInj`/`HFresh` carriers
concretely — the tamper-evidence used by the headline is real here, not hypothetical. -/
def injH (r : Receipt) : Nat :=
  Nat.pair (Nat.pair r.prevHash r.oldCommit) (Nat.pair r.newCommit r.effectsHash) + 1

/-- **`injH` is injective** (the `HInj` carrier, discharged). Two receipts with the same digest agree on
every commitment field, hence are equal — the `Nat.pair` encoding is injective. -/
theorem injH_injective : Function.Injective injH := by
  intro a b hab
  unfold injH at hab
  have h0 : Nat.pair (Nat.pair a.prevHash a.oldCommit) (Nat.pair a.newCommit a.effectsHash)
          = Nat.pair (Nat.pair b.prevHash b.oldCommit) (Nat.pair b.newCommit b.effectsHash) := by
    omega
  rw [Nat.pair_eq_pair, Nat.pair_eq_pair, Nat.pair_eq_pair] at h0
  obtain ⟨⟨hp, ho⟩, hn, he⟩ := h0
  cases a; cases b
  simp_all

/-- **`injH` avoids the genesis sentinel** (the `HFresh` carrier, discharged). No real receipt digests to
`0`, because `injH` is always a successor. -/
theorem injH_fresh : ∀ p, injH p ≠ genesisSentinel := by
  intro p; unfold injH genesisSentinel; omega

/-- The SOURCE document cell's history: a genesis receipt committing `title = 7`, and a head linking onto
it via `injH`. Both receipts commit the record `title = 7`. -/
def qOld : Receipt := { prevHash := genesisSentinel, oldCommit := 7, newCommit := 7, effectsHash := 0 }
def qNew : Receipt := { prevHash := injH qOld, oldCommit := 7, newCommit := 7, effectsHash := 1 }
def qDoc : SourceHistory := ⟨[qNew, qOld], fun _ => .record [("title", .int 7)]⟩
/-- The honest import: local field `quote` IS the source's `title = 7` at the genesis receipt `qOld`. -/
def qImp : Import := ⟨"quote", "title", 7, qOld⟩

/-- `qDoc`'s chain is well-linked under the injective digest (`qNew` links to `injH qOld`; `qOld` pins the
sentinel). -/
theorem qDoc_wellLinked : wellLinked injH qDoc.chain := ⟨rfl, rfl⟩

/-- The honest import is valid against `qDoc`: well-linked chain, cited receipt present, and the source
field held exactly `7` there. -/
theorem qImp_valid : importValid injH qDoc qImp :=
  ⟨qDoc_wellLinked, List.mem_cons_of_mem _ List.mem_cons_self, by decide⟩

/-- The client's TRUSTED committee: the single honest validator key `7`. -/
def committee : List Nat := [7]
/-- A FOREIGN committee the client does not hold — used to show a genuine quote is refused against the
wrong anchor. -/
def foreignCommittee : List Nat := [8]

/-- The honest-signing relation: only the committee key `7` signs, and only a message whose (value,
provenance, sourceField) is a genuine valid finalized read against `qDoc`. This IS the honest-committee
attestation semantics (`importValid` on the message's components). -/
def cSigned : Nat → QuoteMsg → Prop :=
  fun pk m => pk = 7 ∧ wellLinked injH qDoc.chain ∧ m.2.1 ∈ qDoc.chain ∧ readAt qDoc m.2.1 m.2.2 = m.1

/-- The toy verifier: the genuine signature is the fixed tag `42`, producible only for an honestly-signed
message. A signature that is not `42`, or a message that is not a valid finalized read, does not verify. -/
def cVerify : Nat → QuoteMsg → Nat → Prop :=
  fun pk m σ => cSigned pk m ∧ σ = 42

/-- **`cSigUnforgeable` — the toy scheme is unforgeable.** A verifying signature is, by construction, on
an honestly-signed message. (Discharges the `SigUnforgeable` carrier for the witness.) -/
theorem cSigUnforgeable : SigUnforgeable cVerify cSigned :=
  fun _ _ _ h => h.1

/-- **`cPolicy` — the honest committee only signs valid finalized reads.** A committee signature on
`quoteMsg imp` witnesses `importValid injH qDoc imp` (the message's components ARE the import's provenance
obligation). Discharges the `hpolicy` obligation for the witness. -/
theorem cPolicy : ∀ pk imp, pk ∈ committee → cSigned pk (quoteMsg imp) → importValid injH qDoc imp :=
  fun _ imp _ hs => ⟨hs.2.1, hs.2.2.1, hs.2.2.2⟩

/-- The HONEST quote: the valid import, signed by committee key `7` with its genuine signature `42`. -/
def honestQuote : AnchoredQuote Nat Nat := ⟨qImp, 7, 42⟩
/-- A FORGED quote — the same genuine provenance, but a SIGNATURE (`999`) that is not the committee's (it
does not verify). The "fabricated attestation" vector: right content chain, wrong signature. -/
def forgedSignature : AnchoredQuote Nat Nat := ⟨qImp, 7, 999⟩
/-- A FORGED quote of a value the source never committed: claims `title = 99` (it was `7`) at `qOld`,
signed by the committee key. The content-fabrication vector. -/
def forgedValue : AnchoredQuote Nat Nat := ⟨⟨"quote", "title", 99, qOld⟩, 7, 42⟩

/-- **`honest_admits` (positive polarity).** The committee-anchored gate ACCEPTS the honest quote: the
signer is in the trusted committee and its genuine signature verifies on a valid finalized read. -/
theorem honest_admits : anchoredAccept committee cVerify honestQuote :=
  ⟨List.mem_cons_self, ⟨rfl, qDoc_wellLinked, List.mem_cons_of_mem _ List.mem_cons_self, by decide⟩, rfl⟩

/-- **`honest_quote_is_genuine` (THE HEADLINE FIRES, non-vacuously).** Instantiating
`anchored_quote_unforgeable` with the DISCHARGED carriers (`injH_injective`, `injH_fresh`,
`cSigUnforgeable`, `cPolicy`) on the honest quote yields: the cited receipt is in the source chain AND the
quoted value is the source's genuinely-committed `title = 7`. The anti-forge is not vacuous — it produces a
real faithfulness conclusion from the crypto floor. -/
theorem honest_quote_is_genuine :
    honestQuote.imp.provenance ∈ qDoc.chain
      ∧ readAt qDoc honestQuote.imp.provenance honestQuote.imp.sourceField = honestQuote.imp.value :=
  anchored_quote_unforgeable (H := injH) (committee := committee)
    (Verify := cVerify) (Signed := cSigned) (h := qDoc) (h' := qDoc) (q := honestQuote)
    injH_injective injH_fresh cSigUnforgeable cPolicy honest_admits qDoc_wellLinked rfl

/-- **`forged_signature_refused` (THE LC-1 BITE — old path accepts, anchored refuses).** The forged quote
carries the genuine provenance (so the OLD structural gate `structuralAccept` ACCEPTS it), but its
signature is not the committee's, so the committee-anchored gate REFUSES it. This is exactly the hole
`include()` closed: a fabricated attestation that the count-only path waved through is now refused by the
cryptographic gate. -/
theorem forged_signature_refused :
    structuralAccept qDoc forgedSignature ∧ ¬ anchoredAccept committee cVerify forgedSignature := by
  refine ⟨List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
  rintro ⟨_, _, hσ⟩
  exact absurd hσ (by decide)

/-- **`forged_value_refused` (the content-fabrication tooth).** A quote claiming a value the source never
committed (`title = 99`), even signed by the committee key, is REFUSED: the honest committee does not sign
an invalid finalized read, so the signature does not verify. -/
theorem forged_value_refused : ¬ anchoredAccept committee cVerify forgedValue := by
  rintro ⟨_, ⟨_, _, _, hread⟩, _⟩
  exact absurd hread (by decide)

/-- **`wrong_committee_refused` (the anchor tooth).** The genuine quote is REFUSED against a FOREIGN
committee — the anchor is the client's OWN trusted set, never the resource's claimed signers. -/
theorem wrong_committee_refused : ¬ anchoredAccept foreignCommittee cVerify honestQuote :=
  anchored_quote_refuses_untrusted_signer (by decide)

end Witnesses

/-! ## §5 — Axiom hygiene. Every keystone kernel-clean; the crypto floor is the NAMED hypotheses
(`SigUnforgeable`, `HInj`, `HFresh`), discharged concretely in §Witnesses, never a Lean axiom. -/

#assert_all_clean [
  anchored_quote_unforgeable,
  anchored_quote_refuses_untrusted_signer,
  injH_injective,
  injH_fresh,
  qImp_valid,
  cSigUnforgeable,
  cPolicy,
  honest_admits,
  honest_quote_is_genuine,
  forged_signature_refused,
  forged_value_refused,
  wrong_committee_refused
]

end Dregg2.Deos.AnchoredQuote
