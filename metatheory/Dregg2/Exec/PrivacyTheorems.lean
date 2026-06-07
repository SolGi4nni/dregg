/-
# Dregg2.Exec.PrivacyTheorems — D7 privacy soundness OVER the executable kernel primitives.

This is an *additive* module (it edits NOTHING in the hot core `FullForestAuth` / `RecordKernel`
/ `TurnExecutorFull`; gate-wiring is a separate task). It proves two privacy properties directly
on the primitives those modules already ship:

  **(1) NULLIFIER NO-DOUBLE-SPEND** (anti-replay, the Zcash discipline). `RecordKernel` models
  dregg1's off-ledger `note_nullifiers` SET (`apply.rs:941`) with fail-closed double-spend
  rejection: `noteSpendNullifier` inserts `nf` iff absent, returns `none` if present. The
  base facts `note_no_double_spend` / `note_spend_inserts` / `note_spend_then_reject` live in
  `RecordKernel`; here we LIFT the discipline to the chained effect-layer executor
  (`noteSpendChainA`, the real `NoteSpend` entry in `TurnExecutorFull`) and prove the
  *sequential* / *transitive* anti-replay that a multi-step turn forest needs:
    - `chainNoteSpend_no_double_spend` — the chained executor itself fails-closed on a recorded nf;
    - `chainNoteSpend_then_reject`     — after a committed chained spend, a second spend of the SAME
      nf on the resulting state fails-closed (the composed one-step replay barrier);
    - `nullifier_set_monotone` / `nullifier_persists` — a spent nf NEVER leaves the set across any
      committed chained spend, so it stays rejected forever (no resurrection);
    - `noteSpendSeq` + `seq_preserves_spent` / `seq_no_respend` — run a whole LIST of spends; a
      nullifier already spent before the sequence is still rejected if it reappears anywhere in it.
  This is a clean theorem over the kernel's nullifier discipline (pure SET/`Option` logic — no
  crypto). The §8 portal here is ONLY the STARK spending-proof + nullifier-derivation soundness
  (carried at the effect layer); the ledger-side anti-replay — which is what actually stops a
  replay — is FULLY proved.

  **(2) STEALTH FRESHNESS ⇒ UNLINKABILITY** (EIP-5564 / Monero one-time keys), with the crypto as
  an EXPLICIT named hypothesis (a §8 portal *carrier*, never a `sorry`). The one-time destination
  address is, in the real scheme, `P = H(r·V)·G + S` — a recipient-bound function of the ephemeral
  pubkey `R = r·G`. We name that derivation `deriveOneTime : Digest → Digest` (the §8 DH-to-one-time
  carrier) and prove what is *structurally* true of `Authorization.stealth`:
    - `fresh_ephemeral_distinct_onetime` — IF `deriveOneTime` is injective (the carrier hypothesis
      the curve/DH layer discharges), THEN distinct fresh ephemeral pubkeys yield distinct one-time
      addresses. So two payments do not collide on a reused address — the structural precondition of
      unlinkability;
    - `stealth_distinct_statements` — distinct fresh one-time addresses give the two
      `Authorization.stealth` credentials DISTINCT `portalVerify` statements (`CryptoKernel.verify`
      is keyed on the one-time pubkey), so an observer cannot link the two spends by a shared
      verification target;
    - `stealth_ephemeralPk_binds` — the preimage the one-time signature is taken over BINDS the
      ephemeral pubkey (a relay cannot swap `R`), routed through the already-proved
      `SigningMessage.sigMsgStealth_binds_ephemeralPk` (pure byte-list injectivity, no crypto);
    - `stealth_unlinkable_via_graphKernel` — the information-theoretic unlinkability ON THE
      OBSERVER VIEW (`Privacy.GraphPrivacyKernel.unlinkable_law`): two same-recipient one-time
      addresses are view-indistinguishable. The residual *computational* indistinguishability
      advantage bound stays the named §8 carrier (`Crypto.Primitives.unlinkable` /
      `GraphPrivacyKernel`), NOT claimed here.

Style: spec-first, `#guard` witnesses (never `#eval`-comments).
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.FullForestAuth
import Dregg2.Exec.SigningMessage
import Dregg2.Privacy
import Dregg2.CryptoKernel

namespace Dregg2.Exec.PrivacyTheorems

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Crypto (CryptoKernel)

/-! ## §1 — NULLIFIER NO-DOUBLE-SPEND over the executable kernel + chained effect layer.

The base SET discipline (`noteSpendNullifier` fail-closed on a present nf) and its three base
theorems live in `RecordKernel`. We re-export the head fact for locality, then LIFT the discipline
to the chained `NoteSpend` effect entry and to whole spend SEQUENCES. -/

/-- **The base anti-replay, re-stated at this module (PROVED, delegates to `RecordKernel`).** A
nullifier already in the spent set cannot be spent again: `noteSpendNullifier` fails-closed. This
is the head of the discipline everything below lifts. -/
theorem kernel_no_double_spend (k : RecordKernelState) (nf : Nat)
    (h : nf ∈ k.nullifiers) : noteSpendNullifier k nf = none :=
  note_no_double_spend k nf h

/-! ### The chained effect-layer entry (`noteSpendChainA`, the real `NoteSpend`). -/

/-- **`chainNoteSpend_no_double_spend` — PROVED.** The chained `NoteSpend` executor itself
fails-closed on a nullifier already in the spent set: the effect-layer entry inherits the kernel's
double-spend gate. (`noteSpendChainA` matches on `noteSpendNullifier`; the `none` branch propagates
to a `none` result — the turn is rejected, no receipt is appended.) -/
theorem chainNoteSpend_no_double_spend (s : RecChainedState) (nf : Nat) (actor : CellId)
    (spendProof : Bool) (h : nf ∈ s.kernel.nullifiers) :
    noteSpendChainA s nf actor spendProof = none := by
  unfold noteSpendChainA
  by_cases hp : spendProof = true
  · rw [if_pos hp, note_no_double_spend s.kernel nf h]
  · rw [if_neg hp]

/-- A committed chained spend inserts `nf` into the resulting state's nullifier set (the chained
analog of `note_spend_inserts`: the receipt row never touches `nullifiers`, only the kernel does). -/
theorem chainNoteSpend_inserts {s s' : RecChainedState} {nf : Nat} {actor : CellId}
    {spendProof : Bool} (h : noteSpendChainA s nf actor spendProof = some s') :
    nf ∈ s'.kernel.nullifiers := by
  unfold noteSpendChainA at h
  by_cases hp : spendProof = true
  · rw [if_pos hp] at h
    cases hk : noteSpendNullifier s.kernel nf with
    | none => rw [hk] at h; exact absurd h (by simp)
    | some k' =>
      rw [hk] at h
      simp only [Option.some.injEq] at h
      subst h
      exact note_spend_inserts hk
  · rw [if_neg hp] at h; exact absurd h (by simp)

/-- **`chainNoteSpend_then_reject` — PROVED (the composed one-step replay barrier).** After a
committed chained `NoteSpend` of `nf`, a SECOND chained spend of the SAME `nf` on the resulting
state fails-closed. Replay across two effect-layer steps is impossible. -/
theorem chainNoteSpend_then_reject {s s' : RecChainedState} {nf : Nat} {actor actor' : CellId}
    {spendProof spendProof' : Bool} (h : noteSpendChainA s nf actor spendProof = some s') :
    noteSpendChainA s' nf actor' spendProof' = none :=
  chainNoteSpend_no_double_spend s' nf actor' spendProof' (chainNoteSpend_inserts h)

/-! ### Monotonicity: a spent nullifier never leaves the set (no resurrection). -/

/-- **`nullifier_set_monotone` — PROVED.** Any committed chained `NoteSpend` only GROWS the
nullifier set: every previously-spent `nf'` is still present afterward. (The chained spend is a
`cons` onto `nullifiers`; nothing is ever removed.) This is the structural reason a spent note can
never be resurrected. -/
theorem nullifier_set_monotone {s s' : RecChainedState} {nf nf' : Nat} {actor : CellId}
    {spendProof : Bool} (h : noteSpendChainA s nf actor spendProof = some s')
    (hmem : nf' ∈ s.kernel.nullifiers) : nf' ∈ s'.kernel.nullifiers := by
  unfold noteSpendChainA at h
  by_cases hp : spendProof = true
  · rw [if_pos hp] at h
    cases hk : noteSpendNullifier s.kernel nf with
    | none => rw [hk] at h; exact absurd h (by simp)
    | some k' =>
      rw [hk] at h
      simp only [Option.some.injEq] at h
      subst h
      -- `noteSpendNullifier` on the success branch does `nullifiers := nf :: …`; `nf'` survives.
      unfold noteSpendNullifier at hk
      by_cases hin : nf ∈ s.kernel.nullifiers
      · rw [if_pos hin] at hk; exact absurd hk (by simp)
      · rw [if_neg hin] at hk
        simp only [Option.some.injEq] at hk
        subst hk
        exact List.mem_cons_of_mem _ hmem
  · rw [if_neg hp] at h; exact absurd h (by simp)

/-- **`nullifier_persists` — PROVED.** A nullifier spent BEFORE a (possibly unrelated) committed
chained spend is STILL rejected on the resulting state — combine monotonicity with the gate. The
anti-replay is permanent: once spent, forever rejected, regardless of intervening spends. -/
theorem nullifier_persists {s s' : RecChainedState} {nf nf' : Nat} {actor actor' : CellId}
    {spendProof spendProof' : Bool} (h : noteSpendChainA s nf actor spendProof = some s')
    (hmem : nf' ∈ s.kernel.nullifiers) :
    noteSpendChainA s' nf' actor' spendProof' = none :=
  chainNoteSpend_no_double_spend s' nf' actor' spendProof' (nullifier_set_monotone h hmem)

/-! ### Whole-sequence anti-replay: a list of spends never re-spends. -/

/-- Run a LIST of chained note-spends, short-circuiting to `none` on the first rejection (the
fold-`bind` over `noteSpendChainA`). This is the effect-layer shape of a multi-`NoteSpend` turn. -/
def noteSpendSeq (s : RecChainedState) (actor : CellId) (spendProof : Bool) :
    List Nat → Option RecChainedState
  | []          => some s
  | nf :: rest  =>
    match noteSpendChainA s nf actor spendProof with
    | some s' => noteSpendSeq s' actor spendProof rest
    | none    => none

/-- **`seq_preserves_spent` — PROVED.** Any committed spend SEQUENCE preserves every
already-spent nullifier (membership is monotone along the whole fold). -/
theorem seq_preserves_spent {actor : CellId} {spendProof : Bool} :
    ∀ (nfs : List Nat) {s s' : RecChainedState} {nf' : Nat},
      noteSpendSeq s actor spendProof nfs = some s' → nf' ∈ s.kernel.nullifiers →
      nf' ∈ s'.kernel.nullifiers
  | [],         s, s', nf', h, hmem => by
      unfold noteSpendSeq at h; simp only [Option.some.injEq] at h; subst h; exact hmem
  | nf :: rest, s, s', nf', h, hmem => by
      unfold noteSpendSeq at h
      cases hstep : noteSpendChainA s nf actor spendProof with
      | none    => rw [hstep] at h; exact absurd h (by simp)
      | some s1 =>
        rw [hstep] at h
        exact seq_preserves_spent rest h (nullifier_set_monotone hstep hmem)

/-- **`seq_no_respend` — PROVED (the whole-turn anti-replay).** If a nullifier `nf'` is already
spent before a spend SEQUENCE, then no matter what the sequence does, `nf'` remains in the spent
set afterward — so a later spend of `nf'` is rejected. A multi-`NoteSpend` turn forest cannot
double-spend a previously-recorded note. -/
theorem seq_no_respend {actor actor' : CellId} {spendProof spendProof' : Bool} (nfs : List Nat)
    {s s' : RecChainedState} {nf' : Nat}
    (h : noteSpendSeq s actor spendProof nfs = some s') (hmem : nf' ∈ s.kernel.nullifiers) :
    noteSpendChainA s' nf' actor' spendProof' = none :=
  chainNoteSpend_no_double_spend s' nf' actor' spendProof' (seq_preserves_spent nfs h hmem)

/-! ## §2 — STEALTH FRESHNESS ⇒ UNLINKABILITY (EIP-5564 / Monero), crypto as NAMED hypotheses.

`Authorization.stealth oneTimePk ephemeralPk sig` (`FullForestAuth.lean:127`) carries the published
one-time pubkey, the ephemeral pubkey `R`, and the one-time signature; its portal arm is
`portalVerify (.stealth otp _ sig) = CryptoKernel.verify otp sig` — keyed on the one-time pubkey.

In the real scheme the one-time address is `P = H(r·V)·G + S`, a recipient-bound function of the
ephemeral pubkey. We name that derivation `deriveOneTime : Digest → Digest` (the §8 DH-to-one-time
*carrier*) and its injectivity as an EXPLICIT hypothesis — the obligation the curve/DH layer
discharges, never a Lean law. Everything below is then structurally provable. -/

variable {Digest Proof : Type} [AddCommGroup Digest]

omit [AddCommGroup Digest] in
/-- **`fresh_ephemeral_distinct_onetime` — PROVED (structural, carrier-hypothesized).** Given the
recipient-bound derivation `deriveOneTime` and its injectivity `hinj` (the §8 DH carrier — the
obligation that distinct ephemerals can't collude to one address), TWO DISTINCT FRESH ephemeral
pubkeys produce DISTINCT one-time addresses. This is the structural precondition of unlinkability:
two payments to one recipient land on different addresses (no trivial address-reuse linkage). The
crypto (that `deriveOneTime` is genuinely injective / hides the recipient) is the NAMED hypothesis,
NOT a `sorry`. -/
theorem fresh_ephemeral_distinct_onetime
    (deriveOneTime : Digest → Digest) (hinj : Function.Injective deriveOneTime)
    {ep ep' : Digest} (hfresh : ep ≠ ep') :
    deriveOneTime ep ≠ deriveOneTime ep' :=
  fun hcontra => hfresh (hinj hcontra)

/-- **`stealth_distinct_statements` — PROVED.** When two fresh ephemerals give distinct one-time
addresses `deriveOneTime ep ≠ deriveOneTime ep'`, the two `Authorization.stealth` credentials they
key are built over DISTINCT one-time pubkeys — so `portalVerify` (which is `CryptoKernel.verify`
keyed on the one-time pubkey) is asked about two DIFFERENT verification statements. An observer
cannot link the two spends by a shared verification target. (We state it as: the one-time-pubkey
fields differ, hence the two `stealth` credentials are not the same credential.) -/
theorem stealth_distinct_statements [CryptoKernel Digest Proof]
    (deriveOneTime : Digest → Digest) (hinj : Function.Injective deriveOneTime)
    {ep ep' : Digest} (hfresh : ep ≠ ep') (sig sig' : Proof) :
    (FullForestAuth.Authorization.stealth (deriveOneTime ep) ep sig)
      ≠ (FullForestAuth.Authorization.stealth (deriveOneTime ep') ep' sig') := by
  intro hcontra
  -- equal `stealth` constructors force equal one-time-pubkey fields, contradicting distinctness.
  have hotp : deriveOneTime ep = deriveOneTime ep' := by
    injection hcontra
  exact fresh_ephemeral_distinct_onetime deriveOneTime hinj hfresh hotp

/-- **`stealth_distinct_portal_keys` — PROVED.** The portal-verify of a `stealth` credential is
exactly `CryptoKernel.verify` on its one-time pubkey (definitional from `portalVerify`), so two
fresh-derived stealth credentials are verified against DIFFERENT keys. This pins the
"keyed on the one-time pubkey" claim to the actual portal reduction. -/
theorem stealth_distinct_portal_keys [CryptoKernel Digest Proof]
    (otp ep : Digest) (sig : Proof) :
    FullForestAuth.portalVerify (FullForestAuth.Authorization.stealth otp ep sig)
      = CryptoKernel.verify otp sig := rfl

/-! ### The signing-message binds the ephemeral pubkey (already proved, byte-level). -/

open Dregg2.Exec.SigningMessage in
/-- **`stealth_ephemeralPk_binds` — PROVED (delegates to `SigningMessage`).** The preimage the
one-time signature is computed over BINDS the ephemeral pubkey: a different `R` ⇒ a different
preimage, so a relay cannot swap the ephemeral key (and thus cannot redirect / link the payment by
forging a matching signature over a swapped `R`). Pure byte-list injectivity — no crypto. -/
theorem stealth_ephemeralPk_binds
    (ah fid ep ep' bs : Bytes32) (pos n : UInt64)
    (hlen : ep.length = ep'.length) (h : ep ≠ ep') :
    sigMsgStealth ah fid ep bs pos n ≠ sigMsgStealth ah fid ep' bs pos n :=
  sigMsgStealth_binds_ephemeralPk ah fid ep ep' bs pos n hlen h

/-! ### The information-theoretic unlinkability (observer view), via the graph-privacy kernel. -/

open Dregg2.Privacy in
/-- **`stealth_unlinkable_via_graphKernel` — PROVED (delegates to `Privacy.unlinkable`).** Given a
`GraphPrivacyKernel`, two one-time addresses derived for the SAME recipient have the SAME
observer-view — they are information-theoretically indistinguishable on the modelled public
transcript. This is the unlinkability the stealth-address tier promises: two payments to one
recipient cannot be told apart. The residual COMPUTATIONAL advantage bound on the real Poseidon2/DH
transcript is the §8 carrier (`Crypto.Primitives.unlinkable` / the kernel's law-field) — NOT
claimed here. -/
theorem stealth_unlinkable_via_graphKernel [GraphPrivacyKernel]
    (R : Recipient) (a a' : StealthAddr)
    (h : GraphPrivacyKernel.derivedFrom a R) (h' : GraphPrivacyKernel.derivedFrom a' R) :
    GraphPrivacyKernel.addrView a = GraphPrivacyKernel.addrView a' :=
  Dregg2.Privacy.unlinkable R a a' h h'

/-! ## §3 — `#guard` witnesses (non-vacuity; the discipline EVALUATES correctly). -/

-- (1) Nullifier discipline: a fresh spend (valid §8 proof) commits; a repeated spend on the SAME nf
-- fails-closed.
#guard ((noteSpendChainA ⟨res0, []⟩ 7 0 true).map (fun s => s.kernel.nullifiers)) == some [7]  -- some [7]
#guard (((noteSpendChainA ⟨res0, []⟩ 7 0 true).bind
          (fun s => noteSpendChainA s 7 0 true)).isSome) == false  -- false: replay rejected
-- NOTE-PROOF TEETH: a fresh spend with an INVALID §8 proof (false) is rejected fail-closed.
#guard ((noteSpendChainA ⟨res0, []⟩ 7 0 false).isSome) == false  -- false: missing/invalid proof rejected

-- A whole sequence of DISTINCT nfs (valid proof) commits (no rejection); the spent set accumulates all.
#guard ((noteSpendSeq ⟨res0, []⟩ 0 true [3, 5, 8]).map (fun s => s.kernel.nullifiers))
        == some [8, 5, 3]  -- some [8, 5, 3]
-- A sequence that REPEATS a nullifier fails-closed (the second `3` is a double-spend).
#guard ((noteSpendSeq ⟨res0, []⟩ 0 true [3, 5, 3]).isSome) == false  -- false: in-sequence replay rejected
-- A nullifier present BEFORE the sequence stays rejected if it reappears in it.
#guard ((noteSpendSeq ⟨{ res0 with nullifiers := [9] }, []⟩ 0 true [1, 9]).isSome) == false  -- false

-- (2) Stealth: over the `Reference` CryptoKernel, distinct one-time pubkeys ⇒ distinct verify keys.
-- `Reference.verify stmt proof := decide (stmt = proof)`; a credential keyed on otp=1 vs otp=2,
-- with a proof echoing only otp=1, verifies the first and rejects the second — distinct statements.
#guard (FullForestAuth.portalVerify
          (Digest := Crypto.Reference.D) (Proof := Crypto.Reference.P)
          (FullForestAuth.Authorization.stealth 1 100 1)) == true   -- echo matches otp=1
#guard (FullForestAuth.portalVerify
          (Digest := Crypto.Reference.D) (Proof := Crypto.Reference.P)
          (FullForestAuth.Authorization.stealth 2 100 1)) == false  -- echo (1) ≠ otp=2: rejected

/-! ## §4 — Axiom-hygiene tripwires. The keystones are kernel-clean
(axioms ⊆ {propext, Classical.choice, Quot.sound}). The residual §8 portals are:
  * the STARK spending-proof + nullifier-derivation soundness (effect layer) — the LEDGER-side
    anti-replay below is FULLY proved;
  * the DH `deriveOneTime` injectivity (a NAMED hypothesis on the stealth theorems, NOT an axiom);
  * the COMPUTATIONAL unlinkability advantage bound (`Crypto.Primitives.unlinkable` /
    `GraphPrivacyKernel` law-field) — the information-theoretic core is what's proved here.
None of these are axioms these pins would catch. -/

#assert_axioms kernel_no_double_spend
#assert_axioms chainNoteSpend_no_double_spend
#assert_axioms chainNoteSpend_inserts
#assert_axioms chainNoteSpend_then_reject
#assert_axioms nullifier_set_monotone
#assert_axioms nullifier_persists
#assert_axioms seq_preserves_spent
#assert_axioms seq_no_respend
#assert_axioms fresh_ephemeral_distinct_onetime
#assert_axioms stealth_distinct_statements
#assert_axioms stealth_distinct_portal_keys
#assert_axioms stealth_ephemeralPk_binds
#assert_axioms stealth_unlinkable_via_graphKernel

end Dregg2.Exec.PrivacyTheorems
