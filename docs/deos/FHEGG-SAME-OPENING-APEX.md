# fhEgg theory — the same-opening apex, as a Lean relation family

*Written 2026-07-24. Codex named ONE thing as the cryptographic apex it could not close
(`HANDOFF-FHEGG-CODEX-SWARM-RESULTS.md` §53): "BFV-to-private-root same-opening and no-single-viewer witness
generation are still the cryptographic apex, not an implied property of the composition." This doc is the
theory of what closes it — six kernel-clean Lean files under `metatheory/Market/`, every keystone verified by
`lake env lean` (exit 0, `#assert_all_clean`, zero `sorry`). It is the Tier-0 half of `THE-DARK-BAZAAR.md`'s
"the dealer cannot see the cards." Maps onto `FHEGG-MATURITY-ROADMAP.md` §3.1 (shared-witness) and §3.3
(no-single-viewer / distributed proving).*

---

## 0. The gap, precisely

The Dark Bazaar receipt binds two objects **independently**: a `HidingFri` proof about a private book `w`,
and a BFV ciphertext digest. Nothing in that composition proves the ciphertext *encrypts the same `w`* the
proof is about. Tier-1 (built): a trace-builder who SEES `w` proves the clearing over it. Tier-0 (the apex):
the book only ever exists as ciphertext, proven blind. The missing link is **same-opening**: ciphertext and
root must open to the *same* `w`. Without it, an adversary encrypts `w'` while committing a proof about `w`.

## 1. The relation family (what is proved)

| file | keystones | the theorem it carries |
|---|---|---|
| `DarkBazaarSameOpening.lean` | 3 | `SameOpening`: the ciphertext opens to `packedBook w` (real `Bfv.Ct`) AND the root commits the same `w` (real `orderRoot`). `sameOpening_noise_safe` gives it teeth (forces exact decrypt to the committed book). **RED `independent_valid_objects_break_same_opening`** — two independently-valid objects (a ciphertext of `w'`, a root of `w`) violate it: the gap is a *theorem*, made non-vacuous by `delta_diff_unsafe` (a nonzero book difference blows the decrypt margin under the standard `q ≤ 2·t·Δ`). |
| `DarkBazaarDecryptConsistency.lean` | 9 | `decryptConsistent_unique`: a phase under the noise bound UNIQUELY determines the message — a ciphertext cannot open to two books (what makes `SameOpening` well-defined). Failing-side: unbounded noise breaks uniqueness. |
| `DarkBazaarSameOpeningPoly.lean` | 8 | Lifts `SameOpening` to the real per-slot polynomial ciphertext (4 orders = 4 encrypted slots), projecting to the proved scalar relation per slot. `wrong_slot_breaks_sameOpeningPoly` — a wrong slot breaks it. |
| `DarkBazaarSameOpeningGadget.lean` | 11 | **The construction, as a Lean relation (per the AIR-in-Lean rule, never Rust).** `GadgetAccepts` conjoins, over one shared `w`, the decryption-consistency constraint and the Poseidon2 root constraint. FAITHFUL: `gadgetAccepts_sound` (⟹ `SameOpening`) AND `gadget_complete` (converse), so `GadgetAccepts ⟺ SameOpening` — the circuit relation neither over- nor under-constrains the property. Failing-side: a split-book witness is rejected. |
| `DarkBazaarSameOpeningGadgetPoly.lean` | 17 | `gadgetAcceptsPoly_master`: consolidates the above into ONE soundness theorem — `GadgetAcceptsPoly ⟹ SameOpeningPoly` over the real per-slot polynomial ciphertext. `split_slot_fails_gadgetPoly` bites per slot. |
| `DarkBazaarCollectiveOpening.lean` | 17 | **The no-single-viewer piece (§3.3).** `CollectiveOpensTo` models the collective decrypt as the sum of `n` party shares (`s = Σ sᵢ`, never assembled). SOUNDNESS proved: `collective_decrypt_unique` / `collective_book_unique` (collective decrypt is as sound as single-key). HIDING handled honestly: the `(n−1)`-coalition secrecy is discharged by INSTANTIATING the proved `Bfv.Smudging.deployed_smudge_hides`; the below-bound leak references `deployed_smudge_floor_leaks`. Referenced, not re-proved; statistical-security boundary named per Smudging's scope note. |
| `EmitSameOpeningGadget.lean` | 14 | **The EMITTED descriptor (§3.1 constructive residual, first cut).** Emits `GadgetAccepts` as a real `EffectVmDescriptor2` (`sameOpeningGadgetDescriptor`), with `sameOpeningGadget_emit_sound` and `sameOpeningGadget_emit_discharges_apex` — the emitted descriptor discharges the apex. Anti-forgery: a single-column dec gate would be mod-p wrap-forgeable, so it emits an exact base-2¹² limb system. Lean-authored AIR per the ember rule, no Rust. |
| `DarkBazaarQuorumNecessity.lean` | 3 | **The n-of-n SOUNDNESS dual of the hiding.** `dropped_share_breaks_opening` / `collective_missing_share_breaks` — any `n−1` coalition cannot DECRYPT (a party's real share is necessary), with `trivial_share_drop_still_opens` the sharp failing-side. So n-of-n is two-sided: all `n` needed to open, any `n−1` learn nothing. |
| `DarkBazaarCollectiveOpeningPoly.lean` | 19 | **The RNS-polynomial collective lift.** `CollectiveOpensToPoly` + `collective_poly_decrypt_unique` — the collective decrypt lifted to the real per-slot polynomial ciphertext, `wrong_slot_breaks_collectivePoly` the per-slot failing-side. Ties no-single-viewer to `SameOpeningPoly`. |

## 2. What the family establishes, in one sentence

**The property the whole Dark Bazaar rests on — "the dealer cannot see the cards" — is now a Lean relation
family (9 files) that is sound, complete, consolidated over the real polynomial ciphertext, EMITTED as a real
descriptor that discharges it, and TWO-SIDED no-single-viewer (all `n` needed to open AND any `n−1` learn
nothing); and the composition's *failure* to imply it without the gadget is itself a proved RED.** It went
from prose → gap-theorem → faithful construction → emitted descriptor → two-sided collective/house-blind
relation, all kernel-clean, every level with a biting failing-side.

## 3. The honest residuals (the constructive apex, NAMED not faked)

These are the closure work; the relation family above is exactly what they must implement:

1. **Emit `GadgetAcceptsPoly` as a real byte-pinned descriptor** — the Lean→circuit emit path (like the
   existing Cert-F / private-descriptor emitters). Touches `circuit-prove`. (§3.1, "exact typed relation
   identity".)
2. **The RNS-polynomial lift of the decryption columns over collective shares** — the current model is the
   scalar `Bfv` phase; the deployed ciphertext is RNS-polynomial. The relation is stated; the wide emitted
   form is the build.
3. **Malicious-share validity + distributed witness production** (§3.2/§3.3) — no single prover reconstructs
   the book; corrupt partial folds refused/attributed. `CollectiveOpening` states the honest-share soundness
   and hiding; the malicious and distributed-proving protocol is the remaining frontier.

## 4. Why this is the right shape

An emitted circuit is only trustworthy if the relation it enforces *exactly* captures the intended property.
The gadget is proved FAITHFUL (`⟺`), so the eventual descriptor neither admits a wrong-book witness
(soundness) nor rejects an honest one (completeness). Every level carries a biting failing-side, so none of
it is vacuous. And the hiding is tied to the *already-proved* smudging bound rather than re-asserted — the
two dragons' work composes: codex proved `Smudging.lean`; this family instantiates it at the collective
opening. That is the discipline: name the exact gap, prove the relation that closes it, connect to what is
already proved, and never fake the construction.
