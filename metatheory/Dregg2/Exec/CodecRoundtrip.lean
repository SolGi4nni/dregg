/-
# Dregg2.Exec.CodecRoundtrip — parse∘encode roundtrip theorems for the wire codec.

For each grammar production this file proves:

    parseX (sufficient fuel) (encodeX v).toList = some (v, [])

The parser, fed exactly the encoder's output, recovers `v` and consumes the whole string (no
trailing bytes), with no fuel exhaustion. A symmetric codec bug passes a differential silently;
only these theorems, pinning the decoder as the genuine left-inverse of the encoder, catch it.

## Honest receipt — PROVED vs DEFERRED.

**PROVED:**
  * §0 — every leaf: `lit`, `parseInt`/`parseNat`, `parseStr` (escape-free), `ofHex32 ∘ toHex32`
    (lossless on the full 256-bit range), `parseFlag`, the `Auth` tag, dispatch fail-closure lemmas;
  * §1–§3 — `Value`/`FIELDS` scalar leaf, per-asset `BAL` ledger entry, headline `fillJ_*` facts;
  * §5–§6 — recursive `Value`/`FIELDS` tree and the security-critical `Authorization` decoder
    (all 10 variants + recursive `oneOf`, by strong induction on fuel);
  * §7 — the `FullActionA` decoder, complete at all 46 arms;
  * §8–§11c — every wide-state side-table list (AUTHS, Nat-list, BAL-list, per-cell-Nat list
    [lifecycle/deathCert, §10b], ESCROWS, QUEUES, SWISS);
  * §11d — the per-node `CAVEATS` array (`parseCaveatsW`, the soundness-fix discharge leg, `tier ≤ 3`);
  * §12–§13 — the wide `CELLS` store (recursive `Value` payload) and the `CAPS` table (3-arm cap sum);
  * §15 — the RECURSIVE action-TREE (`parseForestW`/`parseChildrenW`: the call-forest + delegation
    edges, by strong induction on fuel — credential §6, caveats §11d, action §7, sub-trees recursive);
  * §14 — the WIDE STATE record (`parseWState`, the 11-field state decoder = the differential's core);
  * §16 — the complete-turn ENVELOPE + WHOLE wire (`parseWTurn`/`parseWWire`, whole-input-consumed).
    The wire codec is now FULLY out of the Lean-side TCB.

**DEFERRED (the one remaining grammar gap — `#eval`-cross-validated at the codec site, no proof yet):**
a NON-empty nested `exerciseA` inner-effect array. The codec boundary `WfActionW .exerciseA` pins
`inner = []` (the bare cap-exercise, proven by `parseActionW_exercise_nil`); a non-empty `;`-joined
inner array needs a fuel-threaded mutual `parseActionsWFuel`-inverts-`encodeActionsW` lemma (issue
`#136`). The de-shadowed EXECUTOR already runs ANY inner list (proven in `TurnExecutorFull`); only the
codec roundtrip THEOREM for the recursive inner grammar is outstanding. Everything else round-trips.

Every digest/commitment field is the low 256 bits of a `Nat`. Proved roundtrips are the identity on
the well-formed value space (`< 2^256`). NON-VACUOUS: the `Wf` hypothesis is satisfiable (demo values
witness it) and the theorem fails without the digest bound (a `2^256`-wrap value is a genuine
counterexample) — real teeth, not a triviality.

Soundness note: no new axioms; keystones are `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}` (a `sorryAx` would fail the pin and the build).
-/
import Dregg2.Exec.CodecRoundtrip.Leaves
import Dregg2.Exec.CodecRoundtrip.Value
import Dregg2.Exec.CodecRoundtrip.Auth
import Dregg2.Exec.CodecRoundtrip.SideTables
import Dregg2.Exec.CodecRoundtrip.Action
import Dregg2.Exec.CodecRoundtrip.Forest
import Dregg2.Exec.CodecRoundtrip.Wire

namespace Dregg2.Exec.CodecRoundtrip

/-! ## §4 — axiom hygiene (the FILL-J no-`sorryAx` pins).

Every keystone is `#assert_axioms`-pinned to the standard kernel triple `{propext, Classical.choice,
Quot.sound}`. -/

#assert_axioms ofHex32_toHex32
#assert_axioms parseDig_encDig
#assert_axioms parseInt_toString
#assert_axioms parseNat_toString
#assert_axioms parseStr_clean
#assert_axioms parseValueW_scalar
#assert_axioms parseBalEntry_encode
#assert_axioms fillJ_digest
#assert_axioms fillJ_amount
#assert_axioms fillJ_value_scalar
#assert_axioms fillJ_bal_entry
#assert_axioms litGo_none_mono
#assert_axioms parseValueW_roundtrip
#assert_axioms parseFieldsW_roundtrip
#assert_axioms parseAuthW_flat
#assert_axioms parseAuthW_roundtrip
#assert_axioms parseAuthListW_roundtrip
#assert_axioms parseActionW_roundtrip
#assert_axioms parseActionW_setfield
#assert_axioms parseNatsW_encode
#assert_axioms parseAuths_encode
#assert_axioms parseNats_encode
#assert_axioms parseBal_encode
#assert_axioms parseCellNats_encode
#assert_axioms parseEscrow_encode
#assert_axioms parseEscrows_encode
#assert_axioms parseQueue_encode
#assert_axioms parseQueues_encode
#assert_axioms parseOptNat_encode
#assert_axioms parseSwiss_encode
#assert_axioms parseSwissTable_encode
#assert_axioms parseCellW_encode
#assert_axioms parseCellsW_encode
#assert_axioms parseCap_encode
#assert_axioms parseCapList_encode
#assert_axioms parseCapEntry_encode
#assert_axioms parseCapsEntries_encode
#assert_axioms parseWState_encode
#assert_axioms parseCaveatW_encode
#assert_axioms parseCaveatsW_encode
#assert_axioms parseActionW_any
#assert_axioms parseForestW_roundtrip
#assert_axioms parseChildrenW_roundtrip
#assert_axioms forestSize_le_encode
#assert_axioms parseWTurn_encode
#assert_axioms parseWWire_encode

end Dregg2.Exec.CodecRoundtrip
