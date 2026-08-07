/-
# CanonicalCodecHealthWire — the derived codec standing in for a shipped hand-written one.

`NightWatchCampaignWire.HealthViewWire` is the smallest live all-derivable wire type in
Path-of-Angels: four `Nat`s (`NightWatchCampaignWire.lean:280`), encoder hand-written at
`:364` (`healthViewJson`). It is the demonstration type because its fields are ALL
derivable — most other small candidates carry a `Digest32`, and there is no proved
`parseBytes32Hex? (bytes32Hex d) = some d` in this tree, so `CanonicalCodec` refuses those
on purpose (see the falsifier).

⚑ 2026-08-07 — THE DEMONSTRATION MOVED, AND ONTO SHIPPED CONTENT. This module derived over
`NightWatchLoopWire.DayWire` until the whole `NightWatchLoop` cone (5 modules, 4,717 lines)
was deleted as unreachable-by-construction dead content — a second Path-of-Angels state
machine sharing no type, no relation and no theorem with the shipped night watch, whose
`Policy` had no public producer. `HealthViewWire` is a strictly better host for the same
demonstration: it is rendered by `stateViewJson` on every player-visible state view of the
game that IS connected to a player, so "the derived encoder is a drop-in for a shipped one"
is now a claim about content someone can actually reach.

## What is shown

* `HealthViewWire.renderCanon` — DERIVED — emits the SAME BYTES as the shipped
  `healthViewJson`, for every value, proved (`renderCanon_eq_healthViewJson`), not sampled.
  That is the replacement criterion: the derived encoder is a drop-in whose drift is a build
  failure.
* `HealthViewWire.readRow_toRow` — DERIVED — is the acceptance direction: the strict reader
  accepts the writer's output for EVERY well-formed value. **No PoA module proves this
  today.** The 33 shipped `_reencodes` theorems prove canonicality (accepted bytes are
  canonical), which the falsifier shows a decoder accepting nothing also satisfies.
* `shipped_health_rows_roundtrip` — the byte-layer roundtrip on the ACTUAL rows the shipped
  state view emits for a judged state, not on an invented value.

## ⚠ A ROW CODEC IS NOT A STATE DECODER — do not read one as the other

`NightWatchCampaignWire.no_state_view_decoder_can_be_sound` proves that NO function
`StateViewWire → NightWatchCampaign.State` can be a right inverse of `StateViewWire.ofState`:
the view erases the consumed-nullifier ledger, so two distinct states share a view. Nothing
here contradicts or weakens that, and nothing here is a step toward one. The derived
`readRow` reconstructs a `HealthViewWire` RECORD from its own canonical row — a wire-level
identity about four `Nat`s. The semantic direction stays impossible, by that theorem.

## What is NOT done here — three things, all stated

1. **The encoder swap is not applied in `NightWatchCampaignWire.lean`.** The landing patch is
   three lines there: `import Dregg2.Games.PathOfAngels.CanonicalCodec`, then
   `deriving instance Dregg2.Canonical.Canonical for HealthViewWire` after the structure, then
   `def healthViewJson (row : HealthViewWire) : String := HealthViewWire.renderCanon row`.
   `renderCanon_eq_healthViewJson` is what makes the swap a no-op on the bytes; it is the
   reason the patch is three lines and not a review. It is left unapplied because the whole
   shipped judge cone is downstream of that file and a red there is a red for every lane
   sharing the tree.
2. **No hand-written reader is replaced, because none exists.** `HealthViewWire` is
   render-only on the shipped path — deliberately, per the theorem above. So the derived
   reader is not measured against a hand-written one here; it is measured against the bytes.
3. **The byte-layer roundtrip is not proved for a general value** (see the section below); it
   is `native_decide`d at four shipped points and one field-distinct point, and labelled as
   points.
-/
import Dregg2.Games.PathOfAngels.CanonicalCodec
import Dregg2.Games.PathOfAngels.NightWatchCampaignWire

/-! ## Derivation

Both the derivation and the `canonWf` witness sit at the ROOT namespace on purpose: the
handler places its declarations beside the structure
(`…NightWatchCampaignWire.HealthViewWire.toRow`, `…readRow`, `…readRow_toRow`), and
`#assert_codec_nonvacuous` looks the witness up at `<type>.canonWf_witness`. Declaring the
witness inside a local namespace would put it somewhere the gate cannot see, and the gate
would refuse — correctly. -/

deriving instance Dregg2.Canonical.Canonical for
  Dregg2.Games.PathOfAngels.NightWatchCampaignWire.HealthViewWire

/-- The satisfiability witness for `readRow_toRow`'s hypothesis. A conditional roundtrip
whose condition no value satisfies is vacuous in a second, quieter way than an unsatisfiable
premise, so `#assert_codec_nonvacuous` refuses without this. The value is a shipped one: seat
1 of the crew the fixture activation seats, as `stateViewJson` renders it. -/
theorem Dregg2.Games.PathOfAngels.NightWatchCampaignWire.HealthViewWire.canonWf_witness :
    Dregg2.Games.PathOfAngels.NightWatchCampaignWire.HealthViewWire.canonWf ⟨1, 0, 0, 0⟩
      = true := by
  decide

/-! ⚑ Why `#assert_axioms` on a DERIVED theorem is not ceremony.

A derived proof is generated by a tactic macro, and a tactic macro is the one place a
generated theorem could go hollow: if `canonical_roundtrip` ever half-succeeds, Lean's
recovery fills the remainder with `sorryAx` and the declaration still enters the environment
with the advertised STATEMENT. A solver reading the emitted table cannot tell the difference —
an unproved lemma emits the same table as a proved one. So every derived theorem is pinned,
and the pin is what makes "uniform coverage" mean something rather than look like something. -/

#assert_axioms Dregg2.Games.PathOfAngels.NightWatchCampaignWire.HealthViewWire.canonWf_witness
#assert_axioms Dregg2.Games.PathOfAngels.NightWatchCampaignWire.HealthViewWire.readRow_toRow
#assert_codec_nonvacuous Dregg2.Games.PathOfAngels.NightWatchCampaignWire.HealthViewWire

namespace Dregg2.Games.PathOfAngels.CanonicalCodecHealthWire

open Dregg2.Games.PathOfAngels.NightWatchCampaignWire

set_option autoImplicit false

/-! ## Byte identity with the shipped encoder

Proved for all values, by `rfl`. It reduces because the derived renderer is built LEFT-nested,
which is how `++` (an `infixl:65`) already associates in every hand-written PoA encoder — so the
two sides differ only by `fieldRender` versus `toString`, which is delta/projection reduction
through the `HasFieldCodec Nat` instance and needs no string-append reasoning at all.

⚠ The handler emitted a RIGHT-nested render until 2026-08-05, under a comment claiming that was
what `++` does. It is not, `String.append` is not definitionally associative over variable
fields, and this `rfl` was the thing that went red. -/
theorem renderCanon_eq_healthViewJson (row : HealthViewWire) :
    HealthViewWire.renderCanon row = healthViewJson row := by
  cases row
  rfl

#assert_axioms renderCanon_eq_healthViewJson

/-- The derived key list is the shipped key list, in the shipped order. Pinned against the
literal spelling rather than against the derived definition — a constant checked against its
own definition is decoration; two independent sources are a gate. Note `recovery_observed`:
the one field whose wire spelling is a `camelToSnake` of the Lean name rather than the name
itself, so this also pins that translation against the shipped bytes. -/
theorem canonKeys_are_the_wire_keys :
    HealthViewWire.canonKeys = ["seat", "wounds", "strain", "recovery_observed"] := by
  rfl

#assert_axioms canonKeys_are_the_wire_keys

/-! ## The byte layer, for finitely many points

The derived `readRow_toRow` stops at the row layer. Crossing to bytes needs
`Dregg2.Canonical.RowAdapterFaithful` (the `Std.TreeMap.Raw` leg) and
`Dregg2.Canonical.ParserAdequate` (Lean's own JSON parser), neither of which is proved for a
general value anywhere in this repository. These run the ACTUAL path — render, then
`Lean.Json.parse`, then the adapter, then the derived reader, then the canonicality
comparison — for concrete values, by compiled evaluation, and say so with `#assert_compiled`
rather than hiding the compiler trust in a `#guard`. Finitely many points are finitely many
points; that is not the general fact and is not labelled as one. -/

/-- A row with a DISTINCT value in every field. The shipped rows below are the real content,
but a fresh crew is all zeros, and a byte theorem over an all-zero record cannot see a field
transposition — every permutation of it renders the same bytes. This one exists so
`healthFixture_bytes` pins field ORDER as well as spelling. -/
def healthFixture : HealthViewWire := ⟨2, 1, 3, 5⟩

theorem healthFixture_bytes :
    HealthViewWire.renderCanon healthFixture
      = "{\"seat\":2,\"wounds\":1,\"strain\":3,\"recovery_observed\":5}" := by
  native_decide

#assert_compiled healthFixture_bytes

theorem healthFixture_decodes :
    Dregg2.Canonical.canonicalDecode HealthViewWire.canonKeys HealthViewWire.readRow
      HealthViewWire.renderCanon 1024 (HealthViewWire.renderCanon healthFixture)
      = some healthFixture := by
  native_decide

#assert_compiled healthFixture_decodes

/-- ⚑ THE ROUNDTRIP ON SHIPPED CONTENT. Every health row the shipped state view actually
emits for a judged state survives render → parse → adapt → read → canonicality-compare and
comes back equal. `fixtureStateA` is the state `NightWatchCampaign.judge` reaches from the
fixture activation, so these are the bytes a player-facing view would carry, not an invented
value chosen to pass. -/
theorem shipped_health_rows_roundtrip :
    ((StateViewWire.ofState fixtureStateA).health.all fun row =>
      decide (Dregg2.Canonical.canonicalDecode HealthViewWire.canonKeys HealthViewWire.readRow
        HealthViewWire.renderCanon 1024 (HealthViewWire.renderCanon row) = some row))
      = true := by
  native_decide

#assert_compiled shipped_health_rows_roundtrip

/-- The shipped view really does emit rows here — without this, the `List.all` above is
vacuously `true` over an empty list, which is the same anti-vacuity failure
`#assert_codec_nonvacuous` exists to catch one layer down. -/
theorem shipped_health_rows_are_nonempty :
    (StateViewWire.ofState fixtureStateA).health.length = 4 := by
  native_decide

#assert_compiled shipped_health_rows_are_nonempty

/-- The strictness the derived reader adds over `exactKeys`: a row whose keys are the right
SET in the wrong ORDER is refused by the reader itself, not merely by the re-encode
comparison downstream. -/
theorem readRow_refuses_transposed_keys :
    (HealthViewWire.readRow [("wounds", Dregg2.Canonical.natToJson 1),
                             ("seat", Dregg2.Canonical.natToJson 2),
                             ("strain", Dregg2.Canonical.natToJson 3),
                             ("recovery_observed", Dregg2.Canonical.natToJson 5)]).isOk
      = false := by
  native_decide

#assert_compiled readRow_refuses_transposed_keys

/-- The wire bound is really enforced: one over `WIRE_U64_MAX` is refused by the reader. -/
theorem readRow_refuses_oversize_field :
    (HealthViewWire.readRow [("seat", Dregg2.Canonical.natToJson (2 ^ 64)),
                             ("wounds", Dregg2.Canonical.natToJson 1),
                             ("strain", Dregg2.Canonical.natToJson 3),
                             ("recovery_observed", Dregg2.Canonical.natToJson 5)]).isOk
      = false := by
  native_decide

#assert_compiled readRow_refuses_oversize_field

/-- The derived bound agrees with the bound the shipped night watch's `objectNat` defaults to
(`NightWatchCampaignAdmission.objectNat`, which `NightWatchCampaignWire`'s parsers call). Two
independent constants, one comparison — if either moves, this reds. -/
theorem wire_bound_agrees :
    Dregg2.Canonical.WIRE_U64_MAX
      = Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission.WIRE_U64_MAX := by
  rfl

#assert_axioms wire_bound_agrees

end Dregg2.Games.PathOfAngels.CanonicalCodecHealthWire
