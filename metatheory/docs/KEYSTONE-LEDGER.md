# Keystone ledger — the AssuranceCase apex, honestly classified — CAMPAIGN CLOSED

**CAMPAIGN CLOSED: every apex pin is accounted-for.** The 110 `#assert_axioms` pins in
`Dregg2/AssuranceCase.lean` are an axiom-hygiene ledger, NOT 110 units of debt. Each is in exactly one
of six shapes; the final sweep classifies the ENTIRE pin-set with no overlooked or mis-classified
keystone, and the breakdown SUMS to the full 110. The last reducible straggler
(`revocation_needs_consensus`) is WELDED, and the three items once named TERMINAL are RE-EXAMINED and
WELDED too (their CR carrier is realizable). The only items that are not `@[load_bearing_keystone]`
audited are the ones whose own proof IS their audit (the impossibility shape) or that the linter already
consumes as a companion (teeth/satisfiable), or are proven conjunctions over already-audited legs.

The discipline: `@[load_bearing_keystone satisfiable:=W teeth:=T]` + `#keystone_audit`
(`Dregg2/Verify/KeystoneLint.lean`) — an apex theorem is audited iff it carries a GENUINE
non-vacuity witness (conclusion exercised on a concrete instance, not vacuous) + discriminating
teeth (a hostile instance refuted) + axiom-cleanliness.

## The FINAL classification (headline — sums to the full pin-set)

The 110 pins = 99 keystone pins (`Dregg2.*`) ∪ 11 local apex-guarantee pins (the five guarantees'
aggregations + their conjunction re-pins + `running_entry_sound` + `deployed_system_secure`).

| class | count | meaning |
|---|---|---|
| **AUDITED** (`@[load_bearing_keystone]` PASS) | **86** | NonAmp · AuthModes · Integrity · Freshness (now incl. `revocation_needs_consensus`) · Unfoolability · Supply · Conservation · Transport · Runnable Wave-4 · the 3 ex-TERMINAL adapters |
| **TEETH / SAT companion** (linter consumes) | **9** | hostile-instance refutations + non-vacuity witnesses that ARE the `teeth :=` / `satisfiable :=` of an audited keystone (auditing them again would be circular) |
| **CALIBRATION** (superseded / support sibling) | **2** | `root_tooth_pins_state` (weaker commitment-only sibling, superseded by the AUDITED `root_tooth_pins_kernel`) · `SimAccepts` (UC-reduction support lemma; the audited apex is `unfoolable_iff_not_foolable`) |
| **CLOSED-apex conjunction** | **1** | `introduce_grounded_and_non_amplifying` = `introduce_authorized ∧ introduce_non_amplifying`, BOTH legs audited individually |
| **IMPOSSIBILITY / NON-PATTERN** | **1** | `dead_undecidable` (`¬∃ decider`) — audited BY its own proof; a `satisfiable` would contradict it |
| **LOCAL apex-guarantee pins** (proven conjunctions) | **11** | the five `*_guarantee` aggregations + `integrity_guarantee_{memory_program,whole_turn,whole_turn_covered}` + `running_entry_sound` + `deployed_system_secure` — each a conjunction over the AUDITED keystones above, kernel-triple clean |
| **TOTAL** | **110** | every pin in a class; 86 + 9 + 2 + 1 + 1 + 11 = 110 ✓ |

**Nothing is left "to audit."** The floor portals proper (`StarkSound`, `Poseidon2SpongeCR`, the
`S_live` CR set, `logHashInjective`, `WitnessDecodes`, ed25519/HMAC/AEAD, `PostGSTProgress`) enter as
Prop-portals / typeclasses and are correctly NOT pins.

## `revocation_needs_consensus` — RESOLVED (WELDED, not parked)

`Liveness.revocation_needs_consensus` (AC:598) is a genuine forward implication
`CrossVatSound parties d view → (∀ v, view v d → d.agreeing v) → Consensus parties d`, whose conclusion
`Consensus parties d` is a two-valued predicate — so the keystone-audit checks bite (it is NOT a `¬∃`
impossibility). It is WELDED with genuine companions in `Dregg2/Liveness.lean`, tagged + audited PASS in
`Dregg2/Verify/KeystoneAuditFreshness.lean` (the revocation-at-finality leg of guarantee D):

  * **satisfiable** (`revocation_needs_consensus_satisfiable`) — a CONCRETE two-vat agreeing revocation
    (`parties = [1,2]`, `d.agreeing := True`, `view := True`): the hypotheses hold AND the conclusion
    `Consensus [1,2] d` FIRES (revocation-under-agreement takes effect). Not vacuous.
  * **teeth** (`revocation_needs_consensus_teeth`) — a UNILATERAL revocation where party `2` did NOT
    agree (`d.agreeing v := v = 1`): `Consensus [1,2] d` is FALSE (`2 ∈ parties` but `¬ agreeing 2`). The
    contrapositive content — "revocation REQUIRES consensus" — made concrete: drop one party's agreement
    and the conclusion collapses. So `Consensus` is two-valued, not `:= True`.

This is welding genuinely (a necessity dressed as a forward implication whose conclusion discriminates),
NOT a `True`-ish stub. `#keystone_audit … revocation_needs_consensus_KS` ⇒ OVERALL PASS, axiom-clean.

## The 3 ex-TERMINAL adapters — RE-EXAMINED + WELDED (none left terminal)

The Wave-4 finding (`Poseidon2SpongeCR` is REALIZABLE by the proven-injective `FloorsNonVacuous.encodeSponge`
/ `encodeSponge_cr`) GENERALIZES to the three items the prior ledger named TERMINAL-CRYPTO-FLOOR. Each
carries its CR hypothesis as a `hash`-PARAMETER (never an `axiom`), so each welds by supplying the
realizable carrier + an honest concrete instance:

  * `Argus.Receipt.published_position_pins_value` (AC:526) — WELDED in
    `Dregg2/Verify/KeystoneAuditArgusReceipt.lean`: `hash := encodeSponge` (`hash₀_cr`), the concrete
    published index `Lpub` opens at position 1, conclusion `r' = r` exercised; teeth `¬ Opens Lpub 1 999`.
  * `UniversalBridge.cap_leaf_value_codec` (AC:534) — WELDED in
    `Dregg2/Verify/KeystoneAuditTerminalAdapters.lean`: equal cap tuples ⇒ equal generic leaves over
    `encodeSponge` (conclusion exercised); teeth via `cap_leaf_flat_injective` (distinct tuples ⇒ distinct
    leaves).
  * `UniversalBridge.index_boundary_mroot_derived` (AC:535) — WELDED in the same module: a PURE list-
    canonicity adapter (the proof uses NO collision-resistance; `hash` is threaded but never CR-used). A
    concrete log `[7,8]` with `finIdx` carrying its rows fires the conclusion; teeth = a dropping reader
    reconstructs a shorter list.

Verdict: **all three are realizable-and-welded; NONE is genuinely terminal.** The deployed-hash CR
remains the trust boundary (the `Poseidon2SpongeCR` Prop-portal), but that enters as a typeclass/hypothesis,
not as one of these pins.

## IMPOSSIBILITY / NON-PATTERN (audited by their proof)

- `Liveness.dead_undecidable` (AC:604) — a halting-reduction `¬∃ decider`; a `satisfiable` would
  CONTRADICT it. Audited by its own proof; operationally resolved via `Lease`/`leaseExpired`. This is the
  one genuine impossibility-shape pin; it is RESOLVED, not parked.

## Where each audit lives (the CI gates)

`Dregg2/Verify/KeystoneAudit{NonAmp,AuthModes,Integrity,Freshness,Unfoolability,Supply,Conservation,
Transport,Runnable,SystemRoots,ArgusReceipt,TerminalAdapters}.lean` — each `#keystone_audit` /
`#keystone_audit_tagged` THROWS on any FAIL, so the audited corpus is a live CI net. `Dregg2.Claims` is
the corpus-wide `#assert_axioms` pin-net (kernel-triple cleanliness). All GREEN, all axiom-clean.

Status: **86 AUDITED · 9 teeth/sat-companion · 2 calibration · 1 closed-conjunction · 1 impossibility ·
11 local apex = 110 pins, every one accounted-for. CAMPAIGN CLOSED.**
