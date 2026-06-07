# Vacuity Sweep — load-bearing-vacuity audit of `metatheory/Dregg2`

Read-only honesty audit. Method: read bodies (not grep counts), trace each `:= True` /
`:= Unit` / `fun _ => True` / `rfl`-equality to whether anything load-bearing (a `*_sound`,
`*_conserves`, `*_forever`/PRODUCTION-CROWN, gate, or `#assert_axioms`'d theorem) depends on
it. Distinguished honest named-crypto hypotheses (OK) from secretly-trivial guarantees (flagged).

## FATAL count: **0**

No soundness / conservation / authority guarantee was found to be *secretly* trivial. The v2
circuit⟺spec crown (`effect2_circuit_full_sound` and its 51 instances), the conservation
keystones, the CaveatChain HMAC reduction, and the crypto floor are all honest: their `:= True`
carriers are either (a) named, refutable cryptographic hypotheses consumed as `→`-antecedents
(OK per the crypto note), (b) explicitly-factored §8 seams stated as `∧`-antecedents, or (c)
emission/demo-only carriers whose bytes are *proved equal* to the sound instance's.

What the sweep *did* find is one **MID** structural-weakness (a named "binding" invariant whose
tag argument is decorative — the real binding predicate is orphaned), the **WART** Ring
seed ember already named, and a handful of decorative-totality notes.

## Severity-sorted table

| # | Severity | Location | Claim advertised | Why weaker than advertised | Load-bearing? |
|---|----------|----------|------------------|----------------------------|---------------|
| 1 | **MID** | `Apps/CompartmentWorkflowMandate.lean:260`, `Apps/StorageGatewayMandate.lean:916` | `cwmInCompartment k comp` / `sgmInBucket k bucket` — "the mandate is bound to compartment `comp` / bucket `bucket`" | Body ignores the `comp`/`bucket` argument entirely: `mandateCell ∈ accounts ∧ programOK k`, identical for *every* tag. The real binding (`cwmInCompartmentStrong := cwmAnchor k = comp`, `sgmInBucketStrong := sgmAnchorIs k bucket`) is **orphaned**. | YES — both appear in the COMPOSED PRODUCTION CROWN `agent_mandate_safety_forever` (`Verify/AppComposition.lean:42,46,53`) |
| 2 | **WART** | `Intent/Ring.lean:196-204,233` | `RingBalanced.perAsset : sentOf r a = recvOf r a` — "per-asset, Σ sent = Σ received (no free mint)" | `sentOf` and `recvOf` are **byte-identical** folds, so `perAsset_of_paired` is `rfl`. The conjunct holds for *every* ring, including non-conserving ones. | Decorative — `RingBalanced`'s teeth (`recvImpSend`/`sendImpRecv` cycle-closure) carry the real rejection; the conservation *theorem* `settleRing_conserves` is independently proved over the real executor. (ember already named this) |
| 3 | WART | `Circuit/Inst/revoke.lean:70` (`revokeAdmit := True`), `Circuit/Inst/pipelinedSendA.lean:62` (`guardProp := True`), `attenuateA.lean:100`, `Circuit/Spec/notecommitment.lean:64` | per-effect circuit admissibility guard | The effect's `execFullA` arm is genuinely TOTAL (`some …`, no `if`), so the `True` guard faithfully reflects the executor. *Modeling* question (should `revoke` be holder-gated?) lives upstream in the forest-level credential gate, not here. | Honest reflection of a total arm; soundness lives in the injective `funcComponent` digest + restFrame, not the guard. |
| 4 | WART | `Crypto/Pedersen.lean:479-487` (`refKernel.binding/extractable := True`, `verify := insC.sum = outsC.sum` over `commit := (+)`) | a "reference" Pedersen verifier kernel | `commit := (+)` is a genuinely toy commitment (additively trivial, not hiding/binding). | Labeled "degenerate reference" / inhabitability witness; the load-bearing soundness consumes `binding : Prop` as a hypothesis on an *abstract* kernel, not this one. |

## Verified-OK (inspected and cleared — NOT vacuity)

| Location | Pattern | Why OK |
|----------|---------|--------|
| `Circuit/Inst/*.lean` `*EWire` (e.g. `burnA.lean:212`, `EffectInstances2.lean:213`), `Circuit/Witness/*` `restFrame := fun _ _ => True` | Emission/demo carriers | `effectCircuit2` reads ONLY `guardGates`; `burnEWire_circuit_eq : effectCircuit2 burnEWire = effectCircuit2 (burnE D hD) := rfl` proves the wire carrier emits the SAME bytes as the SOUND instance. The soundness path (`burnA_full_sound`) goes through `burnE D hD` with the real 16-field `restFrame` + `RestIffNoBal` portal + injective `D`. Never through the `True` carrier. |
| `Authority/CaveatChain.lean:87` `unforgeable : Prop` | named EUF-CMA hypothesis | De-vacuified: welded to `verifyTag_sound : unforgeable → (verifyTag … = true → Tagged …)` and *refuted* on a forgeable instance (`collapseMacKernel`). The exact fix the old `unforgeable := True` lacked. |
| `Exec/EffectsPaired.lean:1313` `okPortal := {verified := True}` | §8 ZK hypothesis | `portalStep` fail-closes on `¬verified` (`portalStep_fails_without_crypto`); `badPortal := False` is the tooth. |
| `Exec/ProofForest.lean:188,194,237` `StepProofValid := True` | §8 per-node seam | `proofForest_factors` states it as an explicit `∧`-antecedent ("assumed; discharged in Rust by `verify_effect_vm`"); the `True` instances are non-vacuity demos, with an unlinked-forest tooth. |
| `Spec/ExecRefinement.lean:218` `ExecRights := Unit` | connectivity-skeleton carrier | De-vacuified alongside by `ExecCapRights := Finset Auth` with real `⊆`-lattice teeth (`amplifying_grant_refused`, `strict_attenuation_witness`). The `Unit` is the *connectivity* projection; rights attenuation lives on the genuine lattice. |
| `Privacy.lean:559` `LegalDerivation _ := True`, `graphRef` | test-kernel instance | Inhabitability witness for the `GraphPrivacyKernel` interface (with a real `unlinkable_law`/`stealth_k_anonymity`), not the load-bearing obligation. |
| `Crypto/{UCBridge,Primitives,NonMembership,Custom,Temporal,Bridge,VerifierKernel,BlindedSet}.lean` `binding/correct/extractable := True` | crypto-floor carriers | Named hypotheses on abstract kernels / inhabitability witnesses; the running surface routes through the realizable Poseidon2-CR bar. (OK per the crypto note.) |
| `Proof/Fairness.lean`, `Proof/Noninterference.lean`, `Privacy.lean:592` `fun _ => True` | refuted-as-vacuous teeth | These are the *negative* witnesses (`¬ Just (fun _ => True) …`, `memRefNat`'s `2 ∉`) proving the surrounding predicate is NOT `fun _ => True`. |
| `Upgrade.lean:330` `bumpEdge := True` | explicitly non-load-bearing | doc states "that route is not load-bearing (`bumpEdge := True`)". |

---

## Detail

### Finding 1 (MID) — the "in-compartment" / "in-bucket" tag is decorative; the binding predicate is orphaned

**Claims to guarantee.** In the composed PRODUCTION CROWN
`Verify/AppComposition.lean:34 agent_mandate_safety_forever`, two of the six per-index conjuncts
are `cwmInCompartment (trajG …).kernel comp` and `sgmInBucket (trajG …).kernel bucket`
(lines 53, 46). The names + the theorem doc ("in-compartment … in-bucket") advertise that the
agent's mandate stays bound to the *specific* compartment `comp` / bucket `bucket` along every
trajectory.

**Why it's actually weaker.** `Apps/CompartmentWorkflowMandate.lean:260`:

```
def cwmInCompartment (_k : RecordKernelState) (_comp : Int) : Prop :=
  mandateCell ∈ _k.accounts ∧ cwmMandateProgramOK _k
```

The `_comp` argument is unused; the body is value-independent of `comp` — it is the *same
proposition for every `comp`*. Identically, `StorageGatewayMandate.lean:916`
`sgmInBucket (_k) (_bucket) := mandateCell ∈ accounts ∧ sgmMandateProgramOK _k` ignores
`_bucket`. So the crown's "stays in compartment `comp`" conjunct is really just "the mandate cell
stays live and its caveat program stays installed" — which is already the *separate* `cwmWF`
conjunct (line 49). The tag conjunct adds nothing about the actual compartment value.

The genuine binding predicates exist but are **orphaned**:
`cwmInCompartmentStrong k comp := cwmAnchor k = comp` (`:233`) and
`sgmInBucketStrong k bucket := sgmAnchorIs k bucket = true ∧ sgmMandateProgramOK k` (`:897`).
Grep confirms they appear ONLY in their own carry-lemmas and two `#guard` smoke-checks over a
single concrete state (`CompartmentWorkflowMandateGated.lean:354-355`); they are **never** in the
`.forever` crown.

This is not `:= True` — the program-live core IS real and non-trivial — but the predicate is
weaker than its name and its CROWN role advertise. It is exactly the "*Strong predicates orphaned
while the weaker conjunct carries the PRODUCTION CROWN*" pattern memory flagged.

**Concrete fix.** Replace the weak `cwmInCompartment`/`sgmInBucket` in the crown with the
`*Strong` predicates (or add the anchor-value conjunct to them), and prove the persistence:
`cwmAnchor` / `sgmAnchor` is preserved across all forest arms via the persisted
`.immutable commitmentAnchorSlot` caveat in `mandateCaveats` (a second cell-record frame on
`fieldOf commitmentAnchorSlot (cell mandateCell)`, which the doc-comments at `:912-915` and
`:256-258` already describe as "the precise residual" needing "a second cell-record frame"). The
honest non-trivial statement the crown should carry: *for every `n`, `cwmAnchor (trajG … n) = comp`*.

**Mitigating honesty.** The doc-comments are unusually candid ("the literal anchor-VALUE conjunct
`sgmAnchorIs k bucket` is NOT carried here … Strictly stronger than `True`"). So this is a
labeled-but-incomplete invariant, not a hidden one. Still MID, because the crown's *name* claims
compartment/bucket binding it does not prove.

### Finding 2 (WART) — Ring `perAsset` is `rfl` over byte-identical folds (ember's seed)

`Intent/Ring.lean:196-204`: `sentOf` and `recvOf` are textually identical
(`(r.filter (·.asset == a)).foldl (· + ·.amount) 0`), so
`perAsset_of_paired (r a) : sentOf r a = recvOf r a := rfl` (`:233`) holds for **every** ring,
conserving or not. The `RingBalanced.perAsset` field (`:223`) is therefore vacuous.

**Load-bearing?** No. The teeth that actually reject a free-mint ring are the cycle-closure
fields `recvImpSend`/`sendImpRecv` (`freeMintRing_rejected`, `:275`), and the headline
conservation theorem `settleRing_conserves` (`:117`) is proved independently by folding the real
executor keystone `recKExecAsset_conserves_per_asset` — it does not route through `perAsset`. So
`RingBalanced` is sound *despite* the vacuous field, but the field itself adds no constraint.

**Fix.** Make `recvOf` genuinely sum the *received* side keyed by `to_` (e.g. credit per receiving
cell), distinct from `sentOf` keyed by `from_`, so `perAsset` becomes a real per-asset
sent=received equation that a fabricated extra-credit leg can violate. Then `perAsset_of_paired`
is no longer `rfl` and the conjunct earns its place.

### Findings 3–4

See table. Both are honest reflections (a total executor arm; a labeled degenerate reference
kernel), flagged only so the modeling decisions are visible: (3) whether `revoke` *should* be
total vs. holder-gated is a real semantic question, but it is correctly an executor/forest-gate
concern, not a per-effect circuit vacuity; (4) `refKernel`'s `commit := (+)` is a toy that should
never be mistaken for the abstract binding hypothesis the conservation soundness actually consumes.

---

## Bottom line

The crown jewels are honest. The one place where a *named, CROWN-level* invariant is weaker than
its name (Finding 1: `cwmInCompartment`/`sgmInBucket` ignore their tag, real `*Strong` orphaned)
is MID and has a clear fix already sketched in the code's own comments. Ember's Ring seed
(Finding 2) is a confirmed vacuous `rfl` conjunct, but decorative — the surrounding theorems carry
the real guarantee. **No FATAL load-bearing vacuity.**
