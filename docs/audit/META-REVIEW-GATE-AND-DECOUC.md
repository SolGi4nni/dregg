# Adversarial meta-review — the non-vacuity GATE and the DECO-UC reduction

**Prior: DISTRUST.** Assume the gate is a rubber stamp and DECO-UC is a restatement until the actual
Lean/Rust proves otherwise. Method: read the statements + proof terms, build the real tree, and
*perform* the tooth-removal experiment rather than trust the self-report.

**What I actually ran (ground truth, not self-report):**
- `cargo test -p dregg-circuit --test security_property_nonvacuity_gate` → **3/3 green** at HEAD `b201f7d76`.
- Renamed a *different* row's real `bites` decl in Lean source and re-ran the gate → **it RED** (below).
- `lake build Dregg2.Crypto.DecoUC` → **Build completed successfully (2964 jobs)**; the `#assert_axioms`
  in both DECO modules elaborated clean (only `{propext, Classical.choice, Quot.sound}`). So the
  greenness and axiom-cleanliness are REAL. Every finding below is *semantic*, not "it doesn't build."

---

## PART 1 — Is the non-vacuity gate itself non-vacuous?

### 1.1 Does the gate red when a real tooth is removed? — YES (verified on an independent row)

The gate's own self-test `meta_gate_bites` case (f) removes `reachable_total_zero_teeth` (row 8) from
the scanned name-set and asserts a red. To avoid trusting the one row the author picked, I mutated a
**different** row in the real Lean source:

```
metatheory/Dregg2/Deos/SealedEscrow.lean:840
-  theorem halfopen_theft_unreachable : ¬ Reachable halfOpenTheft := by
+  theorem halfopen_theft_unreachable_AUDITMANGLED : ¬ Reachable halfOpenTheft := by
```

Re-running `every_security_property_has_biting_tooth` produced:

```
SECURITY-PROPERTY NON-VACUITY GATE RED — 1 load-bearing theorem(s) lack a registered, source-grounded
biting tooth:
  - sealedescrow_no_theft @ Deos/SealedEscrow.lean:753 — `bites` companion `halfopen_theft_unreachable`
    NOT FOUND in metatheory Lean source (stale/renamed/deleted tooth)
```

Then reverted (`git checkout`; 0 `AUDITMANGLED` remain). **Verdict: the gate is NOT a rubber stamp for
name presence — deleting/renaming a real registered tooth reds it.** The source-grounding leg works.

### 1.2 What the gate actually checks — and the three things it does NOT

Read `row_finding` + `scan_lean_decl_names` + `collect_decl_names`. The "source grounding" is a
**bare-name existence check over the whole `metatheory/**/*.lean` tree**. That is strictly weaker than
the manifest's headline ("every load-bearing security theorem HAS a biting non-vacuity tooth"). The gate
does **not**:

1. **Check non-vacuity.** It never reads the tooth's *statement* or proof. A registered tooth defined
   as `theorem attestation_bites : True := trivial` would satisfy the gate. The gate cannot see vacuity
   at all — the actual biting is delegated 100% to the Lean side (`#assert_axioms`, `#keystone_audit_tagged`)
   and to human review. **The Rust gate is a stale-ledger catch, not a non-vacuity verifier.** Its name
   ("non-vacuity gate") overstates what it mechanically enforces.
2. **Check the tooth's kind.** `collect_decl_names` registers `theorem | lemma | def | abbrev`. A
   `def bites := True` counts. Nothing forces a *theorem*.
3. **Check the tooth lives in the file the row names.** The scan is global. A row citing
   `@ metatheory/Dregg2/Circuit/CustomBindingFromFold.lean:147` is satisfied by a decl of that name *anywhere* in the tree.

**Carrier-fires multiplicity hole (concrete).** Rows 13–20 (the eight `*_binding_from_fold` carriers)
all register the SAME `fires: "honest_companion_fires"`. The gate only checks that *one* decl named
`honest_companion_fires` exists. I confirmed all eight files currently each define their own
(`grep` shows 8 decls) — so this is not a *live* vacuity — but **deleting seven of the eight carrier
fires-teeth would NOT red the gate.** The coverage is nominal, not per-carrier.

### 1.3 Is coverage honest? — It is an ALLOWLIST, and I found a genuine omission

The gate is explicit that enumeration is "an explicit allowlist-with-reason" (nothing reflective). The
`manifest.len() >= 20` floor only stops the list from *shrinking*; nothing mechanically forces a new
world-property in. So the honesty question is empirical: are load-bearing world-properties missing?

**Finding — `budget_never_overdrawn` (PrepaidLease.lean:378) is omitted.** It is a genuine load-bearing
economic world-property (`remainingAfter budget rent n = budget − n·rent`, with a refusal half
`insufficient_budget_rejected`), and the manifest's OWN row-21 comment names it as a peer to Vault's
no-dilution and the escrow no-theft it *does* register ("the escrow analogue of Vault's no-dilution /
**Lease's budget conservation**"). Yet there is no `budget_never_overdrawn` row in the ledger. So the
Lease economic invariant is a world-property the author was aware of, called a peer, and did not add.
**The "every load-bearing security-property theorem" claim is over a curated subset with ≥1 known gap.**

### 1.4 Are the sampled registered teeth actually biting? — Yes, the Lean teeth I read all bite

I read the actual companion theorems for the newest / most load-bearing rows. None was vacuous:

| tooth | verdict |
|---|---|
| `reachable_total_zero_teeth` (row 8, the one case (f) leans on) | **Real.** `badKernel` gives asset-1 total `5`, `¬ ExactConservation` by `omega` on `5 = 0`. Two-valued. `nonzero_state_unreachable` is a real bite. |
| `halfopen_theft_unreachable` (row 21) | **Real.** `¬ Reachable halfOpenTheft` — a genuine reachability refutation. |
| `attestation_bites` / `attestation_bites_is_sig_forgery` (row 22) | **Real.** Constructs a concrete `SigForgery` over a forge kernel (`Signed := False`, `sigVerify := fun _ _ _ => true`). |
| `forge_not_ucRealizes` (row 23) | **Real two-valued** — `UCRealizesFAtt` is genuinely FALSE over the forge kernel (but see Part 2.2: it bites only the soundness conjunct). |
| `decoCarrier_bites`, `attestation_invariant_bites` (schema §3.9) | **Real.** `¬ accept ∧ ¬ invariant` / `¬ decoAuthenticated` at the forge kernel. |

So I did **not** find a registered tooth that is itself a `:= True`. The exposure is the *property being
guarded* at row 23, not the tooth (Part 2).

### Part 1 verdict

The gate **is trustworthy as a stale-ledger catch** — it genuinely reds when a registered Lean tooth is
deleted/renamed (verified independently), and the sampled Lean teeth genuinely bite. But it is **weaker
than its name**: it checks bare-name existence only, over the whole tree, with no vacuity / theorem-kind
/ file-locality check, so it *cannot* detect a vacuous tooth if one were introduced; its coverage is a
curated allowlist that already omits at least one named world-property (`budget_never_overdrawn`); and
the eight carriers share one fires-name so per-carrier fires-teeth are not individually enforced. It is
not a rubber stamp, but "every load-bearing security theorem has a biting non-vacuity tooth" is enforced
by Lean + review, **not by this gate** — the gate only enforces that a decl of the registered name exists.

---

## PART 2 — Is DECO-UC a real reduction or a restatement?

### 2.1 Rung 4 `deco_attestation_unforgeable` — a REAL reduction (not circular, not a restatement)

`forgery_yields_break` (DecoUnforgeable.lean:196) is the load-bearing content and it is genuine:

- It takes `hforge : AttForgery = (verify = true ∧ ¬ decoAuthenticated)`, extracts a satisfying witness
  `w` via `deco_verify_sound hext` (STARK extractability), then does an **exhaustive 2×2 case split** on
  `SK.Signed …` × `MK.Tagged …`:
  - (T,T) → `w` witnesses `decoAuthenticated`, contradicting `¬ Auth` (`absurd`);
  - (T,F) → `Or.inr ⟨w.sessionKey, w.transcriptCommit, w.tag, hmacOk, hTagged⟩` — a **constructed** `MacForgery`;
  - (F,_) → `Or.inl ⟨stmt.serverKey, w.sessionKey, w.sig, hsigOk, hSigned⟩` — a **constructed** `SigForgery`.
- The `SigForgery`/`MacForgery` are **built from the forgery's own extracted witness** (explicit anonymous
  constructors), not postulated. The `hsigOk`/`hmacOk` "oracle accepts" facts come from the extracted
  `DecoRelation`, and `¬Signed`/`¬Tagged` from the case split. This is the standard extractor-reduction shape.
- `deco_attestation_unforgeable` then closes it under `Ed25519EufCma SK` and `MacEufCma MK` — the floors
  are **hypotheses** (`∀ …, ¬ SigForgery …`), i.e. the standard cryptographic assumptions, not the
  conclusion. **No circularity: DECO unforgeability reduces to ed25519 EUF-CMA + HMAC + STARK
  extractability (+ Poseidon2 CR for the binding leg).**
- The bite `attestation_bites` genuinely exhibits a forgeable oracle admitting a concrete `AttForgery`
  and runs the reduction to extract a real `SigForgery`. Two-valued.

**Verdict: rung 4 is a genuine reduction to named standard floors. Solid — this is the real deliverable
of the DECO-UC lane.**

### 2.2 Rung 5 `decoUC_realizes` — substantially a RESTATEMENT of rung 4; the rfl-conjunct IS vacuous

The task flagged the "`rfl`-true conjunct." Confirmed, and it is worse than a lone decoration — it
collapses the whole rung-5 Lean proposition back onto rung 4.

**(a) The second conjunct of `UCRealizesFAtt` is vacuously true for ALL inputs.**

```lean
def decoDisclosedView (stmt : Statement Dg) (_w : CircuitIR Dg) : Statement Dg := stmt   -- ignores w
def UCRealizesFAtt verify Auth : Prop :=
  AttRealizes verify Auth ∧
  (∀ stmt w₁ w₂, decoDisclosedView stmt w₁ = decoDisclosedView stmt w₂)
```

Because `decoDisclosedView` is *defined* to discard `w`, the conjunct is `stmt = stmt` — provable by
`rfl` for **any** `verify`, `Auth`, honest or forged. It carries zero information about the deployed
verifier. The "verifier learns nothing about the session" is not *proven about DECO*; it is **baked into
the definition of the view** (a view function chosen constant in the witness). `decoView_witness_free` /
`decoView_indep` are `rfl` for exactly this reason. Therefore `UCRealizesFAtt verify Auth` is logically
**equivalent to `AttRealizes verify Auth`** (= rung-4 soundness). Removing the conjunct does not weaken
the theorem → by the project's own rule ("a labeled vacuity is still broken") the conjunct is a `True`
in a costume.

**(b) `decoUC_realizes` is essentially `P → P`.** It is
`fun r => ⟨r.soundness, r.zk_disclosed⟩ : UCRealizesFAtt`. Its hypothesis `r : DecoUCRealization` must
already supply `soundness : AttRealizes`; its conclusion is `AttRealizes ∧ True`. It **ignores all ten
computational-carrier fields** (`stark_zk`, `handshake_sim`, `simulator_ppt`, `negligible_advantage`,
`composes`, and their `_holds`). So rung 5's headline theorem concludes exactly what its hypothesis's
`soundness` field already is — **it adds nothing over rung 4.**

**(c) The carried computational layer is `True` in every actual instance.** `stark_zk : Prop` etc. are
*arbitrary-`Prop` fields*, and the only builders — `decoUC_realization` (via `ref_ucRealizes`) and
`refDischarge` — instantiate every one to `True` with `trivial`. So the `≈_c` core has no Lean content;
it is a named placeholder. (The header is explicit about this and names the missing CryptHOL/`spmf`
framework precisely — so it is *labeled*, not concealed.)

**(d) The registered bite bites rung-4, not rung-5.** `forge_not_ucRealizes` is
`rintro ⟨hsound, _⟩; exact Forge.forge_not_realizes hsound` — it destructs `UCRealizesFAtt`, **discards
the ZK conjunct**, and refutes via the soundness conjunct alone (the rung-4 forgery). The ZK conjunct is
true even for the forge kernel. So **row 23's biting content is identical to row 22's.** Row 23 is not an
independent world-property; it is rung-4 unforgeability re-dressed as "UC-realization." The manifest
registering it as a distinct "summit" property (23rd load-bearing theorem) overstates the Lean content.

### 2.3 Is the simulator real? — Real but TOY; and the genuine ZK teeth are not wired into the claim

- `decoSim_works` is a genuine computation: `decoSimTranscript` (a witness-free transcript from the
  disclosed statement alone) satisfies `DecoRelation` and the verifier accepts, all by `decide`/`rfl`.
  **But** "the verifier" is `Reference.refKernel.verify = decide (stmt.serverKey = 11 ∧ 1 ≤ amountCents)`
  — a toy two-integer check, **not a STARK**. So `decoSim_works` proves a real witness-free simulator
  *for the toy reference model*; the docstring phrase "the deployed verifier accepts … without a real
  Stripe session" is true only of the toy check. Honest as a non-vacuity *fires*; not evidence of a real
  STARK simulator.
- The genuinely non-vacuous ZK content **does exist** — `decoLeaky_no_simulator` is a real teeth (a view
  leaking `w.sessionKey` has no witness-free simulator; two witnesses `0`/`1` give different views) — but
  it is **not the conjunct wired into `UCRealizesFAtt`**. The load-bearing proposition carries the
  vacuous constant-view conjunct; the real ZK teeth sit beside it, unused by rung 5's headline.

### Part 2 verdict

- **Rung 4 (`deco_attestation_unforgeable`): a REAL reduction** to named standard floors, with a real
  constructed forgery bite. This is sound and is the genuine content of the lane.
- **Rung 5 (`decoUC_realizes`): substantially a RESTATEMENT of rung 4.** The perfect-ZK conjunct in
  `UCRealizesFAtt` is `rfl`-vacuous (the view is defined constant in the witness), so `UCRealizesFAtt ≡
  AttRealizes`; `decoUC_realizes` is `≈ P → P` and ignores all computational carriers (which are `True`
  in practice); and the registered bite refutes only the soundness conjunct — i.e. row 23's teeth are
  row 22's. **Rung 5 does not establish "the deployed protocol UC-realizes `F_attestation`" in Lean
  beyond rung-4 soundness.** The module is scrupulously self-labeling about the carried `≈_c` residue and
  the missing framework, so this is a *labeled* gap rather than concealed laundering — but the manifest's
  presentation of row 23 as a distinct summit world-property with its own biting tooth overstates what
  the Lean actually proves.

---

## Recommendations (closure lanes, in the project's "rise to meet the claim" spirit)

1. **Gate:** rename/reframe from "non-vacuity gate" to what it is (a *tooth-registration stale-ledger
   gate*), OR strengthen the scan to (a) require the tooth be a `theorem`, and (b) require it be defined
   in the file the row names (parse `@ file`), closing the global-name and carrier-multiplicity holes.
2. **Coverage:** add a `budget_never_overdrawn` row (Lease), and audit `Deos/*.lean` for other economic
   world-properties (`escrow_solvent`, `withdraw_no_dilution`, …) that lack a row.
3. **Row 23:** either wire a *load-bearing* ZK conjunct into `UCRealizesFAtt` (a view function that
   actually reads the verifier's observable, so `decoLeaky_no_simulator` becomes the bite that fires on
   it), or relabel row 23 honestly as "rung-4 soundness re-exported under the UC name, computational
   core CARRIED" so the manifest tally does not count a vacuous conjunct as a distinct proven summit.
