# DECO-as-UC — the climb from "authenticity ASSUMED" to "authenticity PROVEN unforgeable"

> **BUILD STATUS (rung a — game-based unforgeability): DONE.** Rung (a) is built and green in
> `metatheory/Dregg2/Crypto/DecoUnforgeable.lean` (`#assert_axioms`-clean, ⊆ `{propext,
> Classical.choice, Quot.sound}`):
> - `F_attestation` (ideal functionality, on `F_LC`) + `decoAuthenticated` (the ground truth =
>   `deco_authenticates_payment`'s conclusion) + `AttReal`/`AttRealizes`.
> - the game `AttForgery`/`AttUnforgeable` (`attUnforgeable_iff_attRealizes`); the reduction
>   `forgery_yields_break` (a forged attestation ⟹ a concrete ed25519 `SigForgery` / HMAC
>   `MacForgery`) ⟹ `deco_attestation_unforgeable` / `deco_attestation_unforgeable_of_carriers`; the
>   binding leg `deco_binding_forgery_to_collision` / `deco_binding_unforgeable` (Poseidon2 CR).
> - `deco_attestation_realizes` (`deco_authenticates_payment` re-read as `AttRealizes`).
> - `governed_holds` instance `attestationDynamics` + `deco_attestation_via_schema` in
>   `metatheory/Metatheory/Adversary/Instances.lean` §3.9 (composes with, distinct from,
>   `decoCarrierDynamics`).
> - both-polarity non-vacuity `attestation_fires` / `Forge.attestation_bites`
>   (+ `attestation_bites_is_sig_forgery`, `forge_not_realizes`); manifest row 22 in
>   `docs/audit/NON-VACUITY-MANIFEST.md` + `circuit/tests/security_property_nonvacuity_gate.rs`.
> - **FLOOR: STANDARD-ONLY.** The reduction closes to ed25519 EUF-CMA + HMAC + Poseidon2 CR + STARK
>   extractability — EXACTLY the `deco_binds_payment` trust base. NO dregg-specific parked assumption
>   was found (the R4 hunt came up empty, as §4 predicted).
>
> **⚑ COORDINATION NOTE for the other Fable (zkOracle lane) — NAMED, NOT MADE here.**
> `zkOracle_sound` (`Dregg2/Crypto/ZkOracle.lean:71`) currently delivers its `authentic` conjunct as
> `∃ w, Deco.DecoRelation … decoStmt w` (`ZkOracle.lean:81`), via `deco_verify_sound` (`:84`) — the
> *satisfying-trace-exists* refinement level. It can now upgrade to the ideal-world statement
> `DecoUnforgeable.decoAuthenticated SK MK KD.compress KD.encode decoStmt` (= "`F_attestation` emitted
> this"), delivered by `DecoUnforgeable.deco_attestation_realizes` instead of `deco_verify_sound`. The
> realization theorem is a drop-in with the same `verify … = true → <authentic conjunct>` shape (it
> additionally needs the `hsigEq`/`hmacEq`/`hsig`/`hmac` §8-carrier hypotheses that
> `deco_authenticates_payment` already takes). This upgrade is the other Fable's to make — do NOT edit
> `ZkOracle.lean` from the DecoUnforgeable lane.


> Closes **survey gap #1** (`docs/audit/SECURITY-PROPERTY-MAP.md:192`): *"DECO payment
> unforgeability is ASSUMED, not proven, and has no UC proof."* This is the crypto keystone
> under zkOracle's `authentic` leg — the money-in carrier of the verified resident.

**Design-only. This doc commits nothing but itself.** It scopes the build; it does not
implement. Every "CURRENT" claim is grounded at `file:line` against HEAD (a settled tree),
verified against the code. All Lean paths under `metatheory/`.

The one-paragraph orientation: DECO's authenticity today is a *soundness refinement*
(`deco_authenticates_payment`, `Dregg2/Crypto/Deco.lean:315` — accept ⟹ the payment facts
genuinely hold) resting on named §8 carriers entering as hypotheses. It is NOT a proof that a
payment *cannot be forged*, and no simulator/UC argument exists for it. The good news: the
correctness leg is *already proven*, and the tree already contains the two exact templates the
two rungs need — `Dregg2/Crypto/Ed25519Reduction.lean` (a game-based forgery reduction to a
NAMED floor) and `Dregg2/Crypto/LightClientUC.lean` (an ideal-functionality + soundness-game +
reduction). The lift is framing + one 3-way case split + non-vacuity teeth, not new mathematics.

---

## 0. What exists today (the ground truth, grounded)

The DECO stack in `Dregg2/Crypto/Deco.lean`:

| Object | file:line | What it gives |
|---|---|---|
| `PaymentFacts` (amount/currency/recipient/paymentIntentId) | `Deco.lean:48` | the disclosed money-in facts |
| `Statement` (serverKey + facts) | `Deco.lean:59` | public inputs; session key/transcript/salt are the private witness |
| `DecoRelation` | `Deco.lean:103` | the 4-link auth chain + non-zero-amount gate |
| `deco_bridge` | `Deco.lean:191` | `Satisfies ↔ DecoRelation`, both directions, `#assert_axioms`-clean |
| `deco_verify_sound` | `Deco.lean:296` | STARK accept ⟹ `∃ w, DecoRelation … stmt w` (the extractability leg) |
| `deco_binds_payment` | `Deco.lean:228` | the relation's runnable gates lift to genuine `Signed`/`Tagged`/opening — **given** the §8 carriers |
| `deco_commitment_binds` | `Deco.lean:249` | Poseidon2 CR ⟹ the committed transcript opens to a UNIQUE field digest |
| `deco_authenticates_payment` | `Deco.lean:315` | the capstone: accept ⟹ a genuine Stripe-authenticated non-zero payment |
| `DecoVerifierKernel` + `.extractable` | `Deco.lean:271/:285` | the deployed §8 verify oracle + the STARK carrier |
| `Reference.refKernel` / `reference_authenticates_payment` | `Deco.lean:492/:532` | a concrete toy kernel witnessing the capstone non-vacuously |
| dial floor = `selective` | `Deco.lean:392` | public = facts + serverKey; **hidden = session key, transcript, salt** |

The named floor (`deco_binds_payment` trust base, `Deco.lean:213-228`, mirrored in the security
map's assumed-floor row `SECURITY-PROPERTY-MAP.md:136`):

- **ed25519 EUF-CMA** — `PortalFloor.SignatureKernel.unforgeable` (`PortalFloor.lean:47`), sharpened
  to the game predicate `Ed25519EufCma` (`Ed25519Reduction.lean:70`).
- **HMAC unforgeability** — `PortalFloor.MacKernelE.unforgeable` (`PortalFloor.lean:270`).
- **Poseidon2 collision-resistance** — `PortalFloor.Poseidon2Kernel.collisionHard` (`PortalFloor.lean:149`).
- **STARK extractability/knowledge-soundness** — `DecoVerifierKernel.extractable` (`Deco.lean:285`);
  deployed `StarkSound` (`Circuit/CircuitSoundness.lean:382`).
- **Web-PKI honest-endpoint** — the external floor: `serverKey`-is-Stripe + `encode`-is-the-schema
  (`Deco.lean:28/:60`). A *deployment trust anchor* (which key is Stripe's), NOT a cryptographic
  hardness assumption — carried by the registration, not a Lean carrier.

The deployed-carrier side already has a home in the adversary frame: `decoCarrierDynamics`
(`Metatheory/Adversary/Instances.lean:483`), `deco_backing_from_fold` + `decoCarrier_bites`
(`:497/:507`) — but that binds the *mint's published `payment_hash` to a verifying sub-proof*, a
DIFFERENT statement from "the DECO attestation itself is unforgeable" (see §5.1). The adversarial
audit of the deployed row (`Circuit/DecoBackingAttack.lean`, `DecoEngine`,
`deployed_admits_unbacked_deco`) shows the deployed AIR alone does not force payment backing —
the repair is the fold (`DecoBindingFromFold`), and *this* plan supplies the missing leg beneath
it: what a verifying DECO leaf actually *means*.

The UC shelf (`Metatheory/Open/PerfectUC.lean`): perfect/statistical composition
`perfectUC_composition` (`:200`), wired ONLY to the disclosure functionality
(`realπ_realizes_idealF`, `:448`); the **computational** UC theorem is explicitly OPEN (`:502`).
**PerfectUC is not wired to DECO** — that is the gap this plan fills.

---

## 1. `F_attestation` — THE IDEAL FUNCTIONALITY

### 1.1 The design (modelled on `F_LC`, `LightClientUC.lean:74`)

The tree already contains the exact shape: `F_LC Produced s := Produced s` — an ideal oracle that
"accepts `s` iff the executor produced it" (`LightClientUC.lean:71-74`), with a real client
`LCReal verify s π := verify s π` (`:79`) that holds NO `Produced` oracle. `F_attestation` is that
pattern instantiated over the DECO objects.

**The ground-truth oracle.** Parametrize by the ideal predicate

```
Authenticated : Statement Dg → Prop
```

read as *"a genuine Stripe TLS session disclosed exactly these `facts` to this `serverKey`."*
`Authenticated` is the DECO analog of `Produced`: the ideal functionality holds the ground truth
of which sessions actually happened — the environment/adversary cannot make it lie. Crucially, for
DECO `Authenticated` is NOT abstract — it *decomposes into the §8 facts*, and that decomposition is
already the conclusion of `deco_authenticates_payment` (`Deco.lean:320-328`):

```
Authenticated stmt  :=  ∃ w : CircuitIR Dg,
     SK.Signed stmt.serverKey w.sessionKey            -- Stripe's key signed the session (EUF-CMA)
   ∧ MK.Tagged w.sessionKey w.transcriptCommit w.tag  -- the transcript was MAC'd under it (HMAC)
   ∧ w.transcriptCommit = compress (encode stmt.facts) w.salt  -- opens to exactly these facts (CR)
   ∧ 1 ≤ stmt.facts.amountCents                        -- the payment succeeded
```

**The interface (three morphisms, the `F_LC` triple):**

- `F_attestation Authenticated stmt : Prop := Authenticated stmt` — the ideal: emit iff a genuine
  session backs `stmt`. (Cf. `F_LC`, `LightClientUC.lean:74`.)
- `AttReal verify stmt proof : Bool := verify stmt proof` — the real DECO verifier (the deployed
  `DecoVerifierKernel.verify`, `Deco.lean:282`); holds no `Authenticated` oracle, runs one STARK
  check. (Cf. `LCReal`, `:79`.)
- The realization relation `AttRealizes verify Authenticated : Prop :=`
  `∀ stmt proof, AttReal verify stmt proof = true → Authenticated stmt` — the deployed verifier is
  indistinguishable from `F_attestation`. (Cf. `Unfoolable`, `LightClientUC.lean:105`.)

**The ideal guarantee.** No environment/adversary can make `F_attestation` emit a FALSE
attestation, because `F_attestation` *is* `Authenticated` — it consults ground truth by fiat. The
non-trivial claim is that the *deployed* verifier realizes it: `AttRealizes verify Authenticated`.
That statement, unfolded, is *exactly* `deco_authenticates_payment` re-read as accept ⟹
`Authenticated` — **the correctness leg already exists**; what is new is (i) naming it as an
ideal-functionality realization, (ii) the *game* whose bad event is a false emission, and (iii) the
reduction of that bad event to a NAMED floor break (§2a).

### 1.2 How zkOracle's `authentic` leg becomes "`F_attestation` emitted this"

Today `zkOracle_sound` (`Dregg2/Crypto/ZkOracle.lean:71`) delivers, for the authentic conjunct,
`∃ w, DecoRelation KD.sigVerify … decoStmt w` (`ZkOracle.lean:81`) via `deco_verify_sound`
(`:84`). That is a *satisfying-trace-exists* statement — the refinement level.

The upgrade: replace that conjunct with `Authenticated decoStmt` (= `F_attestation` emitted),
delivered by the realization theorem (§2a) instead of `deco_verify_sound`. The authentic leg then
reads *"a genuine Stripe session produced these facts,"* an ideal-world statement, not merely *"a
satisfying trace exists."* This is the assumed→proven upgrade of the leg the survey flags.

> ⚠ `ZkOracle.lean` is the OTHER Fable's lane — do NOT edit it here. This plan names the
> one-line consuming swap (`deco_verify_sound` → the realization theorem, `ZkOracle.lean:84`) as a
> coordinated change; the realization theorem is designed to be a drop-in with the same shape
> (`verify … = true → <authentic conjunct>`).

---

## 2. THE TWO RUNGS — weigh + recommend

### (a) GAME-BASED UNFORGEABILITY — the tractable rung-4-for-DECO

**The game.** Mirror `Ed25519Reduction.SigForgery`/`Ed25519EufCma` (`Ed25519Reduction.lean:62/:70`)
and `LightClientUC.Foolable`/`Unfoolable` (`LightClientUC.lean:97/:105`):

```
AttForgery K stmt proof := K.verify stmt proof = true ∧ ¬ Authenticated stmt   -- a verified
                                        -- attestation of a session that did NOT happen
AttUnforgeable K Authenticated := ∀ stmt proof, ¬ AttForgery K stmt proof
```

`AttUnforgeable ↔ AttRealizes` is the exact `unfoolable_iff_not_foolable` equivalence
(`LightClientUC.lean:111`), reproved for DECO in three lines.

**The reduction (the new content).** `deco_verify_sound` (`Deco.lean:296`) gives the *soundness
half*: accept ⟹ `∃ w, DecoRelation … stmt w`. What is missing is the *extractor/reduction* half:
from `DecoRelation` + `¬ Authenticated stmt`, produce a concrete break of a NAMED floor. The chain
gates make this a clean **3-way case split** — a forged attestation of a non-session must break one
of the auth-chain links:

- gate 1 fails to lift ⟹ an **ed25519 `SigForgery`** (`Ed25519Reduction.lean:62`): `sigVerify
  serverKey sessionKey sig = true` yet `¬ Signed serverKey sessionKey`;
- gate 2 fails ⟹ an **HMAC forgery** (the `MacKernelE` analog of `SigForgery`, new-but-mechanical:
  `verifyTag … = true ∧ ¬ Tagged …`);
- gates 3/4 fail ⟹ a **Poseidon2 collision** (`deco_commitment_binds` contrapositive,
  `Deco.lean:249`): two openings of one commitment to distinct field digests;
- the STARK accepts a non-satisfiable statement ⟹ an **extractability break** (`¬ extractable`).

The forward direction is *already proven*: `deco_binds_payment` (`Deco.lean:228`) is exactly
"accept ∧ carriers ⟹ `Authenticated`." So the game-based theorem is:

```
deco_attestation_unforgeable :
  Ed25519EufCma SK → MK.unforgeable → PK.collisionHard → K.extractable →
    AttUnforgeable K Authenticated
```

plus the sharp contrapositive `AttForgery K stmt proof →
(SigForgery ∨ MacForgery ∨ Poseidon2Collision ∨ ¬extractable)` — the standard cryptographic
reduction shape, exactly `Ed25519Reduction.protocol_forgery_to_sig_forgery` /
`eufCma_repels_all_surfaces` (`Ed25519Reduction.lean:239/:246`) generalized from one primitive to
the 4-gate disjunction.

**What it closes.** This turns gap #1 from ASSUMED to *proven-under-standard-assumptions* — in the
same precise sense `Ed25519Reduction` closed the handoff/blocklace/agent-auth surfaces: not "the
primitive is proven" (it never is), but "a protocol break IS a primitive break," so the trust
boundary is the sharp `payment-forgery ⟹ ed25519/HMAC/CR/FRI broken`, not a vague "modulo crypto."

### (b) FULL COMPUTATIONAL UC — the summit (rung 5)

`∃ simulator S, ∀ environment Z, real(π, A) ≈_c ideal(F_attestation, S)`.

**Framework assessment.** `perfectUC_composition` (`PerfectUC.lean:200`) is a real composition
theorem but ONLY in the *perfect collapse* (`≈` is `=`, `Z`'s view a function not an ensemble,
`PerfectUC.lean:79-107`). It **cannot** be extended perfect→computational by tweaking: the module
header states the gap sharply (`PerfectUC.lean:502`, header lines 58-65) — computational UC needs
(i) an interactive-machine/probabilistic execution model (`view_Z` a probability ensemble), (ii) a
simulator witnessing *negligible* advantage, (iii) a hybrid argument over `ρ`. That is **a new
module**, the greenfield core of Elevated-Assurance Pillar 1
(`ELEVATED-ASSURANCE-PROGRAM.md:98-116`, sized LARGE / 2-4 weeks). `perfectUC_composition` survives
as the ε=0 base case / perfect corner, not as the theorem.

**BUT there is a second, cheaper route already bridged into the tree.** `Dregg2/Crypto/UCBridge.lean`
records that the F_com realization obligation "has been **discharged in a real UC / game-based
mechanization**" in `~/dev/breadstuffs/uc-crypthol/Dregg2_FCom.thy`, with
`Dregg2_UC.pedersen.dregg2_pedersen_realizes_F_com` PROVED there (asymptotic variant too). So the
computational-UC summit for `F_attestation` has two sub-routes:
- **(b-i)** build the Lean computational-UC model from `PerfectUC`'s `System`/`Context` skeleton
  (greenfield, LARGE);
- **(b-ii)** mechanize `F_attestation` realization in the existing CryptHOL harness alongside
  `F_com`, reusing `Dregg2_FCom.thy`'s structure, then bridge it back as a named discharged
  obligation the way `UCBridge.lean` already does (MEDIUM given the harness).

### RECOMMENDATION — game-based FIRST; full-UC scoped as the summit (via CryptHOL)

**Build (a) first.** Justification:

1. **It closes the actual gap.** Gap #1 is "unforgeability ASSUMED." The game-based rung *is* the
   unforgeability proof (under standard assumptions) — it answers the survey's exact question. Full
   UC is a *stronger frame* but does not close anything the game does not.
2. **It is a genuine rung-4 result, not a refinement.** `AttUnforgeable` is a *world property* (no
   PPT adversary forges), the poster's "holds against A" strengthened to "realizes the ideal
   against A" once wired through `governed_holds` (§5.1). This is above the current
   `deco_authenticates_payment` refinement rung.
3. **It reuses a proven template near-verbatim.** `Ed25519Reduction.lean` is the whole shape (forge
   predicate → primitive-as-no-forge → protocol-break⟹primitive-break → contrapositive →
   both-directions teeth). The DECO version is that file with a 4-way case split. ~1-2 days,
   `#assert_axioms`-clean.
4. **It is the soundness half the simulator needs.** Not wasted work: (a) is a *prerequisite* of
   (b) — the simulator's soundness obligation IS `AttRealizes` (§3).

**Scope (b) as the summit via route (b-ii).** The CryptHOL harness already exists and is already
bridged (`UCBridge.lean`), so the computational summit is MEDIUM rather than LARGE — do it after
(a) lands, and after Pillar 1's Lean model exists if the fully-in-Lean corner is wanted.

---

## 3. THE SIMULATOR (for the UC path) — construction sketch

**Goal.** Given only `F_attestation`'s output — the ideal transcript = `(stmt.serverKey,
stmt.facts, accept-bit)` — produce a DECO transcript `(sessionKey, sig, transcriptCommit, tag,
fieldsDigest, salt, π)` indistinguishable from a real one, WITHOUT any real Stripe session.

**What the simulator needs (each grounded, each named):**

1. **STARK zero-knowledge** — simulate the proof `π` from `stmt` alone, never touching the witness
   `w`. Grounded: `Metatheory/Open/PerfectZK.lean` already gives the perfect-ZK law
   `hperf : ∀ s w, view s w = sim s` (`PerfectZK.lean:67-72`) — "the real view equals a simulation
   that never saw the witness." The DECO simulator's proof leg IS `PerfectZK.sim` at the DECO
   statement. The named floor: a `StarkZK` carrier (simulation-soundness / honest-verifier ZK of
   the STARK), NEW to the tree, alongside `StarkSound` — Elevated-Assurance Pillar 1 piece 4 names
   exactly this (`ELEVATED-ASSURANCE-PROGRAM.md:110-112`). Standard for zk-STARKs, terminal-by-design.

2. **DECO 3-party-handshake / MPC-TLS simulatability** — produce a session transcript consistent
   with the disclosed facts without real Stripe keys. Ground whether DECO's primitives are
   simulatable — **yes, and the model already exposes the hooks:**
   - gate 3, `transcriptCommit = compress fieldsDigest salt` (`Deco.lean:114`), is a *hiding*
     commitment: `salt` is blinding. The simulator picks a fresh random `salt` and commits to
     `encode stmt.facts` — indistinguishable by the hiding property (the CR floor's dual). The
     `selective` dial floor (`Deco.lean:392`) *already* classes `salt`/`transcript`/`sessionKey`
     as the HIDDEN witness and `facts`/`serverKey` as PUBLIC — i.e. the dial partition IS the
     public-that-F-gives vs hidden-that-S-fabricates split.
   - gates 1/2 (sig over the session key, MAC over the transcript) are the hard part in the REAL
     world, but the simulator lives in the IDEAL world where `F_attestation` *already vouches*
     authenticity — S produces the transcript against a SIMULATED server key. This is the standard
     DECO/MPC-TLS argument: the verifier's view is simulatable because the 3-party handshake
     reveals only the *committed* transcript, not the session key. The named floor: a
     `DecoHandshakeSimulatable` carrier (honest-verifier ZK of the DECO/MPC-TLS three-party
     handshake), NEW as a named carrier, standard for the DECO protocol.

**The simulator's soundness obligation IS the game-based result.** For the ideal/real views to be
indistinguishable, the real client must never accept where F rejects — that is precisely
`AttRealizes`/`AttUnforgeable` (§2a). So the simulator (b) rests on (a) plus the two ZK floors.
This mirrors `LightClientUC`'s discipline: the reduction `unfoolable_of_floor`
(`LightClientUC.lean:160`) is the soundness core; the simulator (`LightClientUC.lean` §5, the
"functionality with no honest-party inputs to relay") is the wrapper.

---

## 4. THE REDUCTION FLOOR — named, each classified

| Assumption | Named carrier (file:line) | Standard? | Role |
|---|---|---|---|
| ed25519 EUF-CMA | `SignatureKernel.unforgeable` (`PortalFloor.lean:47`) / `Ed25519EufCma` (`Ed25519Reduction.lean:70`) | **standard** | gate-1 forgery target |
| HMAC unforgeability | `MacKernelE.unforgeable` (`PortalFloor.lean:270`) | **standard** | gate-2 forgery target |
| Poseidon2 CR | `Poseidon2Kernel.collisionHard` (`PortalFloor.lean:149`) | **standard** | gates 3/4 opening-binding |
| STARK extractability | `DecoVerifierKernel.extractable` (`Deco.lean:285`) / `StarkSound` (`CircuitSoundness.lean:382`) | **standard** | accept ⟹ satisfiable trace |
| Web-PKI honest-endpoint | external: `serverKey`-is-Stripe + `encode`-is-schema (`Deco.lean:28/:60`) | **standard external** | deployment trust anchor, NOT a hardness — a registration parameter |
| *(UC path only)* STARK zero-knowledge | `StarkZK` — **NEW carrier** (Pillar 1 piece 4) | **standard** (zk-STARK) | simulator proof leg |
| *(UC path only)* DECO handshake simulatability | `DecoHandshakeSimulatable` — **NEW carrier** | **standard** (MPC-TLS HVZK) | simulator transcript leg |

**R4-style parked-dregg-specific hunt: NONE for the game rung.** All four game-rung cryptographic
carriers are standard and are *exactly* the `deco_binds_payment` trust base (`Deco.lean:213-228`);
no dregg-specific hardness is smuggled in. The one non-cryptographic item — the Web-PKI/Stripe
endpoint anchor — is a *deployment* trust (which key is Stripe's), flagged with the same terminal
status it carries today, not a reducible open. The UC rung adds exactly two NEW named carriers
(`StarkZK`, `DecoHandshakeSimulatable`), both standard-for-the-primitive, both terminal-by-design —
declare them as `Prop` carriers in the `PortalFloor` discipline (never `axiom`), each with a
Forge/Collide-style non-vacuity refutation (a broken oracle where the carrier is provably FALSE),
matching `PortalFloor §9b`.

---

## 5. THE WIRING

### 5.1 Into `governed_holds` — DECO-UC as a realization against the adversary

Register `F_attestation` unforgeability as a `GovernedDynamics` instance (the schema at
`Metatheory/Adversary/Schema.lean:65`, consumed by `governed_holds`, `:82`):

```
attestationDynamics … : GovernedDynamics
  Control   := Statement Dg × Proof         -- the (stmt, proof) the prover presents
  run c     := c
  accept c  := K.verify c.1 c.2 = true      -- (∧ the named carriers, folded like WitnessDecodes)
  invariant c := Authenticated c.1           -- F_attestation emitted this
  holds     := deco_attestation_unforgeable  -- the §2a game-based realization theorem
```

Then `governed_holds attestationDynamics (stmt, proof) hacc : Authenticated stmt` — DECO-UC as a
`governed_holds` application against the ONE `Adversary` (`Metatheory/Adversary/Model.lean:73`).
This is the poster's **rung 4** ("realizes the ideal against A", above rung 3 "holds against A"):
the malicious prover surface `A.forgedPI`/`A.forgedProof` (`Model.lean:86-89`) cannot forge an
accepting DECO attestation whose session did not happen.

**Distinguish from the existing `decoCarrierDynamics` (`Instances.lean:483`) — they compose, they
do not overlap:**
- `decoCarrierDynamics` = "the mint's published `payment_hash` is BACKED by a verifying DECO
  sub-proof" (the fold-binding, `deco_backing_from_fold`).
- `attestationDynamics` (NEW) = "a verifying DECO sub-proof MEANS a genuine Stripe session"
  (the unforgeability beneath it).
- Composed: `attestation-unforgeability ∘ carrier-backing` = *the mint credited real money* — the
  two legs `DecoBackingAttack.lean` (`deployed_admits_unbacked_deco`) shows are BOTH needed. This
  plan supplies the second, which the deployed row does not force.

Fold `attestationDynamics` into the marquee `assurance_case_governed` (`Instances.lean:639`) as an
Nth instance once built.

### 5.2 Into zkOracle's `authentic` leg

Swap `zkOracle_sound`'s first conjunct (`ZkOracle.lean:81`, delivered by `deco_verify_sound` at
`:84`) from `∃ w, DecoRelation … decoStmt w` to `Authenticated decoStmt`, delivered by
`deco_attestation_unforgeable` (as `AttRealizes`). The authentic leg becomes "a genuine Stripe
session produced these facts." **Coordinated change in the other Fable's lane — named here, not
made.** The realization theorem is shaped as a drop-in (`verify … = true → <authentic>`).

### 5.3 Into the non-vacuity gate

Register ONE new row in `docs/audit/NON-VACUITY-MANIFEST.md` (the ledger, gated by
`circuit/tests/security_property_nonvacuity_gate.rs`):

- **theorem** — `deco_attestation_unforgeable` (the §2a game-based realization).
- **fires** — a genuine attestation IS `Authenticated`: reuse `reference_authenticates_payment`
  (`Deco.lean:532`) — an accepting reference proof yields the genuine payment binding.
- **bites** — a FORGED attestation the reduction REJECTS: a DECO kernel whose sig/mac oracle
  accepts everything (a `Deco`-flavored `PortalFloor.instSignatureForge`, `PortalFloor.lean:472`)
  over which `AttForgery` concretely exists and `Authenticated` is FALSE — modelled exactly on
  `Ed25519Reduction.forge_all_surfaces` (`Ed25519Reduction.lean:297`) and `forge_not_eufCma`
  (`:275`). This is the two-valued proof: strip the carrier and a concrete payment forgery appears.

The gate is a static ledger row (Lean theorems are not reflectively enumerable from Rust); the
in-band `#assert_axioms` on the new theorems keeps it honest.

---

## 6. THE ORDERED BUILD PLAN (recommended rung: game-based first)

Each step names **reused** (existing, grounded) vs **new**.

**Step 1 — `Dregg2/Crypto/DecoUnforgeable.lean` (the game-based rung).** ~200-300 lines.
- *Reuse:* `Deco.DecoRelation`/`deco_verify_sound`/`deco_binds_payment`/`deco_commitment_binds`
  (`Deco.lean:103/:296/:228/:249`); the whole `Ed25519Reduction.lean` template (`SigForgery`,
  `Ed25519EufCma`, `eufCma_iff_sound:81`, `protocol_forgery_to_sig_forgery:239`,
  `eufCma_repels_all_surfaces:246`, the `forge_*` teeth `:275-299`); the `LightClientUC`
  game shape (`Foolable:97`/`Unfoolable:105`/`unfoolable_iff_not_foolable:111`).
- *New:* `Authenticated` (the §1.1 decomposition — literally `deco_authenticates_payment`'s
  conclusion, `Deco.lean:320-328`), `AttForgery`/`AttUnforgeable`/`AttRealizes`; the **HMAC
  forgery** predicate (`MacKernelE` analog of `SigForgery`, ~10 lines); the **4-way reduction**
  `AttForgery → (SigForgery ∨ MacForgery ∨ Poseidon2Collision ∨ ¬extractable)` and its
  contrapositive `deco_attestation_unforgeable`; the non-vacuity teeth over a forge kernel.
- *Gate:* `#assert_axioms` ⊆ `{propext, Classical.choice, Quot.sound}` on every load-bearing arm,
  the `Ed25519Reduction.lean:307-324` discipline.

**Step 2 — the `governed_holds` instance.** ~40 lines, in the `Adversary/Instances.lean:483` style.
- *Reuse:* `GovernedDynamics`/`governed_holds` (`Schema.lean:65/:82`); the `decoCarrierDynamics`
  layout (`Instances.lean:483`) as the sibling shape; `WitnessDecodes`-style faithful folding of
  the carriers into `accept` (`Schema.lean:130`).
- *New:* `attestationDynamics`, `deco_attestation_via_schema`, `attestation_bites`; the §5.1
  composition note distinguishing it from `decoCarrierDynamics`.

**Step 3 — the manifest row + coordinated zkOracle note.** ~docs only.
- *Reuse:* `reference_authenticates_payment` (`Deco.lean:532`) as *fires*; the forge kernel as
  *bites*; the manifest format (`NON-VACUITY-MANIFEST.md` ledger).
- *New:* one ledger row; a tracked note of the `ZkOracle.lean:84` drop-in swap (§5.2), NOT applied.

**Then (the summit, separately scoped) — the computational UC path (b-ii):**

**Step 4 — `F_attestation` in the CryptHOL harness.** ~1 week.
- *Reuse:* `~/dev/breadstuffs/uc-crypthol/Dregg2_FCom.thy` (`dregg2_pedersen_realizes_F_com`) as
  the mechanization template; `PerfectZK.sim`/`hperf` (`PerfectZK.lean:67-72`) as the simulator's
  perfect corner; the §2a game as the soundness half.
- *New:* the `F_attestation` functionality + simulator in CryptHOL; the negligible-advantage bound;
  the two ZK carriers (`StarkZK`, `DecoHandshakeSimulatable`) declared `PortalFloor`-style with
  Forge/Collide refutations; the `UCBridge.lean`-style bridge recording the discharge back into the
  Lean tree.

---

## 7. SIZE ESTIMATE

| Rung | Size | Path | Grounded reuse |
|---|---|---|---|
| **Game-based unforgeability (a)** | **SMALL** (~1-2 days, ~300 Lean lines + instance + manifest row) | one new Lean file, `Ed25519Reduction` template near-verbatim + a 4-way case split over `deco_binds_payment` | `Ed25519Reduction.lean`, `LightClientUC.lean`, `Deco.lean` capstone stack |
| **Full computational UC (b)** | **MEDIUM** via CryptHOL (b-ii, ~1 week given the harness) / **LARGE** via greenfield Lean model (b-i, Pillar-1, 2-4 weeks) | mechanize `F_attestation` realization alongside `F_com`; bridge back | `uc-crypthol/Dregg2_FCom.thy`, `UCBridge.lean`, `PerfectZK.lean`, and (a) as the soundness half |

**The through-line.** (a) closes survey gap #1 cheaply and honestly — turning "DECO authenticity
ASSUMED" into "a payment forgery IS an ed25519/HMAC/CR/FRI break" (proven-under-standard-assumptions,
`#assert_axioms`-clean, toothed), and lifting zkOracle's `authentic` leg from a satisfying-trace
refinement to an ideal-functionality emission. (b) is the summit — a genuine simulator/UC
realization — reachable through the already-bridged CryptHOL harness, resting on (a) as its
soundness half plus two standard, named ZK floors. Every ingredient is named and grounded; nothing
here is aspirational mathematics.
