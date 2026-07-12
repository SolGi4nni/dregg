# The Cleaner Design Latent in dregg/DreggNet — a synthesis

Status: **design synthesis** (2026-07-12), from five grounded ideators (session/tenancy · confined-execution ·
surface/presentation · Lean-metatheory/verification · whole-system), each reading the real source (crates + Lean).
This is proposal-only — a map of the clean design *already present* in what's built, and the smallest moves toward it.
No rewrite; consolidation of the unverified application layer onto the verified core (REORIENT correspondence law, in
the right direction).

## 1. The thesis (what all five found)

The verified core is four words — **Cell · Capability · Turn · Receipt** (`docs/OVERVIEW.md`). Everything built *above*
it — hosting, agents, grains, offerings, surfaces, metering — is reaching for **two more primitives it has not named**,
and pays for that by re-implementing each a dozen times under a dozen names:

- **Session** = the cap-attenuated **WRITE** projection of a cell for an actor (actions → turns → a receipt chain).
- **Surface** = the cap-attenuated **READ** projection of a cell for a viewer (state → affordances → an interaction
  log, which is *also* a receipt chain).

**They are DUAL** — the same `cell::Membrane` (the *already-verified* non-amplification boundary, `cell/src/
membrane.rs:153`) projected per-principal, at the two ends of a cell; both leave `TurnReceipt`s. And:

> **An `Offering` is exactly `Session × Surface`.** `dreggnet-offerings::Offering` *already spells this out* —
> `advance`=Session, `render`/`actions`=Surface, `price`=Meter, `verify`=Receipt (`dreggnet-offerings/src/lib.rs:368`).
> It just wasn't recognized as a substrate primitive.

The core-concept set the whole system is reaching for is **six**: Cell, Capability, Turn, Receipt (clean, exist) +
**Session, Surface** (latent, scattered).

## 2. The convergent diagnosis (same pattern, five dimensions)

Every lens found the *same* shape: **the presentation layer we just built is the genuinely-new part; everything below
it already exists — proven — and was reinvented thinner.** With receipts:

- **Session (tenancy):** ~24 `Session` structs (two `HermesSession`, two `DungeonSession`); 3 `LeaseTerms`; the metered
  hosting relationship implemented at 3 altitudes at once (`HostedLease`⊃`dregg_agent::Session`⊃`agent_platform::
  Tenant`). The hermes/grain offerings re-implemented the session `agent-platform` already rents/drives/settles/lands/
  resumes — with a **mock brain default** while `deos-hermes::ResidentBrain` is a real one.
- **Confinement:** the name `Confinement` is **4 unrelated types on 3 axes** (authority/ambient/proof); ~6 meters; 125
  `*Receipt`/`*Attestation` structs; the gate re-implemented per crate.
- **Verification:** **4 ladders** (spween replay · `Offering::verify`+`RecordVerify` · grain R0–R3 · light-client) all
  re-expressing the same 4 ideas against the same `TurnReceipt` / same root (`post_state_hash = recStateCommit`).
- **Surface:** the new frontends wrote renderers *outside* `deos-view` (duplicating+subsetting its `web`/`discord`
  backends); the cap-gated `AffordanceSurface` (real `is_attenuation`, real `Effect`, **Lean-proven**) never became a
  `ViewNode` producer — so there are 2 affordance types + 2 Discord custom-id schemes.

The Lean **proves the clean design is sound**: `attenuate_le` (attenuation only descends, `CredentialAttenuation.lean`),
`only_connectivity_begets_connectivity` (authority non-forgeability, `Authority.lean`), `execFullForestG_iff_turnSpecG`
+ anti-ghost (the whole-turn triangle, `WholeTurnTriangle.lean`), `project∘step = step∘project` (`Deos/Rerender.lean` —
one render engine correct on every backend), `tool_invocation_commit_iff_admit` (`ToolAccessDelegation.lean`),
`settlement_soundness`. The primitives are *already the proven objects*; they're just unnamed and re-derived.

## 3. The unified architecture

```
  VERIFIED SPINE (exists, keep, don't move):
      cell · turn(TurnExecutor) · capability(c-list cap-root; macaroon/biscuit/sturdyref = ENCODINGS of it) ·
      dregg-payable(Effect::Transfer, per-asset Σδ=0)
                       │
        ┌──────────────┴───────────────┐
   dregg-session (WRITE)           dregg-surface (READ)      ← the two new named primitives
   a cell::Membrane per actor      a cell::Membrane per viewer   both leave TurnReceipt chains
   • Confinement (ONE product      • AffordanceSurface (ONE
     lattice: authority·ambient·     cap-gated set; Lean Deos)
     proof)                        • lower() → ViewNode (IR)
   • Brain (ONE seam: AgentBrain)  • SurfaceBackend ×N
   • Meter (ONE: a StateConstraint   (gpui/html/discord/telegram/
     caveat on a monotone slot)      leptos/rgba)
   • Lease  (ONE: LeaseTerms)
                       │
        Offering  =  Session × Surface + price + verify        ← a substrate primitive
                       │
        Frontend impls (discord/telegram/web/cockpit) = a SurfaceBackend + a thin transport adapter
```

**Cross-cutting unifications (each already proven, just unnamed):**
- **Confinement = one product lattice** `{authority: Mandate, ambient: Jail, proof: Rung}` — the 3 orthogonal
  attenuate-only axes. One `Referee::admit(&Confinement, &Action)` = `deleg_admit` ⊕ the executor's 3 teeth (cap /
  StateConstraint / meter) ⊕ the jail check. Fork/delegate must descend the product `≼` (proven once).
- **Verification = one `TurnLadder`** — 4 rungs (0 tamper-evident · 1 replay-sound · 2 attested · 3 unfoolable), each
  strictly including the one below, all vouching for the same root. A domain supplies (a) a receipt chain, (b) a seed
  re-driver, (c) a leg-minter; the shared ladder names the rung it reaches. `RecordVerify` collapses into rung-1 replay.
- **Render = one `AffordanceSurface` → project_for(viewer) → lower → `ViewNode` → `SurfaceBackend`×N.** `Action.enabled`
  everywhere becomes the **real `is_attenuation` frustum**, not room logic. `telegram`/`web` renderers move *into*
  `deos-view` as backends; a `Frontend` becomes "a `SurfaceBackend` + a transport adapter."
- **Meter = one** (a monotone counter slot bounded by a `StateConstraint`, checked by executor tooth #2 — R2 already
  proved this collapse); `dregg_pay::CreditLedger` becomes *backed by* `Effect::Transfer` (its own stated endgame).
- **Receipt = one** — `TurnReceipt`; the 125 `*Receipt`/`*Attestation` become typed **lenses** over it, indexed by the
  proof `Rung`.

## 4. The enlightenment (emergent capabilities)

- **Fork-a-live-confined-session for free** — currently a named open gap (fork lives on `grain-fork`, drive on
  `agent-platform`); one Session closes it.
- **Reads and writes become one auditable stream** — a Surface's interaction log and a Session's turn chain are the
  *same* `TurnReceipt` object → every *view* is as attestable as every *action* (the "verifiable web" thesis's missing
  half).
- **Paywalled content = rented compute** — a 402-metered read Surface and a leased write Session share one Membrane +
  one `Effect::Transfer` meter.
- **Every offering, on every frontend, by construction** — confine/meter/verify/render are shared; Frontends are thin.
- **Defense-in-depth becomes multiplication, not prose** — an escape must break a proven authority lattice AND an OS
  boundary AND forge a STARK; three individually-proven walls typed as one `Confinement` value; the confinement point
  travels with the receipt.
- **One confinement-proof + one verification-ladder any offering inherits** — hermes / a rented grain / a `.spk` / a
  dungeon NPC each get `attenuate_le`, `confined_cannot_debit_attacker`, `tool_invocation_commit_iff_admit`,
  `settlement_soundness`, and the 4-rung ladder — re-wiring nothing.
- **The token thread closes** — name the c-list cap-tree as ground truth; macaroon/biscuit/sturdyref are its encodings
  (bridged by `derive_cell_macaroon_secret`).

## 5. The smallest first moves (staged-additive, each independently green — no rewrite)

Ordered by leverage-per-effort. Each consolidates onto something that already exists.

1. **Collapse the 3 `LeaseTerms`** (cheapest, highest-leverage). `hosted-lease` exists *only* to reconcile two
   encodings (`exec_terms_of`). Pick `execution-lease::LeaseTerms` canonical; prepaid + `grain-commons::ListingTerms`
   project *to* it; delete the alias layer. ~one afternoon; removes a crate's reason to exist.
2. **Disambiguate `Confinement` by axis** (mechanical rename, no semantics): firmament `Confinement→Jail`; grain-fork
   `Confinement→EgressDoors`; dreggnet-hermes `Confinement→AuthorityProfile`; dregg-agent `Confinement→HostFloor`.
   Then introduce `struct Confinement{authority, ambient, proof}` with the product `≼` proven monotone once.
3. **Name Session** — promote `AgentBrain` + the `TurnReceipt` chain into a `dregg-session` primitive; make
   `dregg_agent::Session`, `agent_platform::Tenant`, `grain_fork::ConfinedSession` alias/re-export it. Make
   **`dreggnet-hermes` depend on `deos-hermes`** (real `ResidentBrain`) instead of re-deriving it; drop the mock-brain
   default. Refactor `dreggnet-hermes`/`dreggnet-grain` offerings to *present over* `agent-platform::Tenant`
   (`open=rent`, `advance=drive_minted`, `verify=verify_r2/landed`).
4. **One `AffordanceSurface` → `ViewNode` → `SurfaceBackend`** — extract a `SurfaceBackend` trait in `deos-view` over the
   existing native/web/discord backends; move `telegram`/`web` renderers *into* `deos-view`; delete
   `dreggnet-web::view_html`; introduce `lower(surface, template, viewer)` so `enabled` = the real cap frustum; collapse
   the 2 Discord custom-id schemes to one.
5. **One `TurnLadder`** — fold the 4 verification ladders into one rung-typed report/error; define `verify` at every
   rung as re-run-the-referee / verify-a-proof-of-the-referee; `Action.enabled` computed from the *very gate* the
   executor enforces.
6. **One `Referee` + one `ReceiptChain` trait** — route the 4 per-crate gates through `Referee::admit`; retype the
   `*Receipt`/`*Attestation` family as lenses over `TurnReceipt` indexed by `Rung`.
7. **Recognize `Offering` as the hosting primitive** (`Session × Surface`) — where moves #3 + #4 meet, and the
   enlightenment becomes load-bearing.

## 6. Honest scope

This is **consolidation, not a rewrite** — the verified spine does not move; every load-bearing guarantee already
exists and is `#assert_axioms`/`#print axioms`-clean in the Lean cited above. The residual seams stay **explicit and
few** (they get *localized*, not hidden): `AuthPortal.soundness` (ed25519/seL4 floor), FRI `recursive_sound` (`hrec`),
cross-cell `Σ_node δ = 0`, the `WHOLE_HISTORY_GAP` (mint each turn's rotated wide-anchored EffectVM leg), and the
ConcreteKernel refinement's honest 2-hot-path scope (extend the commuting squares to the remaining effect families).
The work is *naming the two dual primitives (Session, Surface), composing the three confinement axes into one lattice,
folding four verification ladders into one, and routing every offering through one referee + one receipt + one surface
pipeline* — all onto objects the tree already runs, and the Lean already proves.
