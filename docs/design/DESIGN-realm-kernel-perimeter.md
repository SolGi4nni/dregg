# DESIGN — moving the realm gate to the kernel perimeter

**Status: DESIGN ONLY. Nothing in this document is implemented.** It is the
assessment `docs/design/MUD-SUBSTRATE.md` wiring items **1** and **2** asked
for, written against HEAD after the realm-model graduation (`feeb19e7cd`) and
the `/realm*` HTTP ingress. No kernel, `dregg_turn::Turn`, `proof_verify.rs`,
signing, or Lean file is edited by the lane that wrote this.

The two items, restated:

1. **The catalog gate moves into the executor**, not a standalone function. The
   realm's catalog cell becomes the authority the executor reads, and a turn's
   cited `ruleset_root` is checked for membership *before* the turn commits.
2. **`ruleset_root` becomes a real field of `dregg_turn::Turn`** (and of the
   receipt), so the executor can perform that check and the receipt can commit
   the root.

---

## §0 — The honest verdict up front

**This is not "add a field." It is four changes, and the field is the smallest
of them.** The load-bearing one is not on the wire at all:

> **The realm substrate's cells do not live on the kernel's ledger.**
> `realm_model::RealmWorld` owns a **private `dregg_cell::Ledger`**
> (`realm-model/src/world.rs:134` — `pub struct RealmWorld { ledger: Ledger, … }`,
> constructed by `RealmWorld::new()` at `:154`). The node's authoritative
> ledger is `NodeStateInner::ledger`, a completely disjoint object. The realm,
> instance, catalog, identity, and surface-binding cells exist ONLY in the
> private one.

An executor gate has to read the catalog off **the state it is executing
against**. In Lean that is literally the type: the verified admission predicate
is `admissible (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState) : Bool`
(`metatheory/Dregg2/Exec/Admission.lean:110`) and every leg reads `s.kernel`.
There is no way to write "the cited root is in the addressed realm's catalog"
as a leg of that predicate while the catalog cell is not in `s.kernel`.

So the real order of work is:

| # | change | size | risk |
|---|---|---|---|
| **A** | **Relocate the realm substrate onto the kernel ledger** — realm/instance/catalog/identity become cells the node's executor owns, birthed and mutated by real turns, persisted by the ordinary ledger/receipt-chain durability instead of `REALM_LOG` replay | **largest**; touches `realm-model`, `realm_service`, `persist` | high — it is the whole substrate's storage story |
| **B** | **`Turn` carries the realm context** (`ruleset_root` + the addressed instance) and the receipt commits it | medium (128 struct-literal sites, two hash-domain bumps) | medium — signing/commitment perimeter |
| **C** | **The gate becomes a leg of the Lean admission predicate** + its reason code + rejection theorem + re-proved keystone, surfaced through the FFI seam | medium | **highest soundness stakes** — it is a kernel refusal |
| **D** | **Rust `proof_verify` / `execute` mirrors the same refusal** so the non-FFI build is not weaker than the verified one | small | medium — a Rust-only gate is not verification |

Everything below is the detail. **Nothing here should be fired without ember
deciding §5.**

⚠ **Substrate note, said out loud (CLAUDE.md tripwire).** Change **C** is an
**admission-predicate** change. Admission in this project is **Lean-authored**
(`Dregg2/Exec/Admission.lean`, `Dregg2/Exec/AdmissionReason.lean`,
`Dregg2/Exec/AdmissionWire.lean`), with `turn/src/admission_reason.rs` as an
explicitly-labelled *pure mirror* of the Lean codes. **The new gate is written
in Lean.** It must not be hand-written as a Rust `if` in `proof_verify.rs` and
called "the gate"; the Rust side mirrors a Lean-authored decision, as it does
for all eleven existing gates. Item **D** exists only so the FFI-off build
fails closed the same way — it is not the authority.

---

## §1 — What exactly changes

### 1.1 `dregg_turn::Turn` (item 2)

`Turn` (`turn/src/turn.rs:291`) is a flat struct with no `Default` impl. The
addition:

```rust
/// The realm CONTEXT a turn acts in: which instance it addresses and which
/// body of law it cites. `None` for every turn that is not a realm turn.
#[serde(default)]
pub realm_context: Option<RealmContext>,

pub struct RealmContext {
    /// The instance cell the turn acts inside; its parent realm's catalog
    /// cell is the admission authority.
    pub instance: CellId,
    /// The 32-byte body of law the turn cites (§9.2). Must be listed in the
    /// addressed realm's catalog or the turn is inadmissible.
    pub ruleset_root: [u8; 32],
}
```

**One `Option<struct>` field, not two `Option<[u8;32]>` fields.** Two
independent options admit three nonsense states (root without instance,
instance without root, and — worst — a turn that cites law for one instance
while writing another). One option makes "a realm turn names both" a type-level
fact. This matters because the gate's *soundness* is the pairing: a
`ruleset_root` with no addressed realm has no catalog to check against, so it
would have to fail open or fail closed arbitrarily.

**Which realm?** The gate resolves `realm_context.instance` → its parent realm
→ that realm's catalog cell. The instance cell already commits its parent link
(`realm-model/src/instance.rs` — `Instance.realm`, and the pinned
`PARENT_PIN`). Putting the *realm* on the turn as well would let a caller name
a realm the instance does not belong to; deriving it from the instance cell
removes the choice. **The turn names the instance; the chain names the realm.**

### 1.2 The commitment / signing path (item 2's real cost)

Three hashes are affected, in this order:

**(a) `Turn::hash()` — `turn/src/turn.rs:406`, domain `b"dregg-turn-v3:"`.**
This is the content-address of the whole turn *and* the cipherclerk's signing
message: `Cipherclerk::compute_turn_bytes` (`sdk/src/cipherclerk.rs:4742`) is
literally `turn.hash()`. Adding a field to the hash therefore changes **every
signature preimage in the system**.

The precedent in this file is explicit and should be followed: v2→v3 was bumped
when the execution-proof bundle was added, *precisely so* a stale verifier
fails the signature check rather than silently comparing mismatched preimages.
The same applies here.

- **Do:** bump the domain to `b"dregg-turn-v4:"` and absorb the field
  unconditionally with a presence tag (`[0]` for `None`,
  `[1] ‖ instance ‖ ruleset_root` for `Some`), matching how `memo`,
  `valid_until`, `previous_receipt_hash`, and the execution-proof triple are
  already absorbed.
- **Do NOT** "preserve byte-identity for `None` turns" by appending nothing
  when the field is absent. dregg is greenfield and
  nothing is deployed, so that is a migration costume for a migration that does
  not exist — and it is *also* a real hazard:
  the preimage's tail becomes ambiguous, and an ambiguous preimage is a
  collision surface for exactly the signature that authorizes the turn. Bump
  the domain; it is what the domain tag is for.

**(b) `TurnReceipt::receipt_hash()` — `turn/src/turn.rs:964`, domain
`b"dregg-receipt-v5"`.** If the receipt commits the cited root (item 2 says it
should — "the receipt can commit the root"), this bumps to `v6`. The file
already documents the v4 and v5 bumps and their fencing rationale; a v6 note
should say the same thing about the realm context. Note the receipt already
carries `turn_hash`, so the root is *transitively* bound the moment (a) lands —
committing it directly is about **legibility** (a receipt reader can see the
law without the turn body), not about soundness. **That makes (b) optional and
separable from (a); recommend landing it, but it is not on the critical path.**

**(c) `Faithful8` / circuit public inputs.** If the cited root ever becomes a
public input of an AIR (the natural next step — `param-compose` already binds
`ruleset_root` as a PI at `param-compose/src/pi.rs:57`, **8 felts**, i.e. the
full ~124-bit digest), it must be carried at the **8-felt** width. Squeezing a
`ruleset_root` to one felt at an admission boundary is precisely the
felt-width wound class (`docs/WOUND-felt-width-boundaries-2026-07-19.md`): a
~31-bit lane is 2^15.5-collidable, so "the turn cited the law it proved" would
be forgeable by a laptop. **Nothing in this design puts the root in a circuit —
but the moment someone does, it is 8 felts.**

### 1.3 The gate's placement (item 1)

There are two candidate homes, and **they are not equivalent**:

**Candidate 1 — `proof_verify.rs` (what MUD-SUBSTRATE.md named).** The doc
points at the custom-effect dispatch: "a turn's cited `ruleset_root` must be
checked for membership in the addressed realm's catalog cell BEFORE the
custom-effect verifier is dispatched"
(`turn/src/executor/proof_verify.rs`, `enforce_custom_effect_proofs` at `:253`,
called from `verify_and_commit_proof` at `:184`).

That location is **too narrow**. `verify_and_commit_proof` runs only for
**proof-carrying sovereign turns** (a turn with `execution_proof: Some(..)`).
A realm turn today is a plain `SetField` forest with no execution proof, so a
gate there would never fire on the traffic it is meant to gate — a real gate pointed at a path the
traffic does not take. Put the gate only there and the honest description is "uncatalogued law is refused *for
proof-carrying sovereign realm turns*", which is currently the empty set.

**Candidate 2 — the admission predicate (recommended).** The gate belongs where
the other eleven fail-closed, theorem-backed gates live:

- Lean: `Dregg2.Exec.Admission.admissible`
  (`metatheory/Dregg2/Exec/Admission.lean:110`) gains a leg; `TurnHdr` (`:74`)
  gains the realm context; `Dregg2.Exec.AdmissionReason` gains
  `rulesetNotInCatalog` with `reasonCode` **12**
  (`metatheory/Dregg2/Exec/AdmissionReason.lean:258`).
- Rust mirror: `dregg_turn::AdmissionReason` (`turn/src/admission_reason.rs:20`)
  gains the matching variant/code, and
  `TurnExecutor::validate_without_apply` / `execute_*`
  (`turn/src/executor/execute.rs:1566`) refuse with
  `TurnError::AdmissionRefused { reason: RulesetNotInCatalog }`.

This gets three things Candidate 1 cannot:

1. it fires on **every** turn shape, not just proof-carrying ones;
2. it is refused **before** the fee prologue commits, so a turn citing
   uncatalogued law costs the author nothing and moves nothing — the same
   posture as the DoS cap in `enforce_custom_effect_proofs`;
3. it inherits the keystone `admissionReason_eq_admitted_iff`, so the reported
   reason **cannot lie** about whether the turn was admitted.

**Recommendation: Candidate 2, with Candidate 1 as an additional (not
alternative) tooth** if and when realm turns become proof-carrying — the
catalog check before custom-effect dispatch is a good belt to that suspenders,
and it is cheap once the field exists.

### 1.4 What the gate actually reads (this is item A, and it is the hard part)

The leg, in words: *the cell named by `realm_context.instance` is a live
instance; its parent realm's catalog cell's committed extended-field map
contains `key(ruleset_root) ↦ ruleset_root`.*

The membership test is already non-vacuous and already the right shape
(`realm-model/src/world.rs:467` `is_listed`, and
`realm-model/src/catalog.rs`): the stored **value** is the full 32-byte root,
so `get(key(C)) == Some(C)` is a full-width equality, not an 8-byte-key
coincidence. Unlisting writes zero, which no real root equals. **Keep that
exact discipline when it moves** — the guardian set uses the same pattern
(`realm-model/src/identity.rs::guardian_ext_key`), and it is the reason the
catalog is not a "named carrier."

But every one of those reads is against `RealmWorld`'s **private ledger**. For
the gate to read them from `s.kernel` / the executor's `Ledger`, the substrate
has to move:

- realm cell, catalog cell, instance cell, identity cell, surface-binding cell
  become cells on the node's authoritative ledger;
- `create_realm` / `open_instance` / `list_ruleset` / `settle_instance` /
  `mint_identity` / `bind_surface` become **real turns** through the node's
  executor (they are already just `SetField`/create shapes), instead of direct
  `Ledger::update_with` calls (`realm-model/src/world.rs:200`);
- the durable `REALM_LOG` (`persist/src/tables.rs:303`) and
  `NodeRealms::restore`'s replay **go away**, replaced by the ordinary ledger
  snapshot + receipt-chain durability the keystone already provides. That is a
  *simplification* — one durability story instead of two — but it is a rewrite
  of `node/src/realm_service.rs`'s entire persistence half, and it retires the
  restart canary in its current form.

**This is why §0 says the field is the smallest of the four changes.**

---

## §2 — What BREAKS

### 2.1 Every `Turn` struct literal

`Turn` has **no `Default` impl**, so a new field breaks every struct-literal
construction. Measured at HEAD with `ast-grep` (pattern `Turn { $$$ }`,
filtered to literals carrying both `agent:` and `call_forest:`):

**128 sites across 16 crates** — `turn` 59, `node` 19, `sdk` 18, `demo` 4,
`circuit` 4, `exec-lean` 4, `tests` 3, `redteam` 3, `demo-agent` 3, `teasting`
3, `coord` 2, `intent` 2, and one each in `protocol-tests`, `sel4`,
`circuit-prove`, `dregg-sdk-net`.

Two ways to absorb this, and the choice is real:

- **`#[derive(Default)]` on `Turn` + `..Default::default()` at the 128 sites.**
  Mechanical, but it makes "a turn with no agent, no forest, zero fee" a
  constructible value, which is a footgun on a signed-turn type.
- **Add the field to all 128 literals (`realm_context: None`).** Also
  mechanical, noisier in the diff, and keeps `Turn` un-defaultable.
  **Recommended** — the type should not gain a silent empty value to save a
  sed.

The **278** `TurnBuilder::new` sites are unaffected: `TurnBuilder::build`
(`turn/src/builder.rs:346`) is the single literal that fills the field, plus a
`realm_context(..)` setter alongside `previous_receipt_hash(..)`.

### 2.2 Signature / commitment compatibility

- Every existing signature over a `Turn::hash()` becomes invalid the moment the
  v4 domain lands. **This is fine and it is not a migration problem**: dregg is
  greenfield, nothing is deployed, and the devnet's ledgers are tempdirs and
  hand-run data dirs. There are **no** frozen golden turn-hash vectors — the
  only two files that mention `dregg-turn-v3` are `turn/src/turn.rs` and
  `sdk/src/cipherclerk.rs`. Do **not** build a dual-hash / flag-day /
  byte-identity path; delete v3 and move.
- **Persisted receipt chains in existing data dirs become unverifiable** under
  a v6 receipt domain (`cclerk.verify_own_chain()` is asserted in the node's
  restart tests). That is a data-dir reset, not a code path. Name it in the
  commit; do not write a converter.
- **The Lean↔Rust wire codes must move together.** `AdmissionReason` code 12
  has to be added on both sides in the same change, or
  `AdmissionReason::from_code` starts returning `None` for a real refusal and
  the veto path loses the reason. The Lean side already proves
  `reasonCode_injective_on_tags`; that theorem must be re-checked with the
  twelfth constructor.

### 2.3 The fee / estimate path

`TurnExecutor::estimate_cost` (`turn/src/executor/execute.rs:1556`) walks only
the call forest, so the field costs nothing there. But
**`validate_without_apply` (`:1566`) is the admit-without-applying entry —
pre-checks, mempool, fee estimation** — and its own comments already flag the
danger: a validate↔execute divergence *in the dangerous direction* (validate
accepts what apply refuses) was a real bug that got the agent-lifecycle gate
added there.

**So the realm gate must be added to `validate_without_apply` in the same
change as the executor**, or the mempool will admit and quote a fee for turns
the executor will refuse. That is the single most likely way to ship this
half-done.

Second-order: because the gate is an **admission** refusal, an uncatalogued
turn is rejected *before* `commitPrologue` debits the fee
(`commitPrologue`, `Dregg2/Exec/Admission.lean:253`). That is the desired economics (a refused
turn pays nothing), but it also means the gate is **free to probe**. If catalog
membership is ever privacy-relevant, the free-probe property is the thing to
think about — today it is not (the catalog is public committed law).

### 2.4 Things that do NOT break

- `param-compose`'s `ruleset_root` PI (`param-compose/src/pi.rs:57`) is
  independent and already the right width; the catalog says *which roots are
  law*, the VK proves *a turn obeyed that exact root*. They compose, they do
  not collide.
- The `/realm*` HTTP ingress and `NodeRealms` keep working throughout stages
  1–2 below; they are the thing being *replaced* at stage 4, not broken by
  stages 1–3.
- `Turn::hash` consumers that treat the hash as opaque (the receipt chain, the
  MMR index, `depends_on`) are value-agnostic.

---

## §3 — The smallest safe staging

Five stages. **Each is independently landable and independently green.** The
kernel refusal does not become authoritative until stage 3.

**Stage 0 — decide §5.** No code. The three questions below are genuinely
ember's; two of them change the shape of the `Turn` field.

**Stage 1 — the envelope, inert.** Add `RealmContext` + `Turn.realm_context`,
bump `Turn::hash` to `dregg-turn-v4:`, add the `TurnBuilder` setter, fix the
128 literals. **No gate anywhere.** The field is carried, signed, and ignored.
Green criterion: the whole tree builds and every existing turn test passes with
the new domain (they will, because none of them pin a hash *value*).

**Stage 2 — the substrate moves onto the kernel ledger (item A).** Realm /
instance / catalog / identity / binding cells become cells the node's executor
owns; the lifecycle ops become real turns; `REALM_LOG` replay is retired in
favour of the ordinary ledger durability. **This is the big one and it deserves
its own design pass** — in particular *who* is authorized to list a root
becomes a real `set_state` authority question the moment the catalog cell is on
the shared ledger (today `list_ruleset` is an unauthenticated model method; see
§5.3). Green criterion: the existing restart canary's *properties* survive in
their new form (a realm created through the node survives a restart; an
uncatalogued root is refused), driven, not asserted.

**Stage 3 — the gate, in Lean, behind the shadow veto.** Add the leg to
`admissible`, the `rulesetNotInCatalog` reason (code 12), the rejection theorem
(`admissible_rejects_uncatalogued_ruleset`, in the shape of the eleven at
`Admission.lean:140-232`), re-prove `admissionReason_eq_admitted_iff` and
`reasonCode_injective_on_tags`, and extend `AdmissionWire`/`FFI` to carry the
realm context in `TurnHdr`.

**Then enforce it through the existing strict-veto path before writing a single
Rust `if`.** `turn/src/shadow.rs` already has exactly the right primitive: the
verified verdict can **VETO** a Rust commit, and the veto is documented as
*one-directional* — `lean=false ∧ rust=true` only, it "can only TIGHTEN the
decision (never launder a Rust rejection to a commit)"
(`turn/src/error.rs:134`). A new Lean-side refusal is therefore *exactly* the
case the veto was built for. Running the gate as a Lean veto first means the
kernel refusal is live and authoritative **while the only place the rule is
authored is Lean** — which is the substrate discipline, not a compromise of it.

**Stage 4 — the Rust mirror + `validate_without_apply`.** Add the refusal to
the Rust admission path so the FFI-off build fails closed identically, and to
`validate_without_apply` so the mempool agrees with the executor (§2.3). The
gate to land this: a **differential** test that the Rust refusal and the Lean
verdict agree on a matrix of (listed / unlisted / unlisted-then-listed /
listed-then-unlisted) × (realm turn / non-realm turn) — not two independent
unit tests that each pass.

**Stage 5 — retire the ingress's private substrate.** `NodeRealms` becomes a
thin projection over the kernel ledger; `/realm*` keeps its routes and loses its
private world. **Delete the superseded object; do not land the new one beside
it.**

---

## §4 — The falsifiers (what makes each stage real, not asserted)

Written here so a future lane cannot claim a stage without them.

- **Stage 1:** flip one byte of a `Turn`'s `ruleset_root` and its `hash()` must
  change; a signature over the pre-flip turn must fail on the post-flip turn.
  (Otherwise the field is not bound and the whole design is decorative.)
- **Stage 2:** the catalog cell read by the *executor's* ledger must be the
  same object the ingress writes — assert by listing a root through `/realm`
  and reading it back through a plain ledger cell read, not through
  `RealmWorld`.
- **Stage 3:** the Lean rejection theorem must exhibit a turn violating
  **exactly** this leg (the shape at `Admission.lean:140`), so the gate is not
  vacuously implied by another leg. And: a turn citing an uncatalogued root
  must be vetoed **with** `reasonCode 12`, not merely rejected.
- **Stage 3 canary (the one that matters):** **unlist a root and the SAME turn
  that was admitted must now be refused by the kernel.** This is the exact
  canary realm-model already runs (`catalog_is_committed_law`) and the ingress
  now runs over HTTP
  (`unlisting_law_over_http_refuses_the_same_turn_that_was_admitted`); at the
  kernel perimeter it proves the gate reads **live committed state**, not a
  boot-time snapshot or a host-config set.
- **Stage 4:** the differential matrix above, plus: with `DREGG_LEAN_SHADOW`
  off, an uncatalogued turn is still refused (the FFI-off build is not weaker).

---

## §5 — The decisions that are ember's

These are not implementation details; each changes the object.

### 5.1 Is the realm gate an ADMISSION gate or an EFFECT gate?

Admission (recommended) means: an uncatalogued root makes the **whole turn**
inadmissible, before the fee prologue, cost-free to the author, refused with a
theorem-backed reason. Effect-level means: the turn is admitted and each effect
that touches the realm is refused individually, so a mixed turn partially
applies.

Admission is simpler and matches how realm-model already behaves (a refused
`RealmTurn` mutates nothing). It also makes the gate **free to probe** (§2.3).
Effect-level would let a turn touch a realm and something else atomically —
which is either a feature (cross-realm composition) or a hole, depending on
what you want realms to be. **This choice determines whether a turn can address
more than one realm.**

### 5.2 What does a turn with `realm_context: None` that writes a realm cell do?

Two coherent answers:

- **Realm cells are ordinary cells** — a `None` turn writing one is admitted,
  and the catalog only gates turns that *claim* to be realm turns. This is
  fail-**open** and makes the catalog advisory: an attacker just omits the
  context. **Do not ship this.**
- **A cell that is part of a realm can only be written by a turn that names its
  realm context** — i.e. the *cell* carries the requirement, the turn carries
  the claim. This is fail-closed and is the same shape as the instance-scope
  membrane realm-model already enforces (`Refused::OutsideInstanceScope`,
  `realm-model/src/world.rs`).

The second requires the executor to know, per cell, "this is realm-governed" —
a marker on the cell (a program VK, a lifecycle flag, or membership in the
realm's own committed set). **This is the actual soundness question of the
whole design**, and it does not exist yet in any form.

### 5.3 Who may list a root?

Today `list_ruleset` is an unauthenticated method on the model
(`realm-model/src/world.rs:433`). The moment the catalog cell is on the shared
kernel ledger (stage 2), "who may append a root" becomes a real capability
question with real consequences — the answer *is* who writes the law. §9.2 of
`HOARDLIGHT-LIVING-WORLD.md` already asks for activation height/time, catalog
inclusion proofs, deprecation-without-deletion, and emergency refusal;
MUD-SUBSTRATE.md records catalog governance as **still ember's call**. The
shipped guardian-rotation weld (`sdk/src/guardian_rotation.rs`,
`install_guardian_council_authority`) is the production shape for a guarded
slot and is the natural model.

**Stage 2 cannot land without an answer**, because putting an ungoverned
catalog cell on the authoritative ledger is strictly worse than the current
private one.

### 5.4 (smaller) Does the receipt commit the root directly?

Recommended yes, for legibility; it is already transitively bound via
`turn_hash`, so this is a `dregg-receipt-v6` bump for readability, not
soundness. Separable from everything else.

---

## §6 — What this design does NOT claim

- It does **not** claim the realm gate becomes *proven* by moving to the kernel.
  Stage 3 gives it a Lean-authored predicate with rejection theorems and a
  faithful reason code. That is the same standing as the other eleven admission
  gates — real, machine-checked, and **still sitting on the undischarged
  FRI/STARK floor** for anything that claims a *proof* was verified. Admission is a state predicate, not a proof check; it
  inherits nothing from the prover and grants nothing to it.
- It does **not** claim any of this is required for the `/realm*` ingress to be
  useful. The ingress is a node-hosted, durable, gate-routed admission today.
  What it is **not** — and what this design would make it — is a refusal the
  *kernel* enforces on a *signed* turn.
- It does **not** propose translation validation between a Rust gate and the
  Lean predicate. There is no formal semantics of Rust; the Rust mirror in stage
  4 is a mirror, checked by differential testing, and must be described that way.
