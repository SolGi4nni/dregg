# The Hatchery Abstraction-Mint — an OPEN vocabulary of verified cell-kinds

*From a fixed vocabulary of kernel cell-shapes to an open vocabulary of
user-minted, invariant-carrying KINDS the kernel enforces as first-class.*

The implementation is `sdk/src/hatchery_mint.rs`. This document grounds the
weld it performs and names the slice that remains.

---

## 0. What this is

The kernel does not ship a closed set of "cell types." A cell is whatever its
installed `CellProgram` says it is, and the executor re-evaluates that program
on every state-modifying turn (`turn/src/executor/execute_tree.rs`, via
`CellProgram::evaluate_with_meta`). So the substrate for an *open* vocabulary
is already present — what was missing is the act of **minting**: letting a user
define a new cell-KIND with its own invariant, attest the invariant once, and
have the kernel hold every cell of that kind to it forever.

The abstraction-mint is that act. A `MintedKind` is a verified constructor: a
content-addressed factory whose children all carry — and are forever held to —
one declared invariant.

---

## 1. The two pieces being welded (both already exist)

### The EROS factory — `cell/src/factory.rs`

A `FactoryDescriptor` is a content-addressed, inspectable constructor contract.
Its `state_constraints: Vec<StateConstraint>` field is the load-bearing one
here: per `SLOT-CAVEATS-DESIGN.md` (Lane G), these are the **perpetual** slot
caveats baked into the `CellProgram` of *every* cell the factory produces. The
executor evaluates them on every turn, not just at creation — giving lifetime
invariants (`Monotonic`, `FieldGte`, `WriteOnce`, `FieldDelta`, …). The
descriptor's content hash absorbs `state_constraints`, so the invariant is part
of the constructor's identity: it cannot be silently changed without changing
the factory.

> The factory already does the "born carrying a program-for-life" half. What it
> does *not* carry is an attestation that the baked-in invariant actually
> **holds** as a single-step preservation — and the detector that a cell
> *claiming* the kind genuinely conforms.

### The Hatchery — `HATCHERY.md`, `metatheory/Dregg2/Verify/Contract.lean`

The Hatchery's thesis (`HATCHERY.md` §0) is one extraordinarily reusable
theorem, `Dregg2.Exec.CellCarry.livingCellA_carries` (`CellCarry.lean:57`):

```lean
theorem livingCellA_carries (Good : RecChainedState → Prop)
    (hpres : ∀ s cf, Good s → Good (cellNextA s cf))   -- prove it for ONE step
    (s : RecChainedState) (hinit : Good s) (sched : SchedA) :
    ∀ n, Good (trajA s sched n)                         -- get it for ALL time, ANY adversary
```

The author's *entire* obligation is `hpres` — a single-step preservation. The
coalgebra hands back unbounded-time, every-schedule safety for free. Tier 3
packages this into a first-class value, `Dregg2.Verify.Contract.CellContract`,
whose sole field-obligation is `step_ob : ∀ s c, Inv s → Inv (E.next s c)` and
whose `forever`/`always` derivations are the payoff, free for every contract.

---

## 2. The weld — `MintedKind`

A minted kind is exactly the pairing those two halves were waiting for:

```
MintedKind = a FactoryDescriptor whose state_constraints ARE the invariant
           + the structured Invariant the author declared
           + an HpresProof slot — the attestation the invariant HOLDS
```

| Half | Supplies | In `MintedKind` |
|---|---|---|
| EROS factory | the cell is **born carrying** the invariant as its program-for-life; the executor **enforces** it forever | `descriptor.state_constraints` + `child_program` |
| Hatchery hpres | the attestation the invariant is a **genuine single-step invariant** → "holds forever, any adversary" | `hpres: HpresProof` |

`MintedKind::mint(invariant, mint_authority)`:

1. lowers the declared `Invariant` to its `StateConstraint` set;
2. builds the `child_program` — the invariant as one `Always`-guarded case
   (the program every minted cell carries for life);
3. derives the program's canonical VK (`canonical_program_vk`);
4. assembles a `FactoryDescriptor` that **bakes the invariant into
   `state_constraints` AND pins `child_program_vk` to the program carrying
   them** — so the descriptor self-validates
   (`validate_child_vk_canonical(&child_program)` succeeds).

The kind is content-addressed by `kind_id()` = the descriptor's hash. Because
that hash absorbs `state_constraints`, **distinct invariants are distinct
kinds**, and the invariant cannot be altered without re-minting.

---

## 3. How a user-minted kind becomes first-class

"First-class" means the kernel — not a bolt-on mint layer — does the enforcing.
`MintedKind::evaluate_transition` delegates *straight to the program the
executor runs*:

```rust
self.child_program.evaluate_with_meta(new, old, None, &TransitionMeta::wildcard())
```

There is no second enforcement path to drift from the kernel. A conforming turn
returns `Ok(())`; a violating turn returns
`Err(ProgramError::ConstraintViolated{..})` — the same refusal a re-executing
light client reproduces bit-for-bit. This is the literal sense in which a
*user-defined* kind joins the kernel's vocabulary: the moment its descriptor is
deployed (`AgentRuntime::deploy_factory`), every child is born with the kind's
program and every turn against a child faces the kind's invariant.

The minimal genuine slice shipped:

* `Invariant::BalanceNeverBelow { slot, floor }` → `StateConstraint::FieldGte`
  (the "balance never negative" kind; `floor = 0` is non-negativity).
* `Invariant::MonotoneField { slot }` → `StateConstraint::Monotonic`
  (the "this field is monotone / never decreases" kind).

Both are exercised in the test suite: a conforming turn succeeds, a violating
turn (`balance → 10` below floor `50`; `counter 9 → 4`) is **refused** with a
real `ConstraintViolated` — not a stub, not a flag.

---

## 4. The forge-detector — conformance IS membership

Minting alone does not make a cell honest. A cell could *claim* a kind while
installing a program that omits the invariant. `MintedKind::attest_membership`
is the gate that catches it. Given the program a cell actually installed (what a
validator re-hashes and runs), it admits the cell iff:

1. **Identity** — the program's canonical VK equals the kind's child VK
   (the cell installed *this* kind's program); OR, failing exact identity,
2. **Containment** — the program's constraint set contains every one of the
   kind's invariant constraints (a *stricter* superset is fine — a cell may add
   caveats — but it may not drop the kind's invariant).

A program that drops the invariant — or an empty (`None`) program, or a freer
rule (`FieldLte` where the kind demanded `Monotonic`) — is rejected with
`ForgeRejection::ProgramMissingInvariant`. **Membership-without-conformance is a
forge, and it is rejected.** A differently-*shaped* program that still carries
the invariant (e.g. an extra unrelated case, different VK) is admitted by the
containment check — because conformance, not byte-identity, is the bar.

---

## 5. The bar (Track 2 = Track 1) — met

A passing test suite (`sdk/src/hatchery_mint.rs::tests`, 15 tests, green):

* **mint a kind with an invariant** — `minting_bakes_the_invariant_into_the_descriptor`,
  `distinct_invariants_are_distinct_kinds`,
  `same_invariant_same_child_program_across_authorities`;
* **a conforming turn succeeds** — `balance_conforming_turn_succeeds`,
  `monotone_conforming_turn_succeeds`;
* **a violating turn is REFUSED** (the invariant enforced, not a stub) —
  `balance_violating_turn_is_refused`, `monotone_violating_turn_is_refused`;
* **a cell forging membership-without-conformance is REJECTED** —
  `forged_membership_is_rejected`, `empty_program_is_a_forge_for_any_invariant`,
  with the conformance-not-byte-identity boundary pinned by
  `conforming_superset_program_passes_membership` and
  `forge_that_carries_invariant_under_different_vk_still_conforms`;
* **an attestation is recorded and tied to the proven Lean rung** —
  `attesting_hpres_records_the_crown`, `attested_kind_carries_the_contract_hash_material`,
  and `invariant_matches_lean_rung` (the Rust rejection mirrors the Lean witnesses
  of `metatheory/Dregg2/Deos/Hatchery.lean`).

---

## 6. The hpres proof — bound (the forever-crown is REAL)

The `HpresProof` slot is no longer a `Pending` stand-in. `HpresProof::Attested {
contract_hash }` (`hatchery_mint.rs:189/198/292`, via `MintedKind::attest_hpres`)
binds a minted kind to a machine-checked `Dregg2.Verify.Contract.CellContract`,
and the Lean rung is landed in `metatheory/Dregg2/Deos/Hatchery.lean` — the LAST
of the six house capacities, the house COMPLETE:

1. The per-turn gate **is** the declared invariant (`evalStep_admits_iff_*`), an
   admitted step preserves it (`step_preserves`, the **hpres**), and the same
   `CellContract` carry skeleton lifts it to the unbounded trajectory —
   `invariant_forever` (`Hatchery.lean:233`): under EVERY schedule of admitted
   turns, a minted cell carries its invariant for life.
2. The `Attested` structure **cannot be constructed without a real contract**
   (hence a real `step_ob` proof term), so an attestation is a *proved*
   forever-crown — `attested_enforces_forever` (`Hatchery.lean:291`), not a
   trusted flag — and an attestation for a *different* invariant is rejected by
   the decidable content-hash check, `forged_attestation_rejected`
   (`Hatchery.lean:315`). The Rust `tests::invariant_matches_lean_rung` mirrors
   these witnesses so the executor's rejection is tied to the proven statement.

The DEEPER weld — making the `Attested` forever-crown real for a *pure light
client*, not just a re-executing validator — is also built: the per-turn FOLD
over a re-proved contract-attestation leaf
(`dregg_circuit_prove::hatchery_leaf_adapter::prove_hatchery_leaf`), connected to
the mint leg's claimed `contract_hash` teeth by
`prove_hatchery_binding_node_segmented`. This binds the `(contract_hash,
invariant_digest)` tuple IN the deployed recursion tree, so a mint whose
`contract_hash` is backed by no verifying attestation is UNSAT — the adversarial
refutation `metatheory/Dregg2/Circuit/HatcheryBackingAttack.lean`
(`deployed_admits_unbacked_hatchery`), with the fold tooth biting in
`hatchery_leaf_adapter::tests::forged_contract_hash_is_rejected_by_the_fold`.

**The one honest remaining edge** (per `metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md`,
hatchery row) is not the Lean proof — it is two named descriptor seams: the
deployed mint leg must **dual-expose** its `contract_hash` teeth (a descriptor
PI-exposure change — the VK-affecting "big-bang" piece this node consumes), and
full in-AIR re-verification that a `contract_hash` resolves to a verifying
`CellContract` proof term stays the named off-AIR digest-of-attestation cost.
The forever-crown and the fold machinery are real today; these are the circuit
dual-expose seams, not a missing proof.

---

*a user names a shape and a rule;*
*the kernel holds every child to it, forever —*
*and the egg the user laid hatches honest.*

🥚🔏
