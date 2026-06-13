# 1 · The model: four substances, eight verbs, turns

## 1.1 The sentence

> A **turn** is the exercise of an attenuable, proof-carrying token over
> owned state, leaving a verifiable receipt.

The rest of the system is this sentence, given algebra. This section fixes
the nouns (substances, cells, capabilities, assets, turns, receipts) and the
verbs; §2 gives the authority logic; §3 the guard algebra; §4 the receipt and
its aggregation.

## 1.2 The four substances

The kernel governs four substances. Each has a *discipline of use* — a law
about how it may move through time — and the kernel is the enforcement of
those laws.

| substance | discipline | the law |
|---|---|---|
| **value** | linear — moves, never copies or vanishes | per asset, Σδ = 0 exactly, per turn and per attested run |
| **authority** | produced under non-forgeability — grows, but only by authorized, receipt-disclosed construction; narrows freely along one edge | *only connectivity begets connectivity* (§2) |
| **evidence** | monotone — once known, never unknown | the nullifier/commitment ledgers only grow |
| **state** | guarded-mutable — changes only under `Pred`, only by its owner | the frame rule |

The substance algebra is mechanized as a product of resource cameras
(`Dregg2/Resource.lean`): an ℕ-sum camera carries the linear law; an `Auth`
camera — in which the authoritative element ● may move the total under
authorization while fragments ◯ cannot self-amplify — carries both the
authority and the evidence laws (they are literally the same camera over
∪-monoids, `ConfinesAuthority`); cells and programs carry the guarded law.

Every kernel verb passes **two gates**:

* **admission** — the epistemic half: does the supplied witness realize the
  demanded predicate? (`Verify P w`; §2.2);
* **footprint** — the ontic half: the update is a frame-preserving update of
  the verb's footprint in the product camera — it respects what the
  substances *are*.

These halves are genuinely independent: the camera is provably blind to the
guards (`camera_blind_to_caveats`), and order-shaped validity alone provably
cannot carry exact conservation — the value law needs the issuer-supply
discipline of §1.4.

## 1.3 Cells

A **cell** is the four substances gathered behind one identity:

```
Cell = { operator, lifecycle, nonce,
         bal    : Asset → ℤ,            -- the value column
         clist  : sorted-Merkle of Cap, -- held authority
         program: Pred,                 -- the guarded-state law, self-imposed
         slots  : Slot → Value }
```

Nothing is ownerless; every object in the system *is* a cell or lives in one.
The frame rule — a turn touching one cell leaves every other cell unchanged —
is proven once and read four ways: sovereignty (your cell is untouchable),
joint turns (disjoint footprints compose as separating conjunction), sharding
(disjoint frames commute), and offline operation (a frame advances alone and
merges soundly).

A **capability** is the token: target, rights, caveats (`Pred`), expiry,
revocation epoch. It is attenuable on every axis, revocable by epoch bump,
and storable in slots (a capability is a value; retrieval re-checks the
grantor's epoch, so storage cannot launder revocation).

## 1.4 Assets

An **asset is an issuer cell's promise**: `AssetId` is the issuer's `CellId`.
Mint and burn are the issuer moving value from and to its own well under its
own program; fees are ordinary moves to pot-cells whose programs *are* the
fee policy. Conservation is therefore one law with no exceptions to disclose:
the moved asset's total is exactly invariant
(`RecordKernel.recTransferBal_sum_conserve_moved`) and untouched assets are
pointwise unchanged (`recTransferBal_untouched`) — no cross-asset leakage.

## 1.5 The eight verbs

The kernel signature is eight verbs; each is the structural rule of one
substance's discipline, and the assignment of (substance, polarity) to verbs
is injective — so minimality is a theorem
(`VerbRegistry.minimality`, `VerbRegistry.each_verb_irreplaceable`): drop any
verb and the behavior it provides has no other provider.

| verb | substance / polarity | structural rule |
|---|---|---|
| `create` | birth / introduce | mint a four-substance cell (incl. factory instantiation) |
| `write` | state / neutral | guarded heap/program/permission update under the frame |
| `move` | value / neutral | exchange of the linear substance (fees and burn are moves to wells) |
| `grant` | authority / introduce | authorized production / narrowing along one edge |
| `revoke` | authority / eliminate | epoch-narrowing that stales held authority |
| `shield` / `unshield` | evidence / introduce | note-create / note-spend: grow the evidence ledger |
| `lifecycle` | retirement / eliminate | the seal/destroy/sovereign custody automaton |

The wire vocabulary turns actually carry is larger (52 effect tags), and a
total, compiler-checked cover (`VerbRegistry.classify`,
`classify_total`, `cover_hits_all_three`) sends every tag to exactly one of
three places: a kernel verb; **turn structure** (exercising a capability is a
*use*, not a verb; a refusal is an *outcome*; the nonce is prologue;
pipelining is composition); or a **factory pattern** — a cell program built
from the surviving verbs only (`factory_builtFrom_are_survivors`); §6.3.

## 1.6 Turns

```
Turn  = auth ∘ body ∘ receipt
body ::= verb | seq | par | hole(Pred)
```

A turn is a forest of actions executed as a transaction: every action admits
and every effect lands, or the state is exactly what it was. Each action
carries a demand ⊣ supply pair (the cell demands a predicate, the action
supplies a witnessed authorization; §2.2), the guards in scope (§3), the
proposed effects, and a signed binding to the canonical message (federation,
nonce, action, effects) so an inference cannot be replayed into a context it
was not proved for. Multi-party turns are the same shape under one
commitment, each participant contributing its own authorization; conditional
and pipelined turns are composition structure (`hole(Pred)` is a typed hole a
counterparty's fulfillment discharges).

A committed turn leaves **Q** — the receipt: the committed postcondition
under one commitment scheme (sorted-Poseidon2 Merkle throughout). The witness
proves Q; the disclosure dials project Q; aggregation folds Q; the light
client verifies only Q-chains (§4).
