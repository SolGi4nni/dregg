// =============================================================================
// Section 2: The model — four substances, eight verbs, turns
// =============================================================================

#import "../defs.typ": lean
= The model <sec-model>

The rest of the system is the sentence of @sec-intro, given algebra. This
section fixes the nouns --- substances, cells, capabilities, assets, turns,
receipts --- and the verbs. @sec-authority gives the authority logic;
@sec-proofs the receipt and its aggregation.

== The four substances

The kernel governs four substances. Each has a *discipline of use* --- a law
about how it may move through time --- and the kernel is the enforcement of
those laws.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*substance*], [*discipline*], [*the law*]),
    [*value*], [linear --- moves, never copies or vanishes],
      [per asset, $Sigma delta = 0$ exactly, per turn and per attested run],
    [*authority*], [produced under non-forgeability --- grows only by authorized,
      receipt-disclosed construction; narrows freely along one edge],
      [_only connectivity begets connectivity_ (@sec-authority)],
    [*evidence*], [monotone --- once known, never unknown],
      [the nullifier and commitment ledgers only grow],
    [*state*], [guarded-mutable --- changes only under a predicate, only by its
      owner], [the frame rule],
  ),
  caption: [The four substances and their disciplines.],
)

The substance algebra is mechanized as a product of resource cameras
(`Dregg2/Resource.lean`): an $NN$-sum camera carries the linear law; an `Auth`
camera --- in which the authoritative element may move the total under
authorization while fragments cannot self-amplify (#lean("ConfinesAuthority"))
--- carries both the authority and the evidence laws; cells and programs carry
the guarded law.

Every kernel verb passes *two gates*. *Admission* is the epistemic half: does
the supplied witness realize the demanded predicate? (`Verify P w`; @sec-authority).
*Footprint* is the ontic half: the update is a frame-preserving update of the
verb's footprint in the product camera --- it respects what the substances
*are*. These halves are genuinely independent: the camera is provably blind to
the guards (#lean("camera_blind_to_caveats")), and order-shaped validity alone
provably cannot carry exact conservation --- the value law needs the issuer
supply discipline of @sec-assets below.

== Cells

A *cell* is the four substances gathered behind one identity:

```
Cell = { operator, lifecycle, nonce,
         registers : Fin R → Value,   -- the small named state-machine fields
         heap_root : sorted-Poseidon2 map over (collection, key) → value,
         bal       : Asset → ℤ,       -- the value column
         clist     : sorted-Merkle of Cap,  -- held authority
         program   : Pred }           -- the guarded-state law, self-imposed
```

Nothing is ownerless; every object in the system *is* a cell or lives in one.
Programmable state is a *register file plus a heap*: a small fixed file of named
scalar fields (the state machine that every turn touches, kept flat per-turn in
the circuit) and one register holding `heap_root`, a sorted-Poseidon2 Merkle map
over `(collection, key) → value` for collections of unbounded size, opened only
where a turn reads or writes (`docs/REFINEMENT-DESIGN.md`). The frame rule --- a
turn touching one cell leaves every other cell unchanged --- is proven once and
read four ways: sovereignty (your cell is untouchable), joint turns (disjoint
footprints compose as separating conjunction), sharding (disjoint frames
commute), and offline operation (a frame advances alone and merges soundly).

A *capability* is the token: target, rights, caveats (a predicate), expiry,
revocation epoch. It is attenuable on every axis, revocable by epoch bump, and
storable in slots --- a capability is a value, and retrieval re-checks the
grantor's epoch, so storage cannot launder revocation.

== Assets <sec-assets>

An *asset is an issuer cell's promise*: an `AssetId` is the issuer's `CellId`.
Mint and burn are the issuer moving value from and to its own well under its own
program; fees are ordinary moves to pot-cells whose programs *are* the fee
policy. Conservation is therefore one law with no exceptions to disclose: the
moved asset's total is exactly invariant
(#lean("RecordKernel.recTransferBal_sum_conserve_moved")) and untouched assets
are pointwise unchanged (#lean("RecordKernel.recTransferBal_untouched")) --- no
cross-asset leakage.

== The eight verbs

The kernel signature is eight verbs --- seven constructors, with `shield` and
`unshield` the two directions of one evidence verb. Each is the structural rule
of one substance's discipline, and the assignment of (substance, polarity) to
verbs is injective, so minimality is a theorem
(#lean("VerbRegistry.minimality"), #lean("VerbRegistry.each_verb_irreplaceable")):
drop any verb and the behavior it provides has no other provider.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*verb*], [*substance / polarity*], [*structural rule*]),
    [`create`], [birth / introduce], [mint a four-substance cell (incl. factory instantiation)],
    [`write`], [state / neutral], [guarded register/heap/program/permission update under the frame],
    [`move`], [value / neutral], [exchange of the linear substance (fees and burn are moves to wells)],
    [`grant`], [authority / introduce], [authorized production / narrowing along one edge],
    [`revoke`], [authority / eliminate], [epoch-narrowing that stales held authority],
    [`shield` / `unshield`], [evidence / introduce], [note-create / note-spend: grow the evidence ledger],
    [`lifecycle`], [retirement / eliminate], [the seal / destroy / sovereign custody automaton],
  ),
  caption: [The kernel signature. The verb roster of record is the generated
    verb catalog (`studio/verb-catalog.generated.json`), drift-checked against
    `VerbRegistry`.],
)

The wire vocabulary turns actually carry is larger (the live effect enum), and a
total, compiler-checked cover (#lean("VerbRegistry.classify"),
#lean("VerbRegistry.classify_total")) sends every tag to exactly one of three
places: a *kernel verb*; *turn structure* (exercising a capability is a _use_,
not a verb; a refusal is an _outcome_; the nonce is prologue; pipelining is
composition); or a *factory pattern* --- a cell program built from the surviving
verbs only. The cover existing and compiling *is* the completeness proof: a wire
variant added without a classification does not build.

== Turns

```
Turn  = auth ∘ body ∘ receipt
body ::= verb | seq | par | hole(Pred)
```

A turn is a forest of actions executed as a transaction: every action admits and
every effect lands, or the state is exactly what it was. Each action carries a
demand $tack.l$ supply pair (the cell demands a predicate, the action supplies a
witnessed authorization; @sec-authority), the guards in scope (the guard algebra), the
proposed effects, and a signed binding to the canonical message (federation,
nonce, action, effects) so an inference cannot be replayed into a context it was
not proved for. Multi-party turns are the same shape under one commitment, each
participant contributing its own authorization; conditional and pipelined turns
are composition structure, where `hole(Pred)` is a typed hole a counterparty's
fulfillment discharges.

A committed turn leaves *Q* --- the receipt: the committed postcondition under
one commitment scheme (sorted-Poseidon2 Merkle throughout). The witness proves
Q; the disclosure dial projects Q; aggregation folds Q; the light client
verifies only Q-chains (@sec-proofs). Q is one object in every role.
