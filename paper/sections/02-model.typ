// =============================================================================
// Section 2: The model — four substances, eight verbs, turns
// =============================================================================

#import "../defs.typ": lean
= The model <sec-model>

This section fixes the nouns --- substances, cells, capabilities, assets,
turns, receipts --- and the verbs. The authorization logic is given in
@sec-authority; the receipt and its aggregation in @sec-proofs.

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
(`Dregg2/Resource.lean`). A supply camera carries the linear law: a committed
transfer is a frame-preserving update of the moved balances
(#lean("move_value_fpu")), and a supply-violating mint is not
(#lean("mint_not_value_fpu")). An `Auth` camera carries the authority and
evidence laws: an amplifying grant is rejected by the camera itself
(#lean("amplifying_grant_not_fpu")), confinement of held authority is
frame preservation by definition (#lean("ConfinesAuthority")), and erasing a
known nullifier is not a valid update (#lean("forget_evidence_not_fpu")).
Cells and programs carry the guarded law.

Every kernel verb passes *two gates*. *Admission* is the epistemic half: does
the supplied witness realize the demanded predicate? (`Verify P w`;
@sec-authority). *Footprint* is the ontic half: the update is a
frame-preserving update of the verb's footprint in the product camera --- it
respects what the substances *are*. The halves are independent in both
directions. The camera is blind to the guards: a write that every caveat
rejects, and that the kernel therefore refuses, is still a valid camera update
(#lean("camera_blind_to_caveats")). And order-shaped camera validity alone
cannot carry exact conservation: over the ledger's integer carrier every
authoritative update is frame-preserving (#lean("int_auth_fpu_vacuous")), and
even an ordered carrier admits a coordinated mint
(#lean("nat_auth_coordinated_mint_fpu")). The value law therefore lives in the
issuer supply discipline of @sec-assets, not in the order.

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
Programmable state is a *register file plus a heap*: a small fixed file of
named scalar fields --- the state machine every turn touches --- and one
register holding `heap_root`, the root of a sorted-Poseidon2 Merkle map over
`(collection, key) → value` for collections of unbounded size, opened only
where a turn reads or writes. This is the same five-domain address space ---
registers, heap, capabilities, nullifiers, receipt index --- that the
universal memory model gives one commitment discipline
(`Dregg2/Crypto/UniversalMemory.lean`, mirrored by the executor-state
projection in `turn/src/umem.rs`). Per turn, the deployed circuit binds the
touched cell's register file as flat before/after trace columns and carries
its balance limbs, nonce, and commitment roots among the public inputs; the
deployed layout of record is the emitted staged registry
(`circuit/descriptors/rotation-wide-*.tsv`), and each install appends an
operator-stamped row to `docs/VK-REGEN-LOG.md`.

The frame rule --- a turn touching one cell leaves every other cell unchanged
--- is proven once and read four ways: sovereignty (your cell is untouchable),
joint turns (disjoint footprints compose as separating conjunction), sharding
(disjoint frames commute), and offline operation (a frame advances alone and
merges soundly).

A *capability* is the token: target, rights, caveats (a predicate), expiry,
revocation epoch. It is attenuable on every axis, revocable by epoch bump, and
storable in slots --- a capability is a value, and retrieval re-checks the
grantor's epoch, so storage cannot launder revocation.

== Assets <sec-assets>

An *asset is an issuer cell's promise*: an `AssetId` is the issuer's `CellId`.
Mint and burn are the issuer moving value from and to its own well under its
own program; fees are ordinary moves to pot-cells whose programs *are* the fee
policy. Conservation is therefore one law with no exceptions to disclose: the
moved asset's total is exactly invariant
(#lean("RecordKernel.recTransferBal_sum_conserve_moved")) and untouched assets
are pointwise unchanged (#lean("RecordKernel.recTransferBal_untouched")) ---
no cross-asset leakage.

== The eight verbs

The kernel signature is eight verbs --- seven constructors, with `shield` and
`unshield` the two directions of one evidence verb. Each is the structural
rule of one substance's discipline. The assignment of (substance, polarity) to
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
  caption: [The kernel signature. The roster of record is the registry itself
    (`Dregg2/Substrate/VerbRegistry.lean`), which reifies the wire effect enum
    one Lean tag per variant.],
)

The wire vocabulary turns actually carry is larger than the signature. The
registry classifies it with a total cover (#lean("VerbRegistry.classify"),
#lean("VerbRegistry.classify_total")) that sends every reified tag to exactly
one of three places: a *kernel verb*; *turn structure* (exercising a
capability is a _use_, not a verb; a refusal is an _outcome_; the nonce is
prologue; pipelining is composition); or a *factory pattern* --- a cell
program built from the surviving verbs only. On the live enum the factory
bucket is provably empty (#lean("VerbRegistry.no_live_factory_tags")): the
families the factories replaced were deleted from the wire, not reclassified.
The exhaustiveness check is the compiler's --- a tag added to the roster
without a classification does not compile. Faithfulness of the roster to the
wire enum, however, is established by reification, not by the compiler, and at
present it is behind: the registry classifies the twenty-seven variants of the
verb-lockstep enum, and `turn/src/action.rs` has since grown by six --- a
program write (`SetProgram`), a capability-gated supply entry (`Mint`), a
shielded transfer (`ShieldedTransfer`), and the promise / notify / react
coordination triple. The registry does not yet classify these six.

== Turns

```
Turn  = auth ∘ body ∘ receipt
body ::= verb | seq | par | hole(Pred)
```

A turn is a forest of actions executed as a transaction: every action admits
and every effect lands, or the state is exactly what it was. Each action
carries a demand $tack.l$ supply pair (the cell demands a predicate, the
action supplies a witnessed authorization; @sec-authority), the guards in
scope, the proposed effects, and a signed binding to the canonical message ---
the federation, the action, and its effects --- so an inference cannot be
replayed into a context it was not proved for. Multi-party turns are the same shape under
one commitment, each participant contributing its own authorization.
Conditional and pipelined turns are composition structure, where `hole(Pred)`
is a typed hole a counterparty's fulfillment discharges.

A committed turn leaves *Q* --- the receipt: the committed postcondition under
one commitment scheme (sorted-Poseidon2 Merkle throughout). The witness proves
Q; the disclosure dial projects Q; aggregation folds Q; the light client
verifies only Q-chains (@sec-proofs). Q is one object in every role.
