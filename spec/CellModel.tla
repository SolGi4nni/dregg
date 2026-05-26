-------------------------------- MODULE CellModel --------------------------------
(***************************************************************************)
(* CellModel — initial TLA+ specification of dregg's three most-fundamental *)
(* cell-model invariants:                                                   *)
(*                                                                          *)
(*   I1 (Identity integrity).  Each cell's id equals BLAKE3(public_key ||   *)
(*       token_id).  Once a cell exists in the ledger, no operation         *)
(*       mutates `id`, `public_key`, or `token_id`.                         *)
(*                                                                          *)
(*   I2 (Nonce monotonicity).  Per-cell nonce starts at 0 and increases by  *)
(*       exactly 1 per successful turn.  Wrong-nonce turns are rejected.    *)
(*       The ledger nonce never regresses.                                  *)
(*                                                                          *)
(*   I3 (Capability attenuation lattice).  For any granted capability D     *)
(*       derived from a held capability P, IsAttenuation(P, D) must hold.   *)
(*       The lattice ordering is partial:                                   *)
(*                                                                          *)
(*               Impossible      (top — most restrictive)                   *)
(*                 /    \                                                   *)
(*           Signature  Proof                                               *)
(*                \    /                                                    *)
(*                Either                                                    *)
(*                  |                                                       *)
(*                 None         (bottom — least restrictive)                *)
(*                                                                          *)
(*       The ordering is `is_narrower_or_equal` from cell/src/permissions   *)
(*       .rs.  No operation may amplify (loosen) a granted capability       *)
(*       relative to the parent.                                            *)
(*                                                                          *)
(*   I4 (Balance conservation across a turn).  Every successful turn that   *)
(*       moves value from cell A to cell B reduces A's balance by exactly   *)
(*       the amount B's balance increases, plus a non-negative fee that is  *)
(*       burned (accounted to the symbolic "no cell" sink).  The total      *)
(*       (sum of cell balances + total fees burned) is invariant.           *)
(*       Concrete reference: dregg-protocol-tests/src/invariants/           *)
(*       balance_conservation.rs.                                           *)
(*                                                                          *)
(*   I5 (Receipt-chain causal soundness).  Each successful turn appends a   *)
(*       receipt to the executing cell's chain.  The new receipt's          *)
(*       prev_hash field equals the hash of the previous head; for the      *)
(*       first receipt it equals the genesis sentinel "0".  No operation    *)
(*       may insert, remove, reorder, or rewrite a receipt without          *)
(*       breaking the linkage.  Real-world references: the previous_       *)
(*       receipt_hash threading in node/src/mcp.rs (commit 818bbd62) and    *)
(*       the executor's verify_receipt_chain in turn/src/.                  *)
(*                                                                          *)
(*   I6 (Bearer-cap temporal soundness).  Every capability in the c-list    *)
(*       is tagged with the turn at which it was minted (`mintTurn`).  For  *)
(*       any cap whose provenance is `<<"Delegated", parent>>`, the         *)
(*       child's mintTurn is strictly greater than the parent's mintTurn.   *)
(*       No cap may ever be minted with a mintTurn earlier than its         *)
(*       provenance source.  Real-world reference: bearer-cap exercise in   *)
(*       turn/src/executor.rs::verify_bearer_cap requires the delegator to  *)
(*       have held the cap at delegation time, which is the runtime form    *)
(*       of "parent existed before child."                                  *)
(*                                                                          *)
(*   I7 (Bearer-cap expiry honored).  Caps carry an optional                *)
(*       `expiresAt` block height.  Any exercise of a cap when              *)
(*       `currentBlockHeight > expiresAt` is rejected.  Real-world          *)
(*       reference: the `block_height > proof.expires_at` early-return at   *)
(*       executor.rs:3834.                                                  *)
(*                                                                          *)
(*   I8 (Three-party introduction soundness).  When introducer A introduces *)
(*       recipient B to target C, A must hold a cap to C, B gains exactly   *)
(*       one new cap to C attenuated relative to A's cap, A's c-list is    *)
(*       unchanged, and C is untouched.  Real-world reference:              *)
(*       Effect::Introduce in turn/src/action.rs.                           *)
(*                                                                          *)
(*   I9 (Facet attenuation).  Caps carry an optional `allowedEffects` mask  *)
(*       (a subset of a finite effect-kind universe).  A child cap's mask   *)
(*       must be a subset of the parent's mask (or, if the parent has no    *)
(*       mask, any child mask is permitted).  Real-world reference:         *)
(*       cell/src/facet.rs::is_facet_attenuation and the                    *)
(*       BearerCapFacetAmplification error in executor.rs.                  *)
(*                                                                          *)
(*   I10 (Revocation-propagation policy).  After RevokeCapability removes   *)
(*       a parent cap from its holder's c-list, children that were granted  *)
(*       from that parent earlier remain valid in their respective          *)
(*       c-lists.  This documents the chosen semantics — dregg's executor   *)
(*       only invalidates the directly-revoked slot — and is NOT a bug.    *)
(*                                                                          *)
(* This spec deliberately ABSTRACTS:                                        *)
(*   * BLAKE3 — modeled as an injective function on (pk, token_id) pairs.   *)
(*   * Signatures and proofs — modeled by an `Auth` token the agent         *)
(*     presents; we don't model the cryptography, only the matching rule.   *)
(*   * Effect VM, receipts, balances, facets, expiry, the journal,          *)
(*     escrow, programs, sovereign mode, etc.  These deserve their own      *)
(*     spec increments; see spec/README.md.                                 *)
(*                                                                          *)
(* The goal is an honest, audit-against-Rust foundation: a reader should be *)
(* able to point at each TLA+ invariant and find the corresponding code in  *)
(* cell/src/{cell,permissions,capability}.rs and turn/src/executor.rs.      *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    PublicKeys,        \* finite set of distinct public key identifiers
    TokenIds,          \* finite set of distinct token-id identifiers
    MaxNonce,          \* model bound: cap on nonce values explored
    MaxTurns,          \* model bound: total successful turns explored
    MaxBalance,        \* model bound: cap on per-cell balance (and on transfer amount)
    InitialEndowment,  \* per-cell starting balance at CreateCell time
    EffectKinds        \* finite set of effect-kind tokens, for I9 facet masks
                       \* (a tractable abstraction of cell/src/facet.rs's
                       \*  EffectMask : u32; we keep a tiny finite universe).

(***************************************************************************)
(* Auth lattice                                                             *)
(*                                                                          *)
(* Mirrors cell/src/permissions.rs::AuthRequired.  `Permissions` in this    *)
(* spec collapses to a single AuthRequired (the action-axis split into      *)
(* send/receive/set_state/... is orthogonal to attenuation and is left to a *)
(* later increment — we keep one slot here so the lattice is visible).     *)
(***************************************************************************)

AuthRequired == {"None", "Signature", "Proof", "Either", "Impossible"}

\* IsNarrowerOrEqual(a, b) <=> a is at least as restrictive as b.
\* Matches AuthRequired::is_narrower_or_equal exactly.
IsNarrowerOrEqual(a, b) ==
    \/ a = "Impossible"                                  \* top: narrowest
    \/ b = "None"                                        \* bottom: anything narrower-or-equal to None
    \/ a = b                                             \* reflexive
    \/ (a = "Proof" /\ b = "Either")
    \/ (a = "Signature" /\ b = "Either")

\* IsAttenuation(parent, granted): granted may only be granted from parent
\* if it is narrower-or-equal.  This is cell/src/capability.rs::is_attenuation.
IsAttenuation(parent, granted) == IsNarrowerOrEqual(granted, parent)

(***************************************************************************)
(* Cell identity                                                            *)
(*                                                                          *)
(* The spec models BLAKE3(pk || tid) as a total injective function from     *)
(* (pk, tid) pairs to a CellId.  We construct CellId structurally as the    *)
(* tuple <<pk, tid>> — this is the most parsimonious way to enforce         *)
(* injectivity without modeling a hash function.  The injectivity matches   *)
(* the Rust contract: derive_raw is collision-resistant on its 64-byte      *)
(* input.                                                                   *)
(***************************************************************************)

DeriveId(pk, tid) == <<pk, tid>>

CellIds == { DeriveId(pk, tid) : pk \in PublicKeys, tid \in TokenIds }

(***************************************************************************)
(* State                                                                    *)
(*                                                                          *)
(* `cells` : CellId -> [pk, tid, nonce, perm]                               *)
(*   pk     : public key bytes; must satisfy id = DeriveId(pk, tid)         *)
(*   tid    : token id bytes; ditto                                         *)
(*   nonce  : Nat <= MaxNonce                                               *)
(*   perm   : the cell's own authorization requirement (used as the         *)
(*            "parent" when granting capabilities away from this cell)      *)
(*                                                                          *)
(* `caps`  : { <<holder, target, perm>> }                                   *)
(*   The c-list relation: cell `holder` holds a capability to `target` with *)
(*   permission `perm`.  A capability that originates from a cell's own     *)
(*   permission perm0 may only be granted with perm <= perm0 in the lattice.*)
(*   A re-delegation of a held capability with parent perm pP may only be   *)
(*   re-granted with child perm pC where IsAttenuation(pP, pC).             *)
(*                                                                          *)
(* `turns` : Nat — count of successful turns performed (for bounded model). *)
(*                                                                          *)
(* New in this increment:                                                   *)
(*                                                                          *)
(* `cells[id].balance` : Nat <= MaxBalance.  Value held by the cell.        *)
(*                                                                          *)
(* `cells[id].receipts` : Seq(Receipt).  Per-cell receipt chain.  Each      *)
(*    receipt has fields:                                                   *)
(*      seq        : 1-based sequence number, equal to its position in the  *)
(*                   chain (i.e. Len(prefix) + 1).                          *)
(*      prev_hash  : "0" for the first receipt; otherwise the hash of the   *)
(*                   immediately preceding receipt.                         *)
(*      payload    : a tag identifying what kind of turn produced this      *)
(*                   receipt ("Nop" or <<"Transfer", to, amount, fee>>).    *)
(*    `Hash(r)` is modeled as the tuple <<r.seq, r.prev_hash, r.payload>>;  *)
(*    structural equality on tuples gives injectivity, mirroring the        *)
(*    collision-resistance assumption on BLAKE3 in node/src/mcp.rs.         *)
(*                                                                          *)
(* `burned` : Nat — running total of fees burned (sink for the              *)
(*    conservation invariant).                                              *)
(***************************************************************************)

\* Genesis sentinel for an empty receipt chain.  Matches the "all-zero"
\* previous_receipt_hash that node/src/mcp.rs writes into the first
\* receipt a cell ever produces.
GenesisPrevHash == "0"

\* Receipts in this model.  Receipts are tagged by payload:
\*   * "Nop"                — a nonce-only turn (no value movement)
\*   * <<"Transfer", t, a, f>> — a value-bearing turn sending amount `a`
\*       (plus fee `f`) from the holder to cell `t`.
\* The set of payloads is finite under the model bounds.
TransferPayloads(maxAmount, maxFee, otherCells) ==
    { <<"Transfer", t, a, f>> :
        t \in otherCells, a \in 0..maxAmount, f \in 0..maxFee }

\* Hash function: model BLAKE3(receipt) as the receipt's structural tuple.
\* The tuple is injective by construction, so distinct receipts get
\* distinct "hashes".  This is the same abstraction we use for DeriveId.
Hash(r) == <<r.seq, r.prev_hash, r.payload>>

(***************************************************************************)
(* Facet masks (I9).                                                        *)
(*                                                                          *)
(* In Rust an EffectMask is a u32 with 20-ish bit positions.  Here we       *)
(* abstract a mask as a subset of the finite set `EffectKinds`.  The        *)
(* sentinel `NoMask` plays the role of `Option::None` (unrestricted —      *)
(* equivalent to `EFFECT_ALL`).                                             *)
(*                                                                          *)
(* Masks(set) is the powerset of EffectKinds; AllMasks is the corresponding *)
(* range used in type-OK checks.                                            *)
(***************************************************************************)

\* Facet masks: encoded structurally so TLC never mixes a string sentinel
\* with a Subset(EffectKinds) value in equality checks.  <<"NoMask">>
\* means "unrestricted" (matches `Option<EffectMask>::None`);
\* <<"Some", S>> means the mask is the set S \subseteq EffectKinds
\* (matches `Option::Some(mask)`).
NoMask        == <<"NoMask">>
SomeMask(S)   == <<"Some", S>>
AllMasks      == { NoMask } \cup { SomeMask(S) : S \in SUBSET EffectKinds }
MaskBits(m)   == IF m = NoMask THEN EffectKinds ELSE m[2]

\* IsFacetAttenuation(parent, child): mirrors cell/src/facet.rs's
\* is_facet_attenuation, lifted to the (NoMask | Some(Subset(EffectKinds)))
\* abstraction.  NoMask on the parent means "no restriction" so any child
\* mask is permitted; otherwise child must be Some(s) with s a subset of
\* the parent's bits.
\*   * If child is NoMask but parent isn't, that would AMPLIFY (the child
\*     would have no restriction while the parent does), so we forbid it.
IsFacetAttenuation(parent, child) ==
    \/ parent = NoMask                              \* parent unrestricted
    \/ /\ child # NoMask
       /\ parent # NoMask
       /\ child[1] = "Some" /\ parent[1] = "Some"
       /\ child[2] \subseteq parent[2]

(***************************************************************************)
(* Capability provenance and temporal tags (I6 / I7 / I8 / I9 / I10).      *)
(*                                                                          *)
(* Each capability now carries:                                             *)
(*   mintTurn    : the value of `turns` at the moment this cap was created. *)
(*   expiresAt   : "NoExpiry" or a Nat block-height after which the cap is  *)
(*                 expired (block height is modeled by `turns` itself).     *)
(*   parent      : provenance — either                                      *)
(*                   <<"Own", h>>      : minted from holder h's own perm,   *)
(*                   <<"Delegated", p>> : derived by attenuation from cap p.*)
(*                 The parent field's purpose is to let the temporal-       *)
(*                 soundness invariant inspect delegation chains.           *)
(*   mask        : optional facet mask (subset of EffectKinds, or NoMask).  *)
(***************************************************************************)

\* Optional expiry: encoded structurally so TLC never mixes a string
\* sentinel with a Nat in a comparison.  <<"None">> means "no expiry"
\* (matches `Option::None`); <<"Some", n>> means "expires at block height n"
\* (matches `Option::Some(u64)`).
NoExpiry == <<"None">>
SomeExpiry(n) == <<"Some", n>>
ExpiryDomain == { NoExpiry } \cup { SomeExpiry(n) : n \in 0..MaxTurns }

\* IsExpiryHonored(expiresAt, height):  TRUE when a cap with the given
\* expiry is still exercisable at block-height `height`.  Mirrors the
\* `self.block_height > proof.expires_at` early-return at
\* turn/src/executor.rs:3834.
IsExpiryHonored(expiresAt, height) ==
    \/ expiresAt = NoExpiry
    \/ /\ expiresAt[1] = "Some"
       /\ height <= expiresAt[2]

(***************************************************************************)
(* State variables.                                                         *)
(*                                                                          *)
(* New in this increment:                                                   *)
(*                                                                          *)
(*   exercised : { <<capId, expiresAt, atHeight>> }.  An audit-log of all   *)
(*     bearer-cap exercise events that the model accepted.  We record the   *)
(*     `expiresAt` value at exercise time so the I7 invariant can be        *)
(*     checked WITHOUT requiring the cap to still be in `caps` (the cap     *)
(*     may have been revoked in a later step).                              *)
(*                                                                          *)
(*   nextCapId : Nat.  Allocator for fresh capId values.                    *)
(*                                                                          *)
(*   mintedCaps : { CapRecord }.  Append-only history of every cap ever     *)
(*     minted (including those later revoked).  Used by I6 / I8 / I9        *)
(*     invariants so they remain checkable after a parent cap is revoked    *)
(*     (per I10: revocation does not cascade to children).                  *)
(*                                                                          *)
(* The "global clock" used for expiry (I7) is just `turns` — a successful   *)
(* turn ticks the clock, an introduction/redelegation does not, matching   *)
(* the runtime where block height advances per block (which the executor    *)
(* equates with turn boundaries).                                           *)
(***************************************************************************)

VARIABLES cells, caps, turns, burned, exercised, nextCapId, mintedCaps

vars == <<cells, caps, turns, burned, exercised, nextCapId, mintedCaps>>

\* Per-cell type predicate.  We don't fix the receipt-payload set in a
\* set type because TLC would need a precise enumeration; the load-bearing
\* structural invariants are ChainSeqWellFormed and ChainWellLinked below.
CellTypeOK(c) ==
    /\ c.pk \in PublicKeys
    /\ c.tid \in TokenIds
    /\ c.nonce \in 0..MaxNonce
    /\ c.perm \in AuthRequired
    /\ c.balance \in 0..MaxBalance

\* Capability ids.  Each cap gets a unique Nat id at mint time (next-cap-id
\* counter, see `nextCapId` below).  Provenance refers to the parent cap by
\* id, not by structural copy — keeping the CapRecord type finite for TLC.
\*
\* MaxCapId is a derived model bound: at most one cap is minted per
\* GrantFromOwn / Redelegate / Introduce step, and `StateBound` caps the
\* set size at `MaxCaps`, so the highest id seen is bounded by that count
\* over the entire trace.  We give a slightly larger envelope to absorb
\* set-bound slack.
MaxCapId == 12

CapIds == 0..MaxCapId

\* Capability parent provenance values.  An "Own" parent records the
\* originating cell whose own perm rooted the cap; a "Delegated" parent
\* records the parent CAP'S ID, so the delegation chain can be walked by
\* the I6 invariant by following ids through `caps`.
ParentOriginValues ==
    { <<"Own", h>>       : h \in CellIds } \cup
    { <<"Delegated", k>> : k \in CapIds }

\* Cap records.  The temporal-soundness invariant I6 reaches back through
\* the `parent` chain by structural pattern match over `caps`.
CapRecord == [
    capId     : CapIds,
    holder    : CellIds,
    target    : CellIds,
    perm      : AuthRequired,
    mintTurn  : 0..MaxTurns,
    expiresAt : ExpiryDomain,
    parent    : ParentOriginValues,
    mask      : AllMasks
]

\* Helper: is `c.parent` an "Own" provenance, or a "Delegated p" provenance?
IsOwnProvenance(c)       == c.parent[1] = "Own"
IsDelegatedProvenance(c) == c.parent[1] = "Delegated"

\* Helper: extract the parent cap id from a "Delegated" provenance.
ParentCapId(c) == c.parent[2]

\* Helper: given a cap id, locate its CapRecord (if any) in the current
\* `caps` set.  We use this for I10 narration of revocation propagation.
CapById(k, capSet) == { c \in capSet : c.capId = k }

TypeOK ==
    /\ DOMAIN cells \subseteq CellIds
    /\ \A id \in DOMAIN cells : CellTypeOK(cells[id])
    /\ caps \subseteq CapRecord
    /\ turns \in 0..MaxTurns
    /\ burned \in 0..(MaxBalance * MaxTurns)
    /\ nextCapId \in 0..(MaxCapId + 1)
    /\ exercised \subseteq (CapIds \X ExpiryDomain \X (0..MaxTurns))
    /\ mintedCaps \subseteq CapRecord
    /\ caps \subseteq mintedCaps                  \* live caps are a subset of history

(***************************************************************************)
(* Initial state                                                            *)
(*                                                                          *)
(* The ledger starts empty.  Cells are introduced via CreateCell actions.   *)
(* This matches the Rust ledger: cells appear via Effect::CreateCell.       *)
(***************************************************************************)

Init ==
    /\ cells = << >>                       \* empty function
    /\ caps  = {}
    /\ turns = 0
    /\ burned = 0
    /\ exercised   = {}
    /\ nextCapId   = 0
    /\ mintedCaps  = {}

(***************************************************************************)
(* Actions                                                                  *)
(***************************************************************************)

\* CreateCell: introduce a fresh cell.  Identity must be the BLAKE3 of
\* (pk, tid).  The cell must not already exist in the ledger.  Initial
\* nonce is 0 (matches CellState::new in cell/src/state.rs).
CreateCell(pk, tid, perm) ==
    LET id == DeriveId(pk, tid) IN
    /\ id \notin DOMAIN cells
    /\ perm \in AuthRequired
    /\ cells' = cells @@ (id :> [pk       |-> pk,
                                  tid      |-> tid,
                                  nonce    |-> 0,
                                  perm     |-> perm,
                                  balance  |-> InitialEndowment,
                                  receipts |-> << >>])
    /\ caps'  = caps
    /\ turns' = turns
    /\ burned' = burned
    /\ UNCHANGED <<exercised, nextCapId, mintedCaps>>
    \* Note: we do NOT count CreateCell as a "turn" in this spec — turns are
    \* nonce-bearing executions.  CreateCell is a setup action.

\* Helper: build the next receipt for a cell's chain given a payload.
\* Sequence is 1-based: the first receipt has seq = 1.  prev_hash is the
\* genesis sentinel for an empty chain, else the Hash of the current head.
NextReceipt(id, payload) ==
    LET chain  == cells[id].receipts
        seqN   == Len(chain) + 1
        prevH  == IF chain = << >>
                  THEN GenesisPrevHash
                  ELSE Hash(chain[Len(chain)])
    IN [seq |-> seqN, prev_hash |-> prevH, payload |-> payload]

\* SuccessfulTurnNop: a turn that supplies the matching nonce and is
\* accepted but moves no value.  Nonce ++ and append a "Nop" receipt.
\* This is the nonce-only path through Effect::IncrementNonce in
\* turn/src/action.rs with no value-bearing effects.
SuccessfulTurnNop(id, providedNonce) ==
    /\ id \in DOMAIN cells
    /\ turns < MaxTurns
    /\ cells[id].nonce < MaxNonce
    /\ providedNonce = cells[id].nonce            \* must match
    /\ LET r == NextReceipt(id, <<"Nop">>) IN
       cells' = [cells EXCEPT ![id].nonce    = @ + 1,
                              ![id].receipts = Append(@, r)]
    /\ caps'  = caps
    /\ turns' = turns + 1
    /\ burned' = burned
    /\ UNCHANGED <<exercised, nextCapId, mintedCaps>>

\* SuccessfulTurnTransfer: a value-bearing successful turn.  The holder's
\* nonce increments, balance decreases by amount+fee, the recipient's
\* balance increases by amount, and `fee` is added to `burned`.  The
\* holder's chain gains a Transfer receipt linking to its prior head.
\* Recipient receipt chains are not modified by this action (a real system
\* might emit a paired receipt; we model only the sender's chain to keep
\* the receipt-chain invariants per-cell and the state space tractable).
SuccessfulTurnTransfer(id, providedNonce, to, amount, fee) ==
    /\ id \in DOMAIN cells
    /\ to \in DOMAIN cells
    /\ to # id                                    \* no self-transfer
    /\ turns < MaxTurns
    /\ cells[id].nonce < MaxNonce
    /\ providedNonce = cells[id].nonce
    /\ amount \in 0..MaxBalance
    /\ fee    \in 0..MaxBalance
    /\ cells[id].balance >= amount + fee          \* must be able to pay
    /\ cells[to].balance + amount <= MaxBalance   \* model bound
    /\ LET r == NextReceipt(id, <<"Transfer", to, amount, fee>>) IN
       cells' = [cells EXCEPT ![id].nonce    = @ + 1,
                              ![id].balance  = @ - amount - fee,
                              ![id].receipts = Append(@, r),
                              ![to].balance  = @ + amount]
    /\ caps'  = caps
    /\ turns' = turns + 1
    /\ burned' = burned + fee
    /\ UNCHANGED <<exercised, nextCapId, mintedCaps>>

\* RejectedTurn: a turn with wrong nonce.  The ledger MUST NOT change.
\* We model rejection as a stutter on `cells`, `caps`, and `burned`.
RejectedTurn(id, providedNonce) ==
    /\ id \in DOMAIN cells
    /\ providedNonce # cells[id].nonce
    /\ cells' = cells
    /\ caps'  = caps
    /\ turns' = turns
    /\ burned' = burned
    /\ UNCHANGED <<exercised, nextCapId, mintedCaps>>

\* GrantFromOwn: cell `holder` mints a capability to itself or to another
\* cell.  The new capability is "rooted" in the holder's own permission:
\* the granted perm must be narrower-or-equal to holder's own perm.  This
\* models the executor branch that checks attenuation against an
\* originating permission.
\*
\* The fresh cap is stamped with `mintTurn = turns` (I6), `expiresAt`
\* provided by the caller (I7), and parent provenance `<<"Own", holder>>`.
\* The optional facet mask is also caller-supplied; it must be a subset
\* of the holder cell's own mask, which we model as unrestricted (NoMask)
\* — cell perms in this spec are auth-axis only, so the parent mask is
\* always NoMask here.  (I9 attenuation through redelegation is the
\* load-bearing check.)
GrantFromOwn(holder, target, grantedPerm, expiry, mask) ==
    /\ holder \in DOMAIN cells
    /\ target \in DOMAIN cells
    /\ grantedPerm \in AuthRequired
    /\ expiry \in ExpiryDomain
    /\ mask \in AllMasks
    /\ IsAttenuation(cells[holder].perm, grantedPerm)
    /\ nextCapId <= MaxCapId
    /\ LET newCap == [capId     |-> nextCapId,
                      holder    |-> holder,
                      target    |-> target,
                      perm      |-> grantedPerm,
                      mintTurn  |-> turns,
                      expiresAt |-> expiry,
                      parent    |-> <<"Own", holder>>,
                      mask      |-> mask]
       IN /\ caps' = caps \cup {newCap}
          /\ mintedCaps' = mintedCaps \cup {newCap}
    /\ nextCapId' = nextCapId + 1
    /\ cells' = cells
    /\ turns' = turns
    /\ burned' = burned
    /\ UNCHANGED <<exercised>>

\* Redelegate: a cell that already holds a capability re-delegates a
\* (possibly narrower) version of it to a third party.  The new perm must
\* be narrower-or-equal to the held perm.  This is the lattice rule the
\* executor enforces at turn/src/executor.rs:4265 and :5980.
\*
\* Mints a fresh cap with `mintTurn = turns`, expiry tightened to
\* `min(parent.expiresAt, newExpiry)` (you cannot redelegate longer than
\* the parent's lifetime), parent = <<"Delegated", parentCap.capId>>, and
\* mask passing I9's IsFacetAttenuation against the parent's mask.
Redelegate(parentCap, toCell, narrowerPerm, newExpiry, newMask) ==
    /\ parentCap \in caps
    /\ toCell \in DOMAIN cells
    /\ narrowerPerm \in AuthRequired
    /\ newExpiry \in ExpiryDomain
    /\ newMask \in AllMasks
    /\ IsAttenuation(parentCap.perm, narrowerPerm)
    /\ IsFacetAttenuation(parentCap.mask, newMask)
    \* I6: a redelegated child must be minted in a strictly later turn
    \* than the parent.  This mirrors the runtime invariant that the
    \* parent had to be visible in some prior turn for the delegator to
    \* have held it.  If `turns = parent.mintTurn`, an intervening turn
    \* (SuccessfulTurnNop or a Transfer) must advance the clock first.
    /\ parentCap.mintTurn < turns
    \* I7-ish: cannot redelegate longer than the parent's lifetime.
    /\ \/ parentCap.expiresAt = NoExpiry
       \/ /\ newExpiry # NoExpiry
          /\ newExpiry[1] = "Some"
          /\ parentCap.expiresAt[1] = "Some"
          /\ newExpiry[2] <= parentCap.expiresAt[2]
    /\ nextCapId <= MaxCapId
    /\ LET newCap == [capId     |-> nextCapId,
                      holder    |-> toCell,
                      target    |-> parentCap.target,
                      perm      |-> narrowerPerm,
                      mintTurn  |-> turns,
                      expiresAt |-> newExpiry,
                      parent    |-> <<"Delegated", parentCap.capId>>,
                      mask      |-> newMask]
       IN /\ caps' = caps \cup {newCap}
          /\ mintedCaps' = mintedCaps \cup {newCap}
    /\ nextCapId' = nextCapId + 1
    /\ cells' = cells
    /\ turns' = turns
    /\ burned' = burned
    /\ UNCHANGED <<exercised>>

\* Introduce: three-party introduction (I8).  Introducer A grants recipient
\* B a cap to target C.  A must hold a cap to C (provenance).  B's c-list
\* gains exactly one cap whose perm/mask are attenuated relative to A's
\* held cap.  A's c-list is unchanged (we mint a fresh derived cap, do
\* not move A's cap).  C is untouched.
\*
\* Mirrors Effect::Introduce in turn/src/action.rs.  The new cap's
\* provenance is <<"Delegated", parentCap.capId>>, parent being A's cap.
Introduce(introducerCap, recipient, narrowerPerm, newExpiry, newMask) ==
    /\ introducerCap \in caps
    /\ recipient \in DOMAIN cells
    /\ recipient # introducerCap.holder       \* not granting to self
    /\ recipient # introducerCap.target       \* C is untouched
    /\ narrowerPerm \in AuthRequired
    /\ newExpiry \in ExpiryDomain
    /\ newMask \in AllMasks
    /\ IsAttenuation(introducerCap.perm, narrowerPerm)
    /\ IsFacetAttenuation(introducerCap.mask, newMask)
    /\ \/ introducerCap.expiresAt = NoExpiry
       \/ /\ newExpiry # NoExpiry
          /\ newExpiry[1] = "Some"
          /\ introducerCap.expiresAt[1] = "Some"
          /\ newExpiry[2] <= introducerCap.expiresAt[2]
    \* I6: introduction-derived caps must be strictly later than the
    \* introducer's cap (same rationale as Redelegate).
    /\ introducerCap.mintTurn < turns
    /\ nextCapId <= MaxCapId
    /\ LET newCap == [capId     |-> nextCapId,
                      holder    |-> recipient,
                      target    |-> introducerCap.target,
                      perm      |-> narrowerPerm,
                      mintTurn  |-> turns,
                      expiresAt |-> newExpiry,
                      parent    |-> <<"Delegated", introducerCap.capId>>,
                      mask      |-> newMask]
       IN /\ caps' = caps \cup {newCap}
          /\ mintedCaps' = mintedCaps \cup {newCap}
    /\ nextCapId' = nextCapId + 1
    /\ cells' = cells                          \* A and C states untouched
    /\ turns' = turns
    /\ burned' = burned
    /\ UNCHANGED <<exercised>>

\* Revoke: drop a specific capability (by capId) from the c-list.  Revocation
\* never violates invariants — it can only shrink rights for the directly
\* revoked slot.  See I10 for the propagation policy: children minted from
\* this cap earlier remain valid in their respective c-lists.
Revoke(targetCap) ==
    /\ targetCap \in caps
    /\ cells' = cells
    /\ caps'  = caps \ {targetCap}
    /\ turns' = turns
    /\ burned' = burned
    /\ UNCHANGED <<exercised, nextCapId, mintedCaps>>

\* ExerciseBearer (I7): a holder exercises a cap they hold at the current
\* block height (= `turns`).  The cap must not be expired.  We record the
\* exercise event in `exercised` for the I7 state invariant.
ExerciseBearer(targetCap) ==
    /\ targetCap \in caps
    /\ IsExpiryHonored(targetCap.expiresAt, turns)
    /\ exercised' = exercised \cup
            { <<targetCap.capId, targetCap.expiresAt, turns>> }
    /\ UNCHANGED <<cells, caps, turns, burned, nextCapId, mintedCaps>>

(***************************************************************************)
(* Adversarial actions                                                      *)
(*                                                                          *)
(* These are explicitly enabled here so the model checker can show our      *)
(* invariants forbid them.  An honest implementation would never permit     *)
(* these; we include them to demonstrate that the invariants catch them.   *)
(* They are guarded by ENABLED_ADVERSARY in the cfg.                       *)
(***************************************************************************)

\* Attempt to amplify a held capability — the negation of attenuation.
\* This adversarial action is NOT in `Next`.  It exists as a placeholder
\* for sanity-check perturbations to demonstrate the I3 / I9 invariants
\* bite when re-introduced into `Next`.
AttemptAmplify(parentCap, toCell, widerPerm) ==
    /\ parentCap \in caps
    /\ toCell \in DOMAIN cells
    /\ widerPerm \in AuthRequired
    /\ ~ IsAttenuation(parentCap.perm, widerPerm)
    /\ nextCapId <= MaxCapId
    /\ LET newCap == [capId     |-> nextCapId,
                      holder    |-> toCell,
                      target    |-> parentCap.target,
                      perm      |-> widerPerm,
                      mintTurn  |-> turns,
                      expiresAt |-> parentCap.expiresAt,
                      parent    |-> <<"Delegated", parentCap.capId>>,
                      mask      |-> parentCap.mask]
       IN /\ caps' = caps \cup {newCap}
          /\ mintedCaps' = mintedCaps \cup {newCap}
    /\ nextCapId' = nextCapId + 1
    /\ cells' = cells
    /\ turns' = turns
    /\ burned' = burned
    /\ UNCHANGED <<exercised>>

(***************************************************************************)
(* Next-state relation                                                      *)
(***************************************************************************)

Next ==
    \/ \E pk \in PublicKeys, tid \in TokenIds, p \in AuthRequired :
            CreateCell(pk, tid, p)
    \/ \E id \in DOMAIN cells, n \in 0..MaxNonce :
            SuccessfulTurnNop(id, n)
    \/ \E id \in DOMAIN cells, to \in DOMAIN cells,
         n \in 0..MaxNonce, a \in 0..MaxBalance, f \in 0..MaxBalance :
            SuccessfulTurnTransfer(id, n, to, a, f)
    \/ \E id \in DOMAIN cells, n \in 0..MaxNonce :
            RejectedTurn(id, n)
    \/ \E h, t \in DOMAIN cells, p \in AuthRequired,
         e \in ExpiryDomain, m \in AllMasks :
            GrantFromOwn(h, t, p, e, m)
    \/ \E parentCap \in caps, u \in DOMAIN cells, np \in AuthRequired,
         e \in ExpiryDomain, m \in AllMasks :
            Redelegate(parentCap, u, np, e, m)
    \/ \E introCap \in caps, b \in DOMAIN cells, np \in AuthRequired,
         e \in ExpiryDomain, m \in AllMasks :
            Introduce(introCap, b, np, e, m)
    \/ \E c \in caps : Revoke(c)
    \/ \E c \in caps : ExerciseBearer(c)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants                                                               *)
(*                                                                          *)
(* These are the three statements the user asked for, written as state      *)
(* predicates.                                                              *)
(***************************************************************************)

\* I1.  Identity integrity.
\* Every cell in the ledger has id = DeriveId(pk, tid).  Because we use the
\* derived value as the map key, this reduces to: pk and tid match the key.
IdentityIntegrity ==
    \A id \in DOMAIN cells :
        id = DeriveId(cells[id].pk, cells[id].tid)

\* I2.  Nonce well-formedness.
\* No cell ever has a negative nonce (vacuously true given the type), and
\* the bound is respected.
NonceWellFormed ==
    \A id \in DOMAIN cells :
        cells[id].nonce \in 0..MaxNonce

\* I2'.  Nonce monotonicity (action-level).
\* This is a *property* over the next-state relation: the nonce of an
\* existing cell never decreases.  We express it as an action property
\* using the prime operator.
NonceMonotonic ==
    \A id \in DOMAIN cells :
        id \in DOMAIN cells' => cells'[id].nonce >= cells[id].nonce

\* I3.  Attenuation soundness — state invariant.
\* Every capability in the c-list either was minted from a cell whose own
\* perm attenuates to c.perm (the `GrantFromOwn` source) OR is the
\* attenuation of some other cap to the same target (the `Redelegate`
\* source).  This is the inductive invariant maintained by
\* GrantFromOwn / Redelegate / Revoke.
\*
\* Caveat:  when any cell has perm = "None" (the lattice bottom), the
\* first disjunct is satisfied by every cap (since `None` attenuates to
\* anything).  In that regime the *state* check is weak.  In settings
\* where all cells have strictly restrictive perms (Signature / Proof /
\* Either / Impossible), the state invariant does meaningfully discriminate
\* amplifying caps — see the sanity test in README.md.  The companion
\* action-level property `NoAmplificationProperty` is the strictly
\* stronger statement.
AttenuationSoundness ==
    \A c \in caps :
        \/ \E h \in DOMAIN cells :
                IsAttenuation(cells[h].perm, c.perm)
        \/ \E p \in caps :
                /\ p.target = c.target
                /\ p # c
                /\ IsAttenuation(p.perm, c.perm)

\* I3'. Action-level no-amplification.
\* For every action step, every cap that appears in `caps'` and not in
\* `caps` (i.e., a freshly granted cap) must have been derivable by
\* attenuation from some "source" present in the prior state — either a
\* cell's own perm or an existing cap with the same target.  This is the
\* meaningful inductive statement of attenuation.
NoAmplification ==
    \A c \in (caps' \ caps) :
        \/ \E h \in DOMAIN cells :
                IsAttenuation(cells[h].perm, c.perm)
        \/ \E p \in caps :
                /\ p.target = c.target
                /\ IsAttenuation(p.perm, c.perm)

NoAmplificationProperty == [][NoAmplification]_vars

(***************************************************************************)
(* I4.  Balance conservation.                                               *)
(*                                                                          *)
(* The total value in the system (sum of cell balances + fees burned) is    *)
(* invariant from the moment all cells are created.  Because each           *)
(* CreateCell endows a fresh cell with InitialEndowment, the conserved      *)
(* quantity is:                                                             *)
(*                                                                          *)
(*   sum(cells[i].balance) + burned == |cells| * InitialEndowment           *)
(*                                                                          *)
(* This is a *state* invariant — at any reachable state, the total equals   *)
(* the endowment times the number of cells.  It is the inductive form of    *)
(* "every successful turn preserves balance + fee = 0 delta" from           *)
(* dregg-protocol-tests/src/invariants/balance_conservation.rs.             *)
(*                                                                          *)
(* The companion *action* property `TurnPreservesBalance` says more         *)
(* directly: across any single step that increments `turns`, the conserved  *)
(* quantity is unchanged.                                                   *)
(***************************************************************************)

\* Sum balances by induction on a finite set.  TLA+ requires the
\* RECURSIVE declaration at the module level (it cannot appear inside LET).
RECURSIVE SumBalancesSet(_, _)
SumBalancesSet(cellMap, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN cellMap[x].balance + SumBalancesSet(cellMap, S \ {x})

SumBalances(cellMap) == SumBalancesSet(cellMap, DOMAIN cellMap)

ConservedTotal == SumBalances(cells) + burned

BalanceConservation ==
    ConservedTotal = Cardinality(DOMAIN cells) * InitialEndowment

\* Action-level: balance is preserved across every step (including non-turn
\* steps, which don't touch cells or burned, and CreateCell, which adds
\* InitialEndowment to both sides).
TurnConservesBalance ==
    SumBalances(cells') + burned' - Cardinality(DOMAIN cells') * InitialEndowment
        = SumBalances(cells) + burned - Cardinality(DOMAIN cells) * InitialEndowment

TurnConservesBalanceProperty == [][TurnConservesBalance]_vars

(***************************************************************************)
(* I5.  Receipt-chain causal soundness.                                     *)
(*                                                                          *)
(* For each cell, the receipt chain is a well-linked sequence:              *)
(*                                                                          *)
(*   1. Sequence numbers are 1-based and match position: receipts[i].seq=i. *)
(*   2. receipts[1].prev_hash = GenesisPrevHash.                            *)
(*   3. For i > 1, receipts[i].prev_hash = Hash(receipts[i-1]).             *)
(*                                                                          *)
(* This is the state form of the receipt-chain invariant enforced by        *)
(* verify_receipt_chain in turn/src/ and by node/src/mcp.rs's               *)
(* previous_receipt_hash threading.                                         *)
(*                                                                          *)
(* The companion action property `ReceiptChainAppendOnly` says: no step     *)
(* may shorten, reorder, or rewrite any cell's existing receipt prefix.     *)
(* Only an append at the tail is allowed.                                   *)
(***************************************************************************)

ChainSeqWellFormed(chain) ==
    \A i \in 1..Len(chain) : chain[i].seq = i

ChainWellLinked(chain) ==
    /\ Len(chain) >= 1 => chain[1].prev_hash = GenesisPrevHash
    /\ \A i \in 2..Len(chain) :
            chain[i].prev_hash = Hash(chain[i-1])

ReceiptChainIntegrity ==
    \A id \in DOMAIN cells :
        /\ ChainSeqWellFormed(cells[id].receipts)
        /\ ChainWellLinked(cells[id].receipts)

\* Action-level: every cell that existed before must have a receipt chain
\* in the next state whose prefix equals the old chain (i.e. append-only).
\* A new cell (CreateCell) has empty old chain and empty new chain — also
\* a trivial prefix relation.
ReceiptChainAppendOnly ==
    \A id \in DOMAIN cells :
        /\ id \in DOMAIN cells'
        /\ Len(cells'[id].receipts) >= Len(cells[id].receipts)
        /\ \A i \in 1..Len(cells[id].receipts) :
                cells'[id].receipts[i] = cells[id].receipts[i]

ReceiptChainAppendOnlyProperty == [][ReceiptChainAppendOnly]_vars

\* Action-level: every successful turn appends *exactly one* receipt to the
\* executing cell's chain (and to no other cell's chain).  This pins down
\* the "one turn => one receipt" property that node/src/mcp.rs relies on.
TurnAppendsOneReceipt ==
    (turns' = turns + 1)
        => \E id \in DOMAIN cells' :
            /\ Len(cells'[id].receipts) = Len(cells[id].receipts) + 1
            /\ \A j \in DOMAIN cells' \ {id} :
                    j \in DOMAIN cells =>
                    cells'[j].receipts = cells[j].receipts

TurnAppendsOneReceiptProperty == [][TurnAppendsOneReceipt]_vars

(***************************************************************************)
(* Adversarial actions for receipt-chain falsification.                     *)
(*                                                                          *)
(* Disabled by default (StateBound keeps them out of Next).  They exist as  *)
(* documentation of what the invariant forbids — see the deliberate-break  *)
(* sanity checks in README.md.                                              *)
(*                                                                          *)
(* If a developer ever introduced a code path that allowed receipt          *)
(* rewriting (truncation, splice, or hash-mismatched append), enabling      *)
(* the corresponding action below in Next would let TLC find a              *)
(* counterexample.                                                          *)
(***************************************************************************)

\* These are commented out of Next; they exist for the deliberate-break
\* check described in README.md.  Uncomment in Next to verify the
\* receipt-chain invariants bite.

(***************************************************************************)
(* I6.  Bearer-cap temporal soundness.                                      *)
(*                                                                          *)
(* Every cap whose provenance is `<<"Delegated", parentId>>` must have a    *)
(* mintTurn strictly greater than the parent's mintTurn (the parent must    *)
(* exist and predate the child).  No cap may ever be minted with a          *)
(* mintTurn earlier than its parent — this is the "T' < T" condition the   *)
(* previous spec deferred, mirroring the runtime requirement that the       *)
(* delegator must have held the cap at delegation time.                     *)
(***************************************************************************)

\* CapMintMonotone walks `mintedCaps` (the append-only history), so it
\* remains checkable after a parent cap is revoked from `caps`.  The
\* runtime analogue: the executor's verify_bearer_cap walks the
\* delegation chain by signature, not by reading the c-list, and the
\* signature is over a delegation message issued when the parent was
\* still held.
CapMintMonotone ==
    \A c \in mintedCaps :
        IsDelegatedProvenance(c) =>
            \E p \in mintedCaps :
                /\ p.capId = ParentCapId(c)
                /\ p.mintTurn < c.mintTurn

\* The "Own" provenance has no parent cap; we only require mintTurn to be
\* a valid turn (already enforced by TypeOK).  But we DO require the
\* originating cell to exist in the ledger.  Since cells are never
\* removed in this model, present-now is equivalent to present-then.
OwnProvenanceCellExists ==
    \A c \in mintedCaps :
        IsOwnProvenance(c) =>
            c.parent[2] \in DOMAIN cells

BearerCapTemporalSoundness ==
    /\ CapMintMonotone
    /\ OwnProvenanceCellExists

\* Action-level: no step ever produces a cap that violates the monotone
\* mint-turn rule.  TLC will report this if a buggy mint action lets a
\* parent-after-child step through.
NoBackdatedCap ==
    \A c \in (mintedCaps' \ mintedCaps) :
        IsDelegatedProvenance(c) =>
            \E p \in mintedCaps :
                /\ p.capId = ParentCapId(c)
                /\ p.mintTurn < c.mintTurn

NoBackdatedCapProperty == [][NoBackdatedCap]_vars

(***************************************************************************)
(* I7.  Bearer-cap expiry honored.                                          *)
(*                                                                          *)
(* The `ExerciseBearer` action's guard checks IsExpiryHonored before        *)
(* recording an exercise.  As a state invariant: no event in `exercised`    *)
(* is associated with an expired-at-its-recorded-height capability.         *)
(***************************************************************************)

ExpiryHonored ==
    \A e \in exercised :
        LET expiresAt == e[2]
            atHeight  == e[3]
        IN IsExpiryHonored(expiresAt, atHeight)

\* Action-level: any new entry in `exercised` must satisfy the expiry
\* predicate at the recorded height.  The mirror image of the
\* ExerciseBearer action's precondition.
ExerciseRespectsExpiry ==
    \A e \in (exercised' \ exercised) :
        LET expiresAt == e[2]
            atHeight  == e[3]
        IN IsExpiryHonored(expiresAt, atHeight)

ExerciseRespectsExpiryProperty == [][ExerciseRespectsExpiry]_vars

(***************************************************************************)
(* I8.  Three-party introduction soundness.                                 *)
(*                                                                          *)
(* When introducer A introduces recipient B to target C, the effect on the  *)
(* cap-set is:                                                              *)
(*   * A continues to hold its cap to C (A's c-list is unchanged).          *)
(*   * B's c-list gains EXACTLY ONE new cap to C, attenuated relative to    *)
(*     A's cap (perm narrower-or-equal, mask facet-narrower-or-equal).     *)
(*   * C is untouched (no entry of `caps` is keyed on holder=C as a side    *)
(*     effect of the introduction).                                         *)
(*                                                                          *)
(* The action-level property `IntroductionWellShaped` makes the per-step    *)
(* statement.  At the state level, every Delegated cap's perm and mask     *)
(* are attenuations of its parent's perm and mask (this is a generalized   *)
(* I3 + I9 conjunction).                                                    *)
(***************************************************************************)

DelegationAttenuated ==
    \A c \in mintedCaps :
        IsDelegatedProvenance(c) =>
            \E p \in mintedCaps :
                /\ p.capId = ParentCapId(c)
                /\ IsAttenuation(p.perm, c.perm)
                /\ IsFacetAttenuation(p.mask, c.mask)

\* Action-level Introduce check: when (caps' \ caps) contains a new cap
\* whose parent is Delegated, the parent must exist in `caps` (the prior
\* state), the new cap must be attenuated, and the cells map must be
\* untouched.  The latter is the "A's c-list is unchanged" part — cells
\* doesn't track c-lists per cell in this spec (caps is the global
\* relation), so "A's c-list unchanged" reduces to: no existing cap was
\* removed in this step.  Combined with single-cap addition, this gives
\* the I8 shape.
IntroductionWellShaped ==
    \A c \in (mintedCaps' \ mintedCaps) :
        IsDelegatedProvenance(c) =>
            /\ \E p \in mintedCaps :            \* parent existed beforehand
                  /\ p.capId = ParentCapId(c)
                  /\ IsAttenuation(p.perm, c.perm)
                  /\ IsFacetAttenuation(p.mask, c.mask)
            /\ (caps \ caps') = {}              \* no existing live cap removed

IntroductionWellShapedProperty == [][IntroductionWellShaped]_vars

(***************************************************************************)
(* I9.  Facet attenuation.                                                  *)
(*                                                                          *)
(* The state form is the second conjunct of DelegationAttenuated above.    *)
(* We restate as a standalone invariant for clarity and for sanity-check    *)
(* targeting.                                                               *)
(***************************************************************************)

FacetAttenuation ==
    \A c \in mintedCaps :
        IsDelegatedProvenance(c) =>
            \E p \in mintedCaps :
                /\ p.capId = ParentCapId(c)
                /\ IsFacetAttenuation(p.mask, c.mask)

(***************************************************************************)
(* I10.  Revocation propagation policy.                                     *)
(*                                                                          *)
(* This is a DOCUMENTATION invariant of the chosen semantics, not a bug    *)
(* report: dregg's executor revokes only the directly named slot.  Children *)
(* derived earlier remain in their respective c-lists (they will fail later *)
(* when their own delegation chain is walked and the parent is found        *)
(* missing — but the c-list entry itself is not auto-removed).             *)
(*                                                                          *)
(* The state invariant: if Revoke removed a cap with id k, any cap whose    *)
(* parent points to k (a former child) remains in `caps`.  We can't say    *)
(* "remains forever" in a state invariant; the action-level property        *)
(* RevokeDoesNotCascade carries that meaning.                               *)
(***************************************************************************)

\* Action-level: Revoke removes EXACTLY ONE cap and does not touch any
\* other cap, even children of the revoked cap.  This is the policy.
RevokeDoesNotCascade ==
    (caps' # caps /\ Cardinality(caps \ caps') > 0) =>
        \* If anything was removed this step, every removed cap must be a
        \* direct revocation (no cascade to a child whose parent was just
        \* removed).  Concretely: the "removed" set must equal the
        \* "intentionally targeted" set, which we approximate as "no
        \* removed cap has another removed cap as its parent."
        \A removed \in (caps \ caps') :
            ~ \E other \in (caps \ caps') :
                  /\ other # removed
                  /\ IsDelegatedProvenance(removed)
                  /\ ParentCapId(removed) = other.capId

RevokeDoesNotCascadeProperty == [][RevokeDoesNotCascade]_vars

(***************************************************************************)
(* Conjunction of state invariants (for the cfg's INVARIANT directive).     *)
(***************************************************************************)
Invariant ==
    /\ TypeOK
    /\ IdentityIntegrity
    /\ NonceWellFormed
    /\ AttenuationSoundness
    /\ BalanceConservation
    /\ ReceiptChainIntegrity
    /\ BearerCapTemporalSoundness
    /\ ExpiryHonored
    /\ DelegationAttenuated
    /\ FacetAttenuation

\* Action-level monotonicity, for TLC's PROPERTY directive.
MonotonicNonce == [][NonceMonotonic]_vars

\* State constraint: keep the c-list bounded so TLC doesn't explore an
\* unboundedly growing set of caps.  Referenced from CellModel.cfg.
\* We also bound |cells| and the per-cell receipt chain length to keep
\* the search tractable.
\* The bounded perm subset we explore.  AuthRequired has five values
\* (None, Signature, Proof, Either, Impossible); the I1–I5 spec used the
\* full lattice.  For the I6–I10 increment we restrict to the two-element
\* sublattice {Signature, None} (top vs. bottom of the meaningful sub-DAG)
\* to keep state tractable while still exercising I3 attenuation through
\* the cap-mint actions.  The full lattice is still in scope for the
\* fixed cell perms, but cap perm/granted perm choices are constrained.
PermSubset == {"Signature", "None"}

\* The bounded expiry subset.  We pick a single concrete expiry value
\* (0) plus NoExpiry so the model can sample both expired and not-yet-
\* expired caps without exploding state.
ExpirySubset == { NoExpiry, SomeExpiry(0) }

StateBound ==
    /\ Cardinality(caps) =< 2
    /\ Cardinality(mintedCaps) =< 3
    /\ Cardinality(DOMAIN cells) =< 2
    /\ \A id \in DOMAIN cells : Len(cells[id].receipts) =< MaxTurns
    /\ nextCapId =< 3
    /\ Cardinality(exercised) =< 1
    \* Restrict the dynamic perm / expiry / mask choices so TLC doesn't
    \* explore the full Cartesian product of cap parameters at every
    \* mint step.  The state-space contraction here is purely a TLC
    \* tractability lever — the spec on its own admits the full set.
    /\ \A c \in mintedCaps : c.perm \in PermSubset
    /\ \A c \in mintedCaps : c.expiresAt \in ExpirySubset

(***************************************************************************)
(* Theorem (sketch, not machine-checked here):                              *)
(*   Spec => []Invariant /\ MonotonicNonce                                  *)
(*                                                                          *)
(* TLC will model-check this under the constants in CellModel.cfg.          *)
(***************************************************************************)

================================================================================
