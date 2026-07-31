/-
# Dregg2.Bridge.MinaAccountOpening — **a Mina ACCOUNT, read out of a verified header.**

⚑ **SUBSTRATE, SAID OUT LOUD.** This file authors **NO AIR**. It is a HASH FUNCTION and a REFUSAL:
`(bytes, account, opening) → Bool`, no `Builder`, no gadget, no constraint. It is authored here
rather than in Rust for the same reason `MinaBinprot` and `MinaStateHashDerive` are: what a Mina
*account* IS — which of its fields are in the leaf preimage and in what order — is the whole content
of the claim "this account holds this balance", and rendered in Rust it would be a MIRROR of
openmina's `account.rs` whose correctness was a differential test.

## The hole this closes, and it is the one the word "semantic" names

Before this file, dregg could say six things about Mina — `lc_verify`, `better_tip`, `head_advance`,
`proof_chain_ok`, `state_hash_word_ok`, `wrap_shape_ok` — and **every one of them is about the
CHAIN.** Not one reads an account, a balance, a nonce, a delegation. dregg could follow Mina's chain
and could not observe anything *in* it. That is a consensus bridge, not a light client.

The missing rung is short, and it was always available: `Blockchain_state` carries
`staged_ledger_hash.non_snark.ledger_hash`, which **is** the Merkle root of Mina's account ledger,
and `MinaBinprot` has decoded it since the day `Blockchain_state` stopped being discarded
(`slhLedgerHash`). An account plus a 35-level opening against that root is a statement about Mina
STATE, anchored in a header whose identity `MinaStateHashDerive` re-derives from the same bytes.

## What the caller may conclude, in one sentence

> At the tip whose protocol-state bytes these are, the Mina ledger contained an account with
> **this public key, this balance, this nonce, this delegate**, at leaf index *i* — because the
> leaf recomputed from those fields folds, under Mina's own level-indexed Poseidon, to the ledger
> hash inside the block.

And what it may NOT: nothing about the tip's *canonicity*. This gate answers a question about ONE
header. Whether that header is the chain's best tip is `dregg_mina_better_tip` /
`dregg_mina_head_advance`'s job, and whether it is the block it claims to be is
`MinaStateHashDerive`'s. The three compose; this one does not subsume them.

## Field ORDER is again the whole correctness question, and it is REVERSED

`Account.to_input` (`account.ml:363-375`) folds over the record with

```ocaml
let f mk acc field = mk (Core_kernel.Field.get field t) :: acc in
Poly.Fields.fold ~init:[] ~public_key:(f ...) ... |> List.reduce_exn ~f:append
```

— it **conses**, and there is **no `List.rev`**. `Fields.fold` visits in *declaration* order, so the
absorb order is the declaration order REVERSED:

```
zkapp, permissions, timing, voting_for, delegate, receipt_chain_hash,
nonce, balance, token_symbol, token_id, public_key
```

The labelled arguments on those lines are in a third order entirely and mean nothing. openmina
hardcodes the reversed order with a comment per field
(`crates/ledger/src/account/account.rs:1765-1806`) and agrees exactly. ⚑ And the trap does not
generalise: `Permissions.Poly.to_input` (`permissions.ml:379-393`) has the same `::` fold and **does**
end in `|> List.rev`, so permissions absorb in *declaration* order. One file, two directions.

## Four more leaf facts a structure-level read gets wrong

  1. **The prefixes are `Mina*`, not `Coda*`.** `Hash_prefixes.account = create "MinaAccount"` and
     `merkle_tree i = create (sprintf "MinaMklTree%03d" i)` (`hash_prefixes.ml:28,51`). `CodaAccount`
     / `CodaMklTree` are the LEGACY (pre-Berkeley) names and survive in openmina only under
     `TreeVersion for V1` (`tree_version.rs:69`). A `Coda`-prefixed fold parses, hashes and produces
     a root that is simply not the ledger's — measured here first, against a live block.
  2. **`Merkle_path.t = Left of hash | Right of hash` names the position of YOUR node**, not the
     sibling's: `implied_root` folds `` `Left h -> merge ~height acc h `` (`merkle_path.ml:30-39`,
     `account.rs:1812-1827`). GraphQL surfaces the tag as which of `{left,right}` is non-null, so a
     reader who hashes `[elem.left, elem.right]` transposes every level. The account's own INDEX is
     the cross-check: `nodeIsLeft i ↔ (index >>> i) &&& 1 = 0`.
  3. **`Timing.Untimed` carries `vesting_period = 1`, not 0** — "avoid division by zero"
     (`account_timing.ml:93-106`, `common.rs:162-171`). Zero parses and hashes a different account.
  4. **`txn_version` (32 bits) sits INSIDE the controller run**, immediately after
     `set_verification_key.auth` and before `set_zkapp_uri` (`permissions.ml:384-388`,
     `account.rs:217-232`). It is not appended at either end.

## How the order was settled: against the chain, not against a second reading

Two implementations agreeing is not evidence that either is right. `§7`'s `#guard`s are a live devnet
account — public key, balance, nonce, delegate, permissions and a 35-level opening, all fetched by
`bridge/tools/mina-account-opening.py` — whose recomputed leaf folds to the `staged_ledger_hash`
carried **inside the block's own binprot bytes**. That is a 255-bit equation against a value no
party to this repo chose. Every one of the four traps above breaks it.

⚑ It also costs nothing to re-fetch, which is the point: `mina-account-opening.py --from-tip-creator`
plus `mina-besttip.py --emit-protocol-state` reproduces the fixture from the live network.

## The two pinned externals, and why they are pinned

`zkappDigest = none` means "this account has no zkApp", and the leaf preimage then holds Mina's
`Zkapp_account.default_digest`. That constant is DERIVED here (`§3`) rather than pinned — from the
empty-uri hash, the empty action-state element and the dummy side-loaded VK hash — so only two
irreducible externals remain:

  * `dummyVkHash` — `Pickles.Side_loaded.Verification_key.dummy |> digest_vk`, a Pickles constant
    with no short definition. Pinned from o1js's generated `mocks.dummyVerificationKeyHash`
    (`bindings/crypto/constants.js:1325`), which is emitted from the OCaml.
  * nothing else: the empty action-state element is `Random_oracle.salt
    "MinaZkappActionStateEmptyElt" |> digest` and reduces here.

Both are load-bearing on the real-block `#guard`, so a wrong pin is a RED FILE, not a silent drift.
-/
import Dregg2.Bridge.MinaStateHashDerive

set_option autoImplicit false
-- The Kimchi Poseidon permutation is 55 rounds; the account leaf plus a 35-level fold is 36 of them
-- inside one `decide`. `MinaStateHashDerive` needed the same and for the same reason.
set_option maxRecDepth 1000000

namespace Dregg2.Bridge.MinaAccountOpening

open Dregg2.Bridge.MinaBinprot
open Dregg2.Bridge.MinaChainSelection
open Dregg2.Bridge.MinaStateHashDerive

/-! ## §1 — `Auth_required`, `Permissions`, `Timing` and the account, as Lean data. -/

/-- `Permissions.Auth_required.t` (`permissions.ml:20-26`). -/
inductive Auth where
  | none | either | proof | signature | impossible | both
deriving Repr, DecidableEq

/-- `Auth_required.encode` — the three bits, in the order `Encoding.t` declares them
(`permissions.ml:143-168`, `common.rs:277-294`): `constant`, `signature_necessary`,
`signature_sufficient`. ⚑ `Both` is reachable in the encoding and has no constructor of its own on
the *decoded* side in some readings; it does here, because a served account may carry it. -/
def Auth.bits : Auth → Bool × Bool × Bool
  | .none       => (true,  false, true)
  | .either     => (false, false, true)
  | .proof      => (false, false, false)
  | .signature  => (false, true,  true)
  | .impossible => (true,  true,  false)
  | .both       => (false, true,  false)

/-- `Auth_required.Encoding.to_input` — THREE separate one-bit chunks, not one three-bit chunk
(`permissions.ml:157-161`). The difference is invisible until a 255-bit packing boundary lands
between them. -/
def authI (a : Auth) : Inp :=
  let (c, n, s) := a.bits
  cat [boolI c, boolI n, boolI s]

/-- `Permissions.Poly.Stable.V2.t` (`permissions.ml:361-374`), in DECLARATION order — which is also
the absorb order, because `Poly.to_input` ends in `|> List.rev`. -/
structure Perms where
  editState : Auth
  access : Auth
  send : Auth
  receive : Auth
  setDelegate : Auth
  setPermissions : Auth
  setVerificationKey : Auth
  /-- `Mina_numbers.Txn_version`, 32 bits, absorbed BETWEEN `set_verification_key` and
  `set_zkapp_uri`. -/
  txnVersion : Nat
  setZkappUri : Auth
  editActionState : Auth
  setTokenSymbol : Auth
  incrementNonce : Auth
  setVotingFor : Auth
  setTiming : Auth
deriving Repr, DecidableEq

/-- `Permissions.Poly.to_input`. 13 controllers × 3 bits + one 32-bit version = **71 bits**. -/
def permsI (p : Perms) : Inp :=
  cat [ authI p.editState, authI p.access, authI p.send, authI p.receive,
        authI p.setDelegate, authI p.setPermissions,
        authI p.setVerificationKey, packedI p.txnVersion 32,
        authI p.setZkappUri, authI p.editActionState, authI p.setTokenSymbol,
        authI p.incrementNonce, authI p.setVotingFor, authI p.setTiming ]

/-- A Mina ledger account, with every field the leaf preimage reads.

Field elements (`publicKeyX`, `tokenId`, `receiptChainHash`, `delegateX`, `votingFor`) are their
NUMERIC value in `[0, p)` — the same convention `MinaBinprot.fpLE` reads off the wire and the same
one a Base58Check `Data_hash` decodes to. -/
structure Account where
  /-- `public_key.x`. -/
  publicKeyX : Nat
  /-- `public_key.is_odd`. -/
  publicKeyIsOdd : Bool
  /-- `token_id`; the default (MINA) token is `1`. -/
  tokenId : Nat
  /-- `token_symbol`, as `Token_symbol.to_field`: the ≤ 6 bytes read LITTLE-endian
  (`account.ml:141-163`). The empty symbol is `0`. -/
  tokenSymbol : Nat
  /-- `balance`, in nanomina. -/
  balance : Nat
  /-- `nonce`. -/
  nonce : Nat
  /-- `receipt_chain_hash`. -/
  receiptChainHash : Nat
  /-- `delegate.x` — `Public_key.Compressed.empty` (`x = 0`) when the account delegates to nobody
  (`account.ml:371`, `delegate_opt`). -/
  delegateX : Nat
  /-- `delegate.is_odd`. -/
  delegateIsOdd : Bool
  /-- `voting_for`; `State_hash.dummy` is `0`. -/
  votingFor : Nat
  /-- `timing = Timed _` when true. -/
  isTimed : Bool
  initialMinimumBalance : Nat
  cliffTime : Nat
  cliffAmount : Nat
  /-- ⚑ IGNORED when `isTimed` is false: `Untimed` absorbs the constant `1`. -/
  vestingPeriod : Nat
  vestingIncrement : Nat
  /-- `permissions`. -/
  permissions : Perms
  /-- `zkapp` — `none` means the account has NO zkApp and the preimage carries
  `Zkapp_account.default_digest` (`§3`). `some d` carries an exhibited zkApp digest. -/
  zkappDigest : Option Nat
deriving Repr, DecidableEq

/-- `Account_timing.to_input` (`account_timing.ml:140-159`). ⚑ `Untimed` is
`(false, 0, 0, 0, 1, 0)` — `vesting_period = 1`. 257 bits. -/
def timingI (a : Account) : Inp :=
  cat [ boolI a.isTimed,
        packedI (if a.isTimed then a.initialMinimumBalance else 0) 64,
        packedI (if a.isTimed then a.cliffTime else 0) 32,
        packedI (if a.isTimed then a.cliffAmount else 0) 64,
        packedI (if a.isTimed then a.vestingPeriod else 1) 32,
        packedI (if a.isTimed then a.vestingIncrement else 0) 64 ]

/-! ## §2 — `Random_oracle.salt` WITHOUT the 20-byte prefix rule.

`Hash_prefixes.create` pads-or-truncates to 20 bytes; `Random_oracle.salt` does not, and Mina calls
it directly on strings longer than 20 (`"MinaZkappActionStateEmptyElt"` is 28). Truncating that one
to 20 gives a different element and a different account — so the two salts are separate functions
here rather than one with a flag. -/

/-- `Random_oracle.prefix_to_field` on a RAW string: the bytes read LITTLE-endian, no padding and no
truncation. `prefix_to_field` asserts `8 * length < 255`, so up to 31 bytes. -/
def rawPrefixField (s : String) : Nat := leNat (s.toList.map Char.toNat)

open Dregg2.Circuit.Emit.PastaPoseidon.Ref in
/-- `Random_oracle.salt` on a raw (unpadded) string. -/
def saltRawOf (s : String) : List Nat := absorbAll [0, 0, 0] [rawPrefixField s]

/-- `Random_oracle.digest (salt s)` — the `hash_noinputs` of openmina's parameter tables
(`poseidon/src/hash.rs:232-236`: it returns `last_squeezed`, i.e. the salt state's lane 0, and does
**not** permute again). ⚑ This is NOT `hashFrom (saltOf s) []`, which permutes once more. -/
def saltDigestRaw (s : String) : Nat := (saltRawOf s).getD 0 0

/-! ## §3 — `Zkapp_account.default_digest`, derived rather than pinned. -/

/-- `Zkapp_account.empty_state_element` — `Random_oracle.salt "MinaZkappActionStateEmptyElt" |>
digest` (`zkapp_account.ml`, openmina `ZkAppAccount::empty_action_state`). -/
def emptyActionStateElt : Nat := saltDigestRaw "MinaZkappActionStateEmptyElt"

/-- `hash_zkapp_uri (Some "")` — the empty URI still contributes the trailing `true` bit that makes
the preimage unattainable by any string (`zkapp_account.ml:318-340`), so the packed input is the
single chunk `(1, 1)` and `pack_input` yields `[1]`. -/
def emptyZkappUriHash : Nat := hashFrom (saltOf "MinaZkappUri") (packToFields (packedI 1 1))

/-- `Pickles.Side_loaded.Verification_key.dummy |> digest_vk` — the vk hash a zkApp account carries
when it has no verification key (`zkapp_account.ml:310`, `account.rs:761-767`).

⚑ PINNED, and it is the only pinned external in this file. Source: o1js's generated
`mocks.dummyVerificationKeyHash` (`node_modules/o1js/dist/node/bindings/crypto/constants.js:1325`),
which is emitted from `bindings/ocaml/o1js_constants.ml`. It is load-bearing on §7's real-block
`#guard`, so a wrong value is a red file. -/
def dummyVkHash : Nat :=
  3392518251768960475377392625298437850623664973002200885669375116181514017494

/-- `Zkapp_account.to_input` (`zkapp_account.ml:369-385`) — the same `::`-fold with no `List.rev`, so
again REVERSED declaration order: `zkapp_uri, proved_state, last_action_slot, action_state,
zkapp_version, verification_key, app_state`. -/
def defaultZkappI : Inp :=
  cat ([ fieldI emptyZkappUriHash, boolI false, packedI 0 32 ]
       ++ List.replicate 5 (fieldI emptyActionStateElt)
       ++ [ packedI 0 32, fieldI dummyVkHash ]
       ++ List.replicate 8 (fieldI 0))

/-- **`Zkapp_account.default_digest`** — what `Account.to_input` absorbs for an account with no
zkApp (`account.ml:355-359, 373`). -/
def defaultZkappDigest : Nat :=
  hashFrom (saltOf "MinaZkappAccount") (packToFields defaultZkappI)

/-! ## §4 — `Account.to_input` and the leaf hash. -/

/-- `Public_key.Compressed.to_input` — `x` as a field element, `is_odd` as one bit. Distinct from
`MinaStateHashDerive.pkI` only in taking the two halves apart, so the account's own two keys can be
built without a second `Pk` structure. -/
def compressedI (x : Nat) (isOdd : Bool) : Inp := (fieldI x).app (boolI isOdd)

/-- **`accountI`** — `Account.to_input`, in the REVERSED declaration order §0 derives.

The result is **6 field elements** — `zkapp, voting_for, delegate.x, receipt_chain_hash, token_id,
public_key.x` — and **474 packed bits**, which `pack_input` renders as two more field elements. -/
def accountI (a : Account) : Inp :=
  cat [ fieldI (a.zkappDigest.getD defaultZkappDigest),
        permsI a.permissions,
        timingI a,
        fieldI a.votingFor,
        compressedI a.delegateX a.delegateIsOdd,
        fieldI a.receiptChainHash,
        packedI a.nonce 32,
        packedI a.balance 64,
        packedI a.tokenSymbol 48,
        fieldI a.tokenId,
        compressedI a.publicKeyX a.publicKeyIsOdd ]

/-- **`accountHash`** — `Account.crypto_hash` / `Account.digest` (`account.ml:377-381, 612`). This is
the ledger LEAF. -/
def accountHash (a : Account) : Nat :=
  hashFrom (saltOf "MinaAccount") (packToFields (accountI a))

/-! ## §5 — the level-indexed Merkle fold. -/

/-- `%03d`. -/
def pad3 (n : Nat) : String :=
  let s := toString n
  if s.length ≥ 3 then s else String.ofList (List.replicate (3 - s.length) '0') ++ s

/-- `Hash_prefixes.merkle_tree i` (`hash_prefixes.ml:51`). ⚑ `Mina`, not `Coda`. -/
def mklPrefix (i : Nat) : String := "MinaMklTree" ++ pad3 i

/-- `Ledger_hash.merge ~height` (`ledger_hash.ml:34-38`). -/
def merkleMerge (height l r : Nat) : Nat := hashFrom (saltOf (mklPrefix height)) [l, r]

/-- One opening step. `nodeIsLeft` is the tag `Merkle_path.t` carries: TRUE means the accumulator is
the LEFT operand and the exhibited sibling goes on the right. -/
def openStep (height : Nat) (cur : Nat) (step : Nat × Bool) : Nat :=
  let (sib, nodeIsLeft) := step
  if nodeIsLeft then merkleMerge height cur sib else merkleMerge height sib cur

/-- `Merkle_path.implied_root` (`merkle_path.ml:30-39`) — fold LEAF-FIRST, the level index starting
at 0 and rising toward the root. -/
def impliedRootFrom (height : Nat) (leaf : Nat) : List (Nat × Bool) → Nat
  | [] => leaf
  | s :: rest => impliedRootFrom (height + 1) (openStep height leaf s) rest

/-- `implied_root` from the leaf level. -/
def impliedRoot (leaf : Nat) (path : List (Nat × Bool)) : Nat := impliedRootFrom 0 leaf path

/-- The ledger depth on devnet AND mainnet (`config/mainnet.mlh:1`, `config/devnet.mlh:1`,
`core/src/network.rs:140,218`). A path of any other length is a REFUSAL, not a shorter tree: a
15-level opening reaches a *node*, and a node is not the ledger. -/
def ledgerDepth : Nat := 35

/-- The path directions must be the account INDEX, bit by bit, LSB at the leaf. This is the second,
independent answer the server gives about the same fact, and disagreement between them is a refusal
rather than a preference. -/
def directionsMatchIndex (index : Nat) (path : List (Nat × Bool)) : Bool :=
  (List.range path.length).all (fun i =>
    ((path.getD i (0, true)).2) == (((index >>> i) &&& 1) == 0))

/-! ## §6 — THE DECISION. -/

/-- **`accountOpensToLedgerHash`** — the whole statement, over already-decoded numbers.

`true` exactly when the leaf recomputed from `a`'s fields, folded up `path` under Mina's own
level-indexed Poseidon, equals `ledgerHash` — with the path at the ledger's real depth and its
directions agreeing with the exhibited index. -/
def accountOpensToLedgerHash (a : Account) (index : Nat) (path : List (Nat × Bool))
    (ledgerHash : Nat) : Bool :=
  path.length == ledgerDepth
    && directionsMatchIndex index path
    && impliedRoot (accountHash a) path == ledgerHash

/-- **`accountInBlockLedger`** — THE GATE, over the block's own bytes.

⚑ The ledger hash is DECODED, never supplied. A caller hands over the binprot
`Protocol_state.Value.Stable.V2` prefix and this reads `staged_ledger_hash.non_snark.ledger_hash`
out of it, through `decodeProtocolStateRawChecked` — so the same constants pin and the same
structural refusals that guard the fork-choice route guard this one. There is no argument by which a
caller names the root it wants to open against. -/
def accountInBlockLedger (C : Constants) (bs : List Nat) (a : Account) (index : Nat)
    (path : List (Nat × Bool)) : Bool :=
  match decodeProtocolStateRawChecked C bs with
  | none => false
  | some (ps, _) => accountOpensToLedgerHash a index path ps.blockchain.slhLedgerHash

/-! ### Non-vacuity and fail-closed, stated over the decision itself. -/

/-- ⚑ **THE GATE REFUSES WHEN THE DECODE REFUSES** — never an accept, never a pass-through. -/
theorem the_gate_refuses_when_the_decode_refuses (C : Constants) (bs : List Nat) (a : Account)
    (i : Nat) (p : List (Nat × Bool)) (h : decodeProtocolStateRawChecked C bs = none) :
    accountInBlockLedger C bs a i p = false := by
  unfold accountInBlockLedger; rw [h]

/-- ⚑ **AND IT IS NOT A CONSTANT `false`.** When the bytes decode, the gate is exactly the opening
equation against the ledger hash the bytes carry. -/
theorem the_gate_is_the_opening_equation (C : Constants) (bs : List Nat) (a : Account) (i : Nat)
    (p : List (Nat × Bool)) (ps : ProtocolStateRaw) (rest : List Nat)
    (h : decodeProtocolStateRawChecked C bs = some (ps, rest)) :
    accountInBlockLedger C bs a i p
      = accountOpensToLedgerHash a i p ps.blockchain.slhLedgerHash := by
  unfold accountInBlockLedger; rw [h]

/-- ⚑ **A WRONG DEPTH IS A REFUSAL.** An opening that stops at a node cannot be presented as one
that reaches the ledger, whatever it folds to. -/
theorem a_short_path_is_refused (a : Account) (i : Nat) (p : List (Nat × Bool)) (r : Nat)
    (h : p.length ≠ ledgerDepth) : accountOpensToLedgerHash a i p r = false := by
  unfold accountOpensToLedgerHash
  simp [beq_iff_eq, h]

/-! ## §7 — THE WIRE GATE + `@[export]`. Same `String → String` C-ABI shape as
`dregg_mina_state_hash_word_ok`: `"1"` ACCEPT, `"0"` REJECT, `"ERR"` on any malformed wire (the
caller treats `"ERR"` as REJECT). -/

/-- A `,`-separated `Nat` list; the empty string is `none`, not `some []`. -/
def parseNats? (s : String) : Option (List Nat) :=
  match s.splitOn "," with
  | [] => none
  | parts => parts.foldr (fun p acc => do
      let rest ← acc
      let n ← p.toNat?
      pure (n :: rest)) (some [])

/-- A `key=value` field, fail-closed on a key mismatch or a missing `=`. -/
def parseField? (key part : String) : Option String :=
  match part.splitOn "=" with
  | [k, v] => if k == key then some v else none
  | _ => none

/-- A lowercase hex string → bytes, fail-closed on an odd length or a non-hex digit. -/
def parseHexBytes? (s : String) : Option (List Nat) :=
  let ds := s.toList.map (fun c =>
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
    else none)
  if s.length % 2 == 1 then none
  else
    let rec go : List (Option Nat) → Option (List Nat)
      | [] => some []
      | some hi :: some lo :: rest => (go rest).map (fun t => (hi * 16 + lo) :: t)
      | _ => none
    go ds

/-- `Auth_required` on the wire: the six variants by their OCaml `to_string`
(`permissions.ml:95-105`), which is what the daemon's GraphQL serves. -/
def parseAuth? (s : String) : Option Auth :=
  if s == "None" then some .none
  else if s == "Either" then some .either
  else if s == "Proof" then some .proof
  else if s == "Signature" then some .signature
  else if s == "Impossible" then some .impossible
  else if s == "Both" then some .both
  else none

/-- The 13 controllers, `|`-separated and in DECLARATION order, then the txn version. -/
def parsePerms? (s : String) : Option Perms :=
  match s.splitOn "|" with
  | [c0, c1, c2, c3, c4, c5, c6, tv, c7, c8, c9, c10, c11, c12] => do
      let editState ← parseAuth? c0
      let access ← parseAuth? c1
      let send ← parseAuth? c2
      let receive ← parseAuth? c3
      let setDelegate ← parseAuth? c4
      let setPermissions ← parseAuth? c5
      let setVerificationKey ← parseAuth? c6
      let txnVersion ← tv.toNat?
      let setZkappUri ← parseAuth? c7
      let editActionState ← parseAuth? c8
      let setTokenSymbol ← parseAuth? c9
      let incrementNonce ← parseAuth? c10
      let setVotingFor ← parseAuth? c11
      let setTiming ← parseAuth? c12
      some { editState, access, send, receive, setDelegate, setPermissions,
             setVerificationKey, txnVersion, setZkappUri, editActionState,
             setTokenSymbol, incrementNonce, setVotingFor, setTiming }
  | _ => none

/-- Bits as `0`/`1`, one per level, LSB (leaf) first: `1` means the accumulator is the LEFT operand.
Any other character is a refusal — an absent direction must not read as a default. -/
def parseDirs? (s : String) : Option (List Bool) :=
  s.toList.foldr (fun c acc => do
    let rest ← acc
    if c == '1' then some (true :: rest)
    else if c == '0' then some (false :: rest)
    else none) (some [])

/-- The parsed account plus its opening. -/
structure Request where
  bytes : List Nat
  account : Account
  index : Nat
  path : List (Nat × Bool)
deriving Repr

/-- **`decodeAccountWire`** — the `INPUT` grammar, fail-closed on any deviation.

```
INPUT := "blk="  hex bytes of Protocol_state.Value.Stable.V2 (a PREFIX; the rest of the
                 block may follow and is not read)
       ";pk="   Nat "," Bool01          -- public_key.x , is_odd
       ";tk="   Nat                     -- token_id
       ";ts="   Nat                     -- token_symbol, as Token_symbol.to_field
       ";bal="  Nat                     -- balance, nanomina
       ";non="  Nat                     -- nonce
       ";rch="  Nat                     -- receipt_chain_hash
       ";dlg="  Nat "," Bool01          -- delegate.x , is_odd
       ";vf="   Nat                     -- voting_for
       ";tm="   Bool01 "," Nat*5        -- is_timed , initial_min_balance , cliff_time ,
                                        --   cliff_amount , vesting_period , vesting_increment
       ";perm=" Auth("|" Auth)*5 "|" Nat "|" Auth("|" Auth)*5
       ";zk="   ""  |  Nat              -- empty = NO zkApp (default digest); else the digest
       ";idx="  Nat                     -- leaf index
       ";sib="  Nat("," Nat)*           -- sibling hashes, LEAF FIRST
       ";dir="  ("0"|"1")*              -- 1 = the accumulator is the LEFT operand
```

⚑ `zk=` empty is a CLAIM, not a default: it asserts the account has no zkApp, and the account whose
leaf is checked is then the one carrying `Zkapp_account.default_digest`. An account that does have a
zkApp does not open. -/
def decodeAccountWire (s : String) : Option Request :=
  match s.splitOn ";" with
  | [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] => do
      let bytes ← (parseField? "blk" p0).bind parseHexBytes?
      let pk ← (parseField? "pk" p1).bind parseNats?
      let tokenId ← (parseField? "tk" p2).bind String.toNat?
      let tokenSymbol ← (parseField? "ts" p3).bind String.toNat?
      let balance ← (parseField? "bal" p4).bind String.toNat?
      let nonce ← (parseField? "non" p5).bind String.toNat?
      let receiptChainHash ← (parseField? "rch" p6).bind String.toNat?
      let dlg ← (parseField? "dlg" p7).bind parseNats?
      let votingFor ← (parseField? "vf" p8).bind String.toNat?
      let tm ← (parseField? "tm" p9).bind parseNats?
      let permissions ← (parseField? "perm" p10).bind parsePerms?
      let zkRaw ← parseField? "zk" p11
      let zkappDigest : Option Nat ← if zkRaw == "" then some Option.none
                                     else (zkRaw.toNat?).map Option.some
      let index ← (parseField? "idx" p12).bind String.toNat?
      let sibs ← (parseField? "sib" p13).bind parseNats?
      let dirs ← (parseField? "dir" p14).bind parseDirs?
      match pk, dlg, tm with
      | [pkx, pko], [dgx, dgo], [ti, imb, ct, ca, vp, vi] =>
          if sibs.length == dirs.length ∧ pko < 2 ∧ dgo < 2 ∧ ti < 2 then
            some { bytes,
                   account := { publicKeyX := pkx, publicKeyIsOdd := pko == 1,
                                tokenId, tokenSymbol, balance, nonce, receiptChainHash,
                                delegateX := dgx, delegateIsOdd := dgo == 1, votingFor,
                                isTimed := ti == 1, initialMinimumBalance := imb,
                                cliffTime := ct, cliffAmount := ca, vestingPeriod := vp,
                                vestingIncrement := vi, permissions, zkappDigest },
                   index, path := sibs.zip dirs }
          else Option.none
      | _, _, _ => Option.none
  | _ => Option.none

/-- **`minaAccountOpeningGate`** — THE GATE, at the real devnet/mainnet constants. -/
def minaAccountOpeningGate (s : String) : String :=
  match decodeAccountWire s with
  | some r => if accountInBlockLedger mainnet r.bytes r.account r.index r.path then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_mina_account_state_ok]` — the C-ABI entry `dregg-lean-ffi`
calls. One call per exhibited (block, account, opening). -/
@[export dregg_mina_account_state_ok]
def dregg_mina_account_state_ok (s : String) : String := minaAccountOpeningGate s

/-- The gate string IS the decision, by construction, so §6's theorems are theorems about what the
export returns. -/
theorem minaAccountOpeningGate_eq_decision (s : String) (r : Request)
    (hd : decodeAccountWire s = some r) :
    minaAccountOpeningGate s
      = (if accountInBlockLedger mainnet r.bytes r.account r.index r.path then "1" else "0") := by
  unfold minaAccountOpeningGate; rw [hd]

end Dregg2.Bridge.MinaAccountOpening
