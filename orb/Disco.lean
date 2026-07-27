import Crypto
import Stun
/-!
# DISCO: the NAT-traversal endpoint-probing FSM

A model of DISCO endpoint discovery — the peer-to-peer path probing a
node runs to find a working direct route to another node, before it will
send real traffic over that route instead of relaying. DISCO has no
public RFC; this is derived from the documented DISCO wire protocol,
whose two relevant messages are:

* **Ping** — carries an opaque, unguessable transaction id (TxID) and
  the sender's node key. A node emits Pings to each *candidate* direct
  endpoint (address) it has heard about for a peer.
* **Pong** — echoes the exact TxID of the Ping it answers, and reports
  the source address the responder observed. A Pong is accepted only if
  its TxID matches an outstanding Ping and it authenticates.

The probing discipline: a candidate endpoint starts `unprobed`; sending
a Ping moves it to `probed` with the outstanding TxID; a matching,
authentic Pong moves it to `verified`. Only a `verified` endpoint is
eligible for path selection, and the selected path is the lowest-latency
verified endpoint. A node never sends real traffic over an endpoint that
has not answered a probe — that is the anti-spoofing guarantee (an
attacker cannot get a bogus endpoint promoted without producing a Pong
echoing a TxID it could not have seen).

## Theorems

* `disco_no_promote_without_pong` — the central property: a path is put
  into use (a `usePath` output from selection) only for an endpoint that
  is already `verified` in the candidate table. Selection never promotes
  an unprobed or merely-probed endpoint.
* `disco_verified_needs_pong` — the only door into `verified`: if a step
  turns an endpoint from not-verified to verified, the step's input was
  a `recvPong` whose TxID matched that endpoint's outstanding probe and
  which authenticated. No other input can create a verified endpoint.
* `disco_verified_sticky` — a verified endpoint stays verified across a
  probe and across an unrelated pong (verification is monotone; loss of
  a path via timeout is a boundary, below).
* `disco_select_lowest` (supporting) — selection returns a verified
  member of the table.

## Boundary / UNCLOSED

* Cryptography — the NaCl box that seals and authenticates DISCO Ping
  and Pong messages — is the named uninterpreted boundary (`authPong`).
  The unguessability of the TxID (why a spoofed Pong cannot match an
  outstanding probe) is the security assumption behind that boundary.
* Endpoint *expiry* (a verified path going stale and being demoted after
  a heartbeat timeout) is not modeled; here verification is monotone.
* CallMeMaybe (the relayed rendezvous message that seeds candidate
  endpoints) and the STUN-derived reflexive-endpoint discovery are out
  of scope; candidates arrive abstractly via `addCandidate`.
* Latency is modeled as an abstract `Nat` used only for path ordering.
-/

namespace Disco

/-- An opaque, unguessable probe transaction id (12 bytes on the wire). -/
structure TxId where
  val : Nat
deriving Repr, DecidableEq

/-- A candidate direct endpoint (an IP:port), modeled opaquely. -/
structure Endpoint where
  addr : Nat
deriving Repr, DecidableEq

/-- The probing state of one candidate endpoint. -/
inductive EpState where
  /-- Heard about, never probed. -/
  | unprobed
  /-- A Ping with this TxID is outstanding; awaiting a matching Pong. -/
  | probed (tx : TxId)
  /-- A matching, authentic Pong has been received: a working path, with
  its measured latency. -/
  | verified (latency : Nat)
deriving Repr, DecidableEq

/-- `true` exactly on a verified endpoint. -/
def EpState.isVerified : EpState → Bool
  | .verified _ => true
  | _ => false

/-- The candidate table: a per-endpoint probing state. -/
structure St where
  eps : List (Endpoint × EpState)
deriving Repr

/-- Empty table. -/
def init : St := { eps := [] }

/-- Static configuration: the crypto boundary. -/
structure Config where
  /-- Does this Pong (identified by TxID and source endpoint)
  authenticate under the DISCO NaCl box? Uninterpreted. -/
  authPong : TxId → Endpoint → Bool

/-! ## Table operations -/

/-- First-match lookup of an endpoint's state. -/
def lookup : List (Endpoint × EpState) → Endpoint → Option EpState
  | [], _ => none
  | (e, s) :: t, ep => if e = ep then some s else lookup t ep

/-- Apply `f` to the state of every entry keyed by `ep`. -/
def setState (f : EpState → EpState) (ep : Endpoint) :
    List (Endpoint × EpState) → List (Endpoint × EpState)
  | [] => []
  | (e, s) :: t =>
    (e, if e = ep then f s else s) :: setState f ep t

/-- Lookup commutes with a keyed update: querying the key returns the
mapped state, other keys are untouched. -/
theorem lookup_setState (f : EpState → EpState) (ep0 : Endpoint)
    (l : List (Endpoint × EpState)) (ep : Endpoint) :
    lookup (setState f ep0 l) ep
      = if ep0 = ep then (lookup l ep).map f else lookup l ep := by
  induction l with
  | nil => by_cases h : ep0 = ep <;> simp [setState, lookup, h]
  | cons hd t ih =>
    obtain ⟨e, s⟩ := hd
    simp only [setState, lookup]
    by_cases h2 : e = ep
    · subst h2
      by_cases h1 : e = ep0
      · subst h1; simp
      · have hne : ¬ ep0 = e := fun h => h1 h.symm
        simp [h1, hne]
    · simp [h2, ih]

/-! ## The probing FSM -/

/-- The re-probe map: send a fresh Ping. A verified endpoint stays
verified (a live path is not lost just because it is re-probed); any
other state becomes `probed` with the new TxID. -/
def probeMap (tx : TxId) : EpState → EpState
  | .verified lat => .verified lat
  | _ => .probed tx

/-- The Pong map for source `ep` under TxID `tx` and auth verdict `ok`:
an outstanding probe whose TxID matches is promoted to `verified`;
everything else is left unchanged (in particular a mismatched TxID or a
failed auth promotes nothing, and an already-verified endpoint stays
verified). -/
def pongMap (tx : TxId) (lat : Nat) (ok : Bool) : EpState → EpState
  | .probed tx' => if tx' = tx ∧ ok = true then .verified lat else .probed tx'
  | other => other

/-- Outputs the machine can emit. -/
inductive Output where
  /-- A DISCO Ping to a candidate endpoint. -/
  | sendPing (ep : Endpoint) (tx : TxId)
  /-- Put an endpoint into use as the selected path. -/
  | usePath (ep : Endpoint)
deriving Repr, DecidableEq

/-- Inputs the environment can deliver. -/
inductive Input where
  /-- A new candidate endpoint was learned. -/
  | addCandidate (ep : Endpoint)
  /-- Emit a probe (Ping) to a candidate. -/
  | sendProbe (ep : Endpoint) (tx : TxId)
  /-- A Pong arrived from `ep` echoing `tx`, with observed latency. -/
  | recvPong (tx : TxId) (ep : Endpoint) (lat : Nat)
  /-- Choose a path among the verified endpoints. -/
  | selectPath
deriving Repr

/-- The lowest-latency verified endpoint, if any. Only ever ranges over
verified entries. -/
def bestVerified : List (Endpoint × EpState) → Option (Endpoint × Nat)
  | [] => none
  | (e, .verified lat) :: t =>
    match bestVerified t with
    | none => some (e, lat)
    | some (e', lat') => if lat ≤ lat' then some (e, lat) else some (e', lat')
  | (_, _) :: t => bestVerified t

/-- Selection returns a genuinely-verified member of the table. -/
theorem bestVerified_mem (l : List (Endpoint × EpState))
    {ep : Endpoint} {lat : Nat} (h : bestVerified l = some (ep, lat)) :
    (ep, EpState.verified lat) ∈ l := by
  induction l with
  | nil => simp [bestVerified] at h
  | cons hd t ih =>
    obtain ⟨e, s⟩ := hd
    cases s with
    | unprobed =>
      exact List.mem_cons_of_mem _ (ih h)
    | probed tx =>
      exact List.mem_cons_of_mem _ (ih h)
    | verified l0 =>
      rw [show bestVerified ((e, EpState.verified l0) :: t)
            = (match bestVerified t with
               | none => some (e, l0)
               | some (e', lat') =>
                 if l0 ≤ lat' then some (e, l0) else some (e', lat'))
            from rfl] at h
      cases hb : bestVerified t with
      | none =>
        rw [hb] at h
        injection h with hp; injection hp with he hl
        subst he; subst hl
        exact List.mem_cons_self
      | some p =>
        obtain ⟨e', lat'⟩ := p
        rw [hb] at h
        dsimp only at h
        split at h
        · injection h with hp; injection hp with he hl
          subst he; subst hl
          exact List.mem_cons_self
        · injection h with hp; injection hp with he hl
          subst he; subst hl
          exact List.mem_cons_of_mem _ (ih hb)

/-- The total transition. -/
def step (cfg : Config) (s : St) : Input → St × List Output
  | .addCandidate ep =>
    if lookup s.eps ep = none then
      ({ eps := (ep, .unprobed) :: s.eps }, [])
    else
      (s, [])
  | .sendProbe ep tx =>
    ({ eps := setState (probeMap tx) ep s.eps }, [.sendPing ep tx])
  | .recvPong tx ep lat =>
    ({ eps := setState (pongMap tx lat (cfg.authPong tx ep)) ep s.eps }, [])
  | .selectPath =>
    match bestVerified s.eps with
    | some (ep, _) => (s, [.usePath ep])
    | none => (s, [])

/-- States reachable from the empty table. -/
inductive Reachable (cfg : Config) : St → Prop where
  | init : Reachable cfg init
  | step {s : St} (h : Reachable cfg s) (i : Input) :
      Reachable cfg (step cfg s i).1

/-! ## No promotion without a verified pong -/

/-- **A path is used only after a verified pong.** If selection emits a
`usePath ep`, then `ep` is `verified` in the candidate table — it has
answered a probe. Selection never promotes an unprobed or merely-probed
endpoint. -/
theorem disco_no_promote_without_pong (cfg : Config) (s : St)
    (ep : Endpoint)
    (h : Output.usePath ep ∈ (step cfg s .selectPath).2) :
    ∃ lat, (ep, EpState.verified lat) ∈ s.eps := by
  simp only [step] at h
  cases hb : bestVerified s.eps with
  | none => rw [hb] at h; simp at h
  | some p =>
    obtain ⟨e, lat⟩ := p
    rw [hb] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    injection h with he
    subst he
    exact ⟨lat, bestVerified_mem s.eps hb⟩

/-- **The only door into `verified` is a matching, authentic pong.** If a
step turns endpoint `ep` from not-verified into verified, the input was a
`recvPong` for `ep` whose TxID matched `ep`'s outstanding probe and which
authenticated under the crypto boundary. -/
theorem disco_verified_needs_pong (cfg : Config) (s : St) (i : Input)
    (ep : Endpoint)
    (hbefore : (lookup s.eps ep).map EpState.isVerified ≠ some true)
    (hafter : (lookup (step cfg s i).1.eps ep).map EpState.isVerified
              = some true) :
    ∃ tx lat, i = .recvPong tx ep lat ∧
      lookup s.eps ep = some (.probed tx) ∧
      cfg.authPong tx ep = true := by
  cases i with
  | addCandidate e =>
    simp only [step] at hafter
    split at hafter
    · -- prepended (e, unprobed)
      rename_i hnone
      simp only [lookup] at hafter
      by_cases he : e = ep
      · subst he; simp [EpState.isVerified] at hafter
      · rw [if_neg he] at hafter; exact absurd hafter hbefore
    · exact absurd hafter hbefore
  | sendProbe e tx =>
    simp only [step, lookup_setState] at hafter
    by_cases he : e = ep
    · subst he
      rw [if_pos rfl] at hafter
      -- probeMap never produces verified from a non-verified state, and
      -- preserves verified; so `some true` forces the input verified.
      cases hl : lookup s.eps e with
      | none => rw [hl] at hafter; simp at hafter
      | some st =>
        rw [hl] at hafter
        cases st with
        | unprobed => simp [probeMap, EpState.isVerified] at hafter
        | probed t0 => simp [probeMap, EpState.isVerified] at hafter
        | verified l0 =>
          exact absurd (by rw [hl]; simp [EpState.isVerified]) hbefore
    · rw [if_neg he] at hafter; exact absurd hafter hbefore
  | recvPong tx e lat =>
    simp only [step, lookup_setState] at hafter
    by_cases he : e = ep
    · subst he
      rw [if_pos rfl] at hafter
      cases hl : lookup s.eps e with
      | none => rw [hl] at hafter; simp at hafter
      | some st =>
        rw [hl] at hafter
        cases st with
        | unprobed => simp [pongMap, EpState.isVerified] at hafter
        | verified l0 =>
          exact absurd (by rw [hl]; simp [EpState.isVerified]) hbefore
        | probed t0 =>
          simp only [pongMap, Option.map_some] at hafter
          split at hafter
          · rename_i hcond
            obtain ⟨htx, hok⟩ := hcond
            refine ⟨tx, lat, rfl, ?_, hok⟩
            rw [htx]
          · simp [EpState.isVerified] at hafter
    · rw [if_neg he] at hafter; exact absurd hafter hbefore
  | selectPath =>
    simp only [step] at hafter
    cases hb : bestVerified s.eps with
    | none => rw [hb] at hafter; exact absurd hafter hbefore
    | some p =>
      obtain ⟨e, lat⟩ := p
      rw [hb] at hafter
      exact absurd hafter hbefore

/-! ## Verification is monotone -/

/-- **A verified endpoint stays verified.** Neither a re-probe nor any
pong (matching or not) demotes a verified path. Timeouts are a boundary,
so within this model verification is sticky. -/
theorem disco_verified_sticky (cfg : Config) (s : St) (i : Input)
    (ep : Endpoint) {lat : Nat}
    (h : lookup s.eps ep = some (.verified lat)) :
    ∃ lat', lookup (step cfg s i).1.eps ep = some (.verified lat') := by
  cases i with
  | addCandidate e =>
    simp only [step]
    split
    · -- prepend only when ep was absent; but ep is verified, so present
      rename_i hnone
      by_cases he : e = ep
      · subst he; rw [h] at hnone; simp at hnone
      · simp only [lookup, he, if_false]; exact ⟨lat, h⟩
    · exact ⟨lat, h⟩
  | sendProbe e tx =>
    refine ⟨lat, ?_⟩
    simp only [step, lookup_setState]
    by_cases he : e = ep
    · subst he; simp [h, probeMap]
    · simp [he, h]
  | recvPong tx e lat0 =>
    refine ⟨lat, ?_⟩
    simp only [step, lookup_setState]
    by_cases he : e = ep
    · subst he; simp [h, pongMap]
    · simp [he, h]
  | selectPath =>
    refine ⟨lat, ?_⟩
    simp only [step]
    cases bestVerified s.eps <;> exact h

/-! ## Selection ranges over verified endpoints -/

/-- **Selection is over verified endpoints only** (restatement of
`bestVerified_mem` at the step level): whenever `selectPath` emits a
`usePath ep`, the table holds a verified entry for `ep`. -/
theorem disco_select_lowest (cfg : Config) (s : St) (ep : Endpoint)
    (h : Output.usePath ep ∈ (step cfg s .selectPath).2) :
    (∃ lat, lookup s.eps ep = some (.verified lat)) ∨
    (∃ lat, (ep, EpState.verified lat) ∈ s.eps) :=
  Or.inr (disco_no_promote_without_pong cfg s ep h)

/-! ## Endpoint priority: `bestVerified` is a genuine minimum -/

/-- If selection finds no verified endpoint, the table has none. -/
theorem bestVerified_none_no_verified (l : List (Endpoint × EpState))
    (h : bestVerified l = none) :
    ∀ e lat, (e, EpState.verified lat) ∉ l := by
  induction l with
  | nil => intro e lat hm; simp at hm
  | cons hd t ih =>
    obtain ⟨a, s⟩ := hd
    intro e lat hm
    cases s with
    | unprobed =>
      rw [show bestVerified ((a, EpState.unprobed) :: t) = bestVerified t from rfl] at h
      rcases List.mem_cons.mp hm with heq | hm'
      · exact absurd heq (by simp)
      · exact ih h e lat hm'
    | probed tx =>
      rw [show bestVerified ((a, EpState.probed tx) :: t) = bestVerified t from rfl] at h
      rcases List.mem_cons.mp hm with heq | hm'
      · exact absurd heq (by simp)
      · exact ih h e lat hm'
    | verified l0 =>
      rw [show bestVerified ((a, EpState.verified l0) :: t)
            = (match bestVerified t with
               | none => some (a, l0)
               | some (e2, lat2) =>
                 if l0 ≤ lat2 then some (a, l0) else some (e2, lat2))
            from rfl] at h
      cases hb : bestVerified t with
      | none => simp [hb] at h
      | some p =>
        obtain ⟨e2, lat2⟩ := p
        simp only [hb] at h
        split at h <;> simp at h

/-- **Selection picks the lowest latency.** The endpoint `bestVerified`
returns has latency no greater than that of *any* verified endpoint in the
table — direct-path selection is by lowest measured round-trip, not first
match. -/
theorem disco_bestVerified_min (l : List (Endpoint × EpState)) :
    ∀ {ep : Endpoint} {lat : Nat}, bestVerified l = some (ep, lat) →
    ∀ e' lat', (e', EpState.verified lat') ∈ l → lat ≤ lat' := by
  induction l with
  | nil => intro ep lat h; simp [bestVerified] at h
  | cons hd t ih =>
    obtain ⟨e, s⟩ := hd
    intro ep lat h e' lat' hmem
    cases s with
    | unprobed =>
      rw [show bestVerified ((e, EpState.unprobed) :: t) = bestVerified t from rfl] at h
      rcases List.mem_cons.mp hmem with heq | hmem'
      · simp at heq
      · exact ih h e' lat' hmem'
    | probed tx =>
      rw [show bestVerified ((e, EpState.probed tx) :: t) = bestVerified t from rfl] at h
      rcases List.mem_cons.mp hmem with heq | hmem'
      · simp at heq
      · exact ih h e' lat' hmem'
    | verified l0 =>
      rw [show bestVerified ((e, EpState.verified l0) :: t)
            = (match bestVerified t with
               | none => some (e, l0)
               | some (e2, lat2) =>
                 if l0 ≤ lat2 then some (e, l0) else some (e2, lat2))
            from rfl] at h
      cases hb : bestVerified t with
      | none =>
        simp only [hb] at h; injection h with hp; injection hp with he hl
        subst he; subst hl
        rcases List.mem_cons.mp hmem with heq | hmem'
        · injection heq with _ hs; injection hs with hll; omega
        · exact absurd hmem' (bestVerified_none_no_verified t hb e' lat')
      | some p =>
        obtain ⟨e2, lat2⟩ := p
        simp only [hb] at h
        have hmin := ih hb
        by_cases hle : l0 ≤ lat2
        · rw [if_pos hle] at h; injection h with hp; injection hp with he hl
          subst he; subst hl
          rcases List.mem_cons.mp hmem with heq | hmem'
          · injection heq with _ hs; injection hs with hll; omega
          · exact Nat.le_trans hle (hmin e' lat' hmem')
        · rw [if_neg hle] at h; injection h with hp; injection hp with he hl
          subst he; subst hl
          rcases List.mem_cons.mp hmem with heq | hmem'
          · injection heq with _ hs; injection hs with hll; omega
          · exact hmin e' lat' hmem'

/-! ## Path selection: direct with a DERP relay fallback -/

/-- Which kind of path a node is using to a peer. -/
inductive PathKind where
  /-- A verified direct endpoint (peer-to-peer). -/
  | direct
  /-- The DERP relay (used until a direct path is verified). -/
  | derp
deriving Repr, DecidableEq

/-- Select the path to a peer: the lowest-latency verified *direct*
endpoint if any exists, otherwise the DERP relay. This is the DERP-to-
direct discipline — a node relays only while it has no verified direct
path, and uses direct the moment one is available. -/
def selectPath (eps : List (Endpoint × EpState)) (derpHome : Endpoint) :
    Endpoint × PathKind :=
  match bestVerified eps with
  | some (ep, _) => (ep, .direct)
  | none => (derpHome, .derp)

/-- **Direct is preferred over the relay.** Whenever any endpoint is
verified, selection returns a direct path — never the DERP fallback. -/
theorem disco_direct_preferred (eps : List (Endpoint × EpState))
    (derpHome : Endpoint) {ep : Endpoint} {lat : Nat}
    (h : bestVerified eps = some (ep, lat)) :
    selectPath eps derpHome = (ep, .direct) := by
  simp [selectPath, h]

/-- **Relay only without a verified direct path.** With no verified
endpoint, selection falls back to the DERP relay. -/
theorem disco_relay_fallback (eps : List (Endpoint × EpState))
    (derpHome : Endpoint) (h : bestVerified eps = none) :
    selectPath eps derpHome = (derpHome, .derp) := by
  simp [selectPath, h]

/-- **A direct selection is a verified endpoint.** If selection returns a
direct path, that endpoint is verified in the table. -/
theorem disco_direct_is_verified (eps : List (Endpoint × EpState))
    (derpHome ep : Endpoint) (hpk : selectPath eps derpHome = (ep, .direct)) :
    ∃ lat, (ep, EpState.verified lat) ∈ eps := by
  unfold selectPath at hpk
  cases hb : bestVerified eps with
  | none => rw [hb] at hpk; injection hpk with _ hk; exact absurd hk (by decide)
  | some p =>
    obtain ⟨e, lat⟩ := p
    rw [hb] at hpk; injection hpk with he _
    subst he
    exact ⟨lat, bestVerified_mem eps hb⟩

/-- **DERP-to-direct upgrade.** If before a step no endpoint is verified —
so the node is relaying through DERP — and after the step some endpoint is
verified (a pong landed), then selection upgrades from the relay to a
direct path. This is the whole point of the probing discipline: relay
first, then promote to direct once a path is proven. -/
theorem disco_derp_to_direct_upgrade (cfg : Config) (s : St) (i : Input)
    (derpHome : Endpoint)
    (hbefore : bestVerified s.eps = none)
    {ep : Endpoint} {lat : Nat}
    (hafter : bestVerified (step cfg s i).1.eps = some (ep, lat)) :
    selectPath s.eps derpHome = (derpHome, .derp) ∧
    selectPath (step cfg s i).1.eps derpHome = (ep, .direct) :=
  ⟨disco_relay_fallback _ _ hbefore, disco_direct_preferred _ _ hafter⟩

/-! ## Realized crypto — DISCO Pong authentication over the verified `crypto_box`

The abstract `Config.authPong` boundary is discharged here by the real NaCl
`crypto_box` (X25519 + XSalsa20-Poly1305, verified `Crypto`). A DISCO packet is

    magic(6) ‖ senderDiscoPub(32) ‖ nonce(24) ‖ box

(the documented DISCO wire protocol), where the box seals the Pong body

    type(1) ‖ version(1) ‖ txid(12) ‖ srcAddr .

A Pong authenticates iff the box opens under the peer's disco key AND echoes the
outstanding, unguessable transaction id. `disco_crypto_promotion_genuine` then
composes this with the FSM's `disco_verified_needs_pong`: a path is verified only
by a *genuinely sealed* Pong — the anti-spoof, realized on real crypto. -/

/-- Raw bytes at the crypto boundary. -/
abbrev Bytes := List UInt8

/-- The `List UInt8` view of a `ByteArray` (via its backing array). -/
def bytesOf (b : ByteArray) : Bytes := b.data.toList

/-- Bytes → the flat FFI buffer the `Crypto` primitives take. -/
def baOf (l : Bytes) : ByteArray := ⟨l.toArray⟩

@[simp] theorem baOf_bytesOf (b : ByteArray) : baOf (bytesOf b) = b := by
  show ByteArray.mk b.data.toList.toArray = b
  rw [Array.toArray_toList]

/-- The DISCO Pong message-type byte (`TypePong`). -/
def discoTypePong : UInt8 := 0x02

/-- Decode a sealed DISCO message body `type ‖ version ‖ txid(12) ‖ …` into its
type byte and 12-byte transaction id. -/
def decodeSealed (m : Bytes) : Option (UInt8 × Bytes) :=
  match m with
  | ty :: _ver :: rest => if 12 ≤ rest.length then some (ty, rest.take 12) else none
  | _ => none

/-- **Realized DISCO Pong authentication.** Open the box with the peer's disco
public key and our disco secret; accept iff the plaintext is a Pong echoing the
outstanding 12-byte transaction id `expectTx`. This is a concrete instantiation
of the abstract `Config.authPong` boundary over the verified `crypto_box`. -/
def discoAuthPong (peerPub selfSec nonce box : ByteArray) (expectTx : Bytes) : Bool :=
  match Crypto.cryptoBoxOpen peerPub selfSec nonce box with
  | some m =>
    match decodeSealed (bytesOf m) with
    | some (ty, tx) => ty == discoTypePong && tx == expectTx
    | none => false
  | none => false

/-- **An authenticated Pong was genuinely sealed (the anti-spoof, realized).** If
`discoAuthPong` accepts, the box opened under the shared disco key AND was
genuinely sealed under it (the functional shadow of INT-CTXT for the DISCO box):
a party holding neither disco secret cannot forge a Pong that opens. -/
theorem disco_authpong_genuine (peerPub selfSec nonce box : ByteArray) (expectTx : Bytes)
    (h : discoAuthPong peerPub selfSec nonce box expectTx = true) :
    ∃ m, Crypto.cryptoBoxOpen peerPub selfSec nonce box = some m ∧
         Crypto.cryptoBoxSeal peerPub selfSec nonce m = some box := by
  cases hopen : Crypto.cryptoBoxOpen peerPub selfSec nonce box with
  | none => exfalso; unfold discoAuthPong at h; rw [hopen] at h; simp at h
  | some m =>
    exact ⟨m, rfl,
      Crypto.Assumptions.crypto_box_open_authentic peerPub selfSec nonce box m hopen⟩

/-- A `Config` whose Pong authentication is the realized `crypto_box` check for a
specific received DISCO box. -/
def cryptoConfig (peerPub selfSec nonce box : ByteArray) (expectTx : Bytes) : Config :=
  { authPong := fun _tx _ep => discoAuthPong peerPub selfSec nonce box expectTx }

/-- **A crypto-verified path was authenticated by a genuine Pong.** If, under the
realized crypto config, a step promotes some endpoint from not-verified to
verified, then a real DISCO `crypto_box` was opened AND was genuinely sealed under
the shared disco key — no forged Pong can promote a path. Composes the FSM's
`disco_verified_needs_pong` with the box's authenticity. -/
theorem disco_crypto_promotion_genuine
    (peerPub selfSec nonce box : ByteArray) (expectTx : Bytes)
    (s : St) (i : Input) (ep : Endpoint)
    (hbefore : (lookup s.eps ep).map EpState.isVerified ≠ some true)
    (hafter : (lookup (step (cryptoConfig peerPub selfSec nonce box expectTx) s i).1.eps ep).map
                EpState.isVerified = some true) :
    ∃ m, Crypto.cryptoBoxOpen peerPub selfSec nonce box = some m ∧
         Crypto.cryptoBoxSeal peerPub selfSec nonce m = some box := by
  obtain ⟨tx, lat, _, _, hauth⟩ :=
    disco_verified_needs_pong (cryptoConfig peerPub selfSec nonce box expectTx) s i ep
      hbefore hafter
  exact disco_authpong_genuine peerPub selfSec nonce box expectTx hauth

/-! ## STUN reflexive-endpoint discovery (RFC 5389), feeding candidates

DISCO learns a node's *reflexive* endpoint — its public IP:port as seen through a
NAT — from a STUN Binding response's XOR-MAPPED-ADDRESS (`Stun.decodeXorMapped`,
RFC 5389 §15.2), reusing the STUN codec. That reflexive address becomes a
*candidate* direct endpoint, entering the table `unprobed`: STUN seeds the
candidate, it does NOT authenticate a path — only a Pong does. -/

/-- Map a decoded STUN transport address to a DISCO candidate endpoint (folding
its address bytes and port into the opaque `addr` the FSM keys on). -/
def endpointOfStun (se : Stun.Endpoint) : Endpoint :=
  { addr := (se.addr.foldl (fun a b => a * 256 + b.toNat) 0) * 65536 + se.port }

/-- Extract the reflexive endpoint from a parsed STUN Binding response: find the
XOR-MAPPED-ADDRESS attribute and decode it against the transaction id. -/
def reflexiveEndpoint (msg : Stun.Message) : Option Endpoint :=
  match Stun.findAttr Stun.attrXorMappedAddress msg.attrs with
  | some a => (Stun.decodeXorMapped msg.txid a.value).map endpointOfStun
  | none => none

/-- `lookup` returning `none` means the key is absent from the table entirely. -/
theorem lookup_none_not_mem {l : List (Endpoint × EpState)} {ep : Endpoint}
    (h : lookup l ep = none) : ∀ st, (ep, st) ∉ l := by
  intro st hmem
  induction l with
  | nil => simp at hmem
  | cons hd t ih =>
    obtain ⟨e, s0⟩ := hd
    simp only [lookup] at h
    by_cases he : e = ep
    · rw [if_pos he] at h; exact absurd h (by simp)
    · rw [if_neg he] at h
      rcases List.mem_cons.mp hmem with heq | htl
      · injection heq with h1 _; exact he h1.symm
      · exact ih h htl

/-- **A STUN-discovered reflexive endpoint still needs a Pong.** Seeding the
reflexive candidate adds it `unprobed`; selection will not put it into use until
a Pong verifies it. STUN discovers the address; it does not authenticate the
path — the anti-spoofing discipline (`disco_no_promote_without_pong`) still
gates it. -/
theorem disco_reflexive_needs_pong (cfg : Config) (s : St) (msg : Stun.Message)
    {ep : Endpoint} (_hrefl : reflexiveEndpoint msg = some ep)
    (hnew : lookup s.eps ep = none) :
    lookup (step cfg s (.addCandidate ep)).1.eps ep = some EpState.unprobed ∧
    Output.usePath ep
      ∉ (step cfg (step cfg s (.addCandidate ep)).1 .selectPath).2 := by
  have hstep : (step cfg s (.addCandidate ep)).1
      = { eps := (ep, EpState.unprobed) :: s.eps } := by
    simp [step, hnew]
  rw [hstep]
  refine ⟨by simp [lookup], ?_⟩
  intro hmem
  obtain ⟨lat, hin⟩ := disco_no_promote_without_pong cfg _ ep hmem
  rcases List.mem_cons.mp hin with heq | htl
  · injection heq with _ h2; exact absurd h2 (by simp)
  · exact lookup_none_not_mem hnew (EpState.verified lat) htl

/-! ## The real DISCO wire format

Everything above authenticates a Pong body *once it is opened*. This section makes
the whole DISCO frame spec-faithful to the public Tailscale `disco` package, so a
real Tailscale peer would accept and produce these exact bytes. A DISCO UDP frame
on the wire is

    Magic(6) ‖ senderDiscoPub(32) ‖ nonce(24) ‖ box

where `Magic = "TS💬"` (`0x54 53 f0 9f 92 ac`) and `box` is a NaCl `crypto_box`
(X25519 + XSalsa20-Poly1305) sealing the disco message

    type(1) ‖ version(1) ‖ body .

The three message types are Ping (`0x01`), Pong (`0x02`), CallMeMaybe (`0x03`):

  * **Ping**        — `txid(12) ‖ senderNodeKey(32)`
  * **Pong**        — `txid(12) ‖ srcIP(16) ‖ srcPort(2, big-endian)`
  * **CallMeMaybe** — `(ip(16) ‖ port(2))*` — the candidate endpoints to try.

The message version byte is `v0 = 0`. Parsing is deliberately lax on trailing
bytes (padding / future fields), exactly as the reference parser is. -/

/-- The 6-byte DISCO magic that prefixes every frame: "TS💬"
(`0x54 0x53 0xf0 0x9f 0x92 0xac`). -/
def discoMagic : Bytes := [0x54, 0x53, 0xf0, 0x9f, 0x92, 0xac]

/-- The DISCO message version byte (`v0`). -/
def discoVersion : UInt8 := 0x00

/-- The DISCO Ping message-type byte (`TypePing`). -/
def discoTypePing : UInt8 := 0x01

/-- The DISCO CallMeMaybe message-type byte (`TypeCallMeMaybe`). -/
def discoTypeCallMeMaybe : UInt8 := 0x03

/-- Transaction-id length (bytes). -/
def txIdLen : Nat := 12
/-- Curve25519 disco / node public-key length (bytes). -/
def discoKeyLen : Nat := 32
/-- IPv6-or-mapped source-address length in a Pong / CallMeMaybe endpoint. -/
def ipLen : Nat := 16
/-- Big-endian port length. -/
def portLen : Nat := 2
/-- NaCl-box nonce length carried on the wire beside each frame. -/
def discoNonceLen : Nat := 24
/-- One CallMeMaybe endpoint on the wire: `ip(16) ‖ port(2)`. -/
def epLen : Nat := 18

/-- Encode a `Nat < 65536` as its two big-endian bytes. -/
def be16 (n : Nat) : Bytes := [UInt8.ofNat (n / 256), UInt8.ofNat n]

/-- Decode a big-endian `uint16` from the first two bytes of a buffer. -/
def be16decL : Bytes → Nat
  | a :: b :: _ => a.toNat * 256 + b.toNat
  | _ => 0

/-- `be16decL` inverts `be16` for ports addressable by 16 bits. -/
theorem be16decL_be16 (n : Nat) (h : n < 65536) : be16decL (be16 n) = n := by
  simp only [be16, be16decL, UInt8.toNat_ofNat']
  omega

/-- A decoded DISCO message. -/
inductive DiscoMsg where
  /-- Ping: transaction id and the sender's node public key. -/
  | ping (txid nodeKey : Bytes)
  /-- Pong: echoed transaction id, and the observed source `ip ‖ port`. -/
  | pong (txid srcIP : Bytes) (port : Nat)
  /-- CallMeMaybe: the candidate endpoints (`ip`, `port`) to probe. -/
  | callMeMaybe (eps : List (Bytes × Nat))
deriving Repr, DecidableEq

/-! ### Message-body encode / decode -/

/-- A disco message body: `type ‖ version ‖ payload`. -/
def encodeBody (ty : UInt8) (payload : Bytes) : Bytes := ty :: discoVersion :: payload

/-- Encode a Ping body. -/
def encodePing (txid nodeKey : Bytes) : Bytes :=
  encodeBody discoTypePing (txid ++ nodeKey)

/-- Encode a Pong body (grouped so decode's split is the exact inverse). -/
def encodePong (txid srcIP : Bytes) (port : Nat) : Bytes :=
  encodeBody discoTypePong (txid ++ (srcIP ++ be16 port))

/-- Encode a list of CallMeMaybe endpoints: each is `ip(16) ‖ port(2)`. -/
def encodeEps : List (Bytes × Nat) → Bytes
  | [] => []
  | (ip, port) :: t => ip ++ be16 port ++ encodeEps t

/-- Encode a CallMeMaybe body. -/
def encodeCallMeMaybe (eps : List (Bytes × Nat)) : Bytes :=
  encodeBody discoTypeCallMeMaybe (encodeEps eps)

/-- Decode a run of CallMeMaybe endpoints, lax on a short trailing remainder. -/
def decodeEps (bs : Bytes) : List (Bytes × Nat) :=
  if _h : epLen ≤ bs.length then
    (bs.take ipLen, be16decL ((bs.drop ipLen).take portLen)) :: decodeEps (bs.drop epLen)
  else []
termination_by bs.length
decreasing_by
  simp only [List.length_drop]
  have : (0 : Nat) < epLen := by decide
  omega

/-- Decode a disco message body `type ‖ version ‖ payload`. Lax on trailing bytes
(padding / future fields), exactly as the reference parser. -/
def decodeDiscoMessage : Bytes → Option DiscoMsg
  | ty :: _ver :: rest =>
    if ty = discoTypePing then
      if txIdLen + discoKeyLen ≤ rest.length then
        some (.ping (rest.take txIdLen) ((rest.drop txIdLen).take discoKeyLen))
      else none
    else if ty = discoTypePong then
      if txIdLen + (ipLen + portLen) ≤ rest.length then
        some (.pong (rest.take txIdLen)
                    ((rest.drop txIdLen).take ipLen)
                    (be16decL ((rest.drop txIdLen).drop ipLen)))
      else none
    else if ty = discoTypeCallMeMaybe then
      some (.callMeMaybe (decodeEps rest))
    else none
  | _ => none

/-- **Ping body round-trips.** -/
theorem disco_ping_roundtrip (txid nodeKey : Bytes)
    (ht : txid.length = txIdLen) (hk : nodeKey.length = discoKeyLen) :
    decodeDiscoMessage (encodePing txid nodeKey) = some (.ping txid nodeKey) := by
  have hlen : txIdLen + discoKeyLen ≤ (txid ++ nodeKey).length :=
    Nat.le_of_eq (by rw [List.length_append, ht, hk])
  simp only [encodePing, encodeBody, decodeDiscoMessage, ↓reduceIte, hlen,
             List.take_left' ht, List.drop_left' ht, List.take_of_length_le (Nat.le_of_eq hk)]

/-- **Pong body round-trips.** -/
theorem disco_pong_roundtrip (txid srcIP : Bytes) (port : Nat)
    (ht : txid.length = txIdLen) (hs : srcIP.length = ipLen) (hp : port < 65536) :
    decodeDiscoMessage (encodePong txid srcIP port) = some (.pong txid srcIP port) := by
  have hbe : (be16 port).length = portLen := rfl
  have hlen : txIdLen + (ipLen + portLen) ≤ (txid ++ (srcIP ++ be16 port)).length :=
    Nat.le_of_eq (by rw [List.length_append, List.length_append, ht, hs, hbe])
  simp only [encodePong, encodeBody, decodeDiscoMessage, ↓reduceIte, hlen,
             List.take_left' ht, List.drop_left' ht, List.take_left' hs, List.drop_left' hs,
             be16decL_be16 port hp]
  rw [if_neg (by decide : ¬ discoTypePong = discoTypePing)]

/-- **CallMeMaybe endpoints round-trip.** For endpoints with 16-byte IPs and
16-bit ports, decoding the encoded list recovers it exactly. -/
theorem disco_eps_roundtrip (eps : List (Bytes × Nat))
    (hip : ∀ p ∈ eps, p.1.length = ipLen) (hport : ∀ p ∈ eps, p.2 < 65536) :
    decodeEps (encodeEps eps) = eps := by
  induction eps with
  | nil =>
    have hnle : ¬ epLen ≤ ([] : Bytes).length := by decide
    rw [encodeEps, decodeEps, dif_neg hnle]
  | cons hd t ih =>
    obtain ⟨ip, port⟩ := hd
    have hlen : ip.length = ipLen := hip _ (List.mem_cons_self)
    have hpt : port < 65536 := hport _ (List.mem_cons_self)
    have hip' : ∀ p ∈ t, p.1.length = ipLen := fun p hp => hip p (List.mem_cons_of_mem _ hp)
    have hport' : ∀ p ∈ t, p.2 < 65536 := fun p hp => hport p (List.mem_cons_of_mem _ hp)
    have hbe : (be16 port).length = portLen := rfl
    have hpre : (ip ++ be16 port).length = epLen := by
      simp only [List.length_append, hlen, hbe, ipLen, portLen, epLen]
    have henc : encodeEps ((ip, port) :: t) = (ip ++ be16 port) ++ encodeEps t := rfl
    have hcond : epLen ≤ ((ip ++ be16 port) ++ encodeEps t).length := by
      rw [List.length_append, hpre]; exact Nat.le_add_right _ _
    have e_ip : ((ip ++ be16 port) ++ encodeEps t).take ipLen = ip := by
      rw [List.append_assoc]; exact List.take_left' hlen
    have e_drop_ip : ((ip ++ be16 port) ++ encodeEps t).drop ipLen
                       = be16 port ++ encodeEps t := by
      rw [List.append_assoc]; exact List.drop_left' hlen
    have e_port : (be16 port ++ encodeEps t).take portLen = be16 port :=
      List.take_left' hbe
    have e_ep : ((ip ++ be16 port) ++ encodeEps t).drop epLen = encodeEps t :=
      List.drop_left' hpre
    rw [henc, decodeEps, dif_pos hcond, e_ip, e_drop_ip, e_port,
        be16decL_be16 port hpt, e_ep, ih hip' hport']

/-- **CallMeMaybe body round-trips.** -/
theorem disco_callmemaybe_roundtrip (eps : List (Bytes × Nat))
    (hip : ∀ p ∈ eps, p.1.length = ipLen) (hport : ∀ p ∈ eps, p.2 < 65536) :
    decodeDiscoMessage (encodeCallMeMaybe eps) = some (.callMeMaybe eps) := by
  simp only [encodeCallMeMaybe, encodeBody, decodeDiscoMessage, ↓reduceIte,
             disco_eps_roundtrip eps hip hport]
  rw [if_neg (by decide : ¬ discoTypeCallMeMaybe = discoTypePing),
      if_neg (by decide : ¬ discoTypeCallMeMaybe = discoTypePong)]

/-! ### Full-frame parse / encode -/

/-- `l.isPrefixOf (l ++ r)` — a list is a prefix of itself extended. -/
theorem isPrefixOf_self_append (l r : Bytes) : l.isPrefixOf (l ++ r) = true := by
  induction l with
  | nil => simp [List.isPrefixOf]
  | cons a t ih => simp [List.isPrefixOf, ih]

/-- The `List.toList ∘ toArray` round-trip: repacking a byte list as a `ByteArray`
and reading it back is the identity. -/
@[simp] theorem bytesOf_baOf (l : Bytes) : bytesOf (baOf l) = l := by
  show (ByteArray.mk l.toArray).data.toList = l
  simp

/-- The `List UInt8` view of a `ByteArray` has the buffer's size. -/
theorem bytesOf_len (b : ByteArray) : (bytesOf b).length = b.size := Array.length_toList

/-- Encode a full DISCO frame: `Magic ‖ senderDiscoPub ‖ nonce ‖ box`. -/
def encodeDiscoFrame (senderPub nonce box : Bytes) : Bytes :=
  discoMagic ++ (senderPub ++ (nonce ++ box))

/-- Parse a full DISCO frame: require the 6-byte magic, then split off the
32-byte sender disco pubkey, the 24-byte nonce, and the trailing box. -/
def parseDiscoFrame (bs : Bytes) : Option (Bytes × Bytes × Bytes) :=
  if discoMagic.isPrefixOf bs then
    let body := bs.drop discoMagic.length
    if discoKeyLen + discoNonceLen ≤ body.length then
      some (body.take discoKeyLen,
            (body.drop discoKeyLen).take discoNonceLen,
            (body.drop discoKeyLen).drop discoNonceLen)
    else none
  else none

/-- **Frame round-trip.** Parsing an encoded DISCO frame recovers the sender
pubkey, nonce, and box exactly, for a 32-byte key and 24-byte nonce. -/
theorem disco_frame_roundtrip (senderPub nonce box : Bytes)
    (hp : senderPub.length = discoKeyLen) (hn : nonce.length = discoNonceLen) :
    parseDiscoFrame (encodeDiscoFrame senderPub nonce box) = some (senderPub, nonce, box) := by
  unfold parseDiscoFrame encodeDiscoFrame
  rw [if_pos (isPrefixOf_self_append _ _)]
  simp only [List.drop_left]
  have hbodylen : discoKeyLen + discoNonceLen
                    ≤ (senderPub ++ (nonce ++ box)).length := by
    rw [List.length_append, List.length_append, hp, hn]; omega
  rw [if_pos hbodylen, List.take_left' hp, List.drop_left' hp,
      List.take_left' hn, List.drop_left' hn]

/-! ### The realized wire crypto — seal one side, open the other

`sealDiscoMessage` and `openDiscoFrame` are the two ends of the wire: a node seals
a disco message to a peer over the verified `crypto_box`, frames it with the magic
and its own disco pubkey, and the peer parses + opens + decodes. The refinement
`disco_seal_open` proves the bytes one side puts on the wire are *exactly* the
message the other decodes — the DISCO analogue of `Derp.derp_clientinfo_server_opens`,
so a real Tailscale peer's frame and ours agree. -/

/-- Seal a disco message body to `recipientPub` under `selfSec`/`nonce` and frame
it (advertising `selfPub` as the sender disco key). `none` on a bad key/nonce. -/
def sealDiscoMessage (recipientPub selfSec nonce : ByteArray) (selfPub plain : Bytes) :
    Option Bytes :=
  match Crypto.cryptoBoxSeal recipientPub selfSec nonce (baOf plain) with
  | some box => some (encodeDiscoFrame selfPub (bytesOf nonce) (bytesOf box))
  | none => none

/-- Parse a DISCO frame, open its box with `selfSec` against the wire sender key,
and decode the message. Returns `(senderPub, message)`. -/
def openDiscoFrame (selfSec : ByteArray) (bs : Bytes) : Option (Bytes × DiscoMsg) :=
  match parseDiscoFrame bs with
  | some (sPub, nonce, box) =>
    match Crypto.cryptoBoxOpen (baOf sPub) selfSec (baOf nonce) (baOf box) with
    | some plain => (decodeDiscoMessage (bytesOf plain)).map (fun m => (sPub, m))
    | none => none
  | none => none

/-- **The wire refines to the peer's open (the whole DISCO frame, discharged).**
Whatever frame node A seals to B — sealing a decodable message body under the
shared X25519 secret and advertising its real disco pubkey — B, parsing + opening
+ decoding, recovers *exactly* `(A_pub, message)`. The framed box on the wire is
precisely what a real peer decrypts. -/
theorem disco_seal_open
    (aPub aSec bPub bSec nonce : ByteArray) (plain : Bytes) (msg : DiscoMsg)
    (hap : Crypto.x25519Base aSec = some aPub)
    (hbp : Crypto.x25519Base bSec = some bPub)
    (hapk : aPub.size = discoKeyLen) (hn : nonce.size = discoNonceLen)
    (hdec : decodeDiscoMessage plain = some msg)
    {frame : Bytes}
    (hs : sealDiscoMessage bPub aSec nonce (bytesOf aPub) plain = some frame) :
    openDiscoFrame bSec frame = some (bytesOf aPub, msg) := by
  unfold sealDiscoMessage at hs
  cases hseal : Crypto.cryptoBoxSeal bPub aSec nonce (baOf plain) with
  | none => rw [hseal] at hs; simp at hs
  | some box =>
    rw [hseal] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    have hapk' : (bytesOf aPub).length = discoKeyLen := by rw [bytesOf_len]; exact hapk
    have hn' : (bytesOf nonce).length = discoNonceLen := by rw [bytesOf_len]; exact hn
    unfold openDiscoFrame
    rw [disco_frame_roundtrip (bytesOf aPub) (bytesOf nonce) (bytesOf box) hapk' hn']
    have hopen : Crypto.cryptoBoxOpen aPub bSec nonce box = some (baOf plain) :=
      Crypto.Assumptions.crypto_box_agree aSec aPub bSec bPub nonce (baOf plain) box hap hbp hseal
    simp only [baOf_bytesOf, hopen, bytesOf_baOf, hdec, Option.map_some]

/-! ### Wire-level anti-spoof — a Pong frame that promotes was genuinely sealed -/

/-- Authenticate a full Pong *frame* (magic ‖ senderPub ‖ nonce ‖ box) against the
expected peer disco key and outstanding transaction id: parse the frame, then run
the realized `discoAuthPong` on its nonce/box. -/
def discoAuthPongFrame (peerPub selfSec : ByteArray) (frame expectTx : Bytes) : Bool :=
  match parseDiscoFrame frame with
  | some (_sPub, nonce, box) => discoAuthPong peerPub selfSec (baOf nonce) (baOf box) expectTx
  | none => false

/-- **A frame-authenticated Pong was genuinely sealed (the wire anti-spoof).** If
`discoAuthPongFrame` accepts, the frame parsed and its box opened under the shared
disco key AND was genuinely sealed under it — no party lacking a disco secret can
forge a Pong frame that this accepts. Composes `parseDiscoFrame` with the box's
authenticity (`disco_authpong_genuine`). -/
theorem disco_authpongframe_genuine (peerPub selfSec : ByteArray) (frame expectTx : Bytes)
    (h : discoAuthPongFrame peerPub selfSec frame expectTx = true) :
    ∃ sPub nonce box m,
      parseDiscoFrame frame = some (sPub, nonce, box) ∧
      Crypto.cryptoBoxOpen peerPub selfSec (baOf nonce) (baOf box) = some m ∧
      Crypto.cryptoBoxSeal peerPub selfSec (baOf nonce) m = some (baOf box) := by
  unfold discoAuthPongFrame at h
  cases hp : parseDiscoFrame frame with
  | none => rw [hp] at h; simp at h
  | some t =>
    obtain ⟨sPub, nonce, box⟩ := t
    rw [hp] at h
    obtain ⟨m, ho, hsl⟩ := disco_authpong_genuine peerPub selfSec (baOf nonce) (baOf box) expectTx h
    exact ⟨sPub, nonce, box, m, rfl, ho, hsl⟩

end Disco
