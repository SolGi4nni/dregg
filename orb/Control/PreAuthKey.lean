import Control

/-!
# Control.PreAuthKey — the pre-auth key registration gate

The **primary homelab registration path**: an operator mints a pre-auth key, and
a node registers non-interactively with `tailscale up --authkey=<key>`. The key
travels in `tailcfg.RegisterRequest.Auth.AuthKey`
(github.com/tailscale/tailscale `tailcfg/tailcfg.go`: `RegisterResponseAuth.AuthKey string`
+ `RegisterRequest.Auth *RegisterResponseAuth`); `Control.RegisterRequest.authKey`
is that field. This module supplies the key **model** and wires its verdict into
the already-proven admission seam `Control.Policy.authorizes`.

## Ground truth (cited, PUBLIC sources — never invented)

Modelled on headscale's pre-auth key (github.com/juanfont/headscale):

* `hscontrol/types/preauth_key.go:38-73` — `type PreAuthKey struct` fields:
  `Reusable bool` (`:58`), `Ephemeral bool` (`:59`), `Used bool` (`:60`),
  `Tags []string` (`:65`, "copied to the node during registration", `:62-63`),
  `Expiration *time.Time` (`:68`), `Revoked *time.Time` (`:73`), and the
  hashed-at-rest storage `Prefix string` / `Hash []byte` (`:45-46`).
* `hscontrol/types/preauth_key.go:89-118` — `func (pak *PreAuthKey) Validate()`
  order: `Revoked != nil` → reject (`:100-101`); `Expiration.Before(now)` →
  reject (`:104-105`); `Reusable` → accept (`:109-111`); `Used` → reject
  (`:113-114`). `KeyRecord`/`validateRec` reproduce this order exactly.
* `hscontrol/db/preauth_keys.go:106-126` — the mint: `prefix := rands.HexString(12)`,
  `toBeHashed := rands.HexString(64)` (the **secret**), `keyStr := "hskey-auth-"+prefix+"-"+toBeHashed`,
  `hash := bcrypt.GenerateFromPassword([]byte(toBeHashed), …)`, and the stored
  record keeps `Prefix`/`Hash` — the **secret is never stored**, only its hash.

## What drorb changes (and why)

* **Hash at rest:** headscale uses bcrypt; drorb's crypto law BANS bcrypt as
  not-formally-audited (see `CRYPTO-FFI-README.md` — the former bcrypt was
  removed so the whole surface is aws-lc / HACL*). The secret is a full-entropy
  256-bit CSPRNG token, so it needs no password-stretching KDF: an audited
  one-way hash is the correct primitive. This model is parameterised over an
  abstract `hash : Bytes → Bytes`; the mint exe (`PreAuthMintTool`) instantiates
  it with `Crypto.sha256` (HACL*/EverCrypt, F*-verified) and draws the secret
  from an audited AWS-LC CSPRNG (`aws_lc_rs::rand::fill`), NOT `rand`.

## What is PROVEN vs. ASSUMED

* PROVEN in Lean: the `validate` decision (`admit`/`reject`) is exactly the
  headscale `Validate()` order; `mint` stores only `hash secret` (the raw secret
  is not a field of `KeyRecord` — a type-level guarantee); a valid key is
  **admitted** (`MachineAuthorized = true`) with the key's user/tags; an
  unknown/expired/exhausted/revoked key is **rejected**; the admission decision
  **coincides definitionally with `Control.step` under `preAuthPolicy`** (so the
  foundation's `control_peers_all_authorized` / `control_netmap_needs_authorized`
  carry over verbatim — the gate is EXTENDED, not bypassed).
* ASSUMED (explicit hypotheses, discharged by the crypto primitive, not Lean):
  the one-wayness / collision-resistance of `hash` (`hInj` where a "no false
  admit" theorem needs it) is a property of `Crypto.sha256` (HACL*), stated as a
  hypothesis and never silently used.
-/

namespace Control
namespace PreAuth

open Control

/-! ## §1  The key model -/

/-- Attributes minted into a pre-auth key
(headscale `types.PreAuthKey`: Reusable/Ephemeral/Tags/Expiration + owning User). -/
structure KeyAttrs where
  /-- Reusable (many registrations) vs. one-shot (headscale `Reusable`). -/
  reusable  : Bool
  /-- Registers ephemeral (auto-reaped) nodes (headscale `Ephemeral`). -/
  ephemeral : Bool
  /-- Unix-seconds expiry; `0` = never (headscale `Expiration`, `nil` = never). -/
  expiry    : Nat
  /-- ACL tags copied to the node on registration (headscale `Tags`, `IsTagged`). -/
  tags      : List Bytes
  /-- Owning user id (headscale `UserID`). -/
  user      : Nat
deriving Repr, DecidableEq

/-- A stored pre-auth key record — **HASHED AT REST**. `KeyRecord` has NO field
holding the raw secret; only `keyHash = hash secret` is kept (headscale
`Prefix`/`Hash`, `:45-46`). `used` is the one-shot spend bit (headscale `Used`),
`revoked` the v2-API revoke (headscale `Revoked`). -/
structure KeyRecord where
  keyHash : Bytes
  attrs   : KeyAttrs
  used    : Bool
  revoked : Bool
deriving Repr, DecidableEq

/-- The in-memory key store (the seam persistence makes durable). -/
abbrev Store := List KeyRecord

/-- **mint** — given audited-CSPRNG secret bytes and the desired attributes,
produce the STORED record. Only `hash secret` is written; the secret is handed
to the operator separately (the `keyStr` a client passes to `--authkey`) and is
never a field of the stored record. -/
def mint (hash : Bytes → Bytes) (secret : Bytes) (a : KeyAttrs) : KeyRecord :=
  { keyHash := hash secret, attrs := a, used := false, revoked := false }

/-! ## §2  Validation (the headscale `Validate()` order) -/

/-- Why a presented key was rejected. -/
inductive Reason where
  | unknown | expired | exhausted | revoked
deriving Repr, DecidableEq

/-- The verdict on a presented key: admit (carrying the attributes to stamp on
the node) or reject with a reason. -/
inductive Verdict where
  | admit  (a : KeyAttrs)
  | reject (r : Reason)
deriving Repr, DecidableEq

def Verdict.isAdmit : Verdict → Bool
  | .admit _  => true
  | .reject _ => false

/-- Validate a single record at wall-clock `now`, reproducing headscale
`Validate()` (`preauth_key.go:100-114`) EXACTLY in order: revoked → expired →
(reusable ⇒ admit) → (used ⇒ exhausted) → admit. `expiry = 0` means never. -/
def validateRec (now : Nat) (r : KeyRecord) : Verdict :=
  if r.revoked then .reject .revoked
  else if 0 < r.attrs.expiry ∧ r.attrs.expiry < now then .reject .expired
  else if r.attrs.reusable then .admit r.attrs
  else if r.used then .reject .exhausted
  else .admit r.attrs

/-- First-match lookup of a stored record by the hash of the presented secret
(the drorb analogue of headscale's prefix lookup + `bcrypt.CompareHashAndPassword`,
`preauth_keys.go:225`): compare the audited hash of what the client presented to
the stored `keyHash`. -/
def findByHash (hash : Bytes → Bytes) : Store → Bytes → Option KeyRecord
  | [],     _      => none
  | r :: t, secret => if r.keyHash = hash secret then some r else findByHash hash t secret

/-- **validate** — the whole gate: an unknown secret (no matching hash) is
rejected, otherwise the record's `validateRec` decides. -/
def validate (hash : Bytes → Bytes) (store : Store) (now : Nat) (secret : Bytes) : Verdict :=
  match findByHash hash store secret with
  | none   => .reject .unknown
  | some r => validateRec now r

/-- Spend a one-shot key: mark the matching, non-reusable record `used`
(headscale sets `Used = true` after a one-shot registration). Reusable records
and all others are untouched. -/
def consume (hash : Bytes → Bytes) (secret : Bytes) (store : Store) : Store :=
  store.map (fun r =>
    if r.keyHash = hash secret ∧ r.attrs.reusable = false then { r with used := true } else r)

/-- Spend a one-shot key **by its stored hash** — the persisted-spend form. A
durable `KeyConsumed` event carries the *resolved* `keyHash` (`hash secret`, fixed
at record time), not the secret or the hash function, so replay can re-apply the
spend deterministically. Identical to `consume` once the hash is resolved. -/
def consumeHash (keyHash : Bytes) (store : Store) : Store :=
  store.map (fun r =>
    if r.keyHash = keyHash ∧ r.attrs.reusable = false then { r with used := true } else r)

/-- `consume` is `consumeHash` at the resolved hash — the record-time bridge that
lets the durable log carry `hash secret` as a plain `keyHash`. -/
theorem consume_eq_consumeHash (hash : Bytes → Bytes) (secret : Bytes) (store : Store) :
    consume hash secret store = consumeHash (hash secret) store := rfl

/-! ## §3  Wiring the verdict into the proven admission seam

`Control.Policy.authorizes : NodeKey → Bytes → Bool` is the foundation's
authorization boundary. `preAuthPolicy` instantiates it with the pre-auth
verdict, so every `Control` safety theorem — proven for an ARBITRARY policy —
holds for the pre-auth gate. -/

/-- The concrete policy: a node key presenting `secret` is authorized iff the
pre-auth `validate` admits it. -/
def preAuthPolicy (hash : Bytes → Bytes) (store : Store) (now : Nat) : Control.Policy :=
  { authorizes := fun _nk secret => (validate hash store now secret).isAdmit }

/-- A short machine-readable reject marker for `RegisterResponse.error`. -/
def reasonBytes : Reason → Bytes
  | .unknown   => [1]
  | .expired   => [2]
  | .exhausted => [3]
  | .revoked   => [4]

/-- The full result of driving a `RegisterRequest` through the pre-auth gate:
the (possibly one-shot-spent) store, the new coordination state, the wire
response, and — on admit — the attributes stamped on the node. -/
structure AdmitResult where
  store'    : Store
  state'    : ControlState
  response  : RegisterResponse
  admitted  : Option KeyAttrs
deriving Repr

/-- **The pre-auth admission transition.** A register request bearing a valid
pre-auth key is admitted (`MachineAuthorized = true`) as an `.authorized`
registration carrying the key's `user`; the one-shot key is spent. An
invalid/expired/exhausted/revoked/unknown key yields a merely-`.registered`
entry with `MachineAuthorized = false` (no netmap, by the foundation's
`control_netmap_needs_authorized`). The status decision is *only* the pre-auth
verdict — the same door as `Control.step` under `preAuthPolicy`. -/
def registerWithPreAuth (hash : Bytes → Bytes) (store : Store) (s : ControlState)
    (now : Nat) (req : RegisterRequest) : AdmitResult :=
  match validate hash store now req.authKey with
  | .admit a =>
    let node : Node := { nodeOf req true with user := a.user, tags := a.tags }
    let reg  : Registration := { nodeKey := req.nodeKey, node, status := .authorized }
    { store'   := consume hash req.authKey store
      state'   := { s with nodes := upsertReg s.nodes reg }
      response := { machineAuthorized := true, nodeKeyExpired := false,
                    user := a.user, authURL := [], error := [] }
      admitted := some a }
  | .reject r =>
    let reg : Registration := { nodeKey := req.nodeKey, node := nodeOf req false, status := .registered }
    { store'   := store
      state'   := { s with nodes := upsertReg s.nodes reg }
      response := { machineAuthorized := false, nodeKeyExpired := false,
                    user := 0, authURL := [1], error := reasonBytes r }
      admitted := none }

/-! ## §4  Admission theorems -/

/-- Lookup of the just-registered node returns exactly the record `step` would,
statuswise: `.authorized` iff the verdict admits, else `.registered`. -/
theorem preauth_authorized_iff_validate (hash : Bytes → Bytes) (store : Store)
    (s : ControlState) (now : Nat) (req : RegisterRequest) :
    (lookupReg (registerWithPreAuth hash store s now req).state'.nodes req.nodeKey).map (·.status)
      = some (if (validate hash store now req.authKey).isAdmit then .authorized else .registered) := by
  simp only [registerWithPreAuth]
  cases hv : validate hash store now req.authKey with
  | admit a => simp [hv, Verdict.isAdmit, upsertReg, lookupReg]
  | reject r => simp [hv, Verdict.isAdmit, upsertReg, lookupReg]

/-- **NON-BYPASS: the pre-auth gate IS the proven `Control.step` gate.** The
authorization status the pre-auth path records for a register request is,
node-for-node, the status `Control.step` records under `preAuthPolicy`. Hence
every safety theorem proven of `Control.step` (`control_netmap_needs_authorized`,
`control_peers_all_authorized`, `control_authorized_iff_policy`) transfers to the
pre-auth gate unchanged: the gate is EXTENDED (it additionally spends one-shot
keys and stamps the key's user), never bypassed. -/
theorem preauth_matches_policy_step (hash : Bytes → Bytes) (store : Store)
    (s : ControlState) (now : Nat) (req : RegisterRequest) :
    (lookupReg (registerWithPreAuth hash store s now req).state'.nodes req.nodeKey).map (·.status)
      = (lookupReg (Control.step (preAuthPolicy hash store now) s (.register req)).1.nodes req.nodeKey).map (·.status) := by
  rw [preauth_authorized_iff_validate, Control.control_authorized_iff_policy]
  rfl

/-- **A valid key is ADMITTED with its user and tags.** If the presented key
validates to `admit a`, the register response carries `MachineAuthorized = true`
and the owning `user`, the node is recorded `.authorized` under its node key with
`node.user = a.user`, and the admitted attributes (hence `a.tags`) are returned. -/
theorem preauth_admit (hash : Bytes → Bytes) (store : Store) (s : ControlState)
    (now : Nat) (req : RegisterRequest) (a : KeyAttrs)
    (hv : validate hash store now req.authKey = .admit a) :
    (registerWithPreAuth hash store s now req).response.machineAuthorized = true
    ∧ (registerWithPreAuth hash store s now req).response.user = a.user
    ∧ (registerWithPreAuth hash store s now req).admitted = some a
    ∧ lookupReg (registerWithPreAuth hash store s now req).state'.nodes req.nodeKey
        = some { nodeKey := req.nodeKey, node := { nodeOf req true with user := a.user, tags := a.tags },
                 status := .authorized } := by
  unfold registerWithPreAuth
  rw [hv]
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp [upsertReg, lookupReg]

/-- **An invalid key is REJECTED.** If the presented key validates to `reject r`,
the response carries `MachineAuthorized = false`, the node is recorded merely
`.registered` (so it gets no netmap), and the key store is UNCHANGED (nothing is
spent on a failed attempt). -/
theorem preauth_reject (hash : Bytes → Bytes) (store : Store) (s : ControlState)
    (now : Nat) (req : RegisterRequest) (r : Reason)
    (hv : validate hash store now req.authKey = .reject r) :
    (registerWithPreAuth hash store s now req).response.machineAuthorized = false
    ∧ (lookupReg (registerWithPreAuth hash store s now req).state'.nodes req.nodeKey).map (·.status)
        = some .registered
    ∧ (registerWithPreAuth hash store s now req).store' = store := by
  unfold registerWithPreAuth
  rw [hv]
  refine ⟨rfl, ?_, rfl⟩
  simp [upsertReg, lookupReg]

/-- **EXTENSION of `control_peers_all_authorized` to the pre-auth-produced
state.** After admitting/rejecting a node through the pre-auth gate, any netmap a
subsequent poll yields still names only `.authorized` peers — the foundation
invariant, applied to the state the pre-auth transition produced. This is the
load-bearing reuse: the gate feeds `Control.step`, it does not replace it. -/
theorem preauth_peers_all_authorized (hash : Bytes → Bytes) (store : Store)
    (s : ControlState) (now : Nat)
    (rq : RegisterRequest) (mr : MapRequest) (nm : NetMap)
    (h : (Control.step (preAuthPolicy hash store now)
            (registerWithPreAuth hash store s now rq).state' (.mapPoll mr)).2
          = .mapResp (.full nm)) :
    ∀ p ∈ nm.peers, ∃ rr ∈ (registerWithPreAuth hash store s now rq).state'.nodes,
        rr.node = p ∧ rr.status = .authorized :=
  Control.control_peers_all_authorized _ _ _ _ h

/-! ## §5  Key-lifecycle theorems (expiry / one-shot / reusable / hashed-at-rest) -/

/-- An unknown secret (no stored record hashes to it) is rejected `unknown`. -/
theorem validate_unknown (hash : Bytes → Bytes) (store : Store) (now : Nat) (secret : Bytes)
    (hmiss : ∀ r ∈ store, r.keyHash ≠ hash secret) :
    validate hash store now secret = .reject .unknown := by
  simp only [validate]
  have : findByHash hash store secret = none := by
    induction store with
    | nil => rfl
    | cons h t ih =>
      simp only [findByHash]
      rw [if_neg (hmiss h (by simp))]
      exact ih (fun r hr => hmiss r (by simp [hr]))
  rw [this]

/-- **mint stores only the hash.** The record `mint` writes has `keyHash = hash
secret` and no other trace of `secret` — the hashed-at-rest guarantee (the raw
secret is not even a field of `KeyRecord`). -/
theorem mint_keyHash (hash : Bytes → Bytes) (secret : Bytes) (a : KeyAttrs) :
    (mint hash secret a).keyHash = hash secret := rfl

/-- With `hash` one-way (`hash secret ≠ secret`, the weakest witness of "not
plaintext"), the stored material differs from the secret — a corollary of
`mint_keyHash`, made explicit so "hashed at rest" is a theorem, not a comment.
The full one-wayness of `Crypto.sha256` is a HACL* property, assumed here. -/
theorem mint_not_plaintext (hash : Bytes → Bytes) (secret : Bytes) (a : KeyAttrs)
    (how : hash secret ≠ secret) : (mint hash secret a).keyHash ≠ secret := by
  rw [mint_keyHash]; exact how

/-- Validation of a one-record store whose record hashes to the presented secret
reduces to `validateRec` on that record. -/
theorem validate_cons_self (hash : Bytes → Bytes) (secret : Bytes) (now : Nat)
    (r : KeyRecord) (hk : r.keyHash = hash secret) :
    validate hash [r] now secret = validateRec now r := by
  simp [validate, findByHash, hk]

/-- **A live valid key admits.** A freshly minted, non-revoked key whose expiry
is `0` (never) or still in the future admits with its own attributes. -/
theorem mint_admits (hash : Bytes → Bytes) (secret : Bytes) (a : KeyAttrs) (now : Nat)
    (hlive : a.expiry = 0 ∨ now ≤ a.expiry) :
    validate hash [mint hash secret a] now secret = .admit a := by
  have hexp : ¬(0 < a.expiry ∧ a.expiry < now) := by
    rcases hlive with h | h <;> rintro ⟨h0, hlt⟩ <;> omega
  rw [validate_cons_self hash secret now (mint hash secret a) rfl]
  by_cases hr : a.reusable <;> simp [validateRec, mint, hr, hexp]

/-- **An expired key is rejected.** A minted key with a nonzero expiry strictly
in the past validates to `reject .expired` (headscale `Expiration.Before(now)`). -/
theorem mint_expired_rejected (hash : Bytes → Bytes) (secret : Bytes) (a : KeyAttrs) (now : Nat)
    (hexp : 0 < a.expiry) (hlt : a.expiry < now) :
    validate hash [mint hash secret a] now secret = .reject .expired := by
  rw [validate_cons_self hash secret now (mint hash secret a) rfl]
  simp [validateRec, mint, hexp, hlt]

/-- **A one-shot key is exhausted after one use.** A non-reusable, live key
admits first; after `consume` spends it (`used := true`), the same key validates
to `reject .exhausted` — the one-shot property (headscale `Used ⇒ reject`). -/
theorem oneShot_exhausts (hash : Bytes → Bytes) (secret : Bytes) (a : KeyAttrs) (now : Nat)
    (hns : a.reusable = false) (hlive : a.expiry = 0 ∨ now ≤ a.expiry) :
    validate hash [mint hash secret a] now secret = .admit a
    ∧ validate hash (consume hash secret [mint hash secret a]) now secret = .reject .exhausted := by
  have hexp : ¬(0 < a.expiry ∧ a.expiry < now) := by
    rcases hlive with h | h <;> rintro ⟨h0, hlt⟩ <;> omega
  refine ⟨mint_admits hash secret a now hlive, ?_⟩
  have hcons : consume hash secret [mint hash secret a]
      = [{ mint hash secret a with used := true }] := by
    simp [consume, mint, hns]
  rw [hcons, validate_cons_self hash secret now _ rfl]
  simp [validateRec, mint, hns, hexp]

/-- **One-shot exhaustion via the persisted spend.** After `consumeHash` marks the
key's stored `keyHash` `used`, a live one-shot key validates to `reject .exhausted`.
This is `oneShot_exhausts` phrased over the `keyHash` the durable `KeyConsumed`
event carries — the spend that a restart replays. -/
theorem consumeHash_exhausts (hash : Bytes → Bytes) (secret : Bytes) (a : KeyAttrs) (now : Nat)
    (hns : a.reusable = false) (hlive : a.expiry = 0 ∨ now ≤ a.expiry) :
    validate hash (consumeHash (hash secret) [mint hash secret a]) now secret = .reject .exhausted := by
  rw [← consume_eq_consumeHash]
  exact (oneShot_exhausts hash secret a now hns hlive).2

/-- **A reusable key survives a use.** A reusable, live key still admits after
`consume` — reusable records are never spent (headscale `Reusable ⇒ accept`
before the `Used` check). -/
theorem reusable_persists (hash : Bytes → Bytes) (secret : Bytes) (a : KeyAttrs) (now : Nat)
    (hr : a.reusable = true) (hlive : a.expiry = 0 ∨ now ≤ a.expiry) :
    validate hash (consume hash secret [mint hash secret a]) now secret = .admit a := by
  have hcons : consume hash secret [mint hash secret a] = [mint hash secret a] := by
    simp [consume, mint, hr]
  rw [hcons]; exact mint_admits hash secret a now hlive

/-- **A revoked key is rejected.** A record marked `revoked` validates to
`reject .revoked`, ahead of every other check (headscale `Revoked != nil` first). -/
theorem revoked_rejected (hash : Bytes → Bytes) (secret : Bytes) (a : KeyAttrs) (now : Nat) :
    validate hash [{ mint hash secret a with revoked := true }] now secret = .reject .revoked := by
  rw [validate_cons_self hash secret now _ rfl]
  simp [validateRec]

/-- **No false admit (collision-resistance).** Presenting a secret `bad` that
differs from the only minted secret `good` is rejected `unknown`, PROVIDED `hash`
is injective — the collision-resistance of `Crypto.sha256`, stated as an explicit
hypothesis and discharged by HACL*, not by Lean. -/
theorem wrong_secret_rejected (hash : Bytes → Bytes) (good bad : Bytes) (a : KeyAttrs) (now : Nat)
    (hInj : ∀ x y, hash x = hash y → x = y) (hne : bad ≠ good) :
    validate hash [mint hash good a] now bad = .reject .unknown := by
  apply validate_unknown
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [mint]
  intro hc
  exact hne (hInj good bad hc).symm

end PreAuth
end Control

#print axioms Control.PreAuth.preauth_authorized_iff_validate
#print axioms Control.PreAuth.preauth_matches_policy_step
#print axioms Control.PreAuth.preauth_admit
#print axioms Control.PreAuth.preauth_reject
#print axioms Control.PreAuth.preauth_peers_all_authorized
#print axioms Control.PreAuth.validate_unknown
#print axioms Control.PreAuth.mint_keyHash
#print axioms Control.PreAuth.mint_not_plaintext
#print axioms Control.PreAuth.mint_admits
#print axioms Control.PreAuth.mint_expired_rejected
#print axioms Control.PreAuth.oneShot_exhausts
#print axioms Control.PreAuth.reusable_persists
#print axioms Control.PreAuth.revoked_rejected
#print axioms Control.PreAuth.wrong_secret_rejected
#print axioms Control.PreAuth.consume_eq_consumeHash
#print axioms Control.PreAuth.consumeHash_exhausts
