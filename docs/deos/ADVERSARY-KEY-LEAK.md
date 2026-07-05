# The adversary / key-leak harness — what happens if a private key leaks

This document answers one question: **a dregg private key leaks (or is stolen) — what
is the blast radius, what bounds the damage, and how is it revoked?** It states the
adversary model, the blast-radius analysis, the four containment floors, and the
revocation/rotation story, and it gives an honest verdict: *most of "what if a key
leaks" is already answered by the deployed proofs*; the genuinely-new work is one
named seam.

The companion model is `metatheory/Metatheory/KeyLeak.lean` — a kernel-clean Lean
harness (axioms `propext`/`Classical.choice`/`Quot.sound`
only) that instantiates the adversary as an opaque controller and proves the
blast-radius bound, the containment, and that revocation kills it. It builds under the
`Metatheory.+` glob (`metatheory/lakefile.toml`), so CI covers it.

---

## 1. What a key authorizes — the binding

A dregg key is not a free-floating secret; it is bound to authority at two seams:

* **Macaroon root key → cap-tree.** A token is an HMAC-SHA256 chain rooted in a 32-byte
  secret (`token/src/macaroon_backend.rs:21`, `MacaroonToken.root_key`,
  `Zeroizing<[u8; 32]>`). Verification (`:126`) replays the HMAC chain against that root
  key, then evaluates Datalog. Attenuation (`:140`) appends caveats — it can only add
  restrictions; `attenuate` cannot remove a caveat, and a `sealed` token refuses
  further attenuation (`:141`). **Possessing the root key lets you mint and verify
  tokens under that root** — the macaroon model is symmetric-key, so the root secret is
  the keys-to-the-kingdom *for tokens rooted there*.
* **Pubkey → cell identity.** A cell's id is `blake3::derive_key("dregg-cell-id-v1",
  pubkey ‖ token_id)` (`types/src/lib.rs:701`, `CellId::derive_raw`; the domain variant
  at `:687`). The id is derived from the *public* key, so leaking the *private* key does
  not change which cell you are — it lets you **act as** that cell (sign turns / present
  caps as that principal).

So a leaked private key = a **compromised principal**: an attacker who can now (a)
present every cap that principal holds, and (b) sign/propose turns as that principal.
The question is what that buys them.

---

## 2. The adversary model — leaked key = an opaque controller

The model is exactly the deployed Polis frame
(`metatheory/Polis/Polis.lean`): a controller is an **opaque, universally
quantified function** `ctrl : State → Action` that the safety theorem never inspects —
*"verify the cage, not the animal"* (`polis_safety`, `:102`). The leaked-key attacker
**is** such a controller: it holds the compromised principal's caps and drives the
system with them, and we make no assumption about how clever, adversarial, or
resourceful it is.

This is the load-bearing reframing. The previous obstacle — *"modelling a key leak
needs too much additional proof machinery"* — dissolves once you notice that
`polis_safety` already quantifies over an arbitrary adversary. The leaked-key attacker
is not a new kind of object; it is the controller the cage was always proven against.
`KeyLeak.lean` instantiates this literally (`key_leak_contained` *is* `polis_safety`
with `ctrl := attacker`).

---

## 3. The blast radius — the attenuation-closure of the held c-list

The attacker gains the caps the principal **held**, plus everything derivable from
them by delegation/attenuation. That derivable set is the **blast radius**, and it is
*bounded*:

* The deployed gate is `cell/src/capability.rs:603`, `is_attenuation(held, granted) =
  granted.is_narrower_or_equal(held)` (`cell/src/permissions.rs:52`). Every cap an
  attacker can produce from a held cap must be **narrower-or-equal**: same target,
  narrower-or-equal rights. **No amplification, no new targets.**
* `KeyLeak.lean` models this as `reaches held c := ∃ h ∈ held, isAttenuation h c` — the
  attenuation-closure of the c-list. It is genuinely a closure: `reaches_closed` proves
  a delegate-of-a-reached-cap is still reached (`isAttenuation.trans` — the transitive
  cap graph adds nothing). The keystone `leak_blast_no_amplify` states it as security:
  every cap in the radius confers rights `≤` some held cap, on a cell the principal
  already held a cap to.
* **Teeth (the radius bites):** `leak_blast_no_admin_from_read` — a leaked key holding
  only `read` on cell 7 cannot reach `admin` on cell 7. `leak_blast_no_new_target` — a
  key holding caps only to cell 7 cannot reach cell 9. The blast radius is confined to
  the *attenuation-downward-closure of the principal's own c-list*, full stop.

So the blast radius of a leaked key is precisely: **the caps that principal held, and
their attenuations — never more.** A leaked low-authority key is a low-authority
compromise. This is the first reason a key leak is survivable: dregg has no ambient
authority to amplify into.

---

## 4. The containment — four floors, one uniform proof

Four independent mechanisms bound the damage. Crucially, they are all **floors** in
the Polis sense (states the attacker may not drive a subject below), so they compose by
intersection (`SharedFloor`) and `polis_safety` bounds all of them at once — no
per-mechanism re-proof.

1. **Attenuation / non-amplification** (`§3`). The authority floor is `held ⊆ bound`
   (`KeyLeak.authFloor`, mirroring `granted ⊆ held` / `checkSubset`). The attacker can
   never hold a cap outside the principal's exported bound. `key_leak_contained` proves
   it for every opaque attacker; `key_leak_attacker_blind` proves two different
   attackers are bounded *identically* — possession of the key buys the held caps and
   nothing more.

2. **Conservation (Σδ = 0).** The executor enforces zero-sum balance across every turn
   (`AssetId := issuer-cell, Σδ = 0`). A leaked key **cannot mint value**: it can move
   value it has authority over, but the total is conserved, so the attacker cannot
   inflate. In the harness this is another floor that ANDs into the shared floor exactly
   like authority (the same `SoundPolicy` argument); it is not re-derived because the
   conservation invariant lives in the executor/circuit, not the cap algebra.

3. **Firmament confinement.** A leaked key inside a sandboxed PD only reaches its
   *confined sub-world*. The OS half is real and enforced:
   `sel4/dregg-firmament/src/sandbox.rs` confines a forked child right after `fork()` —
   macOS Seatbelt `(deny default)` + fd-closing (`:20`), Linux
   `unshare(CLONE_NEWUSER|NEWNET|NEWNS|NEWPID)` (`:30`) — so the child has **no ambient
   `open`/`socket`/`execve`**. A key leaked inside that PD reaches only the caps and
   cells granted into the PD, not the host. `KeyLeak.confinedFloor` models this
   ("every held cap targets a confined cell") and `key_leak_contained_confined` bounds
   the attacker by authority **and** confinement simultaneously — one `polis_safety`
   over the combined floor.

4. **Membrane fork-isolation.** A leaked *fork* key reaches only that fork.
   `starbridge-v2/src/shared_fork.rs` is the authority typing of "invite someone into my
   world": the guest is a fresh confined principal in the *fork's* ledger
   (`:202`), holding only caps minted via a genuine `Effect::GrantCapability` attenuated
   by the real powerbox (`Powerbox::grant`, `:251`) — over-authorized grants are
   **dropped, never amplified** (`:270`). Exercising a target that is not in the fork is
   rejected (`:283`). So a leaked fork-key is contained to the fork by the same
   attenuation + confinement floors.

The uniform point: each containment is a floor; `polis_safety` proves *no opaque
controller — and the leaked-key attacker is one — drives any subject below the meet of
these floors.* The containment of a key leak is the deployed safety theorem, re-read.

---

## 5. Revocation and rotation — killing the leak

Containment bounds the *authority* of a leak; revocation bounds it in *time*.

* **The effect.** `Effect::RevokeCapability { cell, slot }` (`turn/src/action.rs:970`)
  is a first-class, `Terminal`-linearity effect (`:1656`) — it grows the revocation set
  and flips the cap out of admissibility. `RevokeDelegation` (the child-cap variant)
  bumps the delegation-epoch root so a committing revoke is bound into the commitment
  (`turn/src/lean_shadow.rs:602`).
* **The bound (proved).** `metatheory/Dregg2/Distributed/Revocation.lean` turns
  revocation into a topology-parametrized guarantee.
  `eventual_bounded_revocation` (`:188`): a cap revoked at origin `m` at time `τ` is
  **not honored** by any node `n` at any `t ≥ τ + delay m n` — honored at most until the
  revocation propagates, never after. `KeyLeak.revoke_kills_leak` restates this on the
  leaked credential self-containedly.
* **n = 1 ⇒ immediate.** Under instantaneous propagation (`delay ≡ 0`, the
  single-machine collapse), the bound becomes `τ` — the synchronous revoke kills the leak
  the instant it lands (`Revocation.immediate_revocation` / `KeyLeak.revoke_kills_leak_immediate`).
  The dregg single-machine principle (`project-dregg4-vision`): on one machine,
  revocation is immediate; distributed, it is a *bounded* stale window
  (`Revocation.tightness_tooth` exhibits a real `[τ, τ+delay)` window — the bound is
  tight, not vacuous).
* **Rotation (KERI-style pre-rotation).** Revocation removes a compromised cap;
  *rotation* replaces the compromised **key** while preserving identity. The
  identity/polis app's pre-rotation commits the *next* key's hash in advance, so a leak
  of the current key cannot seize the rotation — the attacker holds the spent key, and
  the principal rotates to the pre-committed successor. (This is the recovery floor:
  `Metatheory.Polis`'s `humanOK` / bounded recoverability — a leak must not foreclose
  the legitimate holder's recovery.)

---

## 6. The settlement seam — the one genuinely-new piece

There is exactly one place "what if a key leaks" is *not* already discharged: the
**revocation/settlement seam**. A leaked-key turn can be branched in the reversible
substrate and later **settled**; if the leaked cap was revoked *between* branch-time and
settlement, the settled answer must use the **settlement-tip** revocation set, not the
stale branch-time view (`docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md §6.3`). The
theorem to pursue:

> **Settlement Soundness.** If a turn `T` settles on the finalized tip at height `h`,
> every capability `T` exercised is honored by the tip's finalized revocation set at
> `h`, and the commitment at `h` *binds* that revocation set, so a light client
> accepting the settled batch can verify the leaked cap was not already revoked.

This is a *composition* of deployed pieces — `Revocation.eventual_bounded_revocation` +
the finalized-light-client commitment + the cap-bridge — applied with the
`holeFill_binds_in_circuit` discipline to the late-bound *negative* fact of revocation.
It is the only part that must be *built*; everything else is *instantiated*.

---

## 7. The honest verdict — already-covered vs genuinely-new

| Question | Status | Where |
| --- | --- | --- |
| Blast radius bounded (no amplification, no new targets) | **Already proved** — instance of `is_attenuation` | `cell/src/capability.rs:603`; `KeyLeak.leak_blast_no_amplify`, `reaches_closed` |
| Containment (attacker cannot exceed principal's floor) | **Already proved** — instance of `polis_safety` over the authority floor | `Polis.polis_safety`; `KeyLeak.key_leak_contained` |
| Cannot mint value | **Already enforced** — executor `Σδ = 0`, ANDs into the floor | executor conservation; `KeyLeak.combinedFloor` shape |
| Confined to sandbox / fork | **Enforced (OS) + modelled** — firmament + membrane, both floors | `sandbox.rs`, `shared_fork.rs`; `KeyLeak.key_leak_contained_confined` |
| Revocation kills it (bounded, n=1 immediate) | **Already proved** | `Revocation.eventual_bounded_revocation`; `KeyLeak.revoke_kills_leak` |
| Rotation preserves identity, leak can't seize it | **Designed (KERI pre-rotation), recovery floor proved** | identity/polis app; `Polis.humanOK` |
| Settled turn honors settlement-time revocation set | **Genuinely new** — Settlement Soundness, a *composition* to build | §6; `DISTRIBUTED-TIMETRAVEL-SEMANTICS.md §6.3` |

**Bottom line.** "What happens if a key leaks" is, for the static picture (blast
radius, containment, revocation), *already answered by the deployed proofs* — the
leaked-key attacker is the opaque controller `polis_safety` was always proven against,
and `is_attenuation` + conservation + confinement bound it to the leaked principal's
floor. There is no large new proof obligation. The one place new construction is owed
is the **settlement seam**: binding the settlement-time revocation set into the
finalized commitment so a leaked-then-revoked cap cannot be settled. That is a narrow,
named, compose-don't-rederive theorem — not "too much additional machinery."

---

## 8. The model harness

`metatheory/Metatheory/KeyLeak.lean` (kernel-clean):

* `§1` — `reaches` (the blast-radius attenuation-closure), `leak_blast_no_amplify`,
  `reaches_closed`, two amplification/new-target teeth.
* `§2` — `key_leak_contained` (= `polis_safety` with the attacker as controller),
  `key_leak_attacker_blind`, `confinedFloor` + `key_leak_contained_confined` (authority
  ∧ firmament confinement, bounded together).
* `§3` — `revoke_kills_leak` (topology-bounded), `revoke_kills_leak_immediate` (n=1),
  with `#guard`s running the stale-window → propagation → immediacy story end-to-end.

The scenario it encodes: an attacker leaks a key, exercises the principal's caps (and
cannot amplify or reach new cells), is contained to the leaked floor + confined
sub-world for every adversarial strategy, and is killed by a revoke — immediately at
n=1, within a tight propagation bound when distributed.
