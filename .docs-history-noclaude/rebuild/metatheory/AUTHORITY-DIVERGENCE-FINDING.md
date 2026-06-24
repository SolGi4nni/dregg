# Authority Divergence — investigation + enrichment recommendation

**Status: investigation only (no core-model edit). Decision pending ember.**

The l4v→Lean pilot (`Dregg2/Firmament/SeL4Abstract.lean`) transcribed seL4's `auth` enum (12 ctors,
`proof/access-control/Types.thy:51`) and found dregg's `Auth` (7 ctors, `Authority/Positional.lean:37`)
is a **7-of-12 projection**. The relabelling `α : seL4.Auth → Option dregg.Auth`
(`SeL4Abstract.lean:451`) is faithful + injective on the used 7 (`alpha_injective_on_used`,
`SeL4Abstract.lean:479`) but NOT total: `Notify, Read, Write, DeleteDerived, AAuth` have no dregg image
(`alpha_total_iff_used`, `SeL4Abstract.lean:473`).

This note censuses, per missing authority, whether dregg's ACTUAL semantics NEED it.

---

## The structural key: dregg has TWO disjoint `read`/`write` namespaces

The whole "memory Read/Write" question turns on one fact the census surfaced:

| name | type | shape | file |
|---|---|---|---|
| `Authority.Auth.read` / `.write` | authority label on a **cap** | IPC-shaped (endpoint rights) | `Authority/Positional.lean:38` |
| `Crypto.MemoryChecking.Kind.read` / `.write` | **memory-op kind** (addr, val, serial) | memory-shaped | `Crypto/MemoryChecking.lean:56` |

dregg's memory Read/Write authority **already exists and is already distinct** — it just lives in a
DIFFERENT type (`Kind`, the Blum-multiset op kind, `Crypto/UniversalMemory.lean`) from the cap-rights
type (`Auth`). seL4 folds memory access into the SAME `auth` enum as IPC; dregg factors it into a
separate (and far richer — addressed, value-checked, serial-ordered) memory-consistency model. So the
α-conflation `read↦Receive, write↦SyncSend` is **conflating two seL4 ctors with dregg's IPC rights,
while dregg's memory-access authority is modelled elsewhere entirely.** This is the lens for verdict #2.

---

## Per-authority verdicts

### 1. `Notify` — async notification SIGNAL authority → **conflation-to-fix (the strongest case to enrich)**

**Deciding use-site:** `Dregg2/Firmament/SeL4Kernel.lean:248–257` — `Notification.signal` / `.wait`, the
badge-OR accumulator, a FULLY MODELLED, axiom-clean kernel object with green refinement theorems
(`signal_then_wait`, `wait_observes_badge_or`, `second_wait_is_zero`, `SeL4Kernel.lean:719–735`),
refining real Rust (`sel4/dregg-firmament/src/emulated_kernel.rs:388` signal / `:403` wait).

The firmament genuinely realizes BOTH IPC modalities as distinct objects:
- the **synchronous Endpoint** (rendezvous, `SeL4Kernel.lean:288`) — call/recv/reply, and
- the **asynchronous Notification** (badge-OR signal, `SeL4Kernel.lean:238`) — signal/wait.

seL4 distinguishes these in `cap_rights_to_auth` precisely by `SyncSend` (endpoint) vs `Notify`
(notification) on the `AllowWrite` branch (`SeL4Abstract.lean:182`: `if sync then [.SyncSend] else
[.Notify]`). dregg's `Auth` has `write` (which α maps from `SyncSend`) but NO async-notify authority —
so a held cap to a Notification and a held cap to an Endpoint confer the SAME dregg authority (`write`),
even though the kernel treats signalling and synchronous-send as different operations on different
object kinds. The apps lean on this distinction conceptually ("an inbox/pubsub message is a
notification, not an asset move", `Apps/InboxFactory.lean:31`, `Apps/PubsubFactory.lean:22`) but cannot
express it in the authority lattice.

**Verdict: conflation-to-fix.** The notification object is real, modelled, and refined; the *authority
to signal it* is the one genuinely-missing IPC authority. This is where the projection actually loses a
distinction dregg's own firmament makes.

### 2. `Read` / `Write` (memory access, distinct from IPC `Receive`/`SyncSend`) → **acceptable-projection** (modelling choice, not a confusion)

**Deciding use-sites:** memory access authority lives in `Crypto/MemoryChecking.lean:56` (`Kind.read` /
`.write`) and `Crypto/UniversalMemory.lean:75` (the domain-tagged address space), NOT in `Auth`.
`Auth.read`/`.write` are used exclusively as **endpoint cap rights** — every use-site is
`Cap.endpoint t [Auth.read, Auth.write]` (e.g. `Exec/Caps.lean:239`, `Widget/CapabilityGraph.lean:90`,
`Circuit/Argus/Effects/Attenuate.lean:405`) or a rights-subset check on such a cap. There is no
use-site where `Auth.read`/`.write` names a memory-frame access.

So dregg's `Auth.read`/`.write` ARE seL4's `Receive`/`SyncSend` (IPC), correctly — and seL4's *memory*
`Read`/`Write` map onto dregg's `Kind.read`/`.write` (a separate, richer model). The α-map dropping
seL4 `Read`/`Write` to `none` is faithful to dregg's **architecture**: dregg does not put memory access
in the cap-authority lattice; it puts it in a Blum-multiset memory-consistency argument
(`universal_memory_sound`). Memory access is governed there (and arguably MORE strongly — value- and
serial-checked, not just an authority bit).

**Verdict: acceptable-projection.** Not a confusion: dregg genuinely factors memory-access authority
into a separate, stronger model. The only honest follow-up is *documentary* — the α-map's `Read↦none`
/ `Write↦none` arms should cite `Crypto.MemoryChecking.Kind` as "imaged in dregg's memory model, not its
cap lattice," so a reader does not mistake `none` for "dregg ignores memory access." (Caveat: IF dregg
ever wants ONE cap to gate both "may invoke this endpoint" AND "may read this Surface cell's state"
through the same authority lattice — i.e. `Target::Surface` reads becoming cap-authority rather than
memory-model facts — this verdict flips to conflation-to-fix. Today no use-site does that.)

### 3. `DeleteDerived` (authority to delete derived caps = REVOCATION) → **acceptable-projection** (captured elsewhere, as a registry op not an authority bit)

**Deciding use-sites:** revocation is modelled in TWO places, NEITHER as an authority constructor:
- `Dregg2/Authority/Credential.lean:125` — `revoke` = insert credential id into the grow-only
  `RevocationSet` (a nullifier G-Set); `revoke_blocks_verify` is the teeth.
- `Dregg2/Distributed/Revocation.lean` — the topology-parametrized version (`eventual_bounded_revocation`
  / `immediate_revocation`, `Revocation.lean:33,37`), and
- `Dregg2/Firmament/SeL4Kernel.lean:220` — `CNode.revoke`, the synchronous transitive derivation-tree
  revoke (`revoke_kills_all_doomed`, `SeL4Kernel.lean:580`).

In seL4, `DeleteDerived` is the authority a subject needs to revoke caps it derived. dregg models
revocation as a **state operation gated by ownership/registry membership**, not as an authority label on
a policy edge. The firmament's `CNode.revoke` walks the `mintedFrom` derivation tree (`SeL4Kernel.lean:212`)
— it is structurally the seL4 `DeleteDerived` capability's EFFECT, but realized as a kernel operation,
not an `auth`-graph edge. dregg never asks "does this subject hold `DeleteDerived` authority over that
cap?" — it asks "is this cap in my CNode / is this credential id mine to revoke?".

**Verdict: acceptable-projection.** The revocation *capability* is captured (three ways), but as an
operational/registry discipline rather than an authority-lattice constructor. Adding `DeleteDerived` to
`Auth` would NOT connect to any existing dregg revocation proof (they are not authority-edge-gated), so
it would be a dangling constructor. Genuine, but not missing — relocated.

### 4. `AAuth` (architecture-specific: VSpace/ASID/Frame) → **acceptable-projection** (correctly opaque)

**Deciding use-site:** the transcription itself keeps `AAuth` opaque (`SeL4Abstract.lean:83`, the nullary
placeholder; `archCapAuthConferred` opaque, `:199`). dregg has no VSpace/ASID/page-table layer — the
firmament's memory is Frames-as-shared-regions (`SeL4Kernel.lean ObjectType.frame`), with no
architecture-specific address-space authority. No use-site anywhere references an arch authority.

**Verdict: acceptable-projection (clean).** `AAuth↦none` is correct and final. dregg operates above the
arch layer; this is the legitimately-opaque ctor. No enrichment.

---

## Enrichment ripple cost (if `Auth` gains a constructor)

**The good news: the core attenuation algebra does NOT pattern-match on `Auth` constructors.** It treats
`List Auth` / `Finset Auth` generically:
- `attenuate` (`Exec/Caps.lean:79`) — `List.filter` on a `keep` list; constructor-agnostic.
- `capAuthConferred` (`Positional.lean:66`, `EffectsAuthority.lean`) — returns the cap's rights list verbatim; agnostic.
- `authNarrowerOrEqual` / `attenuate_subset` / `attenuate_non_amplifying` — `List.Subset` / membership; agnostic.

So **every cap/attenuation/non-amplification proof is INVARIANT under adding an `Auth` constructor.**
That is the expensive class the brief worried about, and it is ~zero-cost.

The constructor-exhaustive sites that WOULD need a new arm (the COMPLETE list):

| site | file:line | what it needs |
|---|---|---|
| `authCode` felt-encoder ×5 | `Circuit/Witness/{Spawn,Delegate,RefreshDelegation,RevokeDelegation,attenuateA}Witness.lean` (each ~L78) | one new `\| .notify => 7` arm + the felt index |
| FFI `authCode` | `Exec/FFI.lean:430` | one new arm (+ matching Rust marshaller) |
| `Fintype Auth` enumeration | `Exec/Caps.lean:54` (`elems := {…}`) | add ctor to the set; `complete` re-`decide`s |
| toString/display | `Widget/DreggForest.lean:60` | one new arm |

(VERIFIED NOT affected: `Circuit/DescriptorIR2.lean:171,1069` — those `.read`/`.write` matches are the
SEPARATE `MemoryChecking.Kind` / `MapOpKind` enums, not `Authority.Auth`. They stay put.)

**Ripple estimate: ~8–9 mechanical edit sites, ALL one-line arm additions, ZERO proof restructuring.**
The felt-encoders are the only ones with a wire/circuit consequence (a new authority code = a column
value the circuit and the Rust marshaller must agree on; this is a VK/encoding bump, not a proof break).
`Fintype.complete` and every `fin_cases`/`cases a <;> …` proof (e.g. `alpha_injective_on_used`,
`authNarrowerOrEqual_refl`) re-close automatically under `decide`/`simp` with the new ctor.

No `deriving Fintype` to worry about — the `Fintype` instance is the one manual `elems` set
(`Caps.lean:54`), already a single edit.

---

## Recommendation

**Enrich with exactly ONE constructor: `notify`. Accept the projection for Read/Write, DeleteDerived,
AAuth.**

Rationale:
- **`notify` is the one genuine conflation** dregg's own firmament makes-but-cannot-express: it models
  the async Notification object distinctly (`SeL4Kernel.lean:238`) and refines real signal/wait Rust, but
  a Notification cap and an Endpoint cap confer the same dregg authority (`write`). Adding `Auth.notify`
  lets a cap to a Notification confer `notify` where a cap to an Endpoint confers `write`, matching
  seL4's `SyncSend` vs `Notify` split (`SeL4Abstract.lean:182`) — and it makes α **total on the IPC
  authorities** (`Receive, SyncSend, Notify, Reset, Grant, Call, Reply` all imaged), so the firmament's
  IPC/notification authority becomes faithfully seL4-grounded, not 6-of-7-projected.
- **Read/Write, DeleteDerived, AAuth are NOT missing — they are relocated or above-level.** Adding them
  to `Auth` would create dangling constructors that connect to no dregg proof (memory access → the Blum
  model; revocation → the registry/derivation-tree ops; arch → nonexistent in dregg). That is
  enrichment-as-noise, not enrichment-as-grounding.

**Cost of the `notify` enrichment:** the ~9–11 one-line arm additions above + a felt-code/VK bump for
the circuit encoders. **Assurance gain:** α becomes total on all 7 seL4 IPC authorities (vs 6 today —
`Notify` is currently the one IPC ctor going to `none`), so the dregg⊗seL4 grounding covers the
firmament's full IPC + notification authority faithfully. The remaining `none` arms (`Read`, `Write`,
`DeleteDerived`, `AAuth`) become *principled* projections (memory-model / registry-op / above-arch),
each documentable with its dregg home, rather than unexplained gaps.

**If ember declines even `notify`:** the minimal honest action is documentary — annotate α's five `none`
arms (`SeL4Abstract.lean:459–463`) with WHERE each is imaged in dregg (`Notify` → the modelled-but-
unauthority'd Notification object; `Read`/`Write` → `Crypto.MemoryChecking.Kind`; `DeleteDerived` → the
revocation registry + `CNode.revoke`; `AAuth` → above dregg's level), turning "no dregg image" into
"imaged outside the cap lattice, here." That removes the misread that `none` means dregg ignores these.
