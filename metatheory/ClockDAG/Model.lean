/-
# ClockDAG.Model — modeling the Simbi Mesh-Credit / ClockDAG protocol's SAFETY core as a
dregg2 instance, and PROVING its invariants by REUSING dregg2's verified theorems.

## NON-CORE demonstrator
**ClockDAG (`simbi-inc/clockdag-protocol`, the "Simbi Mesh Credit Protocol") is a SEPARATE
project — not Dragon's Egg (dregg2).** Simbi is in production and is NOT scheduled to be
ported onto dregg. This module is a *modeling exercise*: it shows that dregg2's already-proved
primitives (`Spec.Conservation`, `Authority.Blocklace`, `Exec.JointCell`, `Crypto.Merkle` /
`Crypto.NonMembership`) faithfully capture the core SAFETY invariants of a real shipped
mutual-credit DAG ledger. It is in its OWN namespace `ClockDAG.*`, IMPORTS core dregg2 modules
but is NOT part of the core lib (`Dregg2.lean` / `Dregg2/Claims.lean` do not — and must not —
reference it). Verify standalone with `lake env lean ClockDAG/Model.lean`.

The point of the exercise: each ClockDAG safety property below is discharged by *invoking* an
existing dregg2 theorem on a faithfully-mapped instance — we **reuse**, never reprove. The
mapping cites the byte-for-byte spec at `~/pub/clockdag-protocol/SPEC.md`.

## What is modeled vs. the full spec (honest scope)
We model the four SAFETY invariants the lane targets; we do NOT model the wire format
(CBOR/§2), PoW (§12), VRF eligibility (§7 — a `Prop`-carrier seam, like dregg2's `signed`),
gossip/sync (§8–9), demurrage (§11), governance/slashing kinds 7–14 (§5.7), or snapshots'
pruning policy (§10). Cryptographic facts (BLAKE3 collision-resistance, Ed25519 / sr25519-VRF
unforgeability) are §8-style `Prop`-carrier seams discharged outside Lean, EXACTLY as in
dregg2's `Authority.Blocklace` (`signed : Bool`) and `Crypto.Merkle` (`compress` abstract).

### The four invariants (each: SPEC.md section ↦ dregg2 primitive ↦ theorem)
1. `clockdag_transfer_conserves` — SPEC §4 balance-derivation / §5.0 transfer ↦
   `Dregg2.Spec.conservation_over_monoid` over `Bal = ℤ` (credits go negative = debt, the
   mutual-credit invariant). A `kind=0` transfer's `Σδ = 0` preserves the community total.
2. `clockdag_no_double_spend` — SPEC §6 conflict-resolution ↦
   `Dregg2.Authority.Blocklace.equivocation_detectable`: a forking sender (two incomparable
   same-author txs, §6.1) is detected; the witnessing pair IS the proof.
3. `clockdag_htlc_atomic` — SPEC §5.7 kinds 15–17 (SwapLock/SwapClaim/SwapRefund, RFC 0006) ↦
   `Dregg2.Exec.JointCell.joint_cg5_conserves` + `joint_atomic`: a cross-community HTLC swap
   commits both legs or neither, conserving the joint credit total across the two communities.
4. `clockdag_light_client_sound` — SPEC §10 snapshots / §16 vector 07 (Merkle `balances_root`)
   ↦ `Dregg2.Crypto.Merkle.merkle_sound` (inclusion) + `Dregg2.Crypto.NonMembership`
   `nonmembership_sound` (non-inclusion): a light-client inclusion / non-inclusion proof is
   sound against the committed `balances_root`.

Discipline: REUSE proved theorems (no reproof). No `axiom`/`admit`/`native_decide`/`sorry`.
`#assert_axioms` on the four keystones. Imports ONLY existing built dregg2 modules.
-/
import Dregg2.Spec.Conservation
import Dregg2.Authority.Blocklace
import Dregg2.Exec.JointCell
import Dregg2.Crypto.Merkle
import Dregg2.Crypto.NonMembership

namespace ClockDAG

open scoped BigOperators

/-! ## 0. Spec objects, mapped onto dregg2 carriers.

We name the ClockDAG wire objects (SPEC §2) as Lean types whose *shape* is the dregg2
primitive each invariant reuses. The mapping is deliberately thin — the safety content lives
in the reused theorem, not in re-modeled plumbing. -/

/-- A ClockDAG **account id** (`SPEC §1`: `BLAKE3(pubkey)[..20]`). For the safety model the
20-byte address is opaque, so we carry it as a `Nat` label — the same abstraction dregg2 uses
for `Exec.CellId` and `Blocklace.AuthorId`. -/
abbrev Account := Nat

/-- Micro-credits (`SPEC §2` field 4: `amount i64`, `1 credit = 1_000_000 micro`). The signed
`i64` is modeled as `ℤ` — **balances may go negative (debt)**, which is the defining
mutual-credit invariant (`SPEC §3.12`: `balance(sender) - amount >= -credit_limit`, so a
positive balance is NOT required; debt up to the credit limit is the norm). -/
abbrev Micro := Int

/-! ## 1. SAFETY INVARIANT 1 — transfer conserves Σ-credits (SPEC §4, §5.0).

`SPEC §4`: `balance_raw(A,R) = Σ(received) - Σ(sent)`. A `kind=0` transfer (`§5.0`) moves
`amount` from `sender` to `receiver` and **nothing else** — so the per-account deltas over the
community are `[-amount (sender), +amount (receiver)]`, summing to `0`. The community-wide
total credit is therefore invariant under every transfer.

This is EXACTLY `Spec.Conservation`'s `Conservative` `LinearityClass` (`Σδ = 0`) over the
value monoid `Bal = ℤ`. We map a transfer to its delta list and invoke
`Dregg2.Spec.conservation_over_monoid` — REUSED, not reproved. -/

/-- A ClockDAG `kind=0` transfer (`SPEC §5.0`): `amount` micro-credits from `sender` to
`receiver`. (`parents`, `logical_time`, `community`, `pow_nonce` etc. are validation metadata,
§3 — irrelevant to the conservation invariant, so omitted from the safety model.) -/
structure Transfer where
  /-- `SPEC §2` field 2 — the debited account. -/
  sender   : Account
  /-- `SPEC §2` field 3 — the credited account. -/
  receiver : Account
  /-- `SPEC §2` field 4 — micro-credits moved (`i64`, may leave `sender` in debt). -/
  amount   : Micro
  deriving Repr, DecidableEq

/-- **The transfer's per-account `Conservative` deltas** (the `Spec.Conservation` summands):
the sender contributes `-amount`, the receiver `+amount`. This is the `Δ` list whose sum the
conservation law consumes. A `kind=0` transfer is a `Conservative` effect
(`Spec.linearity (.transfer _) = .Conservative`). -/
def Transfer.deltas (t : Transfer) : List Micro := [-t.amount, t.amount]

/-- The transfer's effect color is `Conservative` (`Spec.LinearityClass`) — mapping the
ClockDAG `kind=0` onto dregg2's coloring (`Spec.linearity (.transfer t.amount.natAbs)`). A
transfer is paired (debit matched by credit), never a disclosed mint/burn. -/
theorem transfer_is_conservative (t : Transfer) :
    (Dregg2.Spec.linearity (.transfer t.amount.natAbs)) = Dregg2.Spec.LinearityClass.Conservative :=
  rfl

/-- The transfer's deltas sum to `0` — the `conservedInDomain` premise, discharged by `ring`
on `(-amount) + amount`. This is the §5.0 "no payload, just move" fact. -/
theorem transfer_deltas_sum_zero (t : Transfer) :
    Dregg2.Spec.conservedInDomain (Bal := Micro) Dregg2.Spec.Domain.balance t.deltas := by
  show ([(-t.amount), t.amount] : List Micro).sum = 0
  simp [List.sum_cons]

/-- **`clockdag_transfer_conserves` — SAFETY INVARIANT 1 (REUSES
`Dregg2.Spec.conservation_over_monoid`).** A ClockDAG `kind=0` transfer (`SPEC §5.0`) preserves
the community-wide total credit (`SPEC §4` balance derivation): adding the transfer's per-account
deltas to any prior community total `pre` leaves it unchanged. The conserved quantity is valued
in `ℤ` (`Micro`), so debt (negative balances) is permitted — the mutual-credit invariant. The
proof is a DIRECT application of dregg2's already-verified `conservation_over_monoid` to the
transfer's delta list; we do not reprove conservation. -/
theorem clockdag_transfer_conserves (t : Transfer) (pre : Micro) :
    pre + t.deltas.sum = pre :=
  Dregg2.Spec.conservation_over_monoid (Bal := Micro)
    Dregg2.Spec.Domain.balance pre t.deltas (transfer_deltas_sum_zero t)

/-! ### Multi-account `Finset` form — the §4 ledger picture.

`SPEC §4` derives balances over the whole community (a finite set of accounts). The
`Finset`-sum form of conservation (`conservation_over_monoid_finset`) is the shape ClockDAG's
`balance_raw` actually uses: a balance function `bal : Account → Micro` and a transfer's delta
function `δ`. If `δ` sums to `0` over the community, the post-balances total equals the pre. -/

/-- The delta FUNCTION of a transfer over a community account set: `-amount` at the sender,
`+amount` at the receiver, `0` elsewhere. (`SPEC §4`: only `sender`/`receiver` rows change.) -/
def Transfer.deltaFn (t : Transfer) : Account → Micro :=
  fun a => if a = t.sender then -t.amount else if a = t.receiver then t.amount else 0

/-- **`clockdag_transfer_conserves_ledger` — the §4 community-ledger form (REUSES
`Dregg2.Spec.conservation_over_monoid_finset`).** Given a community account set whose transfer
deltas sum to `0`, applying the transfer to every account's balance leaves the community total
unchanged. The `Σδ = 0` premise is the well-formedness of a balanced transfer (`sender ≠
receiver` both in the community); we take it as the hypothesis the §3 validation establishes,
then hand off to the verified finset conservation theorem. -/
theorem clockdag_transfer_conserves_ledger (t : Transfer) (community : Finset Account)
    (bal : Account → Micro) (hbalanced : (∑ a ∈ community, t.deltaFn a) = 0) :
    (∑ a ∈ community, (bal a + t.deltaFn a)) = ∑ a ∈ community, bal a :=
  Dregg2.Spec.conservation_over_monoid_finset (Bal := Micro) community bal t.deltaFn hbalanced

/-! ## 2. SAFETY INVARIANT 2 — a double-spending (forking) sender is detected (SPEC §6).

`SPEC §6` (conflict resolution): two txs `T1, T2` with the **same `sender`** and overlapping
`logical_time` reachability that together overdraw the credit limit are a *conflict* (a
double-spend). The DAG keeps both; the witness's ordering picks one and marks the other
`INVALID`. The structural precondition — and the thing that makes the double-spend
*detectable* — is that the two same-sender txs are **incomparable in the DAG** (neither is in
the other's causal past; if one observed the other, the sender's `logical_time` monotonicity,
`SPEC §3.8`, would have ordered them and there'd be no conflict).

This is EXACTLY `Authority.Blocklace`'s **equivocation**: two incomparable same-author blocks.
A ClockDAG tx-DAG node maps to a `Blocklace.Block` (author = `sender`, preds = `parents` field
5, `SPEC §2`). We map the conflicting pair to a `Blocklace.Equivocation` and invoke
`Dregg2.Authority.Blocklace.equivocation_detectable` — REUSED. -/

open Dregg2.Authority.Blocklace in
/-- A ClockDAG tx-DAG, modeled as a `Blocklace.Lace` (`SPEC §2`: txs form a DAG via the
`parents` field; each tx is content-addressed by its `tx_id`). `Block.creator` is the tx
`sender`, `Block.preds` is the `parents` array, `Block.id` is the `tx_id`. -/
abbrev TxDag := Dregg2.Authority.Blocklace.Lace

open Dregg2.Authority.Blocklace in
/-- A **double-spend** in ClockDAG (`SPEC §6`): the structural witness is a `Blocklace`
`Equivocation` — two distinct, incomparable, same-`sender` txs in the DAG. We DEFINE the
ClockDAG double-spend to BE the blocklace equivocation (the faithful mapping), so the detection
theorem transports verbatim. -/
def DoubleSpend (B : TxDag) (sender : Account) (t1 t2 : Dregg2.Authority.Blocklace.Block) : Prop :=
  Dregg2.Authority.Blocklace.Equivocation B sender t1 t2

open Dregg2.Authority.Blocklace in
/-- **`clockdag_no_double_spend` — SAFETY INVARIANT 2 (REUSES
`Dregg2.Authority.Blocklace.equivocation_detectable`).** A forking sender that double-spends in
the ClockDAG tx-DAG is DETECTED: the conflicting pair `(t1, t2)` is *witnessed by itself* — the
sender is provably an `Equivocator`, and the two incomparable same-sender txs are exactly the
`EquivocationProof`. No synchrony, quorum, or signature-forgery assumption (`SPEC §6` keeps both
txs and the witness orders them; the *detectability* is purely the DAG structure). The proof is
a DIRECT application of dregg2's verified `equivocation_detectable`. -/
theorem clockdag_no_double_spend {B : TxDag} {sender : Account}
    {t1 t2 : Dregg2.Authority.Blocklace.Block} (ds : DoubleSpend B sender t1 t2) :
    Dregg2.Authority.Blocklace.Equivocator B sender ∧ t1 ≠ t2 ∧
      ¬ Dregg2.Authority.Blocklace.precedes B t1 t2 ∧
      ¬ Dregg2.Authority.Blocklace.precedes B t2 t1 :=
  Dregg2.Authority.Blocklace.equivocation_detectable ds

open Dregg2.Authority.Blocklace in
/-- **`clockdag_honest_sender_no_double_spend` (REUSES `Blocklace.honest_no_equivocation`).**
The dual: a sender that obeys `SPEC §3.8` (logical-time monotonicity — every new tx observes
the sender's previous tx, so its txs are `≺`-totally-ordered) can NEVER double-spend. Honest
`logical_time` discipline ⇒ no fork ⇒ no conflict. Reuses the verified
`honest_no_equivocation`. -/
theorem clockdag_honest_sender_no_double_spend {B : TxDag} {sender : Account}
    (hon : Dregg2.Authority.Blocklace.HonestChain B sender) :
    ¬ Dregg2.Authority.Blocklace.Equivocator B sender :=
  Dregg2.Authority.Blocklace.honest_no_equivocation hon

/-! ## 3. SAFETY INVARIANT 3 — cross-community HTLC swap is atomic (SPEC §5.7, RFC 0006).

`SPEC §5.7` kinds 15–17 (`SwapLock`/`SwapClaim`/`SwapRefund`, RFC 0006) implement a
hash+time-locked **cross-community atomic swap**: credit locked in community `A` is claimed in
community `B` by revealing a secret, or both legs refund. ClockDAG has **no global ledger** —
each community is its own balance namespace (`SPEC §4`: `balance(A,R)` is per-community). So a
swap that moves credit from a cell in community `A` to a cell in community `B` is NOT internally
conserving in either community's ledger; the conserved quantity is the **joint total** across
the two communities, preserved iff the two legs are equal-and-opposite and commit atomically.

This is EXACTLY `Exec.JointCell`'s bilateral `BiTurn` (CG-5): one half-edge out of `A`, one into
`B`, summing to zero, committed all-or-none. The hash-lock secret / time-lock are RFC-0006
`Prop`-carrier seams (like dregg2's `SharedBinding` CG-2 id); the SAFETY content — atomic
commit + joint conservation — is `joint_cg5_conserves` and `joint_atomic`, REUSED. -/

/-- A ClockDAG cross-community HTLC swap (`SPEC §5.7` kinds 15–17, RFC 0006), modeled as a
`JointCell.BiTurn`: lock `amt` out of `srcA` (community `A`) and release it to `dstB` (community
`B`), under each side's authority, both legs bound to the shared hash-lock `sid` (RFC 0006's
secret-hash / swap id — the CG-2 shared identity that ties the two legs). -/
abbrev HtlcSwap := Dregg2.Exec.JointCell.BiTurn

/-- **`clockdag_htlc_atomic` — SAFETY INVARIANT 3 (REUSES
`Dregg2.Exec.JointCell.joint_cg5_conserves`).** A committed cross-community HTLC swap preserves
the **joint credit total** across the two communities `A` and `B`: community `A` loses exactly
what community `B` gains (`SPEC §4` per-community balances + RFC-0006 equal-and-opposite legs).
With no global ledger this joint total is the only conserved measure. DIRECT application of
dregg2's verified bilateral CG-5 keystone. -/
theorem clockdag_htlc_atomic {A B A' B' : Dregg2.Exec.KernelState} {swap : HtlcSwap}
    (h : Dregg2.Exec.JointCell.jointApply A B swap = some (A', B')) :
    Dregg2.Exec.JointCell.jointTotal A' B' = Dregg2.Exec.JointCell.jointTotal A B :=
  Dregg2.Exec.JointCell.joint_cg5_conserves h

/-- **`clockdag_htlc_all_or_nothing` (REUSES `Dregg2.Exec.JointCell.joint_atomic`).** The
HTLC's defining liveness-of-safety property: a swap commits BOTH legs or NEITHER — there is no
state where community `A`'s lock succeeds while `B`'s release fails (RFC 0006: claim reveals the
secret on both sides, or both refund after `time_lock`). The `jointApply` `Option` IS the
atomic gate; reuses the verified `joint_atomic` (success ⇒ both halves committed). -/
theorem clockdag_htlc_all_or_nothing {A B A' B' : Dregg2.Exec.KernelState} {swap : HtlcSwap}
    (h : Dregg2.Exec.JointCell.jointApply A B swap = some (A', B')) :
    Dregg2.Exec.JointCell.applyHalfOut A swap = some A' ∧
      Dregg2.Exec.JointCell.applyHalfIn B swap = some B' :=
  Dregg2.Exec.JointCell.joint_atomic h

/-! ## 4. SAFETY INVARIANT 4 (optional) — light-client inclusion / non-inclusion is sound.

`SPEC §10` snapshots: every `S` rounds a witness emits a `snapshot` tx (kind=4, `SPEC §5.4`)
carrying `balances_root = BLAKE3(canonical-CBOR sorted-by-account {account: balance})`. A LIGHT
client (`SPEC §10`: "light nodes may discard txs … keeping only snapshot") verifies an account's
balance is INCLUDED in (or ABSENT from) the snapshot via a Merkle proof against `balances_root`
(`SPEC §16` vector `07-snapshot.json`). The leaf list is **sorted by account** (§5.4), which is
exactly what `Crypto.NonMembership` requires for non-inclusion.

Inclusion ↦ `Dregg2.Crypto.Merkle.merkle_sound`; non-inclusion ↦
`Dregg2.Crypto.NonMembership.nonmembership_sound`. Both REUSED. The hash `compress` (BLAKE3) is
abstract — its collision-resistance is a §8 seam, never a Lean theorem (matching dregg2). -/

-- A snapshot leaf digest (`SPEC §5.4`: a `BLAKE3` of an `{account: balance}` entry) is
-- opaque, carried at whatever `Digest` type the Merkle gadget is instantiated over.
section LightClient

variable {Digest : Type} (compress : Digest → Digest → Digest)

/-- **`clockdag_light_client_sound` — SAFETY INVARIANT 4a, INCLUSION (REUSES
`Dregg2.Crypto.Merkle.merkle_sound`).** A light-client INCLUSION proof is sound: if the witness
trace satisfies the Merkle AIR against the snapshot's `balances_root` (`SPEC §10`, §16 vector
07), then the claimed `leaf` (an `{account: balance}` entry) is GENUINELY a member of the tree
committed by `balances_root` — the light client cannot be fooled into accepting a balance not in
the snapshot. DIRECT application of dregg2's verified `merkle_sound`. -/
theorem clockdag_light_client_sound (balancesRoot leaf : Digest)
    (proof : Dregg2.Crypto.Merkle.CircuitIR Digest)
    (h : Dregg2.Crypto.Merkle.Satisfies compress proof balancesRoot leaf) :
    Dregg2.Crypto.Merkle.MerkleMembers compress balancesRoot leaf :=
  Dregg2.Crypto.Merkle.merkle_sound compress balancesRoot leaf proof h

/-- **`clockdag_light_client_absent_sound` — SAFETY INVARIANT 4b, NON-INCLUSION (REUSES
`Dregg2.Crypto.NonMembership.nonmembership_sound`).** A light-client NON-inclusion proof is
sound: if the trace satisfies the sorted-adjacency non-membership AIR against `balances_root`
(two bracketing neighbors present + `lo < e < hi`, over the §5.4 sorted-by-account leaf list),
then the queried entry `e` is GENUINELY ABSENT from the snapshot. The light client cannot be
fooled into accepting a false "this account/balance is not in the snapshot". DIRECT application
of dregg2's verified `nonmembership_sound`. -/
theorem clockdag_light_client_absent_sound [LinearOrder Digest]
    (balancesRoot e : Digest) (leaves : List Digest)
    (proof : Dregg2.Crypto.NonMembership.CircuitIR Digest)
    (h : Dregg2.Crypto.NonMembership.Satisfies compress proof balancesRoot e leaves) :
    Dregg2.Crypto.NonMembership.NonMember leaves e :=
  Dregg2.Crypto.NonMembership.nonmembership_sound compress proof balancesRoot e leaves h

end LightClient

/-! ## 5. Non-vacuity — a concrete small ClockDAG-shaped scenario.

A two-community mutual-credit world, with a real transfer (conserving), a detected double-spend
(a forking sender), and a cross-community HTLC swap (atomic, joint-conserving) — all #eval-able,
witnessing that the mapped instances are inhabited and the theorems fire on real data. -/

/-! ### 5.1 A conserving transfer (Invariant 1). -/

/-- Alice (`account 1`) sends `50_000_000` micro (= 50 credits) to Bob (`account 2`). -/
def aliceToBob : Transfer := { sender := 1, receiver := 2, amount := 50_000_000 }

-- The transfer's deltas sum to zero (the §4 balance invariant), and conservation holds for
-- any prior community total (here 1000 micro of pre-existing credit elsewhere).
#guard (aliceToBob.deltas == [-50000000, 50000000])                              -- [-50000000, 50000000]
#guard (aliceToBob.deltas.sum == 0)                                              -- 0  (Σδ = 0, conserving)
example : (1000 : Micro) + aliceToBob.deltas.sum = 1000 := clockdag_transfer_conserves aliceToBob 1000

/-! ### 5.2 A detected double-spend (Invariant 2).

Sender `9` forks: two distinct seq-1 txs `ds1, ds2` that each ack genesis `gen` but NOT each
other — incomparable, a double-spend. We reuse the blocklace demo's exact structural shape. -/

/-- Community genesis tx (`SPEC §6`: the DAG root; here a `kind=6 join`-like base, seq 0). -/
def genTx : Dregg2.Authority.Blocklace.Block := { id := 0, creator := 7, seq := 0, preds := [] }
/-- Forking sender `9`, tx branch A (seq 1) — spends, acks genesis only. -/
def dsTx1 : Dregg2.Authority.Blocklace.Block := { id := 2, creator := 9, seq := 1, preds := [0] }
/-- Forking sender `9`, tx branch B (seq 1) — double-spends the same credit, acks genesis only,
NOT `dsTx1`. The incomparable pair (`SPEC §6` conflict). -/
def dsTx2 : Dregg2.Authority.Blocklace.Block := { id := 3, creator := 9, seq := 1, preds := [0] }

/-- The demo tx-DAG: genesis + the two conflicting txs from sender `9`. -/
def demoTxDag : TxDag := [genTx, dsTx1, dsTx2]

-- The two double-spend txs share sender 9 and seq 1, but neither acks the other (incomparable).
#guard (decide (dsTx1.creator = dsTx2.creator ∧ dsTx1.seq = dsTx2.seq))   -- true  (same sender+seq)
#guard (decide (dsTx1.id ∈ dsTx2.preds ∨ dsTx2.id ∈ dsTx1.preds) == false)         -- false (incomparable)

/-- Sender `9`'s txs are not directly pointed at each other — the structural core of the
double-spend conflict. -/
theorem demo_ds_not_pointed :
    ¬ Dregg2.Authority.Blocklace.pointed demoTxDag dsTx1 dsTx2 ∧
      ¬ Dregg2.Authority.Blocklace.pointed demoTxDag dsTx2 dsTx1 := by
  constructor <;> · rintro ⟨hmem, _, _⟩; revert hmem; decide

/-- In `demoTxDag` every `≺`-chain starts at genesis `genTx` (all nonempty `preds` are `[0]`),
so neither fork tx precedes the other. Mirrors `Blocklace.demo_precedes_left_g0`. -/
theorem demo_precedes_left_gen {x y : Dregg2.Authority.Blocklace.Block}
    (h : Dregg2.Authority.Blocklace.precedes demoTxDag x y) : x = genTx := by
  have edge : ∀ a b, Dregg2.Authority.Blocklace.pointed demoTxDag a b → a = genTx := by
    rintro a b ⟨hmem, hla, hlb⟩
    have hbmem : b ∈ demoTxDag := List.mem_of_find?_eq_some hlb
    have ha0 : a.id = 0 := by
      simp only [demoTxDag, List.mem_cons, List.not_mem_nil, or_false] at hbmem
      rcases hbmem with rfl | rfl | rfl <;> · revert hmem; simp [genTx, dsTx1, dsTx2]
    rw [ha0] at hla
    have : demoTxDag.lookup 0 = some genTx := by decide
    rw [this] at hla; exact (Option.some.injEq _ _ ▸ hla).symm
  induction h with
  | @base a b hp => exact edge a b hp
  | @trans a m b _ _ iha _ => exact iha

/-- Neither fork tx observes the other (a `≺` from `dsTx1`/`dsTx2` would force it to equal
genesis, which `decide` refutes). -/
theorem demo_ds_no_precedes :
    ¬ Dregg2.Authority.Blocklace.precedes demoTxDag dsTx1 dsTx2 ∧
      ¬ Dregg2.Authority.Blocklace.precedes demoTxDag dsTx2 dsTx1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : dsTx1 = genTx := demo_precedes_left_gen h; revert this; decide
  · have : dsTx2 = genTx := demo_precedes_left_gen h; revert this; decide

/-- **The concrete double-spend** — sender `9` forks `dsTx1 ∥ dsTx2` in `demoTxDag`. -/
theorem demo_double_spend : DoubleSpend demoTxDag 9 dsTx1 dsTx2 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  exact ⟨by decide, demo_ds_no_precedes.1, demo_ds_no_precedes.2⟩

/-- **`demo_ds_detected`** — running Invariant 2 on the concrete fork: sender `9` is detected as
a double-spender, with witnessing pair `(dsTx1, dsTx2)`. The double-spend is caught. -/
theorem demo_ds_detected :
    Dregg2.Authority.Blocklace.Equivocator demoTxDag 9 ∧ dsTx1 ≠ dsTx2 ∧
      ¬ Dregg2.Authority.Blocklace.precedes demoTxDag dsTx1 dsTx2 ∧
      ¬ Dregg2.Authority.Blocklace.precedes demoTxDag dsTx2 dsTx1 :=
  clockdag_no_double_spend demo_double_spend

/-! ### 5.3 A cross-community HTLC swap (Invariant 3).

Community `A` (cell 0 holds 100 credits), community `B` (cell 7 holds 20). A swap locks 30 out
of `A`'s cell 0 and releases it into `B`'s cell 7. Joint total 120 is preserved; atomic. -/

/-- Community `A`'s ledger (cell 0: 100, cell 1: 5). -/
def commA : Dregg2.Exec.KernelState :=
  { accounts := {0, 1}, bal := fun c => if c = 0 then 100 else if c = 1 then 5 else 0,
    caps := fun _ => [] }
/-- Community `B`'s ledger (cell 7: 20). -/
def commB : Dregg2.Exec.KernelState :=
  { accounts := {7}, bal := fun c => if c = 7 then 20 else 0, caps := fun _ => [] }
/-- The HTLC swap: lock 30 out of `A`.0, release into `B`.7; hash-lock / swap id `42`. -/
def demoSwap : HtlcSwap :=
  { actorA := 0, srcA := 0, actorB := 7, dstB := 7, amt := 30, sid := 42 }

#guard ((Dregg2.Exec.JointCell.jointApply commA commB demoSwap).isSome)              -- true (commits)
#guard (Dregg2.Exec.JointCell.jointTotal commA commB == 125)                                -- 125 (105 + 20)
#guard ((Dregg2.Exec.JointCell.jointApply commA commB demoSwap).map
        (fun p => Dregg2.Exec.JointCell.jointTotal p.1 p.2) == some 125)                        -- some 125 (conserved)
#guard (Dregg2.Exec.JointCell.halfA demoSwap + Dregg2.Exec.JointCell.halfB demoSwap == 0) -- 0 (equal+opposite)

/-! ## 6. Axiom hygiene — pin the four SAFETY keystones (each reuses a verified dregg2 theorem).

Every invariant is `#assert_axioms`-clean: it rests only on `propext`/`Classical.choice`/
`Quot.sound` (inherited from the reused dregg2 theorem), with no `axiom`/`sorry`/`native_decide`
introduced here. The reuse is total — these are application sites, not reproofs. -/

#assert_axioms clockdag_transfer_conserves
#assert_axioms clockdag_transfer_conserves_ledger
#assert_axioms clockdag_no_double_spend
#assert_axioms clockdag_honest_sender_no_double_spend
#assert_axioms clockdag_htlc_atomic
#assert_axioms clockdag_htlc_all_or_nothing
#assert_axioms clockdag_light_client_sound
#assert_axioms clockdag_light_client_absent_sound
#assert_axioms demo_double_spend
#assert_axioms demo_ds_detected

end ClockDAG
