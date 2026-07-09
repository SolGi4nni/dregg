/-
# `Dregg2.Crypto.LightClientSoundness` — THE UNIVERSAL FOLD as a CRYPTO game: whole-history
light-client soundness reduced to the DL/MSIS/hash FLOOR.

The deployed light client (`lightclient/src/lib.rs::verify_history`, `wasm/src/
bindings_lightclient.rs::verify_finalized_devnet_history`) trusts a WHOLE finalized history by
folding a sequence of finalized-block certificates — each a quorum of HYBRID-SIGNED votes by the
ENROLLED committee, whose ids commit to their ML-DSA keys — and RE-WITNESSING NOTHING. This file
supplies the cryptographic soundness of that fold: it shows that a light client which accepts a
history has accepted a GENUINELY finalized chain — UNLESS a vote was FORGED (a `HybridCombiner.
Forgery` refuting `EufCma`, discharged to `SchnorrDLHard ∨ MSISHard`) or an ML-DSA key NOT COMMITTED
by its committee id was accepted (a hash collision refuting `IdentityCommitment`/`HashCR`).

The model composes three floors already in the tree, with NO fresh carrier:

* **the finalization leg** — `ConsensusSafety.Finalized`: a block is finalized at a height when a
  quorum of `q = n − f` distinct committee members each hold a valid HYBRID vote (`ConsensusSafety.
  ValidVote` under `HybridCombiner.hybrid Cl Pq`);
* **the enrollment leg** — `IdentityCommitment.verify_committed`: each committee member's id
  `H("dregg-hybrid-id-v1", ed ‖ len(ml) ‖ ml)` COMMITS its `(ed25519, ml_dsa)` pair, so the id IS the
  enrollment (`id_commitment_binds` / `attacker_key_not_committed` under `HashCR`);
* **the ordering leg** — a `Chained` list of certificates whose heights are the consecutive naturals
  from the genesis anchor (the fold's `new_height[i] = old_height[i] + 1` temporal tooth).

The `AcceptedHistory` structure IS what the light client builds as it folds. The theorems:

1. **`lightclient_sound`** — acceptance yields a genuinely finalized chain: each step is `Finalized`
   (by construction) AND every HONEST quorum member GENUINELY cast its vote — because an accepted
   `ValidVote` on a body an honest member never cast is a fresh valid signature = a `Forgery` refuting
   its `EufCma`. So under each honest member's `EufCma`, an accepted history is genuine.
2. **`accepting_forged_history_breaks_floor`** — the contrapositive with the floor plugged in: a light
   client that accepts a history crediting an honest member with a vote it never cast BREAKS the floor
   (the `Forgery` yields a `DLSolver` classically / two SelfTargetMSIS solutions on the pq side via
   `HybridCombiner.hybrid_secure_if_either_floor`, impossible under `SchnorrDLHard ∨ MSISHard`). *A
   light client that accepts a FORGED history yields a break of the floor.*
3. **`lightclient_agrees_with_full_node`** — the fold witnesses EXACTLY what a re-executor concludes:
   every step the light client attests, a full node re-executing the same certificates `Finalized`s
   (same object), and — `lightclient_no_fork` — the accepted history never contains two conflicting
   blocks at one height (`consensus_safe_under_floor`), so the light client and a full node never
   disagree.
4. **`no_long_range`** — a history signed by a NON-ENROLLED committee is REJECTED: an attacker who
   keeps the honest ids but swaps in its OWN ml_dsa keys fails the enrollment gate
   (`attacker_key_not_committed`), because the ids do not commit those keys; and accepting it would
   exhibit a hash collision (`accepting_long_range_breaks_hashcr`, `distinct_verifying_pairs_break_
   hashcr`). This is the anti-long-range / anti-pale-ghost tooth.

## No named-carrier laundering

Every irreducible object is either the crypto FLOOR (`SchnorrDLHard`, `MSISHard`, `HashCR`), a
forking REDUCTION hypothesis (a forger ⟹ a solver — a theorem of the existing forking machinery, not
a carrier), or the honest protocol THRESHOLD (`n > 3f`, `≤ f` Byzantine) which is the honest dual of a
crypto floor. `EufCma` is DISCHARGED through `HybridCombiner`; the id binding is DISCHARGED through
`IdentityCommitment` to `HashCR`. Nothing else.

## Teeth (both polarities, load-bearing)

(a) an HONEST finalized 2-step history is ACCEPTED (`toyHistory`); (b) a history crediting a member
with a vote it never cast EXHIBITS the `Forgery` (`tooth_forged_vote_is_forgery`); (c) an attacker key
whose id does not commit it is REJECTED by the enrollment gate (`tooth_attacker_key_rejected`), and
accepting it would be a hash collision.

`#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}).
-/
import Dregg2.Crypto.ConsensusSafety
import Dregg2.Crypto.IdentityCommitment

namespace Dregg2.Crypto.LightClientSoundness

open Dregg2.Crypto.ConsensusSafety
open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.IdentityCommitment
open Dregg2.Crypto.HermineHintMLWE
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.SchnorrCurveField
open Dregg2.Crypto.HermineSelfTargetMSIS

/-! ## §1. The model — an enrolled roster, hybrid-signed certificates, and the folded history. -/

section Model

variable {SKc PKc Sigc SKp PKp Sigp : Type*}
variable {Member : Type*} [DecidableEq Member]
variable {Msg Block Pre IdT : Type*}

/-- **The enrolled roster.** A committee of members, each with an `ed25519` key `edPk`, an `ml_dsa`
key `mlPk`, and a hybrid id `id`; `cr`/`frame` are the id-commitment hash + injective length-framing
(`IdentityCommitment`). This is the roster a light client's genesis/checkpoint config pins — the ids
ARE the enrollment because each commits its two keys. -/
structure Roster where
  /-- The domain-separated id-commitment hash (the `CommitReveal` carrier `IdentityCommitment` uses). -/
  cr : CommitReveal Unit Pre IdT
  /-- The injective length-framed preimage `frame ed ml = ed ‖ len(ml) ‖ ml`. -/
  frame : PKc → PKp → Pre
  /-- The framing is genuinely injective in both keys. -/
  hframe : Function.Injective2 frame
  /-- The committee (a finite set of members). -/
  committee : Finset Member
  /-- Each member's hybrid id. -/
  id : Member → IdT
  /-- Each member's `ed25519` public key. -/
  edPk : Member → PKc
  /-- Each member's `ml_dsa` public key. -/
  mlPk : Member → PKp

/-- The member's HYBRID verification key `(ed25519, ml_dsa)` — the key its finalization votes verify
under, and the SAME pair its id commits to. -/
def memberPk (R : @Roster PKc PKp Member Pre IdT) (m : Member) : PKc × PKp := (R.edPk m, R.mlPk m)

/-- **Enrollment holds** — every committee member's id COMMITS its `(ed25519, ml_dsa)` pair
(`verify_committed_ml_dsa`). The light client's roster-admission gate. -/
def Enrolled (R : @Roster PKc PKp Member Pre IdT) : Prop :=
  ∀ m ∈ R.committee, verify_committed R.cr R.frame (R.id m) (R.edPk m) (R.mlPk m)

/-- **A finalized-block certificate.** Block `block` is finalized at height `height` by a quorum of
`q` distinct committee members, each holding a valid HYBRID vote (`ConsensusSafety.Finalized` over
`HybridCombiner.hybrid Cl Pq`). This is one folded step. -/
structure Cert (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (R : @Roster PKc PKp Member Pre IdT) (voteMsg : ℕ → Block → Msg) (q : ℕ) where
  /-- The block's height (a natural — heights ARE naturals). -/
  height : ℕ
  /-- The finalized block. -/
  block : Block
  /-- The quorum of valid hybrid votes finalizing `block` at `height`. -/
  fin : Finalized (hybrid Cl Pq) R.committee (memberPk R) voteMsg q height block

/-- **The light client's accepted history** — what it BUILDS as it folds: enrollment holds, a list of
finalized certificates, whose heights are the consecutive naturals from the genesis anchor `start`
(the ordering tooth — no reorder, drop, or gap). Its EXISTENCE is acceptance. -/
structure AcceptedHistory (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (R : @Roster PKc PKp Member Pre IdT) (voteMsg : ℕ → Block → Msg) (q start : ℕ) where
  /-- The committee is enrolled: each id commits its keys. -/
  enrolled : Enrolled R
  /-- The folded chain of finalized certificates. -/
  certs : List (Cert Cl Pq R voteMsg q)
  /-- Heights are the consecutive naturals from the genesis anchor: step `i` is at `start + i`. -/
  chained : ∀ i (hi : i < certs.length), (certs.get ⟨i, hi⟩).height = start + i

/-! ## §2. `lightclient_sound` — acceptance yields a GENUINELY finalized chain (unless a vote forged). -/

/-- **`lightclient_sound` — THE HEADLINE.** If the light client ACCEPTS a history (an `AcceptedHistory`),
then every step is a genuinely finalized chain step: it is `Finalized` (by construction) AND every
HONEST quorum member GENUINELY cast its vote (`Q m` holds for the vote body). The second conjunct is
the cryptographic content: an accepted `ValidVote` by an honest member on a body it NEVER cast is a
fresh valid signature = a `HybridCombiner.Forgery` refuting that member's `EufCma`. So under each
honest member's `EufCma`, a light client that accepts a history has accepted a genuine one — every
credited honest vote was really cast. -/
theorem lightclient_sound
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (R : @Roster PKc PKp Member Pre IdT) (voteMsg : ℕ → Block → Msg) (q start : ℕ)
    (honest : Member → Prop) (Q : Member → Msg → Prop)
    (heuf : ∀ m ∈ R.committee, honest m → EufCma (hybrid Cl Pq) (memberPk R m) (Q m))
    (A : AcceptedHistory Cl Pq R voteMsg q start)
    (c : Cert Cl Pq R voteMsg q) (hc : c ∈ A.certs) :
    Nonempty (Finalized (hybrid Cl Pq) R.committee (memberPk R) voteMsg q c.height c.block) ∧
    (∀ m ∈ c.fin.quorum, honest m → Q m (voteMsg c.height c.block)) := by
  refine ⟨⟨c.fin⟩, ?_⟩
  intro m hm hhon
  by_contra hnq
  obtain ⟨σ, hv⟩ := c.fin.votes m hm
  exact heuf m (c.fin.sub hm) hhon ⟨voteMsg c.height c.block, σ, hnq, hv⟩

/-! ## §3. `accepting_forged_history_breaks_floor` — a FORGED accepted history breaks DL/MSIS. -/

/-- **`accepting_forged_history_breaks_floor` — the FLOOR discharge.** With the two per-member forking
reductions (a hybrid forgery ⟹ a `DLSolver` classically, two SelfTargetMSIS solutions on the pq side —
the `HybridCombiner` reductions, NOT carriers), a light client that ACCEPTS a history crediting a
member `m` with a vote for `(c.height, c.block)` that `m` NEVER cast (`¬ Q m body`) yields a
contradiction under `SchnorrDLHard ∨ MSISHard`. The accepted `ValidVote` is a `Forgery`; `EufCma` on
`m`'s hybrid key — produced by `hybrid_secure_if_either_floor` — refutes it. So **a light client that
accepts a FORGED history yields a break of the floor** (DL or MSIS): the ONLY way an accepted history
is not genuine is if the floor already fell. -/
theorem accepting_forged_history_breaks_floor
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (R : @Roster PKc PKp Member Pre IdT) (voteMsg : ℕ → Block → Msg) (q start : ℕ)
    (Q : Member → Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {Mo : Type*} [AddCommGroup Mo] [Module Rq Mo] [ShortNorm Mo]
    {No : Type*} [AddCommGroup No] [Module Rq No] [ShortNorm No]
    (Amap : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (dlFork : ∀ m : Member, Forgery Cl (R.edPk m) (Q m) → DLSolver C G)
    (msisFork : ∀ m : Member, Forgery Pq (R.mlPk m) (Q m) →
      ∃ (w : No) (c c' : Rq) (z z' : Mo), c ≠ c' ∧
        IsSelfTargetMSISSolution Amap t β z c w ∧ IsSelfTargetMSISSolution Amap t β z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented Amap t) ((β + β) + (β + β)))
    (A : AcceptedHistory Cl Pq R voteMsg q start)
    (c : Cert Cl Pq R voteMsg q) (hc : c ∈ A.certs)
    (m : Member) (hm : m ∈ c.fin.quorum)
    (hnever : ¬ Q m (voteMsg c.height c.block)) :
    False := by
  obtain ⟨σ, hv⟩ := c.fin.votes m hm
  have heuf :=
    hybrid_secure_if_either_floor Cl Pq (R.edPk m) (R.mlPk m) (Q m)
      C G Amap t β (dlFork m) (msisFork m) hfloor
  simp only [memberPk] at hv
  exact heuf ⟨voteMsg c.height c.block, σ, hnever, hv⟩

/-! ## §4. `lightclient_agrees_with_full_node` — the fold witnesses exactly a re-executor's verdict. -/

/-- **What a FULL NODE (re-executor) concludes** — the same `Finalized` predicate the light client's
certificate carries. A re-executor walks the votes; the light client folds a succinct certificate;
both reach THIS. -/
def FullNodeFinalizes (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (R : @Roster PKc PKp Member Pre IdT) (voteMsg : ℕ → Block → Msg) (q : ℕ)
    (h : ℕ) (b : Block) : Prop :=
  Nonempty (Finalized (hybrid Cl Pq) R.committee (memberPk R) voteMsg q h b)

/-- **`lightclient_agrees_with_full_node`.** Every step the light client attests, a full node
re-executing the SAME committee's votes `Finalized`s — the light-client fold and the re-executor reach
the IDENTICAL verdict object. Acceptance implies the same finalized set: the light client concludes
nothing a full node would not. -/
theorem lightclient_agrees_with_full_node
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (R : @Roster PKc PKp Member Pre IdT) (voteMsg : ℕ → Block → Msg) (q start : ℕ)
    (A : AcceptedHistory Cl Pq R voteMsg q start)
    (c : Cert Cl Pq R voteMsg q) (hc : c ∈ A.certs) :
    FullNodeFinalizes Cl Pq R voteMsg q c.height c.block :=
  ⟨c.fin⟩

/-- **`lightclient_no_fork` — the light client and a full node never DISAGREE.** Under `n > 3f`,
`≤ f` Byzantine, the honest-voting rule, and the floor `SchnorrDLHard ∨ MSISHard` (discharging each
honest member's `EufCma` via `HybridCombiner`), an accepted history NEVER contains two CONFLICTING
blocks `b ≠ b'` at the same height — exactly `consensus_safe_under_floor` applied to the two folded
certificates. So the light client's fold agrees with a safety-enforcing full node: no fork is ever
attested. -/
theorem lightclient_no_fork
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (R : @Roster PKc PKp Member Pre IdT) (voteMsg : ℕ → Block → Msg) (start : ℕ)
    (Q : Member → Msg → Prop)
    (byz : Finset Member) (n f : ℕ)
    (hn : 3 * f + 1 ≤ n) (hcard : R.committee.card = n)
    (hbyz : byz ⊆ R.committee) (hbyzc : byz.card ≤ f)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {Mo : Type*} [AddCommGroup Mo] [Module Rq Mo] [ShortNorm Mo]
    {No : Type*} [AddCommGroup No] [Module Rq No] [ShortNorm No]
    (Amap : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (dlFork : ∀ m : Member, Forgery Cl (R.edPk m) (Q m) → DLSolver C G)
    (msisFork : ∀ m : Member, Forgery Pq (R.mlPk m) (Q m) →
      ∃ (w : No) (c c' : Rq) (z z' : Mo), c ≠ c' ∧
        IsSelfTargetMSISSolution Amap t β z c w ∧ IsSelfTargetMSISSolution Amap t β z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented Amap t) ((β + β) + (β + β)))
    (hrule : HonestVotingRule voteMsg Q (fun m => m ∈ R.committee ∧ m ∉ byz))
    (A : AcceptedHistory Cl Pq R voteMsg (n - f) start)
    (c c' : Cert Cl Pq R voteMsg (n - f)) (hc : c ∈ A.certs) (hc' : c' ∈ A.certs)
    (hh : c.height = c'.height) (hbne : c.block ≠ c'.block) :
    False :=
  consensus_safe_under_floor Cl Pq R.committee byz R.edPk R.mlPk voteMsg Q n f hn hcard
    hbyz hbyzc C G Amap t β dlFork msisFork hfloor hrule c.height c.block c'.block hbne
    c.fin (by rw [hh]; exact c'.fin)

/-! ## §5. `no_long_range` — a non-enrolled committee is REJECTED by the id-commitment. -/

/-- **`no_long_range` — THE ANTI-LONG-RANGE TOOTH.** An attacker who reuses the honest ids and
`ed25519` keys but swaps in its OWN `ml_dsa` key `mlAtt m₀ ≠ mlPk m₀` for a member is REJECTED by the
enrollment gate: `verify_committed (id m₀) (edPk m₀) (mlAtt m₀)` FAILS. Under `HashCR`, passing it
would (by `id_commitment_binds`) force `(edPk, mlAtt) = (edPk, mlPk)`, contradicting the swap. So a
history signed by a non-enrolled committee cannot even be admitted: the ids do NOT commit those keys. -/
theorem no_long_range
    (R : @Roster PKc PKp Member Pre IdT) (henroll : Enrolled R) (hcr : HashCR R.cr)
    (mlAtt : Member → PKp) (m₀ : Member) (hm₀ : m₀ ∈ R.committee)
    (hdiff : R.mlPk m₀ ≠ mlAtt m₀) :
    ¬ verify_committed R.cr R.frame (R.id m₀) (R.edPk m₀) (mlAtt m₀) :=
  attacker_key_not_committed R.cr R.frame R.hframe hcr (R.id m₀) (R.edPk m₀)
    (R.mlPk m₀) (mlAtt m₀) (fun h => hdiff (congrArg Prod.snd h)) (henroll m₀ hm₀)

/-- **`accepting_long_range_breaks_hashcr` — the reduction.** If a light client nonetheless ACCEPTS
the attacker's non-enrolled key (its enrollment gate passes for `(edPk m₀, mlAtt m₀)`), that is a hash
collision: two DISTINCT key pairs `(edPk, mlPk) ≠ (edPk, mlAtt)` both verifying against one id BREAKS
`HashCR` (`distinct_verifying_pairs_break_hashcr`). So a long-range history is rejected — or the hash
floor already fell. -/
theorem accepting_long_range_breaks_hashcr
    (R : @Roster PKc PKp Member Pre IdT) (henroll : Enrolled R)
    (mlAtt : Member → PKp) (m₀ : Member) (hm₀ : m₀ ∈ R.committee)
    (hdiff : R.mlPk m₀ ≠ mlAtt m₀)
    (haccept : verify_committed R.cr R.frame (R.id m₀) (R.edPk m₀) (mlAtt m₀)) :
    ¬ HashCR R.cr :=
  distinct_verifying_pairs_break_hashcr R.cr R.frame R.hframe (R.id m₀)
    (R.edPk m₀) (R.edPk m₀) (R.mlPk m₀) (mlAtt m₀)
    (fun h => hdiff (congrArg Prod.snd h)) (henroll m₀ hm₀) haccept

end Model

/-! ## §6. Teeth — an honest history is ACCEPTED; a forged vote is a FORGERY; a non-committed key is
REJECTED. Both polarities, load-bearing, over a concrete toy committee. -/

section Teeth

/-- The toy vote body: `voteMsg h b = 100 * h + b` (height and block packed into the signed body). -/
@[reducible] def toyVoteMsg : ℕ → ℕ → ℕ := fun h b => 100 * h + b

/-- The toy id-commitment hash `H((), p) = p`, injective on the committed domain (`HashCR`). -/
def toyCR : CommitReveal Unit (List ℕ) (List ℕ) := ⟨fun _ p => p⟩

theorem toyCR_hashcr : HashCR toyCR := fun _ _ _ h => h

/-- The toy length-framed preimage `frame ed ml = [ed, ml]` (fixed-width ed, then ml). Injective. -/
def toyFrame : ℕ → ℕ → List ℕ := fun ed ml => [ed, ml]

theorem toyFrame_inj : Function.Injective2 toyFrame := by
  intro ed ml ed' ml' h
  simp only [toyFrame, List.cons.injEq, and_true] at h
  exact ⟨h.1, h.2⟩

/-- **The toy enrolled roster.** Members `{0,1,2,3}`; member `m`'s keys are `(m, m)` and its id is
`H((), frame m m) = [m, m]` — so enrollment holds by `rfl`. -/
def toyRoster : @Roster ℕ ℕ ℕ (List ℕ) (List ℕ) where
  cr := toyCR
  frame := toyFrame
  hframe := toyFrame_inj
  committee := {0, 1, 2, 3}
  id := fun m => [m, m]
  edPk := fun m => m
  mlPk := fun m => m

/-- One honest finalized certificate: block `b` at height `h`, quorum `{0,1,2}`, `q = 3`. Each member's
hybrid vote `((m + body), (m + body))` verifies (both halves `sig = pk + body`). -/
def toyCert (h b : ℕ) : Cert toyS toyS toyRoster toyVoteMsg 3 where
  height := h
  block := b
  fin :=
    { quorum := {0, 1, 2}
      sub := by decide
      size := by decide
      votes := fun m _ => ⟨(m + toyVoteMsg h b, m + toyVoteMsg h b), rfl, rfl⟩ }

/-- **(a) AN HONEST FINALIZED HISTORY IS ACCEPTED.** A 2-step history — block `5` finalized at height
`0`, block `6` at height `1` — with the enrolled toy roster and consecutive heights from genesis `0`,
is a genuine `AcceptedHistory`: the light client folds it and accepts. -/
def toyHistory : AcceptedHistory toyS toyS toyRoster toyVoteMsg 3 0 where
  enrolled := fun _ _ => rfl
  certs := [toyCert 0 5, toyCert 1 6]
  chained := by
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> rfl

/-- The honest 2-step history is accepted (non-vacuity of the whole fold). -/
theorem tooth_honest_history_accepted :
    Nonempty (AcceptedHistory toyS toyS toyRoster toyVoteMsg 3 0) :=
  ⟨toyHistory⟩

/-- Member `1`'s honest cast-set: exactly block `5` at height `0` (`Q = {voteMsg 0 5}`). -/
@[reducible] def toyQ1 : ℕ → Prop := fun msg => msg = toyVoteMsg 0 5

/-- **(b) A FORGED VOTE EXHIBITS THE FORGERY.** Member `1` cast only block `5` at height `0`, but a
valid HYBRID vote for the CONFLICTING block `7` at height `0` verifies (`((1 + voteMsg 0 7), (1 +
voteMsg 0 7))` under key `(1, 1)`). Since `voteMsg 0 7` was never cast, that accepted vote is a fresh
valid signature on an un-queried body — a `HybridCombiner.Forgery` on member `1`'s hybrid key. This is
the object `accepting_forged_history_breaks_floor` derives a floor break from. -/
theorem tooth_forged_vote_is_forgery :
    Forgery (hybrid toyS toyS) (memberPk toyRoster 1) toyQ1 :=
  ⟨toyVoteMsg 0 7, (1 + toyVoteMsg 0 7, 1 + toyVoteMsg 0 7), by decide, rfl, rfl⟩

/-- **(c) A NON-COMMITTED ATTACKER KEY IS REJECTED.** The attacker keeps member `1`'s honest `ed = 1`
but swaps in its OWN `ml_dsa = 9 ≠ 1`. `no_long_range` REJECTS it: `¬ verify_committed (id 1)(ed 1)(9)`
— the id `[1,1]` does not commit `9`. The self-carried PQ key cannot pass the enrollment gate. -/
theorem tooth_attacker_key_rejected :
    ¬ verify_committed toyRoster.cr toyRoster.frame (toyRoster.id 1) (toyRoster.edPk 1) 9 :=
  no_long_range toyRoster (fun _ _ => rfl) toyCR_hashcr (fun _ => 9) 1 (by decide) (by decide)

-- The honest hybrid vote verifies under the member's committed key…
#guard decide ((hybrid toyS toyS).verify (memberPk toyRoster 1) (toyVoteMsg 0 5)
  (1 + toyVoteMsg 0 5, 1 + toyVoteMsg 0 5))
-- …but the conflicting body `voteMsg 0 7` was NEVER cast (the forgery witness).
#guard decide (¬ toyQ1 (toyVoteMsg 0 7))
-- The honest id commits the honest keys…
#guard toyFrame 1 1 = [1, 1]
-- …but the attacker's own ml_dsa hashes to a DIFFERENT id — the gate rejects it.
#guard toyFrame 1 9 ≠ [1, 1]

end Teeth

/-! ## §7. Axiom hygiene — every light-client soundness keystone is kernel-clean. -/

#assert_all_clean [
  lightclient_sound,
  accepting_forged_history_breaks_floor,
  lightclient_agrees_with_full_node,
  lightclient_no_fork,
  no_long_range,
  accepting_long_range_breaks_hashcr,
  toyCR_hashcr,
  toyFrame_inj,
  tooth_honest_history_accepted,
  tooth_forged_vote_is_forgery,
  tooth_attacker_key_rejected
]

end Dregg2.Crypto.LightClientSoundness
