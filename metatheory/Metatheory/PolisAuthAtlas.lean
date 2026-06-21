/-
# Metatheory.PolisAuthAtlas — the polis society IS the real atlas cells, not stand-in labels.

`PolisAuthLive` derives the delegation rules from a live cap-state — but its cells were concrete
stand-ins (`10`/`20`/`30`). This file closes that toy edge: the labels are the REAL cell identities
read off `dregg-atlas/data/cells.json` (the deployed `demo` image, `cell_count = 4`), and the
cap-state is the REAL ocap graph that image presents. So the polis reasons over the cells the live
verified image actually contains, by their genuine 256-bit ids.

The demo image's anchors and graph (from the atlas JSON):
  * `service` = `ccfc99…899a` (balance 251000, out-degree 2),
  * `user`    = `2a6969…ab90` (balance 54000, in-degree 2),
  * `treasury`= `87a55e…56cb`.
  * the ocap graph: `service → user` on slots 0 and 1, **both `rights: "None"`, not faceted**.

Because every real edge carries `None`, the live image confers NO inter-agent delegation — a TRUE,
non-vacuous fact about the deployed cells, not a toy: `atlas_confers_no_inter_agent_reach`. The
mechanism is then shown to fire on the SAME real cell ids the moment an edge carries `grant`
(`atlas_grant_unlocks_user`), and the rule-base provably gains exactly that rule
(`atlas_grant_emits_rule`). The grantor/grantee are distinct by their real hashes
(`atlas_grantor_grantee_distinct`, via `atomOf_injective`).

No `sorry`, no load-bearing `True`. The cap-state is transcribed from the atlas JSON by hand (Lean
cannot parse JSON in-kernel); the ids and edge structure are the file's, verbatim.
-/
import Metatheory.PolisAuthLive

namespace Metatheory.PolisAuthAtlas

open Dregg2.Authority Metatheory.PolisDatalog Metatheory.PolisAuthLive
open Metatheory.PolisAuthReachDatalog (atomOf atomOf_injective)

/-! ## §1. The real cell identities (256-bit ids, as `Nat`, from the atlas JSON anchors). -/

/-- `service` = `ccfc9955bdc00352d51a0f096caeb339dc534338a076681e048ef4da6ffa899a` (out-degree 2). -/
def service : Label :=
  92718124850080034428147421702402323162550420838473360637469403401011922110874
/-- `user` = `2a6969a63df11a7d51aac1f9fcb50dd3c3cbdb78e0e3a945eaaadecb486bab90` (in-degree 2). -/
def user : Label :=
  19183387747539712430879675800664406295558027876840052389049790309845460298640
/-- `treasury` = `87a55eb57cfd50fb071c495c094cd6f2759886ba1f6f29ef9231fb2d8b2156cb`. -/
def treasury : Label :=
  61354417981499273372963909963893020996478881748082652526637561649373949023947

/-- The atlas scan domain — the three anchor cells of the `demo` image. -/
def atlasCells : List Label := [service, user, treasury]

/-- The authority delegated around (the demo goal). -/
def target : Auth := Auth.read

/-- The real cell ids are pairwise distinct (their 256-bit hashes differ) — so any cross-cell claim
crosses a genuine boundary. -/
theorem atlas_cells_distinct :
    service ≠ user ∧ user ≠ treasury ∧ service ≠ treasury := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §2. The REAL ocap graph as a cap-state — verbatim from the atlas edges. -/

/-- **The live ocap graph, as a `Caps`.** The atlas shows two edges `service → user` (slots 0, 1),
both `rights: "None"`. `None` rights confer no authority, so each edge is `.endpoint user []`. `user`
and `treasury` hold no outgoing caps (in-degree only / isolated in this image). This is the cap-state
the deployed `demo` image actually presents. -/
def atlasCaps : Caps := fun s =>
  if s = service then [.endpoint user [], .endpoint user []]   -- slot 0, slot 1: rights None
  else []                                                       -- user, treasury: no outgoing caps

/-- **The deployed image emits NO inter-agent delegation rule.** Every real edge carries `None`, so
`delegRulesOf` (which only emits for a grant/control cap) folds to the empty rule-base over the real
cells. A true, non-vacuous fact about the live `demo` image. -/
theorem atlas_has_no_delegation_rules : delegRulesOf atlasCells atlasCaps = [] := by
  unfold atlasCells atlasCaps; decide

/-- **`atlas_confers_no_inter_agent_reach`.** In the deployed `demo` image, `user` cannot derive
`read` by delegation — the real graph's edges are all `rights: None`, so no rule is emitted and no
cross-cell reach exists. The polis reading the REAL cells sees a delegation-free society. -/
theorem atlas_confers_no_inter_agent_reach :
    ¬ ReachesLive target user atlasCells atlasCaps := by
  unfold ReachesLive target atlasCells atlasCaps service user treasury; decide

/-! ## §3. The SAME real cells, one edge upgraded to carry `grant` — the mechanism fires. -/

/-- **A variant of the real image where `service`'s slot-0 edge carries `[read, grant]`.** Same real
cell ids, same graph shape — only the slot-0 rights change from `None` to `[read, grant]`. Now the
edge is a genuine delegation cap, so `delegRulesOf` emits `atomOf user read ← [atomOf service grant]`
read off the live cell `service`, and `service` thereby holds a `grant` reach-fact. -/
def atlasCapsGranting : Caps := fun s =>
  if s = service then [.endpoint user [Auth.read, Auth.grant], .endpoint user []]
  else []

/-- **`atlas_grant_unlocks_user`.** With `service`'s slot-0 edge carrying `grant`, the rule derived
from the real cell fires on `service`'s pooled grant-fact, and grantee `user` reaches `read` — over
the genuine atlas cell ids. -/
theorem atlas_grant_unlocks_user :
    ReachesLive target user atlasCells atlasCapsGranting := by
  unfold ReachesLive target atlasCells atlasCapsGranting service user treasury; decide

/-- **`atlas_grant_emits_rule`.** The rule-base read off the real cells literally GAINS exactly the
delegation rule `atomOf user read ← [atomOf service grant]` when the edge carries `grant`, and it is
ABSENT in the actual (rights-None) image. The rule-base IS what the live cells present. -/
theorem atlas_grant_emits_rule :
    (⟨atomOf user target, [atomOf service Auth.grant]⟩ : Rule)
        ∈ delegRulesOf atlasCells atlasCapsGranting
      ∧ (⟨atomOf user target, [atomOf service Auth.grant]⟩ : Rule)
        ∉ delegRulesOf atlasCells atlasCaps := by
  unfold atlasCells atlasCapsGranting atlasCaps target service user treasury atomOf
  decide

/-- `service` dominates `user` over the REAL cell ids: `user` reaches `read` exactly when `service`'s
edge carries `grant`, and not in the actual delegation-free image. Same roster, same goal — only the
real cell's held rights toggle the grantee's reachability. -/
theorem atlas_service_dominates_user :
    ReachesLive target user atlasCells atlasCapsGranting
      ∧ ¬ ReachesLive target user atlasCells atlasCaps :=
  ⟨atlas_grant_unlocks_user, atlas_confers_no_inter_agent_reach⟩

/-! ## §4. Faithfulness — the delegation crosses a real cell boundary. -/

/-- The grantor `service` and grantee `user` are DISTINCT real cells (their 256-bit hashes differ),
so the unlocked reach-fact is genuinely cross-cell — not `user` deriving from itself under an alias
(`atomOf_injective` separates their atoms). -/
theorem atlas_grantor_grantee_distinct :
    atomOf service Auth.grant ≠ atomOf user target := by
  intro h
  exact absurd (atomOf_injective h).1 (by unfold service user; decide)

/-! ## §5. Runnable — watch the real atlas cells decide on the engine. -/

-- The actual deployed image: no delegation rules (every edge is rights None).
#guard delegRulesOf atlasCells atlasCaps = []
-- The actual image confers no cross-cell reach to `user`.
#guard decide (! decide (ReachesLive target user atlasCells atlasCaps))
-- The grant variant of the same real cells: `user` reaches `read`.
#guard decide (ReachesLive target user atlasCells atlasCapsGranting)

/-! ## §6. Axiom hygiene. -/

#print axioms atlas_cells_distinct
#print axioms atlas_confers_no_inter_agent_reach
#print axioms atlas_grant_unlocks_user
#print axioms atlas_grant_emits_rule
#print axioms atlas_grantor_grantee_distinct

/-!
The polis, grounded in the real atlas cells:

  1. `service`/`user`/`treasury` — the genuine 256-bit cell ids of the deployed `demo` image,
     read off `dregg-atlas/data/cells.json`.
  2. `atlasCaps` — the REAL ocap graph (`service → user` ×2, rights None) as a `Caps`.
  3. `atlas_confers_no_inter_agent_reach` — a TRUE fact about the live image: its rights-None edges
     confer no delegation, so the polis sees a delegation-free society.
  4. `atlas_grant_unlocks_user` + `atlas_grant_emits_rule` — upgrade ONE real edge to carry `grant`
     and the rule-base (read off the cells) gains exactly the delegation rule, unlocking the grantee
     — over the real cell ids, `decide`-checked.
-/

end Metatheory.PolisAuthAtlas
