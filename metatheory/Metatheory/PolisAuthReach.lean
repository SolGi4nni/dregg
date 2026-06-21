/-
# Metatheory.PolisAuthReach — goal-relative viability as REACHABILITY (ember's correction, done).

`PolisAuthViability.Viable` was the DIRECT case: `b` holds a cap conferring `target`. ember's
sharpening: viability is **goal-relative reachability** — `b` is viable iff it can still *reach/derive*
the authority it needs, using whatever caps suffice. So:
  * revoking a cap `b` does not need (it reaches `target` another way) is NOT foreclosure;
  * `b` can be viable WITHOUT directly holding `target`, by DERIVING it (holding `grant`/`control`);
  * foreclosure is only cutting ALL of `b`'s paths to `target`.

Grounded on the real `Dregg2.Authority.Auth`: `grant` is the delegation authority, `control` the
node-cap authority — holding either lets you derive any authority. `Reaches` is the reachability over
that derivation; it generalizes the static `Viable` (which is `Derives = refl` only).

No `sorry`; the load-bearing facts are `decide`-checked on a concrete two-path model.
-/
import Metatheory.SafetyGame
import Metatheory.PolisAuthGame
import Dregg2.Authority.Positional

namespace Metatheory.PolisAuthReach

open Dregg2.Authority Metatheory.SafetyGame Metatheory.PolisGovernorTheory
open Metatheory.PolisAuthGame

/-! ## §1. The derivation relation and reachability. -/

/-- All authorities agent `b` directly holds (conferred by its caps). -/
def heldAuths (caps : Caps) (b : Label) : List Auth := (caps b).flatMap capAuthConferred

/-- **The grant/derivation relation (Bool).** Holding `a` lets you derive `target` iff `a = target`
(you already have it), OR `a = grant` (the delegation authority — you can grant yourself any auth),
OR `a = control` (the node-cap authority — control over an object confers any auth). Grounded in the
real `Auth` constructors. -/
def derivesB (a target : Auth) : Bool :=
  decide (a = target) || decide (a = Auth.grant) || decide (a = Auth.control)

/-- **Goal-relative viability = REACHABILITY.** `b` can reach/exercise `target` iff it holds some
authority that *derives* `target`. Not "b holds all its caps", not even "b holds `target`" — only a
path to `target` matters. (`Derives = refl` recovers the static `Viable`; `grant`/`control` add the
derivation paths.) -/
def reachesB (target : Auth) (b : Label) (caps : Caps) : Bool :=
  (heldAuths caps b).any (fun a => derivesB a target)

def Reaches (target : Auth) (b : Label) (caps : Caps) : Prop := reachesB target b caps = true

instance (target : Auth) (b : Label) (caps : Caps) : Decidable (Reaches target b caps) :=
  inferInstanceAs (Decidable (_ = true))

/-- Every agent in the roster can still reach its goal. -/
def AllReach (target : Auth) (agents : List Label) (caps : Caps) : Prop :=
  ∀ b ∈ agents, Reaches target b caps

instance (target : Auth) (agents : List Label) (caps : Caps) :
    Decidable (AllReach target agents caps) :=
  inferInstanceAs (Decidable (∀ b ∈ agents, Reaches target b caps))

/-! ## §2. A two-path model: B reaches `read` directly AND via `grant`. -/

def A : Label := 0
def B : Label := 1
def tgt : Auth := Auth.read

/-- B's DIRECT path to `read`: an endpoint to B carrying `[read]`. -/
def capRead : Cap := .endpoint B [Auth.read]
/-- B's DERIVATION path to `read`: an endpoint to B carrying `[grant]` (delegation power). -/
def capGrant : Cap := .endpoint B [Auth.grant]

/-- B holds BOTH paths; A holds its own read-cap. -/
def capsBoth : Caps := fun s =>
  if s = A then [.endpoint A [Auth.read]]
  else if s = B then [capRead, capGrant] else []

/-- A revokes B's DIRECT read-cap; B keeps `capGrant` (it can still derive `read`). -/
def capsDropRead : Caps := fun s =>
  if s = A then [.endpoint A [Auth.read]]
  else if s = B then [capGrant] else []

/-- A revokes BOTH of B's caps; every path to `read` is cut. -/
def capsDropAll : Caps := fun s =>
  if s = A then [.endpoint A [Auth.read]] else []

def agents0 : List Label := [A, B]

/-! ## §3. The corrected viability: redundant revocation is fine; only path-cutting forecloses. -/

/-- **B can reach `read` WITHOUT directly holding it** — via `grant` (derivation). The static notion
missed this; reachability captures it. -/
theorem reaches_via_derivation : Reaches tgt B capsDropRead := by decide

/-- **`redundant_revocation_keeps_reach` (ember's correction).** Revoking B's direct `read` cap does
NOT foreclose B: it still reaches `read` through `grant`. Viability keeps GOALS reachable, not
permissions hoarded. -/
theorem redundant_revocation_keeps_reach : Reaches tgt B capsDropRead := by decide

/-- **`foreclosure_cuts_all_paths`.** Only revoking EVERY path to `read` forecloses B. -/
theorem foreclosure_cuts_all_paths : ¬ Reaches tgt B capsDropAll := by decide

/-- Reachability is strictly more permissive than the static "holds a conferring cap": B reaches
`read` at `capsDropRead` while holding NO cap that confers `read` directly. -/
theorem reaches_strictly_generalizes :
    Reaches tgt B capsDropRead ∧ ¬ (∃ c ∈ capsDropRead B, tgt ∈ capAuthConferred c) := by decide

/-! ## §4. The reach-governor: admit redundant revocation, refuse path-cutting. -/

open Classical in
/-- The governor over the REACHABILITY floor: admit the proposed cap-state iff everyone still reaches
their goal, else shield. (This is `genGovStep` over `AllReach`.) -/
noncomputable def reachGov (target : Auth) (agents : List Label) (caps caps' : Caps) : Caps :=
  if AllReach target agents caps' then caps' else caps

/-- **The polis ADMITS the redundant revocation** — everyone still reaches their goal, so dropping
the unneeded direct cap passes unchanged (least-privilege, the right way). -/
theorem reachGov_admits_redundant :
    reachGov tgt agents0 capsBoth capsDropRead = capsDropRead := by
  unfold reachGov
  rw [if_pos (by decide : AllReach tgt agents0 capsDropRead)]

/-- **The polis REFUSES the path-cutting revocation** — it would foreclose B (B can no longer reach
`read`), so it is shielded. -/
theorem reachGov_refuses_foreclosure :
    reachGov tgt agents0 capsBoth capsDropAll = capsBoth := by
  unfold reachGov
  rw [if_neg (by decide : ¬ AllReach tgt agents0 capsDropAll)]

-- Watch it decide (least-privilege vs foreclosure, on the real authorities):
#eval reachesB tgt B capsBoth       -- true  (B reaches read: directly AND via grant)
#eval reachesB tgt B capsDropRead   -- true  (direct cap gone — still reaches via grant: ADMITTED)
#eval reachesB tgt B capsDropAll    -- false (all paths cut: FORECLOSED, refused)

end Metatheory.PolisAuthReach
