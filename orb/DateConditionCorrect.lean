import Reactor.Stage.DateCondition

/-!
# Reactor.Stage.DateConditionCorrect — the date-conditional stage firing, proven GENERAL

`Reactor.Stage.DateCondition.dateCondStage` decides the RFC 9110 §13 date preconditions
(`If-Modified-Since` / `If-Unmodified-Since`) on the built `200`. The `dcRewrite` DECISION
is proven general (`dcRewrite_ims_304`, `dcRewrite_ius_412`, `dcRewrite_passes`), and the
OFF arm is lifted to the stage (`dateCond_offHeaders_id`) — but the stage's actual FIRING
outcome (its `onResponse` running the decision on the built response) was pinned only by
the concrete `witness_rewrite`. This file lifts the three verdicts through the stage's
response phase into GENERAL `∀` theorems.
-/

namespace Reactor.Stage.DateCondition

open Reactor.Pipeline
open Reactor (Response)
open Reactor.Stage.ConditionalRequest (notModifiedOf preconditionFailedOf)

/-- **The firing law.** On a request carrying a date conditional the stage's response
phase runs the proven `dcRewrite` decision on the built response — the firing counterpart
of `dateCond_offHeaders_id` (which covered only the no-conditional arm). -/
theorem dateCond_onResponse_fires (c : Ctx) (b : ResponseBuilder)
    (h : hasDateCond c.req = true) :
    dateCondStage.onResponse c b = b.mapResp (dcRewrite c.req) := by
  show (if hasDateCond c.req then b.mapResp (dcRewrite c.req) else b) = _
  rw [if_pos h]

/-- **J11 (§13.1.4 MUST), general.** A firing request with a failing
`If-Unmodified-Since` on a dated `200` makes the stage emit the `412 Precondition Failed`
— for EVERY context and builder. Lifts `dcRewrite_ius_412` through the response phase. -/
theorem dateCond_onResponse_ius_412 (c : Ctx) (b : ResponseBuilder) (lm : Nat)
    (hfire : hasDateCond c.req = true)
    (h200 : (b.build.status == 200) = true)
    (hd : respLastModScalar b.build = some lm)
    (hf : iusFails c.req lm = true) :
    (dateCondStage.onResponse c b).build = preconditionFailedOf b.build := by
  rw [dateCond_onResponse_fires c b hfire, build_mapResp,
      dcRewrite_ius_412 c.req b.build lm h200 hd hf]

/-- **J09 (§13.1.3 MUST), general.** A firing request with an at-or-after
`If-Modified-Since` (IUS not failing) on a dated `200` makes the stage emit the `304 Not
Modified` — for EVERY context and builder. Lifts `dcRewrite_ims_304`. -/
theorem dateCond_onResponse_ims_304 (c : Ctx) (b : ResponseBuilder) (lm : Nat)
    (hfire : hasDateCond c.req = true)
    (h200 : (b.build.status == 200) = true)
    (hd : respLastModScalar b.build = some lm)
    (hi : iusFails c.req lm = false) (hm : imsUnmodified c.req lm = true) :
    (dateCondStage.onResponse c b).build = notModifiedOf b.build := by
  rw [dateCond_onResponse_fires c b hfire, build_mapResp,
      dcRewrite_ims_304 c.req b.build lm h200 hd hi hm]

/-- **The pass arm, general.** A firing request whose date preconditions are all satisfied
leaves the dated `200` byte-identical — for EVERY context and builder. Lifts
`dcRewrite_passes`. -/
theorem dateCond_onResponse_passes (c : Ctx) (b : ResponseBuilder) (lm : Nat)
    (hfire : hasDateCond c.req = true)
    (h200 : (b.build.status == 200) = true)
    (hd : respLastModScalar b.build = some lm)
    (hi : iusFails c.req lm = false) (hm : imsUnmodified c.req lm = false) :
    (dateCondStage.onResponse c b).build = b.build := by
  rw [dateCond_onResponse_fires c b hfire, build_mapResp,
      dcRewrite_passes c.req b.build lm h200 hd hi hm]

end Reactor.Stage.DateCondition

#print axioms Reactor.Stage.DateCondition.dateCond_onResponse_fires
#print axioms Reactor.Stage.DateCondition.dateCond_onResponse_ius_412
#print axioms Reactor.Stage.DateCondition.dateCond_onResponse_ims_304
#print axioms Reactor.Stage.DateCondition.dateCond_onResponse_passes
