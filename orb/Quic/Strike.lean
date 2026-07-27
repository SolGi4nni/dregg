/-!
# 0-RTT anti-replay: the concrete single-owner strike register (RFC 9001 §9.2)

`Quic.Replay` proves the *distributed* anti-replay property — across a
shared-nothing sharded server, under a demonic replay network, each ticket's
early data is accepted at most once (`accepted_at_most_once`). That model
abstracts the register to a monotone mark set.

This module is the *concrete* register a single owner shard runs: the strike
register that decides, for one ClientHello hash, whether a 0-RTT flight is a
first arrival (accept) or a replay (reject), with a TTL window (RFC 9001 §9.2 /
RFC 8446 Appendix E.5). It mirrors the deployed `check_and_insert`: an entry
maps a hash to its insertion time; a hash seen again inside the TTL is a
**replay** and is rejected without changing the register; a hash never seen, or
whose entry has aged out of the TTL, is **accepted** and (re)recorded.

Headline theorems:

* `fresh_accepted` — a hash never seen is accepted and recorded.
* `replay_rejected` — a hash seen inside the TTL is rejected, register
  unchanged.
* `expired_reaccepted` — a hash whose entry aged past the TTL is accepted
  again and its time refreshed.
* `accept_then_replay_rejected` — the end-to-end guarantee: a fresh flight is
  accepted, and an immediate replay of the *same* hash is rejected. Non-vacuous
  (both outcomes are exhibited on concrete data).
* `at_most_one_accept_in_window` — starting empty, any two checks of one hash
  within a TTL window accept at most once.

Early-data method safety (RFC 8470 / RFC 9110): only idempotent methods may be
processed in 0-RTT, so even an accepted-but-replayed idempotent request is
harmless. `methodSafeForEarlyData` + its theorems pin the safe set.
-/

namespace Quic
namespace Strike

/-- A ClientHello hash (the deployed register keys on a 32-byte digest). -/
abbrev Hash := List UInt8

/-- Wall-clock time, in whatever unit the caller supplies (monotone). -/
abbrev Time := Nat

/-- The strike register: hash → insertion time, plus the TTL window. Entries
are held newest-first (a re-insert prepends), so a lookup sees the most recent
insertion of a hash. -/
structure Reg where
  entries : List (Hash × Time)
  ttl : Nat
deriving Repr

/-- A fresh register with the given TTL. -/
def Reg.new (ttl : Nat) : Reg := ⟨[], ttl⟩

/-- The most recent insertion time recorded for `h`, if any. -/
def Reg.lookup (r : Reg) (h : Hash) : Option Time :=
  (r.entries.find? (fun e => e.1 == h)).map (·.2)

/-- Record `h` at time `now` (prepend, newest-first). -/
def Reg.insert (r : Reg) (h : Hash) (now : Time) : Reg :=
  { r with entries := (h, now) :: r.entries }

/-- Is an entry inserted at `t` still live at `now` under `ttl`? (RFC 9001
§9.2: strictly inside the window.) -/
def live (ttl now t : Time) : Bool := decide (now - t < ttl)

/-- **check-and-insert** (the deployed decision). Returns `(isReplay, r')`:
`isReplay = true` means a live prior entry exists — reject, register unchanged;
`isReplay = false` means accept — the hash is (re)recorded at `now`. -/
def Reg.checkAndInsert (r : Reg) (h : Hash) (now : Time) : Bool × Reg :=
  match r.lookup h with
  | some t => if live r.ttl now t then (true, r) else (false, r.insert h now)
  | none => (false, r.insert h now)

/-! ## Register lemmas -/

theorem lookup_insert_self (r : Reg) (h : Hash) (now : Time) :
    (r.insert h now).lookup h = some now := by
  simp [Reg.insert, Reg.lookup, List.find?_cons]

/-! ## The decision theorems -/

/-- **Fresh accepted.** A hash never seen is accepted (`isReplay = false`) and
recorded at `now`. -/
theorem fresh_accepted (r : Reg) (h : Hash) (now : Time)
    (hnew : r.lookup h = none) :
    (r.checkAndInsert h now).1 = false ∧
      (r.checkAndInsert h now).2.lookup h = some now := by
  unfold Reg.checkAndInsert
  rw [hnew]
  exact ⟨rfl, lookup_insert_self r h now⟩

/-- **Replay rejected.** A hash with a live prior entry is rejected
(`isReplay = true`) and the register is unchanged. -/
theorem replay_rejected (r : Reg) (h : Hash) (t now : Time)
    (hseen : r.lookup h = some t) (hlive : now - t < r.ttl) :
    r.checkAndInsert h now = (true, r) := by
  unfold Reg.checkAndInsert
  rw [hseen]
  simp only [live]
  rw [if_pos (by simp [hlive])]

/-- **Expired re-accepted.** A hash whose only entry has aged past the TTL is
accepted again and its time refreshed to `now`. -/
theorem expired_reaccepted (r : Reg) (h : Hash) (t now : Time)
    (hseen : r.lookup h = some t) (hexp : ¬ now - t < r.ttl) :
    (r.checkAndInsert h now).1 = false ∧
      (r.checkAndInsert h now).2.lookup h = some now := by
  unfold Reg.checkAndInsert
  rw [hseen]
  simp only [live]
  rw [if_neg (by simp [hexp])]
  exact ⟨rfl, lookup_insert_self r h now⟩

/-- **End-to-end: accept then reject.** From a register with no live entry for
`h`, a first flight at `now₁` is accepted, and an immediate replay at `now₂ ≥
now₁` still inside the TTL is rejected. This is the single-register form of
"early data accepted at most once": the second identical flight cannot also be
accepted. -/
theorem accept_then_replay_rejected (r : Reg) (h : Hash) (now₁ now₂ : Time)
    (hnew : r.lookup h = none) (horder : now₁ ≤ now₂)
    (hwin : now₂ - now₁ < r.ttl) :
    (r.checkAndInsert h now₁).1 = false ∧
      ((r.checkAndInsert h now₁).2.checkAndInsert h now₂) =
        (true, (r.checkAndInsert h now₁).2) := by
  have hfresh := fresh_accepted r h now₁ hnew
  refine ⟨hfresh.1, ?_⟩
  have hseen : (r.checkAndInsert h now₁).2.lookup h = some now₁ := hfresh.2
  have httl : (r.checkAndInsert h now₁).2.ttl = r.ttl := by
    unfold Reg.checkAndInsert; rw [hnew]; rfl
  exact replay_rejected (r.checkAndInsert h now₁).2 h now₁ now₂ hseen
    (by rw [httl]; exact hwin)

/-- **At most one accept in a window.** Starting from the empty register,
checking `h` at `now₁` then at `now₂` (with `now₁ ≤ now₂` inside the TTL)
accepts the first and rejects the second — never two accepts. -/
theorem at_most_one_accept_in_window (ttl : Nat) (h : Hash) (now₁ now₂ : Time)
    (horder : now₁ ≤ now₂) (hwin : now₂ - now₁ < ttl) :
    ((Reg.new ttl).checkAndInsert h now₁).1 = false ∧
      (((Reg.new ttl).checkAndInsert h now₁).2.checkAndInsert h now₂).1 = true := by
  have hnew : (Reg.new ttl).lookup h = none := by
    unfold Reg.new Reg.lookup; simp
  obtain ⟨h1, h2⟩ := accept_then_replay_rejected (Reg.new ttl) h now₁ now₂ hnew horder
    (by unfold Reg.new; exact hwin)
  exact ⟨h1, by rw [h2]⟩

/-! ## Early-data method safety (RFC 8470 / RFC 9110 §9.2.1) -/

/-- Only idempotent methods are safe to process in 0-RTT early data: a replayed
GET/HEAD/OPTIONS/TRACE cannot cause an unintended state change. -/
def methodSafeForEarlyData (m : String) : Bool :=
  m == "GET" || m == "HEAD" || m == "OPTIONS" || m == "TRACE"

theorem idempotent_safe :
    methodSafeForEarlyData "GET" = true ∧
    methodSafeForEarlyData "HEAD" = true ∧
    methodSafeForEarlyData "OPTIONS" = true ∧
    methodSafeForEarlyData "TRACE" = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem nonidempotent_unsafe :
    methodSafeForEarlyData "POST" = false ∧
    methodSafeForEarlyData "PUT" = false ∧
    methodSafeForEarlyData "PATCH" = false ∧
    methodSafeForEarlyData "DELETE" = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Non-vacuity: concrete accept-then-reject on real bytes -/

-- A fresh flight for hash `[1,2,3]` is accepted; the immediate replay is
-- rejected. (ttl = 60, both checks at t = 0.)
#guard ((Reg.new 60).checkAndInsert [1, 2, 3] 0).1 == false
#guard (((Reg.new 60).checkAndInsert [1, 2, 3] 0).2.checkAndInsert [1, 2, 3] 0).1 == true
-- A different hash is independently accepted.
#guard (((Reg.new 60).checkAndInsert [1, 2, 3] 0).2.checkAndInsert [9, 9] 0).1 == false
-- After the TTL elapses, the same hash is accepted again.
#guard (((Reg.new 10).checkAndInsert [1, 2, 3] 0).2.checkAndInsert [1, 2, 3] 20).1 == false

#print axioms fresh_accepted
#print axioms replay_rejected
#print axioms accept_then_replay_rejected
#print axioms at_most_one_accept_in_window

end Strike
end Quic
