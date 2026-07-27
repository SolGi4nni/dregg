/-
Route.HostRoute — host-based virtual routing (LEDGER row rt.host).

A request's authoritative host (Host header / SNI authority) selects a
virtual-host route table. Selection is by a THREE-CLASS precedence over the
host pattern, independent of table order:

  * `exact`   — the request host labels equal the pattern (rank 2, highest);
  * `wild`    — the leading-label wildcard `*.rest`, one arbitrary leading
                label followed by `rest` (rank 1);
  * `default` — the fallback authority, matches unconditionally (rank 0).

So `api.example.com` selects an exact `api.example.com` block over a wildcard
`*.example.com` block over the default block, even if the wildcard/default
blocks appear earlier in the table. Within one class the earliest block in
table order wins (first-match tie-break, no ambiguity).

This is the authority-selection layer only: each virtual host carries an
abstract route table `H` (the per-host path router, e.g. the sibling
`Route.Match` / `RouteAdvanced` matcher, is `H`'s job). Selecting a virtual
host hands the request to THAT host's table and no other — the isolation
property `host_route_no_leak` below.

Boundaries (named, uninterpreted):
  * HOST EXTRACTION — the request host arrives as an already-split, already
    lower-cased, port-stripped label list. The Host-header ABNF parse, the SNI
    extension parse, and case-folding happen upstream; they are not modeled.
  * Any cryptographic authority binding (the TLS handshake that authenticates
    the SNI-selected host) is an opaque oracle discharged elsewhere; here the
    host label list is taken as given and only the pure selection DECISION over
    it is proven.

Theorems:
  * `host_route_dispatch` — the selected block's host matches the request, and
    it is a HIGHEST-precedence match: exact > wildcard > default. No matching
    block outranks the chosen one.
  * `host_route_no_leak`  — a request for host A is never served by a block
    bound to a different exact host B (A's request never hits B's table).
  * `host_route_default`  — with no exact and no wildcard match, a request falls
    through to the default block (and only the default block).

Concrete `decide` witnesses (`H := Nat`) show each class is real and distinct.
Core-only Lean (no Mathlib), no crypto engine, no external axioms.
-/

namespace Route.HostRoute

/-! ## Host patterns and their precedence -/

/-- A host pattern over already-split host labels. `exact` pins the full label
list; `wild rest` is the leading-label wildcard `*.rest`; `default` is the
order-independent fallback authority. -/
inductive Host where
  | exact (labels : List String)
  | wild (rest : List String)
  | default
deriving Repr

/-- Precedence rank: exact (2) > wild (1) > default (0). -/
def hostRank : Host → Nat
  | .exact _ => 2
  | .wild _  => 1
  | .default => 0

/-- Match a host pattern against a request's host label list. -/
def hostMatches (req : List String) : Host → Bool
  | .exact ls => decide (req = ls)
  | .wild rest =>
    match req with
    | _ :: tl => decide (tl = rest)
    | []      => false
  | .default => true

/-- A virtual host: a host pattern and its (abstract) per-host route table. -/
structure VHost (H : Type) where
  host : Host
  routes : H

variable {H : Type}

/-- Does this virtual host's authority match the request? -/
def matchesHost (req : List String) (v : VHost H) : Bool :=
  hostMatches req v.host

/-! ### Per-class match predicates (at most one class fires per block) -/

/-- The block is an exact-host block whose labels equal the request. -/
def isExactMatch (req : List String) (v : VHost H) : Bool :=
  match v.host with | .exact ls => decide (req = ls) | _ => false

/-- The block is a wildcard block whose `*.rest` matches the request. -/
def isWildMatch (req : List String) (v : VHost H) : Bool :=
  match v.host with | .wild rest => hostMatches req (.wild rest) | _ => false

/-- The block is the default (fallback) block. -/
def isDefault (v : VHost H) : Bool :=
  match v.host with | .default => true | _ => false

/-! ## Selection: exact class first, then wildcard, then default;
first-match within a class. -/

/-- **Host selection.** Try the highest precedence class first; within a class
take the first (least-index) block. Order-independent across classes. -/
def selectHost (vs : List (VHost H)) (req : List String) : Option (VHost H) :=
  match vs.find? (isExactMatch req) with
  | some v => some v
  | none =>
    match vs.find? (isWildMatch req) with
    | some v => some v
    | none => vs.find? isDefault

/-! ## `List.find?` first-match toolkit (self-contained, core only) -/

theorem find?_true {α} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : p a = true := by
  induction l with
  | nil => simp [List.find?] at h
  | cons b rest ih =>
    cases hb : p b with
    | true => rw [List.find?, hb] at h; cases h; exact hb
    | false => rw [List.find?, hb] at h; exact ih h

theorem find?_mem {α} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : a ∈ l := by
  induction l with
  | nil => simp [List.find?] at h
  | cons b rest ih =>
    cases hb : p b with
    | true => rw [List.find?, hb] at h; cases h; exact List.mem_cons_self
    | false => rw [List.find?, hb] at h; exact List.mem_cons_of_mem _ (ih h)

theorem find?_none_false {α} {p : α → Bool} {l : List α}
    (h : l.find? p = none) : ∀ a ∈ l, p a = false := by
  induction l with
  | nil => intro a ha; cases ha
  | cons b rest ih =>
    intro a ha
    cases hb : p b with
    | true => rw [List.find?, hb] at h; cases h
    | false =>
      rw [List.find?, hb] at h
      rcases List.mem_cons.mp ha with h' | h'
      · subst h'; exact hb
      · exact ih h a h'

theorem find?_isSome_of_mem {α} {p : α → Bool} {a : α} {l : List α}
    (hmem : a ∈ l) (hp : p a = true) : (l.find? p).isSome := by
  induction l with
  | nil => cases hmem
  | cons b rest ih =>
    rcases List.mem_cons.mp hmem with h | h
    · subst h; simp [List.find?, hp]
    · cases hb : p b with
      | true => simp [List.find?, hb]
      | false => simp only [List.find?, hb]; exact ih h

/-! ## Class characterization -/

theorem isExactMatch_exact {req : List String} {v : VHost H}
    (h : isExactMatch req v = true) : ∃ ls, v.host = Host.exact ls := by
  unfold isExactMatch at h
  cases hp : v.host with
  | exact ls => exact ⟨ls, rfl⟩
  | wild r => rw [hp] at h; simp at h
  | default => rw [hp] at h; simp at h

theorem isWildMatch_wild {req : List String} {v : VHost H}
    (h : isWildMatch req v = true) : ∃ rest, v.host = Host.wild rest := by
  unfold isWildMatch at h
  cases hp : v.host with
  | exact ls => rw [hp] at h; simp at h
  | wild r => exact ⟨r, rfl⟩
  | default => rw [hp] at h; simp at h

theorem isDefault_default {v : VHost H}
    (h : isDefault v = true) : v.host = Host.default := by
  unfold isDefault at h
  cases hp : v.host with
  | exact ls => rw [hp] at h; simp at h
  | wild r => rw [hp] at h; simp at h
  | default => rfl

/-- On an exact block, `matchesHost` and `isExactMatch` coincide. -/
theorem isExactMatch_eq {req : List String} {v : VHost H} {ls : List String}
    (hp : v.host = Host.exact ls) : isExactMatch req v = matchesHost req v := by
  simp only [isExactMatch, matchesHost, hostMatches, hp]

/-- On a wildcard block, `matchesHost` and `isWildMatch` coincide. -/
theorem isWildMatch_eq {req : List String} {v : VHost H} {rest : List String}
    (hp : v.host = Host.wild rest) : isWildMatch req v = matchesHost req v := by
  simp only [isWildMatch, matchesHost, hp]

/-- On a default block, `matchesHost` is unconditionally true. -/
theorem matchesHost_default {req : List String} {v : VHost H}
    (hp : v.host = Host.default) : matchesHost req v = true := by
  simp only [matchesHost, hp, hostMatches]

/-! ## Soundness and membership -/

/-- **Soundness.** The selected block's host matches the request. -/
theorem selectHost_sound {vs : List (VHost H)} {req : List String} {v : VHost H}
    (h : selectHost vs req = some v) : matchesHost req v = true := by
  unfold selectHost at h
  cases he : vs.find? (isExactMatch req) with
  | some ve =>
    rw [he] at h; cases h
    have hx := find?_true he
    obtain ⟨ls, hp⟩ := isExactMatch_exact hx
    rw [← isExactMatch_eq hp]; exact hx
  | none =>
    rw [he] at h
    cases hw : vs.find? (isWildMatch req) with
    | some vw =>
      rw [hw] at h; cases h
      have hx := find?_true hw
      obtain ⟨rest, hp⟩ := isWildMatch_wild hx
      rw [← isWildMatch_eq hp]; exact hx
    | none =>
      rw [hw] at h
      have hx := find?_true h
      exact matchesHost_default (isDefault_default hx)

/-- **Membership.** The selected block is one of the declared virtual hosts. -/
theorem selectHost_mem {vs : List (VHost H)} {req : List String} {v : VHost H}
    (h : selectHost vs req = some v) : v ∈ vs := by
  unfold selectHost at h
  cases he : vs.find? (isExactMatch req) with
  | some ve => rw [he] at h; cases h; exact find?_mem he
  | none =>
    rw [he] at h
    cases hw : vs.find? (isWildMatch req) with
    | some vw => rw [hw] at h; cases h; exact find?_mem hw
    | none => rw [hw] at h; exact find?_mem h

/-! ## Main theorems -/

/-- **`host_route_dispatch` — precedence.** The Host header selects a matching
virtual host, and that block is a HIGHEST-precedence match: exact beats wildcard
beats default. No block that also matches the request outranks the chosen one.
Order-independent: the winner is decided by class, not table position. -/
theorem host_route_dispatch {vs : List (VHost H)} {req : List String} {v : VHost H}
    (h : selectHost vs req = some v) :
    matchesHost req v = true
      ∧ ∀ v' ∈ vs, matchesHost req v' = true → hostRank v'.host ≤ hostRank v.host := by
  refine ⟨selectHost_sound h, ?_⟩
  unfold selectHost at h
  cases he : vs.find? (isExactMatch req) with
  | some ve =>
    -- winner is exact (rank 2 = maximum): everything is ≤ 2.
    rw [he] at h; cases h
    obtain ⟨ls, hp⟩ := isExactMatch_exact (find?_true he)
    intro v' _ _
    rw [hp]; cases v'.host <;> simp [hostRank]
  | none =>
    rw [he] at h
    have hnoExact := find?_none_false he
    cases hw : vs.find? (isWildMatch req) with
    | some vw =>
      -- winner is wildcard (rank 1); no exact match exists, so every match ≤ 1.
      rw [hw] at h; cases h
      obtain ⟨rest, hp⟩ := isWildMatch_wild (find?_true hw)
      intro v' hmem hmatch
      rw [hp]
      cases hp' : v'.host with
      | exact ls' =>
        exact absurd (hnoExact v' hmem) (by
          rw [isExactMatch_eq hp']; rw [hmatch]; simp)
      | wild r' => simp [hostRank]
      | default => simp [hostRank]
    | none =>
      -- winner is default (rank 0); neither exact nor wildcard matches exist.
      rw [hw] at h
      have hnoWild := find?_none_false hw
      have hp := isDefault_default (find?_true h)
      intro v' hmem hmatch
      rw [hp]
      cases hp' : v'.host with
      | exact ls' =>
        exact absurd (hnoExact v' hmem) (by
          rw [isExactMatch_eq hp']; rw [hmatch]; simp)
      | wild r' =>
        exact absurd (hnoWild v' hmem) (by
          rw [isWildMatch_eq hp']; rw [hmatch]; simp)
      | default => simp [hostRank]

/-- **`host_route_no_leak` — isolation.** A request whose host is not `hB` is
never served by a virtual host bound to the exact host `hB`: the request for
host A never reaches host B's route table. (RFC 9110 §7.4 no-misdirection at the
authority-selection layer.) -/
theorem host_route_no_leak {vs : List (VHost H)} {req : List String} {v : VHost H}
    {hB : List String} (hexact : v.host = Host.exact hB) (hne : req ≠ hB) :
    selectHost vs req ≠ some v := by
  intro hsel
  have hm := selectHost_sound hsel
  rw [matchesHost, hexact, hostMatches] at hm
  exact absurd hm (by simp [decide_eq_false hne])

/-- **`host_route_default` — fallback.** With no exact-host match and no
wildcard match among the declared blocks, a request falls through to the default
block: selection returns some block and that block is the default (never an
exact or wildcard host). Requires a default block to exist. -/
theorem host_route_default {vs : List (VHost H)} {req : List String}
    (hnoExact : vs.find? (isExactMatch req) = none)
    (hnoWild : vs.find? (isWildMatch req) = none)
    (hdef : ∃ d ∈ vs, isDefault d = true) :
    ∃ v, selectHost vs req = some v ∧ v.host = Host.default := by
  unfold selectHost
  rw [hnoExact, hnoWild]
  obtain ⟨d, hmem, hd⟩ := hdef
  cases hf : vs.find? isDefault with
  | none =>
    have := find?_isSome_of_mem hmem hd
    rw [hf] at this; simp at this
  | some v => exact ⟨v, rfl, isDefault_default (find?_true hf)⟩

/-! ## Concrete witnesses — each precedence class is real and distinct (`H := Nat`)

A three-block table (declared wild-first, exact-second, default-last, so the
result cannot be an artifact of table order) discriminates the three classes:
`api.example.com` → the exact block; `www.example.com` → the wildcard block;
`other.org` → the default block. Three DIFFERENT route tables fire. -/

/-- Wild block FIRST, exact SECOND, default LAST — precedence must beat order. -/
def tables : List (VHost Nat) :=
  [ { host := .wild ["example", "com"],           routes := 2 },
    { host := .exact ["api", "example", "com"],    routes := 1 },
    { host := .default,                            routes := 0 } ]

/-- **Exact beats wildcard (and beats order).** `api.example.com` matches both
the wildcard `*.example.com` (which appears first) and the exact block, and the
exact block's table (`1`) is chosen. -/
theorem demo_exact_wins :
    (selectHost tables ["api", "example", "com"]).map (·.routes) = some 1 := by
  decide

/-- **Wildcard is real.** `www.example.com` has no exact block, so the wildcard
`*.example.com` table (`2`) is chosen over the default. -/
theorem demo_wild_catches :
    (selectHost tables ["www", "example", "com"]).map (·.routes) = some 2 := by
  decide

/-- **Default is real.** An unrelated host matches neither exact nor wildcard and
falls through to the default table (`0`). -/
theorem demo_default_fallthrough :
    (selectHost tables ["other", "org"]).map (·.routes) = some 0 := by
  decide

/-- **No-leak is real.** The `api.example.com` request never selects the
`b.example.net` exact block, whichever tables are present. -/
theorem demo_no_leak :
    (selectHost
      [ { host := .exact ["b", "example", "net"], routes := 9 } ]
      ["api", "example", "com"]).map (·.routes)
      = (none : Option Nat) := by
  decide

end Route.HostRoute
