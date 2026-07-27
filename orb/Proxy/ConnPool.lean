/-
ConnPool — per-backend upstream connection reuse (keep-alive), proven correct.

A reverse-proxy forward first tries to check out an idle keep-alive socket for
the chosen backend and reuses it; only on a pool miss (or a socket that failed
its liveness probe) does it open a fresh `connect(2)`. After a CLEAN, fully
framed keep-alive reply the socket is checked back in for the next forward.

The whole point of reuse is that it must be *invisible*: a forward served over a
pooled socket has to return the exact same bytes to the client as a forward that
dialed fresh. This module proves that, and — crucially — proves the property is
tight: reuse is byte-correct **exactly** when the socket sits at a request
boundary with an empty receive buffer, which is precisely the check-in contract
the host enforces (whole reply consumed, upstream did not signal close) and the
checkout liveness probe re-verifies (a socket carrying pending bytes is retired,
never reused).

Model (sans-IO, byte type `α` abstract):

  * an `Upstream` is a deterministic per-backend responder `serve : id → req →
    reply` — two forwards of the same request to the same backend get the same
    reply bytes (the substrate assumption the whole pool rests on);
  * a `Conn` is a live socket: the backend it is connected to, plus the
    `residual` bytes already sitting in its receive buffer *before* we send our
    request. A socket exactly at a request boundary has `residual = []`;
  * `dial b` is a fresh socket to `b`: empty receive buffer;
  * `forward` reads the residual followed by the backend's reply — on a clean
    socket that is exactly the reply, on a dirty one the stale bytes corrupt the
    framing (which is why a dirty socket must never be reused);
  * a `PoolState` is one backend's idle-socket stack with a retention cap,
    mirroring the per-address `Vec<IdleConn>` capped at `max_idle_per_host`.

Theorems:

  * `reuse_preserves_bytes` — **reuse is invisible**: a pooled socket honoring
    the check-in contract forwards byte-identically to a fresh dial;
  * `reuse_correct_iff_clean` — **and the contract is exactly necessary**: reuse
    matches a fresh dial iff the socket's receive buffer was empty. A socket with
    pending bytes provably diverges — the necessity behind the liveness probe;
  * `session_eq_fresh` — **keep-alive is invisible end to end**: an unbounded
    reuse session over one socket is byte-identical to serving each request on
    its own fresh dial;
  * `checkin_preserves_clean` / `checkout_reusable` — the pool only ever holds
    clean sockets, so every checkout feeds `reuse_preserves_bytes`;
  * `checkin_len_le` / `checkout_len_le` — the idle set never exceeds the
    retention cap (bounded idle fds after a burst).
-/

namespace Proxy.ConnPool

/-- A backend upstream, modeled as a deterministic responder: the exact reply
bytes it returns for a given request. Two forwards of the same request to the
same backend get the same reply — the pool's whole correctness rests on this
determinism, so it is an explicit part of the model, not an assumption smuggled
into a proof. -/
structure Upstream (α : Type) where
  serve : Nat → List α → List α

/-- A live upstream socket: the backend `id` it is connected to, and the
`residual` bytes already sitting in its receive buffer BEFORE we send our
request. A socket exactly at a request boundary — the only kind the pool is
allowed to retain — has an empty residual. -/
structure Conn (α : Type) where
  backend : Nat
  residual : List α
deriving DecidableEq

/-- A freshly dialed socket to backend `b`: connected to `b`, receive buffer
empty (no bytes precede our request). -/
def dial (b : Nat) : Conn α := { backend := b, residual := [] }

/-- Forward `req` over `c`: the client reads whatever was already buffered on the
socket (`residual`) followed by the backend's reply to `req`. On a clean socket
(empty residual) that is exactly the reply; on a dirty one the stale bytes
prefix — and corrupt — the framing, which is why a dirty socket must never be
reused. -/
def forward (u : Upstream α) (c : Conn α) (req : List α) : List α :=
  c.residual ++ u.serve c.backend req

/-- The check-in contract, as a predicate on the socket: a socket may be parked
for reuse only when it sits exactly at the next request boundary — the whole
framed reply consumed — so its receive buffer is empty. -/
def reusable (c : Conn α) : Prop := c.residual = []

/-- After a forward whose reply the client fully consumed, the socket is back at
a request boundary (empty residual), ready for the next forward — the
post-condition the caller must establish before check-in. -/
def afterClean (c : Conn α) : Conn α := { c with residual := [] }

/-! ### Append cancellation (self-contained; no Mathlib) -/

/-- `l ++ X = X` exactly when `l` is empty — proven by a length argument so it
depends only on stable core lemmas. -/
theorem append_left_eq_self {α : Type} (l X : List α) :
    l ++ X = X ↔ l = [] := by
  constructor
  · intro h
    have hlen := congrArg List.length h
    rw [List.length_append] at hlen
    cases l with
    | nil => rfl
    | cons a as => simp only [List.length_cons] at hlen; omega
  · rintro rfl; rfl

/-! ### Reuse is invisible -/

/-- **Reuse is invisible.** A pooled socket that honors the check-in contract
(sits at a request boundary) forwards byte-identically to a fresh dial to the
same backend: the client cannot tell a reused connection from a new one. -/
theorem reuse_preserves_bytes (u : Upstream α) (c : Conn α) (req : List α)
    (hc : reusable c) :
    forward u c req = forward u (dial c.backend) req := by
  simp only [forward, dial, reusable] at *
  rw [hc]

/-- **And the check-in contract is exactly necessary.** A forward over `c`
matches a fresh dial iff `c`'s receive buffer was empty. A socket carrying
pending bytes provably diverges from a fresh dial — this is the necessity behind
the checkout liveness probe, which retires any socket with bytes pending before
the request. The reuse-correctness theorem is therefore not vacuous: it holds on
exactly the clean sockets and fails on every dirty one. -/
theorem reuse_correct_iff_clean (u : Upstream α) (c : Conn α) (req : List α) :
    forward u c req = forward u (dial c.backend) req ↔ reusable c := by
  simp only [forward, dial, reusable, List.nil_append]
  exact append_left_eq_self c.residual (u.serve c.backend req)

/-! ### Keep-alive is invisible end to end -/

/-- A keep-alive session: forward each request in turn over ONE reused socket,
collecting the client-visible reply bytes. Between forwards the socket is drained
clean (`afterClean`) — the state the check-in contract requires. -/
def session (u : Upstream α) (c : Conn α) : List (List α) → List (List α)
  | [] => []
  | req :: rest => forward u c req :: session u (afterClean c) rest

/-- **Keep-alive is invisible end to end.** An unbounded reuse session over one
socket (starting clean) is byte-identical to serving each request on its own
fresh dial to the same backend. Reuse across arbitrarily many requests — and
arbitrarily many reply framings — never perturbs a single client byte. -/
theorem session_eq_fresh (u : Upstream α) (reqs : List (List α)) :
    ∀ c : Conn α, reusable c →
      session u c reqs = reqs.map (fun r => forward u (dial c.backend) r) := by
  induction reqs with
  | nil => intro c _; rfl
  | cons r rest ih =>
    intro c hc
    simp only [session, List.map_cons, List.cons.injEq]
    refine ⟨reuse_preserves_bytes u c r hc, ?_⟩
    have hback : (afterClean c).backend = c.backend := rfl
    have hclean : reusable (afterClean c) := rfl
    rw [ih (afterClean c) hclean, hback]

/-! ### The pool holds only clean sockets, capped -/

/-- One backend's idle-socket stack, mirroring the per-address `Vec<IdleConn>`
capped at `max_idle_per_host`. The multi-backend `HashMap` is a product of these,
so the single-backend theorems lift componentwise. -/
structure PoolState (α : Type) where
  idle : List (Conn α)
  cap : Nat

/-- Park a socket for the next forward: pushed onto the idle stack unless the
retention cap is already reached, in which case it is dropped (closed). -/
def PoolState.checkin (p : PoolState α) (c : Conn α) : PoolState α :=
  if p.idle.length < p.cap then { p with idle := c :: p.idle } else p

/-- Take the warmest idle socket, or `none` when none is warm. -/
def PoolState.checkout (p : PoolState α) : Option (Conn α) × PoolState α :=
  match p.idle with
  | [] => (none, p)
  | c :: rest => (some c, { p with idle := rest })

/-- Every parked socket sits at a request boundary — the check-in invariant
lifted to the whole idle set. -/
def PoolState.allClean (p : PoolState α) : Prop := ∀ c ∈ p.idle, reusable c

/-- **The pool only ever holds clean sockets.** Checking in a socket that honors
the contract preserves the invariant; dropping one at the cap trivially does. -/
theorem checkin_preserves_clean {p : PoolState α} {c : Conn α}
    (hp : p.allClean) (hc : reusable c) : (p.checkin c).allClean := by
  unfold PoolState.checkin PoolState.allClean
  split
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hc
    · exact hp x hx
  · exact hp

/-- **Every checkout feeds `reuse_preserves_bytes`.** A socket taken from a clean
pool is itself clean (so reusing it is byte-identical to a fresh dial), and the
pool stays clean. -/
theorem checkout_reusable {p : PoolState α} (hp : p.allClean)
    {c : Conn α} {p' : PoolState α} (h : p.checkout = (some c, p')) :
    reusable c ∧ p'.allClean := by
  unfold PoolState.checkout at h
  cases hi : p.idle with
  | nil => rw [hi] at h; simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h
  | cons d rest =>
    rw [hi] at h
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨hcd, hp'⟩ := h
    subst hcd hp'
    refine ⟨hp d ?_, fun x hx => hp x ?_⟩
    · rw [hi]; exact List.mem_cons_self ..
    · rw [hi]; exact List.mem_cons_of_mem d hx

/-- **The idle set never exceeds the retention cap.** A check-in either drops the
socket (cap reached) or pushes below the cap. -/
theorem checkin_len_le {p : PoolState α} {c : Conn α}
    (h : p.idle.length ≤ p.cap) : (p.checkin c).idle.length ≤ p.cap := by
  unfold PoolState.checkin
  split
  · simp only [List.length_cons]; omega
  · exact h

/-- Checkout never grows the idle set (it only pops). -/
theorem checkout_len_le {p : PoolState α} {c : Conn α} {p' : PoolState α}
    (h : p.checkout = (some c, p')) : p'.idle.length ≤ p.idle.length := by
  unfold PoolState.checkout at h
  cases hi : p.idle with
  | nil => rw [hi] at h; simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h
  | cons d rest =>
    rw [hi] at h
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨_, hp'⟩ := h
    subst hp'
    show rest.length ≤ (d :: rest).length
    simp only [List.length_cons]; omega

/-! ### Executable checks (concrete, no `native_decide`) -/

/-- A concrete echo upstream: every backend replies with the request bytes. -/
def echo : Upstream Nat := { serve := fun _ req => req }

/-- A fresh dial forwards the reply verbatim. -/
example : forward echo (dial 0) [1, 2, 3] = [1, 2, 3] := rfl

/-- A clean pooled socket (residual empty) forwards identically to a fresh
dial. -/
example :
    forward echo { backend := 0, residual := [] } [1, 2, 3]
      = forward echo (dial 0) [1, 2, 3] := rfl

/-- A DIRTY socket (a stale byte buffered) diverges from a fresh dial — the
concrete witness that the reuse theorem is non-vacuous. -/
example :
    forward echo { backend := 0, residual := [9] } [1, 2, 3]
      ≠ forward echo (dial 0) [1, 2, 3] := by decide

/-- A three-request keep-alive session over one reused socket matches serving
each request fresh. -/
example :
    session echo (dial 0) [[1], [2, 2], [3]] = [[1], [2, 2], [3]] := rfl

end Proxy.ConnPool
