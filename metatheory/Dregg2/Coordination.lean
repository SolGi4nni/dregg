/-
# Dregg2.Coordination — the multiparty-session-type / choreography layer.

Models multi-party, multi-round agent coordination as multiparty session types (MPST):

  * A **global type `G`** (choreography) describes the whole protocol — who communicates with
    whom, in what order, with what branching/recursion (Honda–Yoshida–Carbone JACM 2016);
  * **Projection** `G ↾ p` (`project G p`) gives each role its local endpoint type;
  * A well-formed (projectable) `G` enjoys progress + deadlock-freedom by design (Law 2).

Reified as a cell: a coordination is a protocol-cell whose `CellProgram` is `G`; its
admissibility predicate is "is this the next legal action under `G`" and its state is
messages-so-far. The protocol-cell's coalgebra is a `Boundary.TurnCoalg`, so `G` (resp.
`G ↾ p`) embeds into the final coalgebra `νF` of `Boundary`.

Three orthogonal judgements:
  * **Law 1 (conservation / linearity)** — `Core` / `Resource`;
  * **Law 2 (ordering / session)** — this module's `project` / projectability;
  * **I-confluence** — `Confluence.IConfluent` over a step's write-set × cell-state-lattice,
    NOT detected by the session type. An I-confluent step runs cross-group, partition-tolerant,
    with no atomic commit; a coupled (Σ=0 settlement) step must block.

OPEN: the linearity⇒I-confluence conflation is refuted — these are independent judgements.
The branching `merge` in projection is partial (MPST projection is sound but
incomplete). Recursion (`mu`/`var`) is handled by the `NoRec` precondition; deadlock-freedom
and privacy-by-projection hold on the non-recursive fragment.

Naming note: `to` and `Sort` are Lean reserved tokens — sender/receiver roles use `src`/`dst`;
payload sorts are named `Payload`.
-/
import Dregg2.Confluence
import Dregg2.Boundary

namespace Dregg2.Coordination

universe u

/-! ## Roles, labels, and the global type `G` -/

/-- A protocol **role** (endpoint identity / participant). Abstract — `Nat` here; in
the real system a role resolves to a participant *cell* (the protocol-cell coordinates
cells, so a role is "which cell plays this part"). -/
abbrev Role := Nat

/-- A **branch label** (the `&`/`⊕` selector — which alternative was chosen). -/
abbrev Label := Nat

/-- A **payload sort** carried by a communication (the message type). Abstract.
(Named `Payload` because `Sort` is the reserved universe keyword.) -/
abbrev Payload := Nat

/-- A **recursion variable** name (for `μ`-recursive protocols). -/
abbrev TyVar := Nat

/-- **`GlobalType` — the choreography `G`** (Honda–Yoshida–Carbone): the whole
protocol from a god's-eye view. Constructors:

  * `comm src dst s cont` — `src → dst : ⟨s⟩ . cont`: role `src` sends a value of
    sort `s` to role `dst`, then the protocol continues as `cont` (the binary
    interaction MPST sequences; an atomic N-ary JointTurn step is a dregg2 *extension*,
    `study-choreography` claim #4, CONFIRMED-OPEN);
  * `choice src dst branches` — `src → dst : { ℓᵢ . Gᵢ }`: `src` *selects* a labelled
    branch and `dst` *offers* the set; the choreographic branching point;
  * `mu X G` / `var X` — `μX.G` recursion and its variable (recursive/looping
    protocols); named `mu` because `rec` is a reserved constructor name (clashes with
    the auto-generated recursor `GlobalType.rec`);
  * `done` — `end`: the completed protocol. -/
inductive GlobalType where
  | comm   (src dst : Role) (s : Payload) (cont : GlobalType)
  | choice (src dst : Role) (branches : List (Label × GlobalType))
  | mu      (X : TyVar) (body : GlobalType)
  | var     (X : TyVar)
  | done
  deriving Inhabited

/-! ## Local (endpoint) types -/

/-- **`LocalType` — an endpoint type** `G ↾ p` (one role's view). Constructors mirror
`GlobalType` but are *directed* — a `comm` splits into the sender's `send` and the
receiver's `recv`; a `choice` splits into the active role's `select` and the passive
role's `offer`:

  * `send dst s cont` — `!⟨s⟩ dst . cont`: output a value to `dst`;
  * `recv src s cont` — `?⟨s⟩ src . cont`: input a value from `src`;
  * `select dst branches` — `dst ⊕ { ℓᵢ . Lᵢ }`: internal choice (we pick a label);
  * `offer src branches` — `src & { ℓᵢ . Lᵢ }`: external choice (we accept any label);
  * `mu X L` / `var X` — endpoint recursion (`mu`, not `rec`, per the recursor clash);
  * `done` — `end` (this role is finished / not involved). -/
inductive LocalType where
  | send   (dst : Role) (s : Payload) (cont : LocalType)
  | recv   (src : Role) (s : Payload) (cont : LocalType)
  | select (dst : Role) (branches : List (Label × LocalType))
  | offer  (src : Role) (branches : List (Label × LocalType))
  | mu      (X : TyVar) (body : LocalType)
  | var     (X : TyVar)
  | done
  deriving Inhabited

/- **`DecidableEq LocalType`** — decidable equality for endpoint types. The default
`deriving DecidableEq` handler cannot cope with the *nested* `List (Label × LocalType)`
in `select`/`offer`, so we discharge it by structural recursion through a Boolean
equality test `beq` (proved correct against `=` by a structural `beq_iff`), then read off
the `Decidable` instance from that correctness lemma. This makes `mergeLocal`'s `if
L₁ = L₂` computable. -/
namespace LocalType

/- Structural Boolean equality on endpoint types (and, mutually, on labelled-branch
lists). Sound & complete against `=` (`beq_iff` below). -/
mutual
def beq : LocalType → LocalType → Bool
  | send d₁ s₁ k₁,   send d₂ s₂ k₂   => d₁ == d₂ && s₁ == s₂ && beq k₁ k₂
  | recv s₁ p₁ k₁,   recv s₂ p₂ k₂   => s₁ == s₂ && p₁ == p₂ && beq k₁ k₂
  | select d₁ bs₁,   select d₂ bs₂   => d₁ == d₂ && beqBranches bs₁ bs₂
  | offer s₁ bs₁,    offer s₂ bs₂     => s₁ == s₂ && beqBranches bs₁ bs₂
  | mu X₁ b₁,        mu X₂ b₂          => X₁ == X₂ && beq b₁ b₂
  | var X₁,          var X₂            => X₁ == X₂
  | done,            done              => true
  | _,               _                => false
/-- Boolean equality on labelled-branch lists (mutual helper for `beq`). -/
def beqBranches : List (Label × LocalType) → List (Label × LocalType) → Bool
  | [],              []              => true
  | (ℓ₁, L₁) :: r₁, (ℓ₂, L₂) :: r₂ => ℓ₁ == ℓ₂ && beq L₁ L₂ && beqBranches r₁ r₂
  | _,               _              => false
end

/- `beq` is sound & complete: `beq a b = true ↔ a = b` (and the branch-list version),
proved by mutual structural induction. -/
mutual
theorem beq_iff : ∀ a b : LocalType, beq a b = true ↔ a = b
  | send d₁ s₁ k₁, b => by
      cases b <;> simp only [beq, Bool.and_eq_true, beq_iff_eq, reduceCtorEq,
        false_iff, send.injEq, not_and] <;>
        (try rw [beq_iff k₁ _]) <;> (try tauto)
  | recv s₁ p₁ k₁, b => by
      cases b <;> simp only [beq, Bool.and_eq_true, beq_iff_eq, reduceCtorEq,
        false_iff, recv.injEq, not_and] <;>
        (try rw [beq_iff k₁ _]) <;> (try tauto)
  | select d₁ bs₁, b => by
      cases b <;> simp only [beq, Bool.and_eq_true, beq_iff_eq, reduceCtorEq,
        false_iff, select.injEq, not_and] <;>
        (try rw [beqBranches_iff bs₁ _]) <;> (try tauto)
  | offer s₁ bs₁, b => by
      cases b <;> simp only [beq, Bool.and_eq_true, beq_iff_eq, reduceCtorEq,
        false_iff, offer.injEq, not_and] <;>
        (try rw [beqBranches_iff bs₁ _]) <;> (try tauto)
  | mu X₁ b₁, b => by
      cases b <;> simp only [beq, Bool.and_eq_true, beq_iff_eq, reduceCtorEq,
        false_iff, mu.injEq, not_and] <;>
        (try rw [beq_iff b₁ _]) <;> (try tauto)
  | var X₁, b => by
      cases b <;> simp [beq, beq_iff_eq]
  | done, b => by
      cases b <;> simp [beq]
theorem beqBranches_iff : ∀ bs₁ bs₂ : List (Label × LocalType),
    beqBranches bs₁ bs₂ = true ↔ bs₁ = bs₂
  | [], bs₂ => by cases bs₂ <;> simp [beqBranches]
  | (ℓ₁, L₁) :: r₁, bs₂ => by
      cases bs₂ with
      | nil => simp [beqBranches]
      | cons hd₂ tl₂ =>
          obtain ⟨ℓ₂, L₂⟩ := hd₂
          simp only [beqBranches, Bool.and_eq_true, beq_iff_eq, List.cons.injEq,
            Prod.mk.injEq]
          rw [beq_iff L₁ L₂, beqBranches_iff r₁ tl₂]
          try tauto
end

instance : DecidableEq LocalType := fun a b =>
  decidable_of_iff (beq a b = true) (beq_iff a b)

end LocalType

/-! ## Projection `G ↾ p`

The heart of MPST. `project G p` computes role `p`'s endpoint type. It is **partial in
the branching case** by nature: when `p` is *not* the role driving a `choice`, its
continuations across the branches must agree up to a **merge** operator `⊔ₗ`, and the
classical merge is partial — projection is **sound but incomplete** (`study-choreography`
claim #2, CONFIRMED). We define the directed comm/recursion cases computably and route
branching through an abstract, deliberately-partial `mergeLocal`. -/

/-- **`mergeLocal` — the MPST branch-merge `⊔ₗ`.** Reconciles a non-active role's
continuations across the branches of a `choice` it neither selects nor offers. The
classical operator is *partial* (defined only on "mergeable" continuations — e.g.
identical, or differing only in disjoint `offer` labels), which is the source of MPST
projection's incompleteness. Modelled as `Option`. We commit to the **simplest SOUND classical merge**: two
continuations are mergeable iff they are *identical* (`L₁ = L₂ ⇒ some L₁`, else `none`).
This is the conservative core of the classical MPST merge (the standard full-merge that
unions disjoint `offer` branches is a strict, sound superset; restricting to identity
keeps soundness — projection still implements the global protocol — at the cost of
rejecting some projectable choreographies, i.e. the CONFIRMED incompleteness of claim
#2). `DecidableEq LocalType` (derived above) makes this computable. -/
def mergeLocal : LocalType → LocalType → Option LocalType :=
  fun L₁ L₂ => if L₁ = L₂ then some L₁ else none

/- **`project G p` = `G ↾ p` — projection of the choreography onto an endpoint** (with
its mutual branch helpers). Directed split:
  * `comm a b s k`: if `p = a` ⇒ `send b s (k↾p)`; if `p = b` ⇒ `recv a s (k↾p)`;
    else `p` is uninvolved in this message ⇒ skip to `k↾p`.
  * `choice a b bs`: if `p = a` ⇒ `select b (bs↾p)`; if `p = b` ⇒ `offer a (bs↾p)`;
    else `p` must reconcile the branches via `mergeLocal` (`projectBranches`) — the
    partial case. We default a failed/absent merge to `done` so `project` is TOTAL as a
    function (the *partiality* lives,, in `mergeLocal` returning `none`); a real
    implementation surfaces "not projectable" as a `Projectable` failure.
  * `mu X g` / `var X` / `done`: structural.
`projectMap`/`projectBranches` recurse on the branch list so the structural-recursion
checker sees each `g` as a subterm of the `choice`. Fully computable now that
`mergeLocal` is concrete (the identity merge, decidable via `DecidableEq LocalType`). -/
mutual
  /-- Projection of a global type onto a single role (`G ↾ p`). -/
  def project : GlobalType → Role → LocalType
    | GlobalType.comm src dst s cont, p =>
        if p = src then LocalType.send dst s (project cont p)
        else if p = dst then LocalType.recv src s (project cont p)
        else project cont p
    | GlobalType.choice src dst branches, p =>
        if p = src then LocalType.select dst (projectMap branches p)
        else if p = dst then LocalType.offer src (projectMap branches p)
        else (projectBranches branches p).getD LocalType.done
    | GlobalType.mu X body, p  => LocalType.mu X (project body p)
    | GlobalType.var X, _      => LocalType.var X
    | GlobalType.done, _       => LocalType.done

  /-- Project each labelled global continuation, keeping the labels (for the
  active-role `select`/`offer` cases). -/
  def projectMap : List (Label × GlobalType) → Role → List (Label × LocalType)
    | [],            _ => []
    | (ℓ, g) :: rest, p => (ℓ, project g p) :: projectMap rest p

  /-- Project a list of labelled continuations onto a *passive* role and `mergeLocal`
  them into one local type (the source of MPST projection incompleteness). -/
  def projectBranches : List (Label × GlobalType) → Role → Option LocalType
    | [],             _ => some LocalType.done
    | [(_, g)],       p => some (project g p)
    | (_, g) :: rest, p =>
        match projectBranches rest p with
        | some l => mergeLocal (project g p) l
        | none   => none
end

/-! ## Well-formedness (projectability) -/

/- The set of roles occurring in `G` (senders/receivers of any communication or
choice). Used to quantify "every participant" in well-formedness and fidelity. -/
mutual
  /-- Roles occurring in a global type (`comm`/`choice` senders & receivers). -/
  def roles : GlobalType → List Role
    | GlobalType.comm src dst _ cont => src :: dst :: roles cont
    | GlobalType.choice src dst bs   => src :: dst :: rolesBranches bs
    | GlobalType.mu _ body           => roles body
    | GlobalType.var _               => []
    | GlobalType.done                => []

  /-- Roles occurring in a branch list (mutual helper so each `g` is a subterm). -/
  def rolesBranches : List (Label × GlobalType) → List Role
    | []            => []
    | (_, g) :: rest => roles g ++ rolesBranches rest
end

/- **`MergesAt G p` — the real per-role merge-success predicate.** Recurses through `G`
exactly as `project … p` does, and at every `choice` where `p` is the *passive* role
(neither selector nor offerer) it demands that the branch-merge actually reconciled —
`projectBranches branches p ≠ none` — i.e. `mergeLocal` never returned `none` while
computing `project G p`. This is the genuine MPST projectability side-condition; it is
NOT vacuous (see `var_not_mergesAt` for a `G`/`p` that FAILS it). `projectBranches` is
already concrete (the identity merge of `mergeLocal`), so this predicate has real,
falsifiable content. -/
mutual
  def MergesAt : GlobalType → Role → Prop
    | GlobalType.comm _ _ _ cont, p => MergesAt cont p
    | GlobalType.choice src dst branches, p =>
        if p = src then MergesAtMap branches p
        else if p = dst then MergesAtMap branches p
        else
          -- passive role: the branch-merge MUST succeed *and* each branch projects
          (projectBranches branches p ≠ none) ∧ MergesAtMap branches p
    | GlobalType.mu _ body, p => MergesAt body p
    | GlobalType.var _, _      => True
    | GlobalType.done, _       => True

  /-- Every labelled branch's continuation merges at `p` (mutual helper). -/
  def MergesAtMap : List (Label × GlobalType) → Role → Prop
    | [],             _ => True
    | (_, g) :: rest, p => MergesAt g p ∧ MergesAtMap rest p
end

/-- **`Projectable G` — well-formedness = every role projects successfully.** A `G` is
well-formed iff for every role the merge in every branching reconciles (no `mergeLocal`
failure). The content is "no `mergeLocal` invoked while computing `project G p`
returned `none`" — made concrete via `MergesAt`. A `choice` whose passive-role branches
disagree (identity-merge fails) is NOT `Projectable`. -/
def Projectable (G : GlobalType) : Prop :=
  ∀ p : Role, p ∈ roles G → MergesAt G p

/-- **`Projectable` is non-vacuous.** A two-branch `choice` whose passive role's continuations
disagree fails `MergesAt` (identity merge returns `none`). Concretely `0 → 1 : { a . (2→3 done) , b . done }`:
role `2` is passive; its two branch projections disagree and the merge rejects them. -/
theorem projectBranches_can_fail :
    ∃ (branches : List (Label × GlobalType)) (p : Role),
      projectBranches branches p = none := by
  refine ⟨[(0, GlobalType.comm 2 3 0 GlobalType.done), (1, GlobalType.done)], 2, ?_⟩
  -- branch 0 projects (for role 2, the sender) to `send 3 0 done`; branch 1 to `done`;
  -- identity `mergeLocal (send …) done = none`.
  decide

/-! ## The protocol-cell: `CellProgram` IS `G` (the coalgebra embedding)

`dregg2 §6`: a coordination is reified as a **protocol-cell** whose coalgebra
structure-map (`Boundary.TurnCoalg.step`) is driven by `G`. The cell's carrier is "the
protocol state" — the *residual* choreography (protocol-remaining); a turn advances it
to `G'`; the observation is the public protocol head. -/

/-- **`ProtocolCell` — the choreography reified as a cell.** Ties a global type `G` to
the `Boundary.TurnCoalg` whose `step` IS `G`'s transition: its carrier ranges over the
*residual* global types (protocol-so-far → protocol-remaining), the observation
component (`Obs`) exposes the public protocol head, the admissible-turn component
(`AdmissibleTurn`) is "play the next legal action of `G`," and `residual` decodes a
carrier-state back to the global type it represents (the witness that `coalg.step` IS
`G`'s transition — a Moore coalgebra of `G`). -/
structure ProtocolCell (Obs AdmissibleTurn : Type u) where
  /-- The choreography this cell runs. -/
  G        : GlobalType
  /-- The underlying behaviour coalgebra (a `νF` element), `Boundary`'s `TurnCoalg`. -/
  coalg    : Dregg2.Boundary.TurnCoalg Obs AdmissibleTurn
  /-- The carrier-point that is "the protocol at the start" (the cell's current state). -/
  start    : coalg.Carrier
  /-- Decode a carrier-state back to the residual global type it represents. -/
  residual : coalg.Carrier → GlobalType
  /-- The protocol-cell starts at `G`. -/
  start_is_G : residual start = G

/-! ## Duality and progress (the content of fidelity / deadlock-freedom)

The load-bearing fact projection guarantees is **duality**: the sender's projected head
of a `comm a b` is a `send` to `b` and the receiver's is the dual `recv` from `a`. A
configuration is **stuck** when a role is blocked on an input/external-choice with no
matching output anywhere — deadlock-freedom-by-design is exactly the absence of stuck,
non-`done` reachable configurations. We state these structurally so the theorems below
are genuine (not `⟨_, rfl⟩`-trivial). -/

/-- A role is **waiting** when its endpoint type is a `recv`/`offer` (blocked on input
or external choice) — the only states from which a system can deadlock. -/
def LocalType.waiting : LocalType → Bool
  | LocalType.recv _ _ _ => true
  | LocalType.offer _ _  => true
  | _                    => false

/-- A role is **terminated** when its endpoint type is `done` (it has no further
obligation). -/
def LocalType.terminated : LocalType → Bool
  | LocalType.done => true
  | _              => false

/-- **`Dual L₁ L₂`** — the two endpoints can synchronise *now*: a `send dst s` faces a
`recv src s` of the matching sort (and dually). This is the per-step compatibility MPST
projection must produce; the existence of a dual partner for every `waiting` role is
exactly progress. -/
def Dual : LocalType → LocalType → Prop
  | LocalType.send _ s₁ _, LocalType.recv _ s₂ _ => s₁ = s₂
  | LocalType.recv _ s₁ _, LocalType.send _ s₂ _ => s₁ = s₂
  | LocalType.select _ _,  LocalType.offer _ _   => True
  | LocalType.offer _ _,   LocalType.select _ _  => True
  | _,                     _                     => False

/-! ## Theorems — fidelity, deadlock-freedom, the I-confluent fragment, privacy -/

/-- **`projection_sound` — MPST fidelity / EPP soundness.** The projected endpoints
`{ G ↾ p | p ∈ roles G }` in parallel realize exactly `G`. Stated via head-duality: for a
protocol-cell running `comm a b s k` with `a ≠ b`, the sender's projection is a `send` and
the receiver's the dual `recv`, so they synchronise on exactly the prescribed message.
(The full statement is a bisimulation of the composed projections to `pc.coalg`, whose
discharge is OPEN.) -/
theorem projection_sound
    {Obs AdmissibleTurn : Type u}
    (pc : ProtocolCell Obs AdmissibleTurn)
    (wf : Projectable pc.G)
    (a b : Role) (s : Payload) (k : GlobalType)
    (hG : pc.G = GlobalType.comm a b s k) (hab : a ≠ b) :
    Dual (project pc.G a) (project pc.G b) := by
  -- Rewrite `pc.G` to `comm a b s k`; compute both projections and unfold `Dual`.
  rw [hG]
  simp only [project, if_true, if_neg hab.symm, Dual]


/-- **`StepEffect` — the per-protocol-step effect** whose I-confluence the third
judgement classifies. A choreography step (one `comm`/`choice` action, as it lands in
the participant cells) induces an update on the touched cells' merge-state `S`; whether
that update is I-confluent (`Confluence.IConfluent` over the cell-state lattice) decides
cross-group runnability. Abstractly, a step is the cell invariant its writes must
preserve. -/
structure StepEffect (S : Type u) [Dregg2.Confluence.MergeState S] where
  /-- The cell invariant the step's writes must preserve (`balance ≥ 0`, set-membership,
  a `WriteOnce` slot — `Confluence.Invariant`). -/
  inv : Dregg2.Confluence.Invariant S

/-- **`iconfluent_fragment_crossgroup_free` — the I-confluent fragment runs cross-group
free; the coupled fragment must block.** The classifier is NOT the session type — it is
`Confluence.IConfluent` over the step's write-set × cell-state-lattice (an independent
third judgement):

  * **I-confluent step** (commutative/monotone): if `Confluence.IConfluent step.inv`, the
    step needs no cross-group coordination — it runs partition-tolerant, no atomic commit
    (`Confluence.Tier1Eligible`). A choreography whose steps are all I-confluent runs fully
    cross-group free.
  * **Coupled step** (atomic Σ=0 settlement): if `¬ Confluence.IConfluent step.inv`, the
    step must block under partition (`Confluence.nonpairwise_escalation`; matches BEC Thm 3.1).

The load-bearing content: when the step is I-confluent, any two invariant-preserving versions
of the touched state merge invariant-safely — that is what "partition-tolerant, no commit"
means, i.e. `Confluence.admits_sound` specialised to `step.inv`. The bare definitional unfold
`Tier1Eligible ↔ IConfluent` is recorded as `tier1Eligible_iff_iconfluent_def` below.

OPEN: a choreography that statically partitions these two fragments over Byzantine parties is
an open problem (likely new). -/
theorem iconfluent_fragment_crossgroup_free
    {S : Type u} [Dregg2.Confluence.MergeState S]
    (step : StepEffect S)
    (hI : Dregg2.Confluence.IConfluent step.inv)
    (x y : S) (hx : step.inv x) (hy : step.inv y) :
    step.inv (x ⊔ y) :=
  -- An I-confluent step's concurrent merges preserve its invariant — the cross-group-free
  -- guarantee. This fails for the coupled (Σ=0 settlement) fragment, which must escalate.
  hI x y hx hy

/-- **`tier1Eligible_iff_iconfluent_def` — the definitional unfold.** `Tier1Eligible` is
defined as `IConfluent`, so the coincidence is `Iff.rfl` with no independent content.
Named `_def` to distinguish it from the cross-group-freedom theorem above. -/
theorem tier1Eligible_iff_iconfluent_def
    {S : Type u} [Dregg2.Confluence.MergeState S]
    (step : StepEffect S) :
    Dregg2.Confluence.Tier1Eligible step.inv
      ↔ Dregg2.Confluence.IConfluent step.inv :=
  Iff.rfl

/-! ### The non-recursion fragment `NoRec` (precondition for privacy)

`privacy_by_projection` ("an uninvolved role projects to `done`") is false as a bare statement
over all `GlobalType`s: `project (var X) p = LocalType.var X` while `roles (var X) = []`, so
for `G = var 0` every `p` satisfies `p ∉ roles G` yet `project G p ≠ done` (kernel-checked
counterexample, see `privacy_var_counterexample`). Likewise for `mu`.

The honest fix is to restrict to `NoRec G`: `G` built from `comm`/`choice`/`done` only.
On this fragment the privacy property is a genuine theorem — the passive-role branch-merge
of `done` with `done` is `some done`. -/
mutual
  /-- `NoRec G` — `G` uses no recursion constructors (`mu`/`var`) anywhere. The honest
  precondition under which an uninvolved role provably projects to `done`. -/
  def NoRec : GlobalType → Prop
    | GlobalType.comm _ _ _ cont => NoRec cont
    | GlobalType.choice _ _ bs   => NoRecBranches bs
    | GlobalType.mu _ _          => False
    | GlobalType.var _           => False
    | GlobalType.done            => True

  /-- Every branch continuation is recursion-free (mutual helper). -/
  def NoRecBranches : List (Label × GlobalType) → Prop
    | []             => True
    | (_, g) :: rest => NoRec g ∧ NoRecBranches rest
end

/-- **The bare statement IS false (kernel-checked counterexample).** For `G = var 0`,
role `5 ∉ roles G = []`, yet `project G 5 = var 0 ≠ done`. This is exactly why
`privacy_by_projection` MUST carry the `NoRec` hypothesis: without it the conclusion
fails on the open-recursion fragment. -/
theorem privacy_var_counterexample :
    ∃ (G : GlobalType) (p : Role), p ∉ roles G ∧ project G p ≠ LocalType.done := by
  refine ⟨GlobalType.var 0, 5, ?_, ?_⟩
  · simp [roles]
  · decide

/- **`privacy_by_projection` — each endpoint sees only its own projection.** A participant `p`
learns only `project G p`; co-parties' moves are hidden by the protocol structure. An
uninvolved role (not in `roles G`) projects to `done` (learns nothing).

SCOPE: holds on the non-recursive fragment `NoRec G` (see `privacy_var_counterexample`
for the counterexample on `var`). Proved by mutual structural recursion (the `GlobalType`
nested inductive prevents `induction`); the companion `privacy_branches` proves the
passive-role collapse.

OPEN: the full cryptographic conformance ("`p` ZK-proves its move is admissible under a
committed `G` without revealing `G`") awaits composition of the ZK substrate with MPST. -/
mutual
  theorem privacy_by_projection :
      ∀ (G : GlobalType), NoRec G → ∀ (p : Role), p ∉ roles G →
        project G p = LocalType.done
    | GlobalType.comm src dst s cont, hnr, p, hp => by
        -- `p ∉ src :: dst :: roles cont` ⇒ `p ≠ src`, `p ≠ dst`, `p ∉ roles cont`.
        simp only [roles, List.mem_cons, not_or] at hp
        obtain ⟨hsrc, hdst, hcont⟩ := hp
        simp only [project, if_neg hsrc, if_neg hdst]
        exact privacy_by_projection cont hnr p hcont
    | GlobalType.choice src dst branches, hnr, p, hp => by
        simp only [roles, List.mem_cons, not_or] at hp
        obtain ⟨hsrc, hdst, hbr⟩ := hp
        simp only [project, if_neg hsrc, if_neg hdst]
        -- passive role: `(projectBranches branches p).getD done = done`.
        rw [privacy_branches branches hnr p hbr]; rfl
    | GlobalType.mu X body, hnr, _, _ => absurd hnr (by simp [NoRec])
    | GlobalType.var X, hnr, _, _ => absurd hnr (by simp [NoRec])
    | GlobalType.done, _, _, _ => rfl

  /-- Passive-role branch collapse: if every branch continuation is `NoRec` and `p` occurs
  in no branch, the whole branch-merge yields `some done` (each branch projects to `done`,
  and the identity `mergeLocal done done = some done`). -/
  theorem privacy_branches :
      ∀ (branches : List (Label × GlobalType)), NoRecBranches branches →
        ∀ (p : Role), p ∉ rolesBranches branches →
          projectBranches branches p = some LocalType.done
    | [], _, _, _ => rfl
    | [(ℓ, g)], hnr, p, hbr => by
        -- single branch: `projectBranches [(ℓ,g)] p = some (project g p)`.
        simp only [NoRecBranches] at hnr
        simp only [rolesBranches, List.append_nil] at hbr
        simp only [projectBranches, privacy_by_projection g hnr.1 p hbr]
    | (ℓ, g) :: hd2 :: tl2, hnr, p, hbr => by
        simp only [NoRecBranches] at hnr
        obtain ⟨hg, htl⟩ := hnr
        simp only [rolesBranches, List.mem_append, not_or] at hbr
        obtain ⟨hgr, htlr⟩ := hbr
        -- recurse on the (nonempty) tail, then merge `done` with `done`.
        have htail : projectBranches (hd2 :: tl2) p = some LocalType.done :=
          privacy_branches (hd2 :: tl2) htl p (by
            simp only [rolesBranches, List.mem_append, not_or]; exact htlr)
        have hgdone : project g p = LocalType.done := privacy_by_projection g hg p hgr
        simp only [projectBranches, htail, hgdone, mergeLocal, if_true]
end

/- Axiom-hygiene: `privacy_by_projection` rests only on the three standard kernel axioms. -/
#assert_axioms privacy_by_projection
#assert_axioms privacy_branches


/-! ## The operational endpoint-configuration LTS (reachability machinery)

A `waiting` head `recv src s` nested below earlier actions has its `Dual` partner only among
reachable configurations, not necessarily the initial projection. We build the small-step
reduction `GStep`, its reflexive-transitive closure `GReach`, and prove progress over reachable
residuals. We work at the level of `G`'s own reduction (Honda–Yoshida–Carbone) because by
`projection_sound` the composed endpoint system is in lockstep bisimulation with `G`'s
reduction: reachable endpoint configs are exactly `{ project G' p | G ⟶* G' }`. -/

/-- **`GStep G G'` — the choreography's small-step reduction** (the head action fires):
  * `comm a b s k ⟶ k` — the message `a → b : ⟨s⟩` is exchanged, the protocol continues;
  * `choice a b bs ⟶ Gᵢ` — role `a` selects a branch `(ℓ, Gᵢ) ∈ bs` and `b` follows it.
This is the operational dynamics whose reachable residuals carry the `Dual` partners that
a nested `recv` is waiting for. (Recursion `mu`/`var` is handled by `NoRec`-restriction in
the progress theorem; the head-firing of `comm`/`choice` is the load-bearing case.) -/
inductive GStep : GlobalType → GlobalType → Prop where
  | comm   (a b : Role) (s : Payload) (k : GlobalType) : GStep (GlobalType.comm a b s k) k
  | choice (a b : Role) (bs : List (Label × GlobalType)) (ℓ : Label) (g : GlobalType)
      (hmem : (ℓ, g) ∈ bs) : GStep (GlobalType.choice a b bs) g

/-- **`GReach G G'`** — the reflexive-transitive closure of `GStep`: `G'` is a residual the
protocol can reach from `G` by zero or more head-firings. The set of **reachable
configurations**. Head-recursive, mirroring `Proof.LTS.AbsRun`. -/
inductive GReach : GlobalType → GlobalType → Prop where
  | refl (G : GlobalType) : GReach G G
  | step {G G' G'' : GlobalType} (s : GStep G G') (rest : GReach G' G'') : GReach G G''

/-- Membership extraction for `NoRecBranches`: if every branch is `NoRec` and `(ℓ,g)` is a
branch, then `g` is `NoRec`. (Used by `GStep.noRec_preserved`.) -/
theorem noRec_of_mem_branches : ∀ {bs : List (Label × GlobalType)} {ℓ : Label}
    {g : GlobalType}, NoRecBranches bs → (ℓ, g) ∈ bs → NoRec g
  | [], _, _, _, hmem => absurd hmem (by simp)
  | (ℓ', g') :: tl, ℓ, g, hnr, hmem => by
      simp only [NoRecBranches] at hnr
      rcases List.mem_cons.mp hmem with heq | htl
      · obtain ⟨_, rfl⟩ := Prod.mk.injEq .. ▸ heq; exact hnr.1
      · exact noRec_of_mem_branches hnr.2 htl

/-- `GStep` preserves `NoRec`: firing the head of a recursion-free choreography lands in a
recursion-free residual (the residual is a structural subterm). Load-bearing so the
reachable-config progress theorem stays inside the honest `NoRec` fragment. -/
theorem GStep.noRec_preserved {G G' : GlobalType} (h : GStep G G') (hnr : NoRec G) :
    NoRec G' := by
  cases h with
  | comm a b s k => exact hnr
  | choice a b bs ℓ g hmem =>
      simp only [NoRec] at hnr
      exact noRec_of_mem_branches hnr hmem

/-- `GReach` preserves `NoRec` (iterate `GStep.noRec_preserved`). -/
theorem GReach.noRec_preserved {G G' : GlobalType} (h : GReach G G') (hnr : NoRec G) :
    NoRec G' := by
  induction h with
  | refl => exact hnr
  | step s _ ih => exact ih (s.noRec_preserved (by assumption))

/-! ### Head-duality at any configuration

The head-duality proved at the initial config holds at every reachable config, by the same
computation: the two participants of the head action project to a `Dual` pair. -/

/-- Head-duality at any `comm a b s k` config with `a ≠ b`: the sender's projection is a
`send` and the receiver's the dual `recv`. -/
theorem dual_comm_heads {a b : Role} (s : Payload) (k : GlobalType) (hab : a ≠ b) :
    Dual (project (GlobalType.comm a b s k) a) (project (GlobalType.comm a b s k) b) := by
  simp only [project, if_true, if_neg hab.symm, Dual]

/-- Head-duality at any `choice a b bs` config with `a ≠ b`: the selector's projection is a
`select` and the offerer's an `offer`, which are `Dual`. -/
theorem dual_choice_heads {a b : Role} (bs : List (Label × GlobalType)) (hab : a ≠ b) :
    Dual (project (GlobalType.choice a b bs) a) (project (GlobalType.choice a b bs) b) := by
  simp only [project, if_true, if_neg hab.symm, Dual]

/- **`NoSelfComm G`** — no communication or choice has a role talking to itself
(`src ≠ dst` everywhere, including inside every branch). The standard MPST well-scoping
side-condition; it is what guarantees the head action's two participants are *distinct*
roles (so head-duality applies — a self-loop `comm a a` would project to a single role
seeing both `send` and `recv`, which is not a two-party synchronisation). Cheap, genuine,
and orthogonal to `Projectable` (merge-success). -/
mutual
  /-- `NoSelfComm G` — no `comm`/`choice` has `src = dst` (anywhere, incl. every branch). -/
  def NoSelfComm : GlobalType → Prop
    | GlobalType.comm src dst _ cont => src ≠ dst ∧ NoSelfComm cont
    | GlobalType.choice src dst bs   => src ≠ dst ∧ NoSelfCommBranches bs
    | GlobalType.mu _ body           => NoSelfComm body
    | GlobalType.var _               => True
    | GlobalType.done                => True

  def NoSelfCommBranches : List (Label × GlobalType) → Prop
    | []             => True
    | (_, g) :: rest => NoSelfComm g ∧ NoSelfCommBranches rest
end

/-- Membership extraction for `NoSelfCommBranches`. -/
theorem noSelf_of_mem_branches : ∀ {bs : List (Label × GlobalType)} {ℓ : Label}
    {g : GlobalType}, NoSelfCommBranches bs → (ℓ, g) ∈ bs → NoSelfComm g
  | [], _, _, _, hmem => absurd hmem (by simp)
  | (ℓ', g') :: tl, ℓ, g, hns, hmem => by
      simp only [NoSelfCommBranches] at hns
      rcases List.mem_cons.mp hmem with heq | htl
      · obtain ⟨_, rfl⟩ := Prod.mk.injEq .. ▸ heq; exact hns.1
      · exact noSelf_of_mem_branches hns.2 htl

/-- `GStep` preserves `NoSelfComm` (the residual is a subterm / branch continuation). -/
theorem GStep.noSelf_preserved {G G' : GlobalType} (h : GStep G G') (hns : NoSelfComm G) :
    NoSelfComm G' := by
  cases h with
  | comm a b s k => exact hns.2
  | choice a b bs ℓ g hmem =>
      simp only [NoSelfComm] at hns
      exact noSelf_of_mem_branches hns.2 hmem

/-- `GReach` preserves `NoSelfComm`. -/
theorem GReach.noSelf_preserved {G G' : GlobalType} (h : GReach G G') (hns : NoSelfComm G) :
    NoSelfComm G' := by
  induction h with
  | refl => exact hns
  | step s _ ih => exact ih (s.noSelf_preserved (by assumption))

/-! ### The initial-projection statement is false — a kernel-checked counterexample.

Progress quantified over only the initial projections is false for a `Projectable` `G`. -/

/-- **`deadlock_initial_counterexample` (kernel-checked).** For `G = 0→2:⟨0⟩ . 0→1:⟨1⟩ . end`,
which is `Projectable` + `NoSelfComm` + `NoRec`: role `1` projects to `recv 0 1 done` (waiting)
but role `0`'s initial head is the sort-`0` send to `2`; the sort-`1` send to `1` is buried
beneath it. No initial projection has a sort-`1` `send`, so role `1` has no `Dual` partner
at the initial config — the partner appears only in the reachable residual after `0→2` fires.
The faithful progress statement must quantify over reachable configs. -/
theorem deadlock_initial_counterexample :
    ∃ (G : GlobalType), Projectable G ∧ NoSelfComm G ∧ NoRec G ∧
      ∃ p ∈ roles G, (project G p).waiting = true ∧
        ¬ ∃ q ∈ roles G, Dual (project G p) (project G q) := by
  refine ⟨GlobalType.comm 0 2 0 (GlobalType.comm 0 1 1 GlobalType.done), ?_, ?_, ?_, 1, ?_, ?_, ?_⟩
  · -- Projectable: no `choice`, so `MergesAt` is trivially `True` at every role.
    intro p _; simp only [MergesAt]
  · -- NoSelfComm: 0≠2 and 0≠1.
    refine ⟨by decide, ?_⟩; exact ⟨by decide, trivial⟩
  · -- NoRec: only comm/done.
    simp only [NoRec]
  · -- role 1 ∈ roles G.
    simp [roles]
  · -- role 1's projection is `recv 0 1 done` — waiting.
    decide
  · -- NO `Dual` partner among the initial projections.
    rintro ⟨q, hq, hdual⟩
    -- Reduce `roles G` to the concrete list `[0, 2, 0, 1]`, then case on which role `q` is and
    -- refute `Dual` by computation: q=0 ⇒ Dual (recv 0 1 _) (send 2 0 _) reduces to `(1:ℕ)=0`;
    -- q=2 and q=1 reduce to `Dual (recv …) (recv …) = False`.
    simp only [roles, rolesBranches, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;>
      simp [project, Dual] at hdual

/-! ### `deadlock_freedom_by_design` — restated over reachable configs and proved.

The Carbone–Montesi progress theorem: a reachable non-terminal config always has an enabled
communication. We prove it for the `NoRec` + `NoSelfComm` fragment. -/

/-- **`deadlock_freedom_by_design` — Carbone–Montesi progress.** A well-scoped (`NoSelfComm`),
recursion-free (`NoRec`) choreography is deadlock-free: every reachable non-`done` configuration
has an enabled communication — the two participants of its head action project to a `Dual` pair.
The old form (over initial projections) is false (`deadlock_initial_counterexample`); the
correct statement quantifies over `GReach G G'`. -/
theorem deadlock_freedom_by_design
    (G : GlobalType) (hnr : NoRec G) (hns : NoSelfComm G)
    (G' : GlobalType) (hreach : GReach G G') (hdone : G' ≠ GlobalType.done) :
    ∃ (a b : Role), a ≠ b ∧ Dual (project G' a) (project G' b) := by
  have hnr' : NoRec G' := hreach.noRec_preserved hnr
  have hns' : NoSelfComm G' := hreach.noSelf_preserved hns
  -- Case on the head constructor of `G'`: `mu`/`var` excluded by `NoRec`, `done` by hypothesis.
  cases G' with
  | comm a b s k =>
      have hab : a ≠ b := hns'.1
      exact ⟨a, b, hab, dual_comm_heads s k hab⟩
  | choice a b bs =>
      have hab : a ≠ b := hns'.1
      exact ⟨a, b, hab, dual_choice_heads bs hab⟩
  | mu X body => exact absurd hnr' (by simp [NoRec])
  | var X => exact absurd hnr' (by simp [NoRec])
  | done => exact absurd rfl hdone

/- **`Guarded G`** — every `choice` has at least one branch (no empty external choice
`a → b : {}`, which is itself a stuck state with no branch to select). The
standard MPST well-formedness side-condition for the *progress-step* form: an empty
`offer`/`select` is stuck not because of any reachability gap but because there is
literally nothing to fire. (For the `Dual`-pair form `deadlock_freedom_by_design` this is
NOT needed — an empty `choice` still projects to a `Dual` `select`/`offer` pair — so we
keep `Guarded` only here.) -/
mutual
  /-- `Guarded G` — every `choice` has a nonempty branch list (no empty external choice). -/
  def Guarded : GlobalType → Prop
    | GlobalType.comm _ _ _ cont => Guarded cont
    | GlobalType.choice _ _ bs   => bs ≠ [] ∧ GuardedBranches bs
    | GlobalType.mu _ body       => Guarded body
    | GlobalType.var _           => True
    | GlobalType.done            => True

  def GuardedBranches : List (Label × GlobalType) → Prop
    | []             => True
    | (_, g) :: rest => Guarded g ∧ GuardedBranches rest
end

/-- Membership extraction for `GuardedBranches`. -/
theorem guarded_of_mem_branches : ∀ {bs : List (Label × GlobalType)} {ℓ : Label}
    {g : GlobalType}, GuardedBranches bs → (ℓ, g) ∈ bs → Guarded g
  | [], _, _, _, hmem => absurd hmem (by simp)
  | (ℓ', g') :: tl, ℓ, g, hg, hmem => by
      simp only [GuardedBranches] at hg
      rcases List.mem_cons.mp hmem with heq | htl
      · obtain ⟨_, rfl⟩ := Prod.mk.injEq .. ▸ heq; exact hg.1
      · exact guarded_of_mem_branches hg.2 htl

/-- `GStep` preserves `Guarded` (the residual is a subterm / branch continuation). -/
theorem GStep.guarded_preserved {G G' : GlobalType} (h : GStep G G') (hg : Guarded G) :
    Guarded G' := by
  cases h with
  | comm a b s k => exact hg
  | choice a b bs ℓ g hmem =>
      simp only [Guarded] at hg
      exact guarded_of_mem_branches hg.2 hmem

/-- `GReach` preserves `Guarded`. -/
theorem GReach.guarded_preserved {G G' : GlobalType} (h : GReach G G') (hg : Guarded G) :
    Guarded G' := by
  induction h with
  | refl => exact hg
  | step s _ ih => exact ih (s.guarded_preserved (by assumption))

/-- **`deadlock_freedom_progress_step` — progress as "can take a step".** Every reachable
non-`done` `NoRec` + `Guarded` residual has a `GStep` successor — the protocol is never stuck. -/
theorem deadlock_freedom_progress_step
    (G : GlobalType) (hnr : NoRec G) (hgrd : Guarded G)
    (G' : GlobalType) (hreach : GReach G G') (hdone : G' ≠ GlobalType.done) :
    ∃ G'', GStep G' G'' := by
  have hnr' : NoRec G' := hreach.noRec_preserved hnr
  have hgrd' : Guarded G' := hreach.guarded_preserved hgrd
  cases G' with
  | comm a b s k => exact ⟨k, GStep.comm a b s k⟩
  | choice a b bs =>
      -- `Guarded` gives `bs ≠ []`, so there is a head branch `(ℓ, g)` to fire.
      have hne : bs ≠ [] := hgrd'.1
      cases bs with
      | nil => exact absurd rfl hne
      | cons hd tl =>
          obtain ⟨ℓ, g⟩ := hd
          exact ⟨g, GStep.choice a b ((ℓ, g) :: tl) ℓ g (by simp)⟩
  | mu X body => exact absurd hnr' (by simp [NoRec])
  | var X => exact absurd hnr' (by simp [NoRec])
  | done => exact absurd rfl hdone

/- Axiom-hygiene: the LTS keystones rest only on the three standard kernel axioms. -/
#assert_axioms deadlock_freedom_by_design
#assert_axioms deadlock_freedom_progress_step
#assert_axioms deadlock_initial_counterexample
#assert_axioms GStep.noRec_preserved
#assert_axioms GReach.noRec_preserved
#assert_axioms GStep.noSelf_preserved
#assert_axioms GReach.noSelf_preserved
#assert_axioms GStep.guarded_preserved
#assert_axioms GReach.guarded_preserved
#assert_axioms dual_comm_heads
#assert_axioms dual_choice_heads


end Dregg2.Coordination
