//! First-class **typed interfaces** for cells — the keystone of
//! CELLS-AS-SERVICE-OBJECTS (Stage 1).
//!
//! A cell already does method-dispatch: an [`crate::Action`] carries a
//! `method: Symbol` + `args`, and a [`CellProgram::Cases`] program can scope a
//! transition to a method via [`TransitionGuard::MethodIs`]. What was missing is
//! a first-class, on-cell, **typed** description of that interface that the cell
//! commitment binds and a light client can witness. This module is that
//! description.
//!
//! # The pieces
//!
//! 1. [`Semantics`] — the replayable-vs-service-cell distinction made a TYPED
//!    bit. A `Replayable` method is a pure verified-turn template (re-running it
//!    against the same pre-state reproduces the same post-state); a `Serviced`
//!    method is answered by the cell ACTING AS A SERVICE OBJECT — it reads other
//!    cells and produces a result that is NOT a pure replay (the OFE theorem
//!    `crossCellRead_refines_observedField` is the soundness prerequisite that a
//!    serviced read is itself provable).
//! 2. [`MethodSig`] — one method: its `symbol` (the BLAKE3 method-name hash an
//!    `Action` targets), the `args_schema` it expects, the `auth_required` to
//!    invoke it, and its `semantics`.
//! 3. [`InterfaceDescriptor`] — a named set of methods, **content-addressed** by
//!    its `interface_id` (the sorted-Poseidon2 root over the method leaves, the
//!    SAME machinery the cap-root uses).
//! 4. [`InterfaceRef`] — the on-cell reference the [`crate::Cell`] carries and the
//!    commitment binds: the `interface_id` plus the method count (so a verifier
//!    sees WHICH interfaces a cell exposes and HOW MANY methods each declares).
//!
//! # Auto-derivation (no new authoring)
//!
//! A cell that ALREADY does method-dispatch — a [`CellProgram::Cases`] program
//! with [`TransitionGuard::MethodIs`] guards — gets its `Replayable` interface
//! for FREE: [`InterfaceDescriptor::derive_replayable`] lifts each method-guard
//! into a [`MethodSig`] with [`Semantics::Replayable`]. The interface is then
//! exactly the methods the cell already implements, with no extra declaration.
//!
//! # S2+ follow-ons (named, NOT built this pass)
//!
//! - **the `invoke()` front door** — a first-class `Effect::Invoke { interface,
//!   method, args }` that the executor dispatches against the bound descriptor,
//!   so a caller targets a METHOD by interface rather than open-coding effects.
//! - **the `Serviced`-method receipt shape** — the receipt carrier for a serviced
//!   answer: the cross-cell reads it observed (the OFE-witnessed `ObservedField`
//!   set) + the produced result, so a light client can re-check a service answer.
//! - **the captp interface handshake** — exchanging an `InterfaceDescriptor` over
//!   the CapTP wire on `CapHello`, so a remote peer learns a cell's typed
//!   interface before invoking (the typed analogue of an E `Far` reference's
//!   method table).

use serde::{Deserialize, Serialize};

use crate::permissions::AuthRequired;
use crate::program::{CellProgram, TransitionGuard};
use crate::state::FieldElement;

/// A method symbol — the BLAKE3 hash of a method name, stored as a field
/// element. Identical in shape to `dregg_turn::action::Symbol` (a cell-side
/// mirror so this crate need not depend on `dregg-turn`): the value an
/// [`crate::Action::method`]-equivalent dispatch targets.
pub type Symbol = FieldElement;

/// Compute a method symbol from its name (BLAKE3, matching
/// `dregg_turn::action::symbol`).
pub fn method_symbol(name: &str) -> Symbol {
    *blake3::hash(name.as_bytes()).as_bytes()
}

/// **The replayable-vs-service distinction, made a typed bit.**
///
/// A cell is either re-running a pure template or acting as a service object.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Semantics {
    /// A **pure verified-turn template.** Re-executing the method against the
    /// same pre-state reproduces the same post-state — the light-client replay
    /// model the protocol already enforces for every ordinary turn. Every method
    /// auto-derived from a [`CellProgram::Cases`] guard is `Replayable`: a cell
    /// program's method-dispatch IS a replayable transition.
    Replayable,
    /// A **service-cell method.** The cell answers by READING the cells it serves
    /// (the OFE cross-cell read, `crossCellRead_refines_observedField`) and
    /// producing a result that is not a pure replay of its own pre-state. This is
    /// the typed marker for "this method makes the cell a service object"; the
    /// receipt shape that witnesses the serviced reads is an S2 follow-on.
    Serviced,
}

impl Semantics {
    /// The canonical 1-byte tag for content-addressing (`Replayable = 0`,
    /// `Serviced = 1`).
    #[inline]
    pub fn tag(self) -> u8 {
        match self {
            Semantics::Replayable => 0,
            Semantics::Serviced => 1,
        }
    }
}

/// The argument schema a method declares — a TYPED shape for the `args` vector an
/// invocation carries, kept deliberately small for S1.
///
/// Stage 1 fixes the schema at the granularity the executor already enforces: the
/// number of [`FieldElement`] arguments (an `Action` carries `args:
/// Vec<FieldElement>`). `Fixed(n)` declares "exactly `n` field-element args";
/// `Variadic` declares "any number" (the method reads its own arity). Richer
/// per-argument typing (felt vs cell-id vs commitment) is an S2 refinement; the
/// arity bound is the part the invoke() front door needs first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ArgsSchema {
    /// Exactly `0..=n` field-element arguments — the method takes a fixed arity.
    Fixed(u8),
    /// Any number of field-element arguments.
    Variadic,
}

impl ArgsSchema {
    /// The canonical bytes for content-addressing: a tag byte (`Fixed = 0`,
    /// `Variadic = 1`) followed by the arity for `Fixed`.
    fn commitment_bytes(self) -> [u8; 2] {
        match self {
            ArgsSchema::Fixed(n) => [0, n],
            ArgsSchema::Variadic => [1, 0],
        }
    }
}

/// **One method of an interface.**
///
/// Identified by `symbol` (the value a dispatch targets), with the `args_schema`
/// it expects, the `auth_required` to invoke it, and its `semantics` (replayable
/// template vs serviced read).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MethodSig {
    /// The method symbol (BLAKE3 method-name hash) a dispatch targets.
    pub symbol: Symbol,
    /// The typed shape of the `args` this method expects.
    pub args_schema: ArgsSchema,
    /// What a caller must hold to invoke this method.
    pub auth_required: AuthRequired,
    /// Whether this method is a pure replayable template or a serviced read.
    pub semantics: Semantics,
}

impl MethodSig {
    /// A replayable method (the default for an auto-derived method-guard): the
    /// given `symbol`, a `Variadic` arg schema (the program guard does not pin an
    /// arity), `AuthRequired::None` baseline auth, and [`Semantics::Replayable`].
    pub fn replayable(symbol: Symbol) -> Self {
        MethodSig {
            symbol,
            args_schema: ArgsSchema::Variadic,
            auth_required: AuthRequired::None,
            semantics: Semantics::Replayable,
        }
    }

    /// The 7-felt-equivalent canonical leaf of this method as a single Poseidon2
    /// felt — the SAME sorted-Poseidon2 machinery the cap-root uses. The leaf
    /// absorbs `[symbol_limbs(8), args_tag, args_n, auth_tag, semantics_tag]` so
    /// any change to ANY field (symbol, arity, auth, replay-vs-service) moves the
    /// leaf — and therefore the interface_id, and therefore the cell commitment.
    pub fn leaf_felt(&self) -> dregg_circuit::field::BabyBear {
        use dregg_circuit::field::BabyBear;
        use dregg_circuit::poseidon2::hash_many;

        let mut inputs: Vec<BabyBear> = Vec::with_capacity(12);
        // 8 limbs of the method symbol (the dispatch key).
        inputs.extend_from_slice(&BabyBear::encode_hash(&self.symbol));
        // args schema (tag + arity).
        let [args_tag, args_n] = self.args_schema.commitment_bytes();
        inputs.push(BabyBear::new(args_tag as u32));
        inputs.push(BabyBear::new(args_n as u32));
        // auth tag (the tier byte; Custom additionally folds its vk_hash).
        inputs.push(auth_tag_felt(&self.auth_required));
        // replay-vs-service.
        inputs.push(BabyBear::new(self.semantics.tag() as u32));
        hash_many(&inputs)
    }
}

/// Encode an [`AuthRequired`] into a single auth-tag felt, mirroring the cell
/// commitment's `auth_required_to_tag` (the tier byte for built-ins; for
/// `Custom { vk_hash }` the tier byte folded with the 8 vk_hash limbs, so two
/// `Custom`s with distinct vk_hashes yield distinct tags).
fn auth_tag_felt(auth: &AuthRequired) -> dregg_circuit::field::BabyBear {
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::poseidon2::hash_many;
    let tier = match auth {
        AuthRequired::None => 0u32,
        AuthRequired::Signature => 1,
        AuthRequired::Proof => 2,
        AuthRequired::Either => 3,
        AuthRequired::Impossible => 4,
        AuthRequired::Custom { .. } => 5,
    };
    match auth {
        AuthRequired::Custom { vk_hash } => {
            let mut inputs = Vec::with_capacity(9);
            inputs.push(BabyBear::new(tier));
            inputs.extend_from_slice(&BabyBear::encode_hash(vk_hash));
            hash_many(&inputs)
        }
        _ => BabyBear::new(tier),
    }
}

/// **A first-class, typed, content-addressed interface descriptor.**
///
/// A named set of [`MethodSig`]s. Its `interface_id` is the content address: the
/// sorted-Poseidon2 root over the method leaves (the SAME `cap_root` machinery),
/// so two descriptors with the same methods (in any order) share one id, and any
/// change to any method changes the id.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterfaceDescriptor {
    /// The content address: the sorted-Poseidon2 root over the method leaves
    /// (32-byte felt encoding). Recomputable from `methods` via
    /// [`InterfaceDescriptor::compute_interface_id`]; carried so a holder of the
    /// descriptor need not re-fold to identify it.
    pub interface_id: [u8; 32],
    /// The methods this interface declares.
    pub methods: Vec<MethodSig>,
}

impl InterfaceDescriptor {
    /// Build a descriptor from a set of methods, computing its `interface_id`.
    pub fn new(methods: Vec<MethodSig>) -> Self {
        let interface_id = Self::compute_interface_id(&methods);
        InterfaceDescriptor {
            interface_id,
            methods,
        }
    }

    /// Compute the content-address of a method set: the 32-byte encoding of the
    /// sorted-Poseidon2 root over the per-method leaves ([`MethodSig::leaf_felt`]).
    /// Order-independent (the leaves are SORTED before folding, exactly like the
    /// cap-root), so the id is canonical regardless of the order methods were
    /// declared in.
    ///
    /// The fold is a domain-separated Poseidon2 chain over the sorted leaves
    /// (`hash_many([acc, leaf])` per step from a fixed seed), the same Poseidon2
    /// machinery the cap-root and the v9 authority digest use. Sorting makes it
    /// canonical; the leaf-count seed binds the arity so `{a}` and `{a, a}` (were
    /// dedup ever bypassed) cannot collide.
    pub fn compute_interface_id(methods: &[MethodSig]) -> [u8; 32] {
        use dregg_circuit::field::BabyBear;
        use dregg_circuit::poseidon2::hash_many;
        let mut leaves: Vec<BabyBear> = methods.iter().map(MethodSig::leaf_felt).collect();
        leaves.sort_by_key(|f| f.as_u32());
        // Seed with a domain tag + the leaf count so the fold is arity-bound and
        // domain-separated from a bare cap/heap root.
        let mut acc = hash_many(&[BabyBear::new(0x1FACE), BabyBear::new(leaves.len() as u32)]);
        for leaf in &leaves {
            acc = hash_many(&[acc, *leaf]);
        }
        crate::commitment::felt_to_bytes32(acc)
    }

    /// Recompute the `interface_id` from the current `methods` and confirm it
    /// matches the stored value — the anti-forgery tooth for a descriptor decoded
    /// from outside a trust boundary (a turn body, gossip ingest, a snapshot).
    pub fn verify_id(&self) -> bool {
        Self::compute_interface_id(&self.methods) == self.interface_id
    }

    /// The on-cell reference for this descriptor (the value the cell carries and
    /// the commitment binds).
    pub fn as_ref(&self) -> InterfaceRef {
        InterfaceRef {
            interface_id: self.interface_id,
            method_count: self.methods.len() as u32,
        }
    }

    /// Look up a method by symbol.
    pub fn method(&self, symbol: &Symbol) -> Option<&MethodSig> {
        self.methods.iter().find(|m| &m.symbol == symbol)
    }

    /// **Auto-derive the REPLAYABLE interface a cell ALREADY implements** from its
    /// [`CellProgram`].
    ///
    /// A cell that does method-dispatch via [`CellProgram::Cases`] +
    /// [`TransitionGuard::MethodIs`] guards gets its interface for FREE: every
    /// distinct `MethodIs { method }` that appears in any case's guard (including
    /// nested `AnyOf`/`AllOf`) becomes a [`MethodSig::replayable`]. The methods
    /// are DEDUPLICATED (a method named in two cases yields one `MethodSig`) and
    /// the resulting `interface_id` is order-independent.
    ///
    /// A program with no method-dispatch (`None`, `Predicate`, `Circuit`, or
    /// `Cases` whose guards name no method) auto-derives the EMPTY interface — a
    /// cell that does not dispatch on method exposes no replayable methods.
    pub fn derive_replayable(program: &CellProgram) -> Self {
        let mut symbols: Vec<Symbol> = Vec::new();
        if let CellProgram::Cases(cases) = program {
            for case in cases {
                collect_method_symbols(&case.guard, &mut symbols);
            }
        }
        // Deduplicate (a method named in two cases is ONE method). Stable on
        // first appearance; the interface_id is order-independent anyway.
        symbols.dedup_by(|a, b| a == b);
        let mut seen: Vec<Symbol> = Vec::with_capacity(symbols.len());
        for s in symbols {
            if !seen.contains(&s) {
                seen.push(s);
            }
        }
        let methods = seen.into_iter().map(MethodSig::replayable).collect();
        Self::new(methods)
    }
}

impl InterfaceDescriptor {
    /// **Compile this interface into a `dregg_dfa::RouteTable`** — the keystone
    /// of CELLS-AS-SERVICE-OBJECTS Stage 2: *a cell's interface IS a route table*,
    /// and method dispatch is the verified DFA [`dregg_dfa::Router`]
    /// classification (linear-time, BLAKE3-committed, AIR-provable via
    /// `dregg_dfa::air`).
    ///
    /// Each [`MethodSig::symbol`] (the 32-byte BLAKE3 method-name hash) becomes an
    /// EXACT-MATCH route over its raw bytes → a [`dregg_dfa::RouteTarget::handler`]
    /// whose name is the lowercase hex of the symbol (see [`handler_for_symbol`]).
    /// A classification of a method symbol thus resolves, in the verified router,
    /// to exactly the handler naming the bound method.
    ///
    /// Distinctness is structural: every method symbol is a full 32-byte BLAKE3
    /// digest, so no symbol can be a byte-prefix of another — the exact-match
    /// `Pattern::word` routes never overlap, and the router's longest-match
    /// resolution is exact. The reuse here is total: NO hand-rolled dispatch; the
    /// `dfa` crate's [`dregg_dfa::RouteTableBuilder`] (and its BLAKE3 commitment)
    /// is the dispatch primitive.
    ///
    /// The returned table's [`dregg_dfa::RouteTable::commitment`] is a function of
    /// the routed symbols (and their handler names), so it is itself a content
    /// address of the dispatchable surface — a sibling to `interface_id`, in the
    /// DFA crate's own commitment scheme.
    pub fn to_route_table(&self) -> dregg_dfa::RouteTable {
        let mut builder = dregg_dfa::RouteTableBuilder::new();
        for m in &self.methods {
            builder = builder.route_pattern(
                dregg_dfa::Pattern::word(&m.symbol),
                dregg_dfa::RouteTarget::handler(handler_for_symbol(&m.symbol)),
            );
        }
        builder.compile()
    }

    /// Resolve a method by routing its `symbol` through THIS interface's
    /// [`dregg_dfa::Router`] — the verified-dispatch front door. Returns the
    /// matched [`MethodSig`] (and the handler name the router classified to) when
    /// `symbol` names a declared method, `None` otherwise.
    ///
    /// This is the soundness-bearing path the `Effect::Invoke` executor arm calls:
    /// the method is found by the SAME `dregg_dfa::Router::classify` a federation
    /// constitution audits, not by an ad-hoc `find`. The router's verdict and the
    /// descriptor's [`InterfaceDescriptor::method`] lookup must agree (the
    /// returned `MethodSig` is re-fetched from `methods` by the classified handler
    /// name); a mismatch yields `None`, fail-closed.
    pub fn route_method(&self, symbol: &Symbol) -> Option<&MethodSig> {
        let table = self.to_route_table();
        let router = dregg_dfa::Router::new(table);
        let class = router.classify(&symbol[..])?;
        let handler = match class.target {
            dregg_dfa::RouteTarget::Handler(name) => name.clone(),
            _ => return None,
        };
        // The router classified `symbol` to `handler`; re-derive the method the
        // handler names and confirm it is exactly the routed symbol (defense in
        // depth — the handler name IS the symbol hex, so this binds the verdict
        // back to a concrete declared method).
        self.methods
            .iter()
            .find(|m| handler_for_symbol(&m.symbol) == handler && &m.symbol == symbol)
    }

    /// **The route-MEMBERSHIP witness** that `method` belongs to this interface,
    /// as a serialized `dregg_dfa::AirTrace` over the interface's route table.
    ///
    /// `invoke()` is NOT a kernel effect — it DESUGARS to the underlying effect a
    /// method names. The one fact a light client must witness about the dispatch
    /// (beyond the underlying effect's existing circuit rung) is that the invoked
    /// method M is actually a member of the cell's COMMITTED interface. That fact
    /// is exactly "the route table derived from the committed
    /// [`InterfaceDescriptor`] accepts M's symbol bytes" — and the DFA's EXISTING
    /// route-membership AIR (`dregg_dfa::air`) witnesses it. No new in-circuit
    /// machinery: the same `AirTrace`/`verify_acceptance` pair the slot-caveat
    /// `WitnessedPredicateKind::Dfa` verifier already uses.
    ///
    /// Returns the serialized proof bytes together with the route-table
    /// commitment (`router_root`) the witness binds — the caller re-checks via
    /// [`InterfaceDescriptor::verify_route_membership`]. Returns `None` if
    /// `method` is not a declared method (no membership to witness).
    pub fn route_membership_witness(&self, method: &Symbol) -> Option<(Vec<u8>, [u8; 32])> {
        // Only a declared method has a membership witness (fail-closed).
        self.route_method(method)?;
        let table = self.to_route_table();
        let root = table.commitment;
        let air = dregg_dfa::compile_to_air_from_table(&table, &method[..]);
        Some((air.to_proof_bytes(), root))
    }

    /// Verify a [`InterfaceDescriptor::route_membership_witness`] for `method`:
    /// the serialized `AirTrace` must (a) bind THIS interface's route-table
    /// commitment, and (b) prove the DFA accepts `method`'s symbol bytes — i.e.
    /// M is a member of the committed interface. Reuses
    /// [`dregg_dfa::verify_acceptance`]; adds nothing in-circuit.
    pub fn verify_route_membership(&self, method: &Symbol, proof_bytes: &[u8]) -> bool {
        let root = self.to_route_table().commitment;
        matches!(
            dregg_dfa::verify_acceptance(root, &method[..], proof_bytes),
            Ok(true)
        )
    }
}

/// The canonical [`dregg_dfa::RouteTarget::handler`] name for a method symbol:
/// the lowercase hex of the 32-byte symbol. Reversible (a verifier can map a
/// classified handler back to the method it names) and auditable (a route table
/// derived from an interface is legible as "symbol-hex → handler").
pub fn handler_for_symbol(symbol: &Symbol) -> String {
    let mut s = String::with_capacity(64);
    for b in symbol.iter() {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// Walk a [`TransitionGuard`] and collect every method symbol it dispatches on
/// (the `MethodIs { method }` guards, including those nested under
/// `AnyOf`/`AllOf`).
fn collect_method_symbols(guard: &TransitionGuard, out: &mut Vec<Symbol>) {
    match guard {
        TransitionGuard::MethodIs { method } => out.push(*method),
        TransitionGuard::AnyOf(children) | TransitionGuard::AllOf(children) => {
            for child in children {
                collect_method_symbols(child, out);
            }
        }
        TransitionGuard::Always
        | TransitionGuard::EffectKindIs { .. }
        | TransitionGuard::SlotChanged { .. } => {}
    }
}

/// **The on-cell reference to an [`InterfaceDescriptor`]** — the value a
/// [`crate::Cell`] carries in `Cell::interfaces` and the cell commitment binds.
///
/// The cell carries the REFERENCE (the content-address + method count), not the
/// full descriptor: the descriptor is referenced by `interface_id`, and a holder
/// resolves the full method table out-of-band (or via the S2 captp handshake).
/// The commitment binding the `interface_id` is what makes "this cell exposes
/// THIS interface" a light-client-witnessable fact — change a method, the
/// `interface_id` changes, the cell commitment changes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterfaceRef {
    /// The content-address of the referenced [`InterfaceDescriptor`].
    pub interface_id: [u8; 32],
    /// How many methods the referenced interface declares (so a verifier sees the
    /// interface's surface area without resolving the full descriptor).
    pub method_count: u32,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::{StateConstraint, TransitionCase};

    fn cases_program(method_names: &[&str]) -> CellProgram {
        let cases = method_names
            .iter()
            .map(|name| TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: method_symbol(name),
                },
                constraints: vec![],
            })
            .collect();
        CellProgram::Cases(cases)
    }

    #[test]
    fn interface_id_is_order_independent() {
        let a = InterfaceDescriptor::new(vec![
            MethodSig::replayable(method_symbol("send")),
            MethodSig::replayable(method_symbol("dequeue")),
        ]);
        let b = InterfaceDescriptor::new(vec![
            MethodSig::replayable(method_symbol("dequeue")),
            MethodSig::replayable(method_symbol("send")),
        ]);
        assert_eq!(a.interface_id, b.interface_id);
        assert!(a.verify_id());
    }

    #[test]
    fn changing_a_method_changes_the_interface_id() {
        let base = InterfaceDescriptor::new(vec![MethodSig::replayable(method_symbol("send"))]);

        // Different symbol.
        let other_symbol =
            InterfaceDescriptor::new(vec![MethodSig::replayable(method_symbol("recv"))]);
        assert_ne!(base.interface_id, other_symbol.interface_id);

        // Same symbol, different auth.
        let other_auth = InterfaceDescriptor::new(vec![MethodSig {
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol("send"))
        }]);
        assert_ne!(base.interface_id, other_auth.interface_id);

        // Same symbol, different semantics (Replayable -> Serviced).
        let other_sem = InterfaceDescriptor::new(vec![MethodSig {
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol("send"))
        }]);
        assert_ne!(base.interface_id, other_sem.interface_id);

        // Same symbol, different arity.
        let other_args = InterfaceDescriptor::new(vec![MethodSig {
            args_schema: ArgsSchema::Fixed(2),
            ..MethodSig::replayable(method_symbol("send"))
        }]);
        assert_ne!(base.interface_id, other_args.interface_id);
    }

    #[test]
    fn derive_replayable_lifts_method_guards() {
        let program = cases_program(&["send", "dequeue"]);
        let iface = InterfaceDescriptor::derive_replayable(&program);

        assert_eq!(iface.methods.len(), 2);
        assert!(iface.method(&method_symbol("send")).is_some());
        assert!(iface.method(&method_symbol("dequeue")).is_some());
        // Auto-derived methods are all Replayable.
        for m in &iface.methods {
            assert_eq!(m.semantics, Semantics::Replayable);
        }
        // It equals the hand-built descriptor over the same methods.
        let hand = InterfaceDescriptor::new(vec![
            MethodSig::replayable(method_symbol("send")),
            MethodSig::replayable(method_symbol("dequeue")),
        ]);
        assert_eq!(iface.interface_id, hand.interface_id);
    }

    #[test]
    fn derive_replayable_deduplicates_and_walks_nested_guards() {
        // `send` appears twice (once nested in an AnyOf); it must yield ONE method.
        let cases = vec![
            TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: method_symbol("send"),
                },
                constraints: vec![],
            },
            TransitionCase {
                guard: TransitionGuard::AnyOf(vec![
                    TransitionGuard::MethodIs {
                        method: method_symbol("send"),
                    },
                    TransitionGuard::MethodIs {
                        method: method_symbol("close"),
                    },
                ]),
                constraints: vec![StateConstraint::Immutable { index: 0 }],
            },
        ];
        let iface = InterfaceDescriptor::derive_replayable(&CellProgram::Cases(cases));
        assert_eq!(iface.methods.len(), 2, "send must be deduplicated");
        assert!(iface.method(&method_symbol("send")).is_some());
        assert!(iface.method(&method_symbol("close")).is_some());
    }

    #[test]
    fn non_dispatching_program_derives_empty_interface() {
        // A pure-invariant Cases program (Always guard, no method) exposes no
        // replayable methods.
        let program = CellProgram::Cases(vec![TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![StateConstraint::Monotonic { index: 0 }],
        }]);
        let iface = InterfaceDescriptor::derive_replayable(&program);
        assert!(iface.methods.is_empty());

        // None / Predicate / Circuit also derive empty.
        assert!(
            InterfaceDescriptor::derive_replayable(&CellProgram::None)
                .methods
                .is_empty()
        );
        assert!(
            InterfaceDescriptor::derive_replayable(&CellProgram::Predicate(vec![]))
                .methods
                .is_empty()
        );
    }

    #[test]
    fn interface_compiles_to_route_table_and_routes_each_method() {
        let iface = InterfaceDescriptor::new(vec![
            MethodSig::replayable(method_symbol("send")),
            MethodSig::replayable(method_symbol("dequeue")),
            MethodSig {
                auth_required: AuthRequired::Signature,
                ..MethodSig::replayable(method_symbol("close"))
            },
        ]);

        // Every declared method routes — via the dfa Router — to itself.
        for name in &["send", "dequeue", "close"] {
            let sym = method_symbol(name);
            let m = iface
                .route_method(&sym)
                .unwrap_or_else(|| panic!("method {name} must route"));
            assert_eq!(m.symbol, sym);
        }

        // An undeclared method does NOT route (fail-closed).
        assert!(iface.route_method(&method_symbol("undeclared")).is_none());

        // The route table is deterministic + commitment-bound (the dfa BLAKE3
        // commitment), and order-independent in routing outcome.
        let t1 = iface.to_route_table();
        let t2 = iface.to_route_table();
        assert_eq!(t1.commitment, t2.commitment);
    }

    #[test]
    fn route_membership_witness_proves_declared_method_and_rejects_others() {
        let iface = InterfaceDescriptor::new(vec![
            MethodSig::replayable(method_symbol("send")),
            MethodSig::replayable(method_symbol("dequeue")),
        ]);

        // A declared method yields a membership witness that verifies against
        // THIS interface's committed route table — via the EXISTING dfa AIR.
        let send = method_symbol("send");
        let (proof, root) = iface
            .route_membership_witness(&send)
            .expect("declared method has a membership witness");
        assert_eq!(root, iface.to_route_table().commitment);
        assert!(iface.verify_route_membership(&send, &proof));

        // An undeclared method has NO membership witness (fail-closed).
        assert!(
            iface
                .route_membership_witness(&method_symbol("undeclared"))
                .is_none()
        );

        // A witness for one method does not verify as membership of another.
        let dequeue = method_symbol("dequeue");
        assert!(!iface.verify_route_membership(&dequeue, &proof));

        // A witness does not verify against a DIFFERENT interface (different
        // committed route-table root).
        let other = InterfaceDescriptor::new(vec![MethodSig::replayable(method_symbol("send"))]);
        // `other` has a different method set ⇒ different route-table commitment,
        // so the `send` witness minted against `iface` must not verify here.
        assert_ne!(other.to_route_table().commitment, root);
        assert!(!other.verify_route_membership(&send, &proof));
    }

    #[test]
    fn route_table_router_verdict_matches_descriptor_lookup() {
        let iface = InterfaceDescriptor::new(vec![
            MethodSig::replayable(method_symbol("alpha")),
            MethodSig::replayable(method_symbol("beta")),
        ]);
        // The verified router and the descriptor's own `method()` lookup agree.
        for name in &["alpha", "beta"] {
            let sym = method_symbol(name);
            assert_eq!(
                iface.route_method(&sym).map(|m| m.symbol),
                iface.method(&sym).map(|m| m.symbol),
            );
        }
    }

    #[test]
    fn handler_name_is_reversible_symbol_hex() {
        let sym = method_symbol("send");
        let name = handler_for_symbol(&sym);
        assert_eq!(name.len(), 64);
        // The handler name uniquely identifies the symbol it was derived from.
        assert_ne!(name, handler_for_symbol(&method_symbol("recv")));
    }

    #[test]
    fn interface_ref_carries_id_and_count() {
        let iface = cases_program(&["a", "b", "c"]);
        let desc = InterfaceDescriptor::derive_replayable(&iface);
        let r = desc.as_ref();
        assert_eq!(r.interface_id, desc.interface_id);
        assert_eq!(r.method_count, 3);
    }
}
