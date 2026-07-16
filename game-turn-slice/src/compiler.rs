//! # `StateConstraint` → `ConstraintExpr` compiler + bit-decomposition range gadget.
//!
//! ## The gap this closes (the de-risk finding)
//!
//! A game's rules are the executor referee `dregg_cell::program::CellProgram`
//! (`StateConstraint` teeth). The recursion-foldable custom-leaf adapter
//! [`dregg_circuit_prove::custom_leaf_adapter::cellprogram_to_descriptor2`] consumes a
//! DIFFERENT type — the circuit-DSL `dregg_circuit::dsl::circuit::CellProgram` (a
//! `CircuitDescriptor` of `ConstraintExpr`). There is NO bridge between them in-tree, and
//! the ORDERING teeth (`FieldGte`/`FieldLte`/`Monotonic`/…) do NOT lower as atoms — the DSL
//! has NO inequality primitive, and the naive range-`Lookup` form is REFUSED by the adapter
//! ("IR-v2 lookups target fixed-semantics declared tables only"). The de-risk PROVED,
//! hand-authored, that an HP-floor via bit-decomposition DOES lower. This module GENERALIZES
//! that: a compiler from executor teeth to `ConstraintExpr`s, with a real bit-decomposition
//! range gadget for the ordering teeth.
//!
//! ## The range gadget — how `≥` becomes bit constraints (NOT a `Lookup`)
//!
//! To assert a linear head `H(new, old) ≥ 0` where `H` is small (fits in `n` bits), emit:
//!   * `n` boolean columns `b_0..b_{n-1}`, each pinned by a `ConstraintExpr::Binary`;
//!   * one recomposition `ConstraintExpr::Polynomial`: `H − Σ_k 2^k·b_k == 0`.
//!
//! The Binary gates force `b_k ∈ {0,1}`; the recomposition forces `H = Σ 2^k b_k ∈ [0, 2ⁿ−1]`.
//! Because `2ⁿ ≪ p` (BabyBear `p ≈ 2³¹`), a NEGATIVE integer head lands at the field value
//! `p − |H| ≈ 2³¹`, which no `n`-bit sum can reach — so the recomposition is UNSAT and the leaf
//! does not prove. This is a genuine non-negativity range proof, sound through the real
//! STARK/FRI quotient (every constraint is a low-degree polynomial — no membership step). The
//! ordering teeth reduce to `H ≥ 0`:
//!
//! | tooth                              | head `H`                        |
//! |------------------------------------|---------------------------------|
//! | `FieldGte { i, v }`                | `new[i] − v`                    |
//! | `FieldLte { i, v }`                | `v − new[i]`                    |
//! | `FieldLteField { l, r }`           | `new[r] − new[l]`               |
//! | `FieldLteOther { i, o, δ }`        | `new[o] + δ − new[i]`           |
//! | `Monotonic { i }`                  | `new[i] − old[i]`               |
//! | `StrictMonotonic { i }`            | `new[i] − old[i] − 1`           |
//! | `InRangeTwoSided { i, lo, hi }`    | `new[i] − lo` AND `hi − new[i]` |
//! | `DeltaBounded { i, d }`            | `d − (new−old)` AND `d + (new−old)` |
//! | `AffineLe { Σ kⱼ·new[fⱼ] ≤ c }`    | `c − Σ kⱼ·new[fⱼ]`              |
//!
//! ## The clean (algebraic) teeth — a single `Polynomial`/`Binary`
//!
//! | tooth                              | `ConstraintExpr`                        |
//! |------------------------------------|-----------------------------------------|
//! | `FieldEquals { i, v }`             | `Polynomial(new[i] − v)`                |
//! | `SumEquals { idx, v }`             | `Polynomial(Σ new[idx] − v)`            |
//! | `AffineEq { Σ kⱼ·new[fⱼ] = c }`    | `Polynomial(Σ kⱼ·new[fⱼ] − c)`          |
//! | `FieldDelta { i, δ }`              | `Polynomial(new[i] − old[i] − δ)`       |
//! | `SumEqualsAcross { in, out }`      | `Polynomial(Σ new[in] − Σ old[in] − Σ new[out])` |
//! | `MonotonicSequence { i }`          | `Polynomial(new[i] − old[i] − 1)`       |
//! | `WriteOnce { i }`                  | `Polynomial(old[i]·(new[i] − old[i]))`  (zero-old free, nonzero-old frozen) |
//! | `MemberOf { i, {0,1} }`            | `Binary(new[i])`                        |
//! | `MemberOf { i, S }`               | `Polynomial(∏_{s∈S}(new[i] − s))`       |
//!
//! ## Named residuals (out of scope — precise blockers, not fakes)
//!
//! Teeth that read state the local trace does NOT carry, or that need a crypto carrier:
//!   * host/context reads (`SenderIs`, `SenderInSlot`, `SenderAuthorized`, `Renounced`,
//!     `BalanceGte/Lte`, `RateLimit*`, `TemporalGate`, `FieldGteHeight`, `RateBound`,
//!     `CooledSince`, `UntilEvent`, `SinceEvent`, `ChallengeWindow`, `DelegationEpochEquals`);
//!   * crypto / cross-cell / witness carriers (`PreimageGate`, `KeyRotationGate`,
//!     `TemporalPredicate`, `Witnessed`, `BoundDelta`, `Custom`, `CapabilityUniqueness`);
//!   * `AllowedTransitions` (a pair-disjunction — needs a per-pair selector / `TableFunction`
//!     lowering, the named follow-up).
//! These stack ON TOP of the adapter's own `ConstraintExpr`-level residuals (the fact-sponge
//! `Hash`, `MerkleHash8`, an unseeded `ChainedHash2to1`) — which this compiler never emits.

use std::collections::HashMap;

use dregg_cell::program::StateConstraint;
use dregg_cell::{WitnessedPredicate, WitnessedPredicateKind};
use dregg_circuit::dsl::circuit::{
    CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};
use dregg_circuit::dsl::descriptors::merkle_poseidon2_descriptor;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::merkle_types::compute_parent_poseidon2;

/// A precise refusal: the tooth kind and why it has no faithful local-trace carrier here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Blocker {
    pub tooth: &'static str,
    pub reason: String,
}

/// A concrete executor assignment that cannot be represented faithfully by this
/// single-BabyBear-limb game leaf.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessError {
    MissingSlot {
        side: &'static str,
        index: u8,
    },
    OutOfRange {
        side: &'static str,
        index: u8,
        value: u64,
        limit: u128,
    },
}

impl std::fmt::Display for Blocker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.tooth, self.reason)
    }
}

fn blocked(tooth: &'static str, reason: impl Into<String>) -> Blocker {
    Blocker {
        tooth,
        reason: reason.into(),
    }
}

/// A reference to a cell-state slot, on either side of the transition. In a leaf both sides
/// are ordinary witness columns on the same row (the range gadget compares `new[i]` to
/// `old[i]` as two columns — no cross-row window is needed).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum SlotRef {
    New(u8),
    Old(u8),
}

/// The witness-fill plan for one range gadget: the linear head `Σ termsⱼ + constant` (as a
/// signed integer over the assigned slot values) whose non-negativity the bit columns witness.
#[derive(Clone, Debug)]
struct RangeFill {
    tooth: &'static str,
    /// `(coeff, slot)` terms of the head, as signed integers.
    terms: Vec<(i128, SlotRef)>,
    /// The head's constant addend.
    constant: i128,
    /// The allocated bit columns (LSB first).
    bit_cols: Vec<usize>,
    /// The bit columns' names (for the witness map).
    bit_names: Vec<String>,
}

/// Read a `FieldElement`'s numeric value the way the executor does: big-endian u64 in the
/// last 8 bytes (`dregg_cell::program::field_from_u64`'s inverse).
fn field_low_u64(f: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// `x mod p` as a canonical `u32` (handles negative `x`).
fn fmod(x: i128) -> u32 {
    let p = BABYBEAR_P as i128;
    (((x % p) + p) % p) as u32
}

/// The compiler / lowering context. Allocates trace columns on demand (one per referenced
/// `new`/`old` slot, plus fresh bit columns per range gadget), accumulates the emitted
/// `ConstraintExpr`s, and records the range-gadget witness-fill plans. After lowering the
/// teeth, [`Self::finish`] assembles a real `dregg_circuit::dsl::circuit::CellProgram` and
/// [`Self::witness`] produces the trace witness for a concrete slot assignment.
pub struct GameProgramCompiler {
    name: String,
    /// Bit-width of the range gadgets. Must exceed the largest head any gated slot can take
    /// (a design parameter: `2^range_bits ≪ p` keeps the non-negativity proof sound).
    range_bits: usize,
    columns: Vec<ColumnDef>,
    col_of: HashMap<SlotRef, usize>,
    constraints: Vec<ConstraintExpr>,
    ranges: Vec<RangeFill>,
    public_input_count: usize,
    max_degree: usize,
}

impl GameProgramCompiler {
    pub fn new(name: impl Into<String>, range_bits: usize) -> Self {
        assert!(
            range_bits >= 1 && (1u128 << range_bits) < BABYBEAR_P as u128,
            "range_bits must keep 2^range_bits < p"
        );
        Self {
            name: name.into(),
            range_bits,
            columns: Vec::new(),
            col_of: HashMap::new(),
            constraints: Vec::new(),
            ranges: Vec::new(),
            public_input_count: 0,
            max_degree: 1,
        }
    }

    /// Declare a RAW public-input count with NO binding — every slot is committed by the
    /// in-circuit PI-commitment but constrained to NOTHING (a value the prover may publish
    /// freely). This is the shape the disease lives in; prefer [`Self::bind_public_input`],
    /// which makes each PI a CONSTRAINED output of the trace. Retained only for the door's
    /// state-binding prefix (`[old8 ‖ new8]`), whose lanes are fold-connected, not AIR-bound.
    pub fn with_public_inputs(mut self, n: usize) -> Self {
        self.public_input_count = self.public_input_count.max(n);
        self
    }

    /// **CONSTRAIN a public input.** Bind the `new`-side output slot `index` to the NEXT public
    /// input via a real `ConstraintExpr::PiBinding` (`local[col] − pi[idx] == 0`, lowered by the
    /// custom-leaf adapter to `Base(PiBinding{First,..})` — the validated foldable path). The
    /// bound slot is an ordinary trace column the teeth CONSTRAIN, so "this turn published
    /// `pi[idx] = winner`" becomes "`winner` is exactly what the constrained transition
    /// produced" — the structural cure for `boundaries: vec![]`: a published output that is
    /// bound AND derived, not merely bound. Returns the assigned `pi_index`.
    ///
    /// Call AFTER any door prefix has claimed the low PI slots (via [`Self::with_public_inputs`]):
    /// bindings are appended above `public_input_count`, so the caller controls the layout, exactly
    /// as `param-compose`/`automatafl` emit `[old8 ‖ new8 ‖ ..bound_app_pis]`.
    pub fn bind_public_input(&mut self, index: u8) -> usize {
        let col = self.slot_col(SlotRef::New(index));
        let pi_index = self.public_input_count;
        self.public_input_count += 1;
        self.constraints
            .push(ConstraintExpr::PiBinding { col, pi_index });
        pi_index
    }

    fn col_name(slot: SlotRef) -> String {
        match slot {
            SlotRef::New(i) => format!("new_{i}"),
            SlotRef::Old(i) => format!("old_{i}"),
        }
    }

    /// Allocate (or return) the value column carrying `slot`.
    fn slot_col(&mut self, slot: SlotRef) -> usize {
        if let Some(&c) = self.col_of.get(&slot) {
            return c;
        }
        let idx = self.columns.len();
        self.columns.push(ColumnDef {
            name: Self::col_name(slot),
            index: idx,
            kind: ColumnKind::Value,
        });
        self.col_of.insert(slot, idx);
        idx
    }

    /// Allocate `n` fresh boolean bit columns; returns `(indices, names)`.
    fn alloc_bits(&mut self, tag: &str, n: usize) -> (Vec<usize>, Vec<String>) {
        let mut idxs = Vec::with_capacity(n);
        let mut names = Vec::with_capacity(n);
        for k in 0..n {
            let idx = self.columns.len();
            let name = format!("bit_{tag}_{k}");
            self.columns.push(ColumnDef {
                name: name.clone(),
                index: idx,
                kind: ColumnKind::Binary,
            });
            idxs.push(idx);
            names.push(name);
        }
        (idxs, names)
    }

    fn note_degree(&mut self, d: usize) {
        if d > self.max_degree {
            self.max_degree = d;
        }
    }

    /// Emit a `Polynomial` constraint `Σ_j coeff_j·∏ cols_j + const == 0` (const via empty
    /// `col_indices`). `terms` are `(signed_coeff, columns)`.
    fn poly(terms: Vec<(i128, Vec<usize>)>, constant: i128) -> ConstraintExpr {
        let mut poly_terms: Vec<PolyTerm> = terms
            .into_iter()
            .map(|(c, cols)| PolyTerm {
                coeff: BabyBear::new(fmod(c)),
                col_indices: cols,
            })
            .collect();
        if constant % (BABYBEAR_P as i128) != 0 {
            poly_terms.push(PolyTerm {
                coeff: BabyBear::new(fmod(constant)),
                col_indices: vec![],
            });
        }
        ConstraintExpr::Polynomial { terms: poly_terms }
    }

    /// THE RANGE GADGET. Given a linear head `H = Σ (coeff, slot) + constant` that must be
    /// `≥ 0` (and small), allocate `range_bits` bit columns and emit:
    ///   * one `Binary` per bit, and
    ///   * a recomposition `Polynomial`: `H − Σ_k 2^k·b_k == 0`.
    /// Records the fill plan so [`Self::witness`] can decompose the concrete head into bits.
    fn emit_range(
        &mut self,
        tooth: &'static str,
        tag: &str,
        terms: Vec<(i128, SlotRef)>,
        constant: i128,
    ) -> Vec<ConstraintExpr> {
        let n = self.range_bits;
        // Materialize the head's slot columns.
        let col_terms: Vec<(i128, usize)> =
            terms.iter().map(|&(c, s)| (c, self.slot_col(s))).collect();
        let (bit_cols, bit_names) = self.alloc_bits(tag, n);

        let mut emitted = Vec::with_capacity(n + 1);
        // Binary pins.
        for &b in &bit_cols {
            emitted.push(ConstraintExpr::Binary { col: b });
        }
        // Recomposition: H − Σ 2^k b_k == 0.
        let mut poly: Vec<(i128, Vec<usize>)> =
            col_terms.iter().map(|&(c, col)| (c, vec![col])).collect();
        for (k, &b) in bit_cols.iter().enumerate() {
            poly.push((-(1i128 << k), vec![b]));
        }
        emitted.push(Self::poly(poly, constant));
        self.note_degree(2); // Binary is degree 2; the recomposition is linear.

        self.ranges.push(RangeFill {
            tooth,
            terms,
            constant,
            bit_cols,
            bit_names,
        });
        self.constraints.extend(emitted.clone());
        emitted
    }

    /// Emit a bare polynomial-equality tooth over the given `(coeff, slot)` head and constant
    /// (`Σ head + constant == 0`), returning the single emitted constraint.
    fn emit_poly_eq(&mut self, terms: Vec<(i128, SlotRef)>, constant: i128) -> Vec<ConstraintExpr> {
        let col_terms: Vec<(i128, Vec<usize>)> = terms
            .into_iter()
            .map(|(c, s)| (c, vec![self.slot_col(s)]))
            .collect();
        let c = Self::poly(col_terms, constant);
        self.constraints.push(c.clone());
        vec![c]
    }

    /// **THE COMPILER.** Lower one executor `StateConstraint` tooth into circuit
    /// `ConstraintExpr`(s), allocating any columns / bit witnesses it needs into `self`. The
    /// returned vec is the constraints this tooth contributed (also appended to `self`).
    /// Ordering teeth go through the bit-decomposition range gadget; the algebraic teeth
    /// become one `Polynomial`/`Binary`; the named residuals return a precise [`Blocker`].
    pub fn lower_state_constraint(
        &mut self,
        sc: &StateConstraint,
    ) -> Result<Vec<ConstraintExpr>, Blocker> {
        use StateConstraint as SC;
        match sc {
            // ---------- clean algebraic teeth ----------
            SC::FieldEquals { index, value } => {
                let v = field_low_u64(value) as i128;
                Ok(self.emit_poly_eq(vec![(1, SlotRef::New(*index))], -v))
            }
            SC::SumEquals { indices, value } => {
                let v = field_low_u64(value) as i128;
                let terms = indices.iter().map(|&i| (1i128, SlotRef::New(i))).collect();
                Ok(self.emit_poly_eq(terms, -v))
            }
            SC::AffineEq { terms, c } => {
                let ts = terms
                    .iter()
                    .map(|&(k, f)| (k as i128, SlotRef::New(f)))
                    .collect();
                Ok(self.emit_poly_eq(ts, -(*c as i128)))
            }
            SC::FieldDelta { index, delta } => {
                let d = field_low_u64(delta) as i128;
                Ok(self.emit_poly_eq(
                    vec![(1, SlotRef::New(*index)), (-1, SlotRef::Old(*index))],
                    -d,
                ))
            }
            SC::SumEqualsAcross {
                input_fields,
                output_fields,
            } => {
                // Σ new[in] − Σ old[in] − Σ new[out] == 0.
                let mut terms: Vec<(i128, SlotRef)> = Vec::new();
                for &i in input_fields {
                    terms.push((1, SlotRef::New(i)));
                    terms.push((-1, SlotRef::Old(i)));
                }
                for &o in output_fields {
                    terms.push((-1, SlotRef::New(o)));
                }
                Ok(self.emit_poly_eq(terms, 0))
            }
            SC::MonotonicSequence { seq_index } => {
                // new == old + 1.
                Ok(self.emit_poly_eq(
                    vec![
                        (1, SlotRef::New(*seq_index)),
                        (-1, SlotRef::Old(*seq_index)),
                    ],
                    -1,
                ))
            }
            SC::WriteOnce { index } => {
                // old·(new − old) == 0: zero-old admits any new; nonzero-old freezes.
                let new_c = self.slot_col(SlotRef::New(*index));
                let old_c = self.slot_col(SlotRef::Old(*index));
                let c = ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![old_c, new_c],
                        },
                        PolyTerm {
                            coeff: BabyBear::new(fmod(-1)),
                            col_indices: vec![old_c, old_c],
                        },
                    ],
                };
                self.note_degree(2);
                self.constraints.push(c.clone());
                Ok(vec![c])
            }
            SC::MemberOf { index, set } => {
                let new_c = self.slot_col(SlotRef::New(*index));
                if set.len() == 2 && set.contains(&0) && set.contains(&1) {
                    let c = ConstraintExpr::Binary { col: new_c };
                    self.note_degree(2);
                    self.constraints.push(c.clone());
                    Ok(vec![c])
                } else {
                    // ∏_{s∈S}(new − s) == 0. Degree |S|. Expand the product into a Polynomial.
                    let mut poly: Vec<PolyTerm> = vec![PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![],
                    }];
                    for &s in set {
                        // multiply running poly by (new_c − s).
                        let mut next: Vec<PolyTerm> = Vec::new();
                        for t in &poly {
                            let mut with_col = t.col_indices.clone();
                            with_col.push(new_c);
                            next.push(PolyTerm {
                                coeff: t.coeff,
                                col_indices: with_col,
                            });
                            next.push(PolyTerm {
                                coeff: t.coeff * BabyBear::new(fmod(-(s as i128))),
                                col_indices: t.col_indices.clone(),
                            });
                        }
                        poly = next;
                    }
                    let c = ConstraintExpr::Polynomial { terms: poly };
                    self.note_degree(set.len().max(1));
                    self.constraints.push(c.clone());
                    Ok(vec![c])
                }
            }

            // ---------- ordering teeth → the bit-decomposition range gadget ----------
            SC::FieldGte { index, value } => {
                let v = field_low_u64(value) as i128;
                Ok(self.emit_range(
                    "FieldGte",
                    &format!("gte_{index}"),
                    vec![(1, SlotRef::New(*index))],
                    -v,
                ))
            }
            SC::FieldLte { index, value } => {
                let v = field_low_u64(value) as i128;
                Ok(self.emit_range(
                    "FieldLte",
                    &format!("lte_{index}"),
                    vec![(-1, SlotRef::New(*index))],
                    v,
                ))
            }
            SC::FieldLteField {
                left_index,
                right_index,
            } => Ok(self.emit_range(
                "FieldLteField",
                &format!("ltef_{left_index}_{right_index}"),
                vec![
                    (1, SlotRef::New(*right_index)),
                    (-1, SlotRef::New(*left_index)),
                ],
                0,
            )),
            SC::FieldLteOther {
                index,
                other,
                delta,
            } => Ok(self.emit_range(
                "FieldLteOther",
                &format!("lteo_{index}_{other}"),
                vec![(1, SlotRef::New(*other)), (-1, SlotRef::New(*index))],
                *delta as i128,
            )),
            SC::Monotonic { index } => Ok(self.emit_range(
                "Monotonic",
                &format!("mono_{index}"),
                vec![(1, SlotRef::New(*index)), (-1, SlotRef::Old(*index))],
                0,
            )),
            SC::StrictMonotonic { index } => Ok(self.emit_range(
                "StrictMonotonic",
                &format!("smono_{index}"),
                vec![(1, SlotRef::New(*index)), (-1, SlotRef::Old(*index))],
                -1,
            )),
            SC::InRangeTwoSided { index, lo, hi } => {
                // new − lo ≥ 0  AND  hi − new ≥ 0.
                let mut out = self.emit_range(
                    "InRangeTwoSided(lo)",
                    &format!("range_lo_{index}"),
                    vec![(1, SlotRef::New(*index))],
                    -(*lo as i128),
                );
                out.extend(self.emit_range(
                    "InRangeTwoSided(hi)",
                    &format!("range_hi_{index}"),
                    vec![(-1, SlotRef::New(*index))],
                    *hi as i128,
                ));
                Ok(out)
            }
            SC::DeltaBounded { index, d } => {
                // |new − old| ≤ d  ⟺  d − (new−old) ≥ 0  AND  d + (new−old) ≥ 0.
                let mut out = self.emit_range(
                    "DeltaBounded(+)",
                    &format!("dbnd_hi_{index}"),
                    vec![(-1, SlotRef::New(*index)), (1, SlotRef::Old(*index))],
                    *d as i128,
                );
                out.extend(self.emit_range(
                    "DeltaBounded(-)",
                    &format!("dbnd_lo_{index}"),
                    vec![(1, SlotRef::New(*index)), (-1, SlotRef::Old(*index))],
                    *d as i128,
                ));
                Ok(out)
            }
            SC::AffineLe { terms, c } => {
                // c − Σ kⱼ·new[fⱼ] ≥ 0.
                let head = terms
                    .iter()
                    .map(|&(k, f)| (-(k as i128), SlotRef::New(f)))
                    .collect();
                Ok(self.emit_range("AffineLe", "affle", head, *c as i128))
            }

            // ---------- named residuals (precise blockers, not fakes) ----------
            SC::Immutable { .. } => Err(blocked(
                "Immutable",
                "the first-write init carve-out (old_state=None ⇒ nonce-0 admits) is a host/nonce \
                 fact the local trace does not carry; the pure new==old invariant would forbid the \
                 legitimate init write. Use WriteOnce (zero-old admits) for the lowerable form",
            )),
            SC::FieldDeltaInRange { .. } => Err(blocked(
                "FieldDeltaInRange",
                "two-sided relative delta band; lowerable via TWO range gadgets on \
                 (new−old−min_delta) and (max_delta−(new−old)) — a straightforward follow-up, not \
                 wired in this slice",
            )),
            SC::AllowedTransitions { .. } => Err(blocked(
                "AllowedTransitions",
                "an (old,new) pair allow-list is a disjunction; it lowers via a per-pair selector \
                 or a TableFunction over the (old,new) grid (the named follow-up), not a single \
                 local gate",
            )),
            SC::SenderIs { .. }
            | SC::SenderInSlot { .. }
            | SC::SenderAuthorized { .. }
            | SC::Renounced { .. } => Err(blocked(
                "Sender*/Authorized/Renounced",
                "reads the turn sender / a Merkle authorized-set membership proof — host context + \
                 a hash carrier the local trace does not hold",
            )),
            SC::BalanceGte { .. } | SC::BalanceLte { .. } => Err(blocked(
                "Balance*",
                "reads the cell's sealed kernel balance (not one of the 16 trace slots); a \
                 balance column + its effect-vm binding is the follow-up",
            )),
            SC::FieldGteHeight { .. }
            | SC::FieldLteHeight { .. }
            | SC::TemporalGate { .. }
            | SC::CooledSince { .. }
            | SC::ChallengeWindow { .. } => Err(blocked(
                "height/temporal",
                "reads ctx.block_height (external, receipt-snapshotted); no local-trace carrier — \
                 needs a height public input + binding",
            )),
            SC::RateLimit { .. } | SC::RateLimitBySum { .. } | SC::RateBound { .. } => {
                Err(blocked(
                    "rate",
                    "backed by an executor-side per-(cell,sender,epoch) counter — cross-turn state \
                     outside a single leaf",
                ))
            }
            SC::UntilEvent { .. } | SC::SinceEvent { .. } | SC::DelegationEpochEquals { .. } => {
                Err(blocked(
                    "event/epoch context",
                    "reads an OLD event register / the per-cell delegation_epoch stamp — context \
                     the single-leaf local trace does not carry faithfully",
                ))
            }
            SC::PreimageGate { .. } | SC::KeyRotationGate { .. } => Err(blocked(
                "preimage/rotation",
                "a Poseidon2/BLAKE3 preimage exhibit — a hash carrier (the adapter's Hash-site \
                 path), not a pure algebraic gate",
            )),
            SC::Witnessed { wp } => Err(blocked(
                "Witnessed",
                format!(
                    "a witness-attached predicate ({:?}) is NOT a per-row LOCAL gate — it lowers \
                     to its OWN foldable leaf, not into this per-turn game gate. MerkleMembership \
                     lowers via `lower_witnessed_merkle_membership` (the 4-ary Poseidon2 \
                     membership circuit → a foldable custom leaf, the same recurrence \
                     `MerkleAir`/the executor verifier checks); the other kinds \
                     (Temporal/Dfa/BlindedSet/Bridge/Custom) are each their own circuit, out of \
                     this per-gate slice",
                    wp.kind
                ),
            )),
            SC::TemporalPredicate { .. } | SC::Custom { .. } => Err(blocked(
                "temporal-predicate/custom",
                "a witness-attached proof verified by a registry verifier / DSL runtime — its \
                 own circuit, not a local gate",
            )),
            SC::BoundDelta { .. } => Err(blocked(
                "BoundDelta",
                "a CROSS-CELL bilateral delta match — spans two cells' traces; the aggregate γ.2 \
                 match loop, not a single-cell leaf",
            )),
            SC::CapabilityUniqueness { .. } => Err(blocked(
                "CapabilityUniqueness",
                "a structural check on a cap-set root commitment — a hash/merkle carrier, not a \
                 local gate",
            )),
            SC::PrefixOf { .. } | SC::Reachable { .. } => Err(blocked(
                "PrefixOf/Reachable",
                "path-prefix / DAG-reachability search — lowerable as a bounded gadget but not a \
                 single local gate; out of scope for this slice",
            )),
            SC::AnyOf { .. } | SC::AllOf { .. } => Err(blocked(
                "AnyOf/AllOf",
                "boolean composition — AllOf lowers by lowering each conjunct; AnyOf needs a \
                 selector-guarded disjunction gadget (the follow-up). Lower the leaves directly \
                 for now",
            )),
            SC::HeapField { .. } => Err(blocked(
                "HeapField",
                "constrains the unbounded heap map (fields_map), not a fixed register column; a \
                 heap-open carrier is the follow-up",
            )),
            SC::BoundedBy { .. } => Err(blocked(
                "BoundedBy",
                "a composable see-then-set (slot may change only if witness slot is nonzero) — a \
                 selector-guarded gate; the follow-up, not wired in this slice",
            )),
            SC::CountGe { .. } => Err(blocked(
                "CountGe",
                "an in-program M-of-N: the witness re-exhibits a committed set whose sorted-set \
                 commitment must match a slot — a hash/set carrier, not a local gate",
            )),
            SC::SenderMemberOf { .. } => Err(blocked(
                "SenderMemberOf",
                "reads the turn sender against a member board — host context, no local-trace carrier",
            )),
            SC::BalanceDeltaLte { .. } | SC::BalanceDeltaGte { .. } => Err(blocked(
                "BalanceDelta*",
                "a per-turn rate bound on the sealed kernel balance (not a trace slot); a balance \
                 column + effect-vm binding + a range gadget on the delta is the follow-up",
            )),
            // Any remaining variant is an unmapped residual (context / crypto / cross-cell
            // carrier the single-cell local trace does not hold). Named precisely, not faked.
            other => Err(blocked(
                "unmapped",
                format!("no faithful single-cell local-trace carrier in this slice for {other:?}"),
            )),
        }
    }

    /// Assemble the lowered teeth into a real circuit-DSL `CellProgram` (the type
    /// [`dregg_circuit_prove::custom_leaf_adapter::cellprogram_to_descriptor2`] consumes).
    pub fn finish(&self) -> CellProgram {
        let descriptor = CircuitDescriptor {
            name: self.name.clone(),
            trace_width: self.columns.len(),
            max_degree: self.max_degree,
            columns: self.columns.clone(),
            constraints: self.constraints.clone(),
            // No `BoundaryDef`s: PI bindings ride `ConstraintExpr::PiBinding` inside `constraints`
            // (from [`Self::bind_public_input`]), which the custom-leaf adapter lowers to
            // `Base(PiBinding{First,..})` — the validated foldable path automatafl/param-compose
            // use. A bound output is therefore a CONSTRAINED published PI, not a free value.
            boundaries: vec![],
            public_input_count: self.public_input_count,
            lookup_tables: vec![],
        };
        CellProgram::new(descriptor, 1)
    }

    /// The trace width (number of allocated columns).
    pub fn width(&self) -> usize {
        self.columns.len()
    }

    /// The emitted constraints so far.
    pub fn constraints(&self) -> &[ConstraintExpr] {
        &self.constraints
    }

    /// Produce the trace witness (`column name → per-row values`) for a concrete slot
    /// assignment, constant across `num_rows` rows (every constraint is local per-row). Fills
    /// each value column from the assignment and each range gadget's bit columns from the LSB
    /// decomposition of that gadget's integer head. A head that is negative or `≥ 2^range_bits`
    /// (a forgery / out-of-range value) yields bits that do NOT recompose it — so the leaf's
    /// recomposition constraint is UNSAT and the proof fails. Returns `(witness, num_rows)`.
    pub fn witness(
        &self,
        assign: &SlotAssignment,
        num_rows: usize,
    ) -> Result<HashMap<String, Vec<BabyBear>>, WitnessError> {
        let mut w: HashMap<String, Vec<BabyBear>> = HashMap::new();
        let limit = 1u128 << self.range_bits;

        // Value columns.
        for (slot, _) in &self.col_of {
            let name = Self::col_name(*slot);
            let (side, index, val) = match slot {
                SlotRef::New(i) => (
                    "new",
                    *i,
                    assign
                        .new_slots
                        .get(i)
                        .copied()
                        .ok_or(WitnessError::MissingSlot {
                            side: "new",
                            index: *i,
                        })?,
                ),
                SlotRef::Old(i) => (
                    "old",
                    *i,
                    assign
                        .old_slots
                        .get(i)
                        .copied()
                        .ok_or(WitnessError::MissingSlot {
                            side: "old",
                            index: *i,
                        })?,
                ),
            };
            if val as u128 >= limit {
                return Err(WitnessError::OutOfRange {
                    side,
                    index,
                    value: val,
                    limit,
                });
            }
            w.insert(name, vec![BabyBear::from_u64(val); num_rows]);
        }

        // Range-gadget bit columns: decompose the integer head into range_bits bits (LSB
        // first). The head is reduced mod p first (so a negative head lands at p−|H|, whose
        // low bits will NOT recompose it — the forgery-rejection mechanism).
        for r in &self.ranges {
            let mut head: i128 = r.constant;
            for &(coeff, slot) in &r.terms {
                let val = match slot {
                    SlotRef::New(i) => assign.new_slots[&i],
                    SlotRef::Old(i) => assign.old_slots[&i],
                };
                head += coeff * val as i128;
            }
            let canon = fmod(head); // canonical field rep of the head
            for (k, name) in r.bit_names.iter().enumerate() {
                let bit = (canon >> k) & 1;
                w.insert(name.clone(), vec![BabyBear::new(bit); num_rows]);
            }
        }

        Ok(w)
    }

    /// The range-gadget teeth this program carries (name + whether its head is in-range for a
    /// given assignment) — a diagnostic for the driving tests.
    pub fn range_head(&self, assign: &SlotAssignment, tooth_tag_bit0: usize) -> Option<i128> {
        self.ranges
            .iter()
            .find(|r| r.bit_cols.first() == Some(&tooth_tag_bit0))
            .map(|r| {
                let mut head = r.constant;
                for &(coeff, slot) in &r.terms {
                    let val = match slot {
                        SlotRef::New(i) => assign.new_slots.get(&i).copied().unwrap_or(0),
                        SlotRef::Old(i) => assign.old_slots.get(&i).copied().unwrap_or(0),
                    };
                    head += coeff * val as i128;
                }
                head
            })
    }

    /// Names of the range-gadget teeth (for reporting which ordering teeth are present).
    pub fn range_teeth(&self) -> Vec<&'static str> {
        self.ranges.iter().map(|r| r.tooth).collect()
    }
}

/// A concrete (old, new) slot-value assignment for building a leaf witness. Slot values are
/// the executor's big-endian-u64 numeric lane (games use small values well under `2^range_bits`).
#[derive(Clone, Debug, Default)]
pub struct SlotAssignment {
    pub new_slots: HashMap<u8, u64>,
    pub old_slots: HashMap<u8, u64>,
}

impl SlotAssignment {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn set_new(mut self, index: u8, value: u64) -> Self {
        self.new_slots.insert(index, value);
        self
    }
    pub fn set_old(mut self, index: u8, value: u64) -> Self {
        self.old_slots.insert(index, value);
        self
    }
}

// ===========================================================================
// The `Witnessed { MerkleMembership }` tooth → a foldable Poseidon2 membership leaf.
//
// The hidden-hand tooth (`dregg_multiway_tug::hidden_hand`) proves a play is a member
// of the committed hand root by a 4-ary Poseidon2 Merkle authentication path, checked
// IN THE CLEAR by the real cell evaluator + `WitnessedPredicateRegistry`. This is NOT a
// per-row local gate on the game-state columns — it is a MULTI-ROW circuit with its own
// trace (a hash level per row), so it lowers to its OWN foldable custom leaf rather than
// into the per-turn `GameProgramCompiler` gate. The leaf REUSES the deployed circuit-DSL
// `merkle_poseidon2_descriptor` (the same `MerkleHash` 4-ary recurrence
// `dregg_circuit::merkle_types::MerkleAir` proves and the executor verifier
// `compute_parent_poseidon2` walks), so the fold checks the identical relation Phase 2
// checks in the clear. The played cards NEVER enter the leaf's public inputs — the PIs
// are only `[leaf_commitment, hand_root]`, so the hand stays private-in-fold (the cards
// are not in the proof/PIs; the membership hides the rest of the hand).
// ===========================================================================

/// One Poseidon2 authentication level: the played node's position among its four siblings
/// (`0..=3`) plus the three sibling node values. Mirrors the executor tooth's `PathLevel`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MembershipLevel {
    pub position: u8,
    pub siblings: [BabyBear; 3],
}

/// A concrete 4-ary Poseidon2 membership witness: the committed leaf, the authentication
/// path (leaf → root), and the committed root. The `leaf` is the app-side blinded leaf
/// commitment (e.g. `hidden_hand::card_leaf`); this compiler stays game-agnostic and only
/// walks the Poseidon2 recurrence.
#[derive(Clone, Debug)]
pub struct MerkleMembershipWitness {
    pub leaf: BabyBear,
    pub levels: Vec<MembershipLevel>,
    pub root: BabyBear,
}

/// The foldable custom leaf a `Witnessed { MerkleMembership }` tooth lowers to: the
/// circuit-DSL `CellProgram` (`merkle_poseidon2_descriptor`), its per-column trace witness,
/// the row count (= path depth), and the public inputs `[leaf, root]` (the cards are NOT
/// among them — the hand is private-in-fold). Feed it to
/// `dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_with_commitment`.
pub struct LoweredMembership {
    pub program: CellProgram,
    pub witness_values: HashMap<String, Vec<BabyBear>>,
    pub num_rows: usize,
    pub public_inputs: Vec<BabyBear>,
}

/// Decode the 32-byte root commitment a `Witnessed { MerkleMembership }` predicate carries
/// (a canonical BabyBear `u32` in the low four LE bytes — the exact shape
/// `turn::executor::membership_verifier::root_felt_from_slot` reads and
/// `hidden_hand::root_to_bytes` writes) into its field element.
pub fn root_felt_from_commitment(bytes: &[u8; 32]) -> BabyBear {
    let mut b = [0u8; 4];
    b.copy_from_slice(&bytes[0..4]);
    BabyBear::new_canonical(u32::from_le_bytes(b))
}

/// **LOWER the hidden-hand tooth into the fold.** Given a `Witnessed { MerkleMembership }`
/// predicate and a concrete membership witness (leaf opening + authentication path + root),
/// build the foldable [`LoweredMembership`] leaf: the `merkle_poseidon2_descriptor` circuit
/// (the SAME 4-ary Poseidon2 recurrence the executor tooth checks in the clear) with a trace
/// that climbs the path to the committed root, and PIs `[leaf, root]`.
///
/// The lowering BINDS the tooth to the witness (non-vacuous): it decodes the predicate's
/// committed root and REFUSES if it disagrees with the witness root, walks the Poseidon2
/// path with [`compute_parent_poseidon2`] and REFUSES if it does not climb to that root (a
/// fabricated card / tampered path / wrong opening has no path to the root), and REFUSES a
/// non-`MerkleMembership` kind or a non-power-of-two depth (the base trace height must be a
/// power of two). The returned leaf proves iff an honest in-committed-hand play; a forged
/// one is refused here (before proving) or, if the caller corrupts the trace after lowering,
/// is UNSAT in the fold (the `MerkleHash` chip lookup / the root boundary pin bites).
pub fn lower_witnessed_merkle_membership(
    wp: &WitnessedPredicate,
    witness: &MerkleMembershipWitness,
) -> Result<LoweredMembership, Blocker> {
    if wp.kind != WitnessedPredicateKind::MerkleMembership {
        return Err(blocked(
            "Witnessed",
            format!(
                "lower_witnessed_merkle_membership called on a {:?} predicate; only \
                 MerkleMembership lowers to the 4-ary Poseidon2 membership leaf",
                wp.kind
            ),
        ));
    }
    // Bind the tooth's committed root to the witness — the leaf proves membership under the
    // EXACT root the executor tooth carries, not a free one.
    let committed = root_felt_from_commitment(&wp.commitment);
    if committed != witness.root {
        return Err(blocked(
            "Witnessed",
            format!(
                "the tooth's committed root {} does not match the witness root {}",
                committed.as_u32(),
                witness.root.as_u32()
            ),
        ));
    }
    let depth = witness.levels.len();
    if depth == 0 {
        return Err(blocked(
            "Witnessed",
            "an empty membership path has no foldable leaf".to_string(),
        ));
    }
    if !depth.is_power_of_two() {
        return Err(blocked(
            "Witnessed",
            format!(
                "membership path depth {depth} is not a power of two; the leaf's base trace \
                 height must be a power of two"
            ),
        ));
    }

    // Walk the 4-ary Poseidon2 path exactly as `MerkleAir` / the executor verifier does,
    // materializing the descriptor's per-column trace as we climb.
    let mut current = witness.leaf;
    let mut current_col = Vec::with_capacity(depth);
    let mut sib0 = Vec::with_capacity(depth);
    let mut sib1 = Vec::with_capacity(depth);
    let mut sib2 = Vec::with_capacity(depth);
    let mut position_col = Vec::with_capacity(depth);
    let mut parent_col = Vec::with_capacity(depth);
    for lvl in &witness.levels {
        if lvl.position > 3 {
            return Err(blocked(
                "Witnessed",
                format!(
                    "membership path position {} out of range 0..=3",
                    lvl.position
                ),
            ));
        }
        let parent = compute_parent_poseidon2(current, lvl.position, &lvl.siblings);
        current_col.push(current);
        sib0.push(lvl.siblings[0]);
        sib1.push(lvl.siblings[1]);
        sib2.push(lvl.siblings[2]);
        position_col.push(BabyBear::from_u64(lvl.position as u64));
        parent_col.push(parent);
        current = parent;
    }
    if current != witness.root {
        return Err(blocked(
            "Witnessed",
            format!(
                "the membership path does not climb to the committed root (fabricated card / \
                 tampered path / wrong opening): got {}, expected {}",
                current.as_u32(),
                witness.root.as_u32()
            ),
        ));
    }

    let mut witness_values = HashMap::new();
    witness_values.insert("current".to_string(), current_col);
    witness_values.insert("sib0".to_string(), sib0);
    witness_values.insert("sib1".to_string(), sib1);
    witness_values.insert("sib2".to_string(), sib2);
    witness_values.insert("position".to_string(), position_col);
    witness_values.insert("parent".to_string(), parent_col);

    Ok(LoweredMembership {
        program: CellProgram::new(merkle_poseidon2_descriptor(), 1),
        witness_values,
        num_rows: depth,
        // The cards are NOT here — only the (blinded) leaf commitment + the hand root.
        public_inputs: vec![witness.leaf, witness.root],
    })
}
