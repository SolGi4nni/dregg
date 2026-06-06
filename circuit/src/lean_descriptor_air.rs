//! Generic Plonky3 AIR driven by a Lean-emitted circuit descriptor.
//!
//! This module is the FIRST concrete "swap": instead of hand-coding one AIR per
//! circuit, we ingest a *data-driven* descriptor — the Rust mirror of Lean's
//! `Dregg2.Exec.CircuitEmit.EmittedDescriptor` — and interpret it at `eval`-time
//! to drive the real `p3-uni-stark` prover. Lean becomes the verified
//! source-of-truth for the circuit's algebraic statement; Plonky3 is the real
//! prover.
//!
//! ## The descriptor shape (mirrors `CircuitEmit.lean`)
//!
//! ```text
//! EmittedExpr        = var Nat | const Int | add e e | mul e e
//! EmittedConstraint  = { lhs : EmittedExpr, rhs : EmittedExpr }   -- lhs = rhs
//! EmittedDescriptor  = { name, traceWidth, constraints }
//! ```
//!
//! A constraint `lhs = rhs` means the polynomial `lhs - rhs` must vanish on the
//! witness row. The witness layout is implicit: variable index `i` is column `i`
//! of the trace row (exactly as `Circuit.encode` in Lean).
//!
//! ## How this differs from the hand-coded AIRs
//!
//! `P3MerklePoseidon2Air` (in `plonky3_prover.rs`) hard-codes its Poseidon2 round
//! constraints in Rust. `LeanDescriptorAir` instead WALKS the `LeanExpr` AST at
//! `eval`-time, building the same `AB::Expr` polynomial the descriptor names. The
//! generic AIR therefore enforces *whatever* constraints Lean emitted — the same
//! machinery serves the kernel `transferCircuit`, the full-state `StateCommit`
//! circuit, or any other Lean-emitted descriptor — without a per-circuit Rust AIR.
//!
//! ## Trace / soundness model
//!
//! The emitted constraints (PART I of `CircuitEmit.lean`) are PER-ROW polynomial
//! gates: there are no transition (`next`) or boundary (`first`/`last`) terms. So
//! a single satisfying witness row, repeated to a power-of-2 height, satisfies the
//! AIR on every row. A trace that breaks a gate makes that gate's polynomial
//! non-zero on every row, which the quotient/FRI check rejects (or the debug-build
//! prover panics on the constraint violation). The round-trip test below asserts
//! BOTH directions: a satisfying assignment proves+verifies, a tampered one is
//! rejected.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::{prove, verify};

use crate::field::{BABYBEAR_P, BabyBear};
use crate::plonky3_prover::{DreggProof, create_config, to_p3};

// ============================================================================
// PART 1 — Rust mirror of the Lean descriptor
// ============================================================================

/// The Rust mirror of Lean's `EmittedExpr` (`var`/`const`/`add`/`mul`).
///
/// `Var(i)` reads column `i` of the current trace row; `Const(c)` is a field
/// constant; `Add`/`Mul` are field operations. Identical in shape to the existing
/// data-driven `ConstraintExpr` AST, but kept minimal to match exactly what
/// `CircuitEmit.emitExpr` produces.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeanExpr {
    /// Column index into the current row (= Lean variable index).
    Var(usize),
    /// A signed integer constant (reduced into BabyBear at eval-time).
    Const(i64),
    /// Field addition.
    Add(Box<LeanExpr>, Box<LeanExpr>),
    /// Field multiplication.
    Mul(Box<LeanExpr>, Box<LeanExpr>),
}

impl LeanExpr {
    /// Convenience: `Var(i)`.
    pub fn var(i: usize) -> Self {
        LeanExpr::Var(i)
    }
    /// Convenience: `Const(c)`.
    pub fn constant(c: i64) -> Self {
        LeanExpr::Const(c)
    }
    /// Convenience: `Add(a, b)`.
    pub fn add(a: LeanExpr, b: LeanExpr) -> Self {
        LeanExpr::Add(Box::new(a), Box::new(b))
    }
    /// Convenience: `Mul(a, b)`.
    pub fn mul(a: LeanExpr, b: LeanExpr) -> Self {
        LeanExpr::Mul(Box::new(a), Box::new(b))
    }

    /// The maximum column index referenced by this expression, if any. Used to
    /// sanity-check `trace_width` against the constraints.
    fn max_var(&self) -> Option<usize> {
        match self {
            LeanExpr::Var(i) => Some(*i),
            LeanExpr::Const(_) => None,
            LeanExpr::Add(a, b) | LeanExpr::Mul(a, b) => match (a.max_var(), b.max_var()) {
                (Some(x), Some(y)) => Some(x.max(y)),
                (Some(x), None) | (None, Some(x)) => Some(x),
                (None, None) => None,
            },
        }
    }

    /// The total degree of this expression as a polynomial over the columns.
    /// `Const` = 0, `Var` = 1, `Add` = max, `Mul` = sum. Used to set the AIR's
    /// `max_constraint_degree` so the config's FRI blowup is sufficient.
    fn degree(&self) -> usize {
        match self {
            LeanExpr::Const(_) => 0,
            LeanExpr::Var(_) => 1,
            LeanExpr::Add(a, b) => a.degree().max(b.degree()),
            LeanExpr::Mul(a, b) => a.degree() + b.degree(),
        }
    }

    /// Evaluate this expression as an `AB::Expr` polynomial over the row columns.
    /// `Var(i)` → `local[i]`, `Const(c)` → field constant, `Add`/`Mul` → field ops.
    /// Mirrors how `P3MerklePoseidon2Air::eval` reads `local[..]` and combines.
    fn eval_expr<AB>(&self, local: &[AB::Var]) -> AB::Expr
    where
        AB: AirBuilder,
        AB::F: PrimeField32,
    {
        match self {
            LeanExpr::Var(i) => local[*i].into(),
            LeanExpr::Const(c) => const_to_expr::<AB>(*c),
            LeanExpr::Add(a, b) => a.eval_expr::<AB>(local) + b.eval_expr::<AB>(local),
            LeanExpr::Mul(a, b) => a.eval_expr::<AB>(local) * b.eval_expr::<AB>(local),
        }
    }
}

/// The Rust mirror of Lean's `EmittedConstraint`: the gate equation `lhs = rhs`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanConstraint {
    /// Left-hand side polynomial.
    pub lhs: LeanExpr,
    /// Right-hand side polynomial. The gate enforces `lhs - rhs == 0`.
    pub rhs: LeanExpr,
}

impl LeanConstraint {
    /// Build a constraint `lhs = rhs`.
    pub fn new(lhs: LeanExpr, rhs: LeanExpr) -> Self {
        LeanConstraint { lhs, rhs }
    }

    /// The constraint's polynomial degree: `max(deg lhs, deg rhs)` (since the
    /// enforced polynomial is `lhs - rhs`).
    fn degree(&self) -> usize {
        self.lhs.degree().max(self.rhs.degree())
    }
}

/// The Rust mirror of Lean's `Dregg2.Exec.CircuitEmit.RangeSpec`: a wire that must lie
/// in `[0, 2^bits)`.
///
/// This is the FIELD-SOUNDNESS tooth. The Lean circuit is sound over `ℤ`, but the Rust
/// ingestion maps `i64 → BabyBear` (modulus `p ≈ 2³¹`). Without a range check, a balance
/// set near `p` would WRAP and forge value. The AIR enforces `wire ∈ [0, 2^bits)` by
/// BIT-DECOMPOSITION (`bits` boolean aux columns recomposing to the wire), which is
/// UNSATISFIABLE on any wrapped value (it has no `bits`-bit preimage). The Lean side emits
/// only the bit-width `bits`, NOT the `2^bits` table (which is astronomically large).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RangeSpec {
    /// The wire (column) index in the BASE trace that must be range-checked.
    pub wire: usize,
    /// The bit-width `k`: the wire must lie in `[0, 2^k)`.
    pub bits: usize,
}

/// The Rust mirror of Lean's `EmittedDescriptor` (+ optional `ranges`): name, trace width,
/// constraints, and the field-soundness range checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanDescriptor {
    /// AIR identity string (carried for fingerprint/debug; does not affect the math).
    pub name: String,
    /// Number of distinct BASE wires = base trace width (variable index = column index).
    /// The full AIR trace is wider: it appends `Σ ranges.bits` boolean aux columns for the
    /// bit-decomposition range gates (see `air_width` / `aux_offset`).
    pub trace_width: usize,
    /// The constraint list. Every constraint `lhs = rhs` must hold on each row.
    pub constraints: Vec<LeanConstraint>,
    /// The range checks (`wire ∈ [0, 2^bits)`), enforced in the AIR by bit-decomposition.
    /// Empty (the default for descriptors that omit `"ranges"`) ⇒ no range gates, identical
    /// behaviour to the pre-range-check AIR (so existing goldens are unaffected).
    pub ranges: Vec<RangeSpec>,
}

impl LeanDescriptor {
    /// Build a descriptor with no range checks (back-compatible constructor).
    pub fn new(name: impl Into<String>, trace_width: usize, constraints: Vec<LeanConstraint>) -> Self {
        LeanDescriptor {
            name: name.into(),
            trace_width,
            constraints,
            ranges: Vec::new(),
        }
    }

    /// Build a descriptor WITH range checks.
    pub fn with_ranges(
        name: impl Into<String>,
        trace_width: usize,
        constraints: Vec<LeanConstraint>,
        ranges: Vec<RangeSpec>,
    ) -> Self {
        LeanDescriptor {
            name: name.into(),
            trace_width,
            constraints,
            ranges,
        }
    }

    /// The total number of boolean aux columns the range gates need (`Σ ranges.bits`). These
    /// are appended AFTER the `trace_width` base columns.
    fn total_range_bits(&self) -> usize {
        self.ranges.iter().map(|r| r.bits).sum()
    }

    /// The FULL AIR trace width: base wires plus all bit-decomposition aux columns.
    fn air_width(&self) -> usize {
        self.trace_width + self.total_range_bits()
    }

    /// The starting aux column index for the `r`-th range check (ranges are laid out in
    /// order, each consuming `bits` consecutive boolean columns after the base wires).
    fn aux_offset(&self, range_index: usize) -> usize {
        self.trace_width
            + self.ranges[..range_index].iter().map(|r| r.bits).sum::<usize>()
    }

    /// The maximum polynomial degree across all constraints (at least 1, so the
    /// quotient machinery is well-defined even for a trivial constraint list). The range
    /// gates add a degree-2 booleanity constraint (`b·(b−1)`) per aux bit, so when any
    /// range check is present the AIR degree is at least 2.
    fn max_degree(&self) -> usize {
        let arith = self
            .constraints
            .iter()
            .map(LeanConstraint::degree)
            .max()
            .unwrap_or(1)
            .max(1);
        // Booleanity `b·(b−1) = 0` is degree 2; recomposition `Σ bᵢ·2ⁱ − wire = 0` is degree 1.
        let range_deg = if self.ranges.is_empty() { 0 } else { 2 };
        arith.max(range_deg)
    }

    /// Validate that every variable index (in constraints AND range specs) is within
    /// `trace_width`, and that each range `bits` is sane. Returns a descriptive error.
    fn check_var_bounds(&self) -> Result<(), String> {
        for (ci, c) in self.constraints.iter().enumerate() {
            let mv = c.lhs.max_var().into_iter().chain(c.rhs.max_var()).max();
            if let Some(m) = mv {
                if m >= self.trace_width {
                    return Err(format!(
                        "constraint {} references column {} but trace_width is {}",
                        ci, m, self.trace_width
                    ));
                }
            }
        }
        for (ri, r) in self.ranges.iter().enumerate() {
            if r.wire >= self.trace_width {
                return Err(format!(
                    "range {} checks column {} but trace_width is {}",
                    ri, r.wire, self.trace_width
                ));
            }
            // 0 bits = range [0,1) = {0}, valid but degenerate; cap at 63 so `1i64 << bit`
            // (used in the trace builder) never overflows i64.
            if r.bits > 63 {
                return Err(format!(
                    "range {} on column {} has bits {} > 63 (would overflow i64 weights)",
                    ri, r.wire, r.bits
                ));
            }
        }
        Ok(())
    }
}

// ============================================================================
// PART 1b — JSON decode: parse a Lean-emitted descriptor string into LeanDescriptor
// ============================================================================
//
// Lean's `Dregg2.Exec.CircuitEmit.emitDescriptorJson` renders an `EmittedDescriptor`
// to this exact grammar (see the doc-comment on the Lean def):
//
//   {"name":S,"trace_width":N,"constraints":[{"lhs":<expr>,"rhs":<expr>},…]}
//   <expr> = {"t":"var","v":i} | {"t":"const","v":c}
//          | {"t":"add","l":<expr>,"r":<expr>} | {"t":"mul","l":<expr>,"r":<expr>}
//
// We hand-roll a minimal recursive-descent parser for THIS FIXED schema rather than
// pull in serde_json (not a dependency of this crate; only `serde` derive is). The
// emitter is whitespace-free and key order is fixed, but the parser tolerates
// arbitrary whitespace and does not rely on key order — it scans for the keys it
// needs. This keeps the swap a pure additive change with no new crate dependency.

/// A tiny cursor over the JSON bytes (whitespace-skipping, fixed-schema).
struct JsonCursor<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> JsonCursor<'a> {
    fn new(s: &'a str) -> Self {
        JsonCursor { s: s.as_bytes(), i: 0 }
    }

    fn skip_ws(&mut self) {
        while self.i < self.s.len() && (self.s[self.i] as char).is_whitespace() {
            self.i += 1;
        }
    }

    fn peek(&mut self) -> Option<u8> {
        self.skip_ws();
        self.s.get(self.i).copied()
    }

    /// Consume an exact byte, erroring with context on mismatch.
    fn expect(&mut self, c: u8) -> Result<(), String> {
        self.skip_ws();
        match self.s.get(self.i) {
            Some(&b) if b == c => {
                self.i += 1;
                Ok(())
            }
            Some(&b) => Err(format!(
                "expected '{}' at byte {}, found '{}'",
                c as char, self.i, b as char
            )),
            None => Err(format!("expected '{}' but hit end of input", c as char)),
        }
    }

    /// Parse a double-quoted string with no escape handling beyond what the Lean
    /// emitter produces (the only strings are the AIR name + the fixed keys/tags,
    /// none of which contain quotes or backslashes).
    fn parse_string(&mut self) -> Result<String, String> {
        self.expect(b'"')?;
        let start = self.i;
        while self.i < self.s.len() && self.s[self.i] != b'"' {
            // The fixed schema never escapes; a backslash would be unexpected.
            if self.s[self.i] == b'\\' {
                return Err(format!("unexpected escape in string at byte {}", self.i));
            }
            self.i += 1;
        }
        if self.i >= self.s.len() {
            return Err("unterminated string".to_string());
        }
        let out = std::str::from_utf8(&self.s[start..self.i])
            .map_err(|e| format!("invalid utf8 in string: {e}"))?
            .to_string();
        self.i += 1; // closing quote
        Ok(out)
    }

    /// Parse a (possibly negative) integer literal into i64.
    fn parse_int(&mut self) -> Result<i64, String> {
        self.skip_ws();
        let start = self.i;
        if self.peek() == Some(b'-') {
            self.i += 1;
        }
        let digits_start = self.i;
        while self.i < self.s.len() && self.s[self.i].is_ascii_digit() {
            self.i += 1;
        }
        if self.i == digits_start {
            return Err(format!("expected integer at byte {}", start));
        }
        std::str::from_utf8(&self.s[start..self.i])
            .ok()
            .and_then(|t| t.parse::<i64>().ok())
            .ok_or_else(|| format!("malformed integer at byte {}", start))
    }

    /// Expect a specific quoted key followed by a colon: `"key":`.
    fn expect_key(&mut self, key: &str) -> Result<(), String> {
        let got = self.parse_string()?;
        if got != key {
            return Err(format!("expected key \"{}\", found \"{}\"", key, got));
        }
        self.expect(b':')
    }
}

/// Parse one `<expr>` object: `{"t":"var"|"const"|"add"|"mul", …}`.
fn parse_expr(c: &mut JsonCursor) -> Result<LeanExpr, String> {
    c.expect(b'{')?;
    c.expect_key("t")?;
    let tag = c.parse_string()?;
    let expr = match tag.as_str() {
        "var" => {
            c.expect(b',')?;
            c.expect_key("v")?;
            let v = c.parse_int()?;
            if v < 0 {
                return Err(format!("negative variable index {v}"));
            }
            LeanExpr::Var(v as usize)
        }
        "const" => {
            c.expect(b',')?;
            c.expect_key("v")?;
            LeanExpr::Const(c.parse_int()?)
        }
        "add" | "mul" => {
            c.expect(b',')?;
            c.expect_key("l")?;
            let l = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("r")?;
            let r = parse_expr(c)?;
            if tag == "add" {
                LeanExpr::add(l, r)
            } else {
                LeanExpr::mul(l, r)
            }
        }
        other => return Err(format!("unknown expr tag \"{other}\"")),
    };
    c.expect(b'}')?;
    Ok(expr)
}

/// Parse one constraint object: `{"lhs":<expr>,"rhs":<expr>}`.
fn parse_constraint(c: &mut JsonCursor) -> Result<LeanConstraint, String> {
    c.expect(b'{')?;
    c.expect_key("lhs")?;
    let lhs = parse_expr(c)?;
    c.expect(b',')?;
    c.expect_key("rhs")?;
    let rhs = parse_expr(c)?;
    c.expect(b'}')?;
    Ok(LeanConstraint::new(lhs, rhs))
}

/// Parse one range-spec object: `{"wire":i,"bits":k}` (Lean's `RangeSpec.toJson`).
fn parse_range(c: &mut JsonCursor) -> Result<RangeSpec, String> {
    c.expect(b'{')?;
    c.expect_key("wire")?;
    let wire = c.parse_int()?;
    if wire < 0 {
        return Err(format!("negative range wire {wire}"));
    }
    c.expect(b',')?;
    c.expect_key("bits")?;
    let bits = c.parse_int()?;
    if bits < 0 {
        return Err(format!("negative range bits {bits}"));
    }
    c.expect(b'}')?;
    Ok(RangeSpec {
        wire: wire as usize,
        bits: bits as usize,
    })
}

/// **`parse_descriptor`** — decode a Lean-emitted descriptor string (the output of
/// `CircuitEmit.emitDescriptorJson` / `Transfer.transferDescriptorJson`) into a
/// `LeanDescriptor` the generic AIR can prove. This is the wire-decode half of the
/// swap: Lean emits the verified circuit's algebraic statement as JSON, Rust parses
/// it back into the AST the `LeanDescriptorAir` interprets at `eval`-time.
///
/// Grammar: `{"name":S,"trace_width":N,"constraints":[{"lhs":<e>,"rhs":<e>},…]}`.
/// Tolerant of whitespace; does not depend on key order within objects.
pub fn parse_descriptor(json: &str) -> Result<LeanDescriptor, String> {
    let mut c = JsonCursor::new(json);
    c.expect(b'{')?;

    let mut name: Option<String> = None;
    let mut trace_width: Option<usize> = None;
    let mut constraints: Option<Vec<LeanConstraint>> = None;
    // `ranges` is OPTIONAL (absent ⇒ []), so the existing goldens that omit it parse identically.
    let mut ranges: Option<Vec<RangeSpec>> = None;

    loop {
        // key
        let key = c.parse_string()?;
        c.expect(b':')?;
        match key.as_str() {
            "name" => name = Some(c.parse_string()?),
            "trace_width" => {
                let n = c.parse_int()?;
                if n < 0 {
                    return Err(format!("negative trace_width {n}"));
                }
                trace_width = Some(n as usize);
            }
            "constraints" => {
                c.expect(b'[')?;
                let mut v = Vec::new();
                if c.peek() == Some(b']') {
                    c.expect(b']')?;
                } else {
                    loop {
                        v.push(parse_constraint(&mut c)?);
                        match c.peek() {
                            Some(b',') => {
                                c.expect(b',')?;
                            }
                            Some(b']') => {
                                c.expect(b']')?;
                                break;
                            }
                            other => {
                                return Err(format!(
                                    "expected ',' or ']' in constraint array, found {:?}",
                                    other.map(|b| b as char)
                                ));
                            }
                        }
                    }
                }
                constraints = Some(v);
            }
            "ranges" => {
                c.expect(b'[')?;
                let mut v = Vec::new();
                if c.peek() == Some(b']') {
                    c.expect(b']')?;
                } else {
                    loop {
                        v.push(parse_range(&mut c)?);
                        match c.peek() {
                            Some(b',') => {
                                c.expect(b',')?;
                            }
                            Some(b']') => {
                                c.expect(b']')?;
                                break;
                            }
                            other => {
                                return Err(format!(
                                    "expected ',' or ']' in ranges array, found {:?}",
                                    other.map(|b| b as char)
                                ));
                            }
                        }
                    }
                }
                ranges = Some(v);
            }
            other => return Err(format!("unknown top-level key \"{other}\"")),
        }
        match c.peek() {
            Some(b',') => {
                c.expect(b',')?;
            }
            Some(b'}') => {
                c.expect(b'}')?;
                break;
            }
            other => {
                return Err(format!(
                    "expected ',' or '}}' in descriptor object, found {:?}",
                    other.map(|b| b as char)
                ));
            }
        }
    }

    let name = name.ok_or("descriptor missing \"name\"")?;
    let trace_width = trace_width.ok_or("descriptor missing \"trace_width\"")?;
    let constraints = constraints.ok_or("descriptor missing \"constraints\"")?;
    let ranges = ranges.unwrap_or_default();
    Ok(LeanDescriptor::with_ranges(name, trace_width, constraints, ranges))
}

// ============================================================================
// Field conversion: i64 -> BabyBear / AB::Expr (handles negatives)
// ============================================================================

/// Reduce a signed `i64` into a canonical `BabyBear`, handling negatives via the
/// field modulus. `c mod p` with the result lifted into `[0, p)`.
pub fn i64_to_babybear(c: i64) -> BabyBear {
    let p = BABYBEAR_P as i64;
    let r = ((c % p) + p) % p; // in [0, p)
    BabyBear::new(r as u32)
}

/// A signed integer constant as an `AB::Expr` over BabyBear. Negatives are
/// reduced modulo p first (the field has no native sign).
fn const_to_expr<AB>(c: i64) -> AB::Expr
where
    AB: AirBuilder,
    AB::F: PrimeField32,
{
    let bb = i64_to_babybear(c);
    AB::Expr::from(AB::F::from_u32(bb.as_u32()))
}

// ============================================================================
// PART 2 — The generic AIR
// ============================================================================

/// A GENERIC Plonky3 AIR that interprets a `LeanDescriptor` at `eval`-time.
///
/// `width()` is the descriptor's `trace_width`; `eval` walks each constraint's
/// `lhs`/`rhs` ASTs into `AB::Expr` polynomials over the current row and asserts
/// `lhs - rhs == 0`. This is the data-driven analogue of `P3MerklePoseidon2Air`:
/// same column-access pattern, but the constraint set comes from Lean, not Rust.
pub struct LeanDescriptorAir {
    /// The descriptor whose constraints this AIR enforces.
    pub desc: LeanDescriptor,
}

impl LeanDescriptorAir {
    /// Wrap a descriptor as an AIR.
    pub fn new(desc: LeanDescriptor) -> Self {
        LeanDescriptorAir { desc }
    }
}

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for LeanDescriptorAir {
    fn width(&self) -> usize {
        // The FULL trace width: base wires + bit-decomposition aux columns for the range gates.
        self.desc.air_width()
    }

    fn num_public_values(&self) -> usize {
        // The PART-I emitted constraints are pure per-row gates (no PiBinding);
        // public inputs are not consumed by this generic interpreter.
        0
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(self.desc.max_degree())
    }
}

impl<AB: AirBuilder> Air<AB> for LeanDescriptorAir
where
    AB::F: PrimeField32,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();

        // For each emitted constraint `lhs = rhs`, build both sides as AB::Expr
        // over the current row's columns and assert their difference vanishes.
        for c in &self.desc.constraints {
            let lhs = c.lhs.eval_expr::<AB>(local);
            let rhs = c.rhs.eval_expr::<AB>(local);
            builder.assert_zero(lhs - rhs);
        }

        // RANGE GATES (field-soundness). For each range `wire ∈ [0, 2^bits)`, the trace
        // carries `bits` boolean aux columns (the bit-decomposition of `wire`), laid out at
        // `[aux_offset(r), aux_offset(r) + bits)`. We enforce:
        //   (1) BOOLEANITY  per bit `b`:  `b·(b − 1) = 0`  ⇒  every aux cell ∈ {0,1}.
        //   (2) RECOMPOSITION:  `Σ bᵢ·2ⁱ = local[wire]`  ⇒  `wire` equals its bit-sum.
        // Together these force `wire ∈ [0, 2^bits)`: any out-of-range / field-WRAPPED value has
        // no `bits`-bit decomposition whose weighted sum recomposes to it, so the system is
        // UNSATISFIABLE on a forged wire. (With `2^bits = 2³² > p ≈ 2³¹`, a wrapped balance can
        // never be recomposed by booleans, closing the `i64 → BabyBear` value-forgery hole.)
        for (ri, r) in self.desc.ranges.iter().enumerate() {
            let off = self.desc.aux_offset(ri);
            // Accumulate `Σ bᵢ·2ⁱ` while doubling the weight each step (no i64 shift overflow).
            let mut recomposed: AB::Expr = AB::Expr::ZERO;
            let mut weight: AB::Expr = AB::Expr::ONE;
            for i in 0..r.bits {
                let bit: AB::Expr = local[off + i].into();
                // (1) booleanity: b·(b − 1) = 0.
                builder.assert_zero(bit.clone() * (bit.clone() - AB::Expr::ONE));
                // (2) accumulate b·2ⁱ.
                recomposed = recomposed + bit * weight.clone();
                weight = weight.clone() + weight; // 2ⁱ → 2ⁱ⁺¹
            }
            let wire: AB::Expr = local[r.wire].into();
            builder.assert_zero(recomposed - wire);
        }
    }
}

// ============================================================================
// PART 3 — Trace builder
// ============================================================================

/// The minimum trace height. p3-uni-stark needs a power-of-2 height; we use the
/// same small size the hand-coded AIRs prove at (depth-4 traces work end-to-end
/// in `plonky3_prover.rs`). Since the emitted gates are per-row, repeating one
/// satisfying row to this height keeps every row satisfying.
const MIN_TRACE_HEIGHT: usize = 4;

/// Build a `RowMajorMatrix<P3BabyBear>` from a single witness row by REPEATING it
/// to a power-of-2 height. The per-row gates hold on every copy of a satisfying
/// row, and fail on every copy of a tampered row — so repetition is sound for
/// this constraint class.
///
/// `assignment` has length `trace_width` (the BASE wire values; `i64` so callers can
/// pass signed values, reduced into the field here). The row is EXTENDED with the
/// bit-decomposition aux columns for every range check, in `ranges` order — exactly the
/// layout `LeanDescriptorAir::eval` reads (see `aux_offset`).
///
/// ## Range aux columns & how out-of-range FAILS
///
/// For a range `wire ∈ [0, 2^bits)`, the aux columns are the `bits` LOW bits of the wire's
/// FIELD representative (`i64_to_babybear(v)`). If the wire is honestly in `[0, 2^bits)`, those
/// bits recompose to the field value and the AIR's recomposition gate `Σ bᵢ·2ⁱ = wire` holds.
/// If the wire is out of range (e.g. a field-WRAPPED forgery whose field value `≥ 2^bits`), the
/// low `bits` bits DROP the high bits, so `Σ bᵢ·2ⁱ ≠ wire` and the recomposition gate is VIOLATED
/// — the prover panics (debug) / the proof fails to verify (release). Thus no proof exists for an
/// out-of-range value. (Booleanity always holds since each emitted bit is 0/1 by construction; the
/// recomposition gate is what rejects the forgery.)
pub fn build_trace(desc: &LeanDescriptor, assignment: &[i64]) -> RowMajorMatrix<P3BabyBear> {
    assert_eq!(
        assignment.len(),
        desc.trace_width,
        "assignment length {} must equal trace_width {}",
        assignment.len(),
        desc.trace_width
    );

    let height = MIN_TRACE_HEIGHT; // already a power of two
    let width = desc.air_width().max(1);

    // The single row, as P3BabyBear: base wires followed by the range aux (bit) columns.
    let row: Vec<P3BabyBear> = if desc.air_width() == 0 {
        // Degenerate: no columns at all. p3 still needs width >= 1; emit a zero column.
        vec![P3BabyBear::ZERO]
    } else {
        let mut row: Vec<P3BabyBear> = Vec::with_capacity(width);
        // Base wires.
        for &v in assignment {
            row.push(to_p3(i64_to_babybear(v)));
        }
        // Aux bit columns, one block per range (in order), the low `bits` bits of the
        // wire's field representative.
        for r in &desc.ranges {
            // The field representative of the (possibly wrapped) wire value, in [0, p).
            let field_val = i64_to_babybear(assignment[r.wire]).as_u32() as u64;
            for i in 0..r.bits {
                let bit = (field_val >> i) & 1;
                row.push(to_p3(BabyBear::new(bit as u32)));
            }
        }
        debug_assert_eq!(row.len(), width, "built row width must equal air_width");
        row
    };

    let mut values = Vec::with_capacity(height * width);
    for _ in 0..height {
        values.extend_from_slice(&row);
    }
    RowMajorMatrix::new(values, width)
}

// ============================================================================
// PART 4 — Prove / Verify API
// ============================================================================

/// Prove that `assignment` satisfies the Lean-emitted `desc`, using the real
/// p3-uni-stark prover with a `LeanDescriptorAir`.
///
/// Returns a `DreggProof` (the same proof type the hand-coded AIRs produce, so
/// downstream verification plumbing is unchanged). In debug builds, the p3 prover
/// PANICS if a constraint is violated; in release it produces a proof that
/// `verify_descriptor` then rejects. Either way a tampered assignment cannot
/// yield an accepted proof.
pub fn prove_descriptor(desc: &LeanDescriptor, assignment: &[i64]) -> Result<DreggProof, String> {
    desc.check_var_bounds()?;
    let config = create_config();
    let air = LeanDescriptorAir::new(desc.clone());
    let matrix = build_trace(desc, assignment);
    // No public inputs for the PART-I per-row gate class.
    let public: Vec<P3BabyBear> = vec![];
    Ok(prove(&config, &air, matrix, &public))
}

/// Verify a `DreggProof` against the Lean-emitted `desc`.
pub fn verify_descriptor(desc: &LeanDescriptor, proof: &DreggProof) -> Result<(), String> {
    let config = create_config();
    let air = LeanDescriptorAir::new(desc.clone());
    let public: Vec<P3BabyBear> = vec![];
    verify(&config, &air, proof, &public)
        .map_err(|e| format!("LeanDescriptorAir verification failed: {:?}", e))
}

/// Convenience: prove then verify a satisfying assignment end-to-end.
pub fn prove_and_verify_descriptor(
    desc: &LeanDescriptor,
    assignment: &[i64],
) -> Result<DreggProof, String> {
    let proof = prove_descriptor(desc, assignment)?;
    verify_descriptor(desc, &proof)?;
    Ok(proof)
}

// ============================================================================
// Test descriptor: the `transferCircuit` shape (hardcoded mirror of Lean)
// ============================================================================

/// A small descriptor mirroring the Lean `transferCircuit` shape: a conservation
/// gate plus two boolean (`bit == 1`) gates over a 6-wide trace.
///
/// Column layout (the implicit witness vector, var index = column):
/// - 0: srcPre   1: dstPre   2: srcPost   3: dstPost
/// - 4: bitA     5: bitB     (two "is-set" flags, each enforced `== 1`)
///
/// Gates:
/// - C1 (conservation): `srcPost + dstPost = srcPre + dstPre`
///   i.e. `srcPost + dstPost - srcPre - dstPre == 0`.
/// - C2: `bitA = 1`.
/// - C3: `bitB = 1`.
#[cfg(test)]
fn transfer_test_descriptor() -> LeanDescriptor {
    use LeanExpr::*;

    // C1: srcPost + dstPost = srcPre + dstPre
    let conservation = LeanConstraint::new(
        Add(Box::new(Var(2)), Box::new(Var(3))), // lhs: srcPost + dstPost
        Add(Box::new(Var(0)), Box::new(Var(1))), // rhs: srcPre + dstPre
    );

    // C2: bitA = 1
    let bit_a = LeanConstraint::new(Var(4), Const(1));

    // C3: bitB = 1
    let bit_b = LeanConstraint::new(Var(5), Const(1));

    LeanDescriptor::new(
        "dregg-transfer-test-v1",
        6,
        vec![conservation, bit_a, bit_b],
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The acceptance gate: a SATISFYING transfer assignment proves+verifies, and
    /// a TAMPERED one (breaking the conservation gate) is rejected. This proves the
    /// generic Lean-descriptor AIR genuinely enforces the emitted constraints.
    #[test]
    fn lean_descriptor_air_roundtrip() {
        let desc = transfer_test_descriptor();

        // ---- Satisfying assignment ----
        // srcPre=100, dstPre=20, srcPost=70, dstPost=50  (70+50 == 100+20 == 120)
        // bitA=1, bitB=1.
        let good = [100i64, 20, 70, 50, 1, 1];
        // Sanity: conservation holds and bits are 1.
        assert_eq!(good[2] + good[3], good[0] + good[1]);
        assert_eq!(good[4], 1);
        assert_eq!(good[5], 1);

        let proof = prove_and_verify_descriptor(&desc, &good)
            .expect("satisfying transfer assignment must prove and verify");

        // The proof verifies against the descriptor.
        verify_descriptor(&desc, &proof).expect("re-verify of satisfying proof must succeed");

        // ---- Tampered assignment: break conservation ----
        // srcPost bumped by 1 so srcPost+dstPost = 121 != 120.  Bits still 1.
        let bad = [100i64, 20, 71, 50, 1, 1];
        assert_ne!(bad[2] + bad[3], bad[0] + bad[1]);

        // In debug builds the p3 prover panics on the violated constraint; in
        // release it returns a proof that verification rejects. Either path means
        // the forgery is NOT accepted. We catch the panic so the test asserts the
        // soundness outcome uniformly across build profiles.
        let forged = std::panic::catch_unwind(|| {
            // prove may panic (debug) — catch it.
            let p = prove_descriptor(&desc, &bad)?;
            // if it didn't panic (release), verification must reject.
            verify_descriptor(&desc, &p)
        });

        match forged {
            // Prover panicked on the broken constraint: forgery rejected. Good.
            Err(_) => {}
            // Prover produced a proof: verification MUST have errored.
            Ok(verify_result) => {
                assert!(
                    verify_result.is_err(),
                    "TAMPERED transfer assignment MUST be rejected (conservation gate broken), \
                     but a proof verified"
                );
            }
        }

        // ---- Tampered assignment: break a bit gate ----
        // bitA = 2 (not 1).  Conservation still holds.
        let bad_bit = [100i64, 20, 70, 50, 2, 1];
        assert_eq!(bad_bit[2] + bad_bit[3], bad_bit[0] + bad_bit[1]);
        assert_ne!(bad_bit[4], 1);

        let forged_bit = std::panic::catch_unwind(|| {
            let p = prove_descriptor(&desc, &bad_bit)?;
            verify_descriptor(&desc, &p)
        });
        match forged_bit {
            Err(_) => {}
            Ok(verify_result) => {
                assert!(
                    verify_result.is_err(),
                    "TAMPERED bit assignment MUST be rejected (bit gate broken), \
                     but a proof verified"
                );
            }
        }
    }

    /// The EXACT JSON string Lean's `Dregg2.Circuit.Transfer.transferDescriptorJson`
    /// (`#eval transferDescriptorJson`) emits for the REAL `emittedTransfer` circuit —
    /// the verified `transferCircuit` serialized via `CircuitEmit.emitDescriptorJson`.
    /// Copied verbatim from `lake build Dregg2.Circuit.Transfer`'s `#eval` output.
    ///
    /// Wire layout (Transfer.lean §1): 0=srcPre 1=dstPre 2=srcPost 3=dstPost 4=amt
    /// 5=authBit 6=nonnegBit 7=availBit 8=distinctBit 9=srcLiveBit 10=dstLiveBit.
    /// Nine gates: six `bit == 1` guards + debit (`srcPost = srcPre + (-1)*amt`) +
    /// credit (`dstPost = dstPre + amt`) + conservation (`srcPost+dstPost = srcPre+dstPre`).
    const TRANSFER_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-transfer-v1","trace_width":11,"constraints":[{"lhs":{"t":"var","v":5},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":6},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":7},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":8},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":9},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":10},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":2},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}}},{"lhs":{"t":"var","v":3},"rhs":{"t":"add","l":{"t":"var","v":1},"r":{"t":"var","v":4}}},{"lhs":{"t":"add","l":{"t":"var","v":2},"r":{"t":"var","v":3}},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"var","v":1}}}]}"#;

    /// THE swap acceptance test: the REAL Lean-emitted `transferCircuit` (parsed from
    /// the JSON Lean actually prints) drives the real Plonky3 prover. A satisfying
    /// conserving-transfer witness proves+verifies; a tampered (value-forging) witness
    /// is rejected. This is the end-to-end "Lean emits → Rust proves" wire.
    #[test]
    fn lean_emitted_transfer_roundtrip() {
        // ---- Parse the EXACT Lean-emitted descriptor ----
        let desc = parse_descriptor(TRANSFER_DESCRIPTOR_JSON)
            .expect("Lean-emitted transfer descriptor must parse");

        // Structural check: the parsed descriptor matches the Lean facts
        // (#guard emittedTransfer.constraints.length == 9, traceWidth == 11).
        assert_eq!(desc.name, "dregg-transfer-v1");
        assert_eq!(desc.trace_width, 11);
        assert_eq!(desc.constraints.len(), 9);

        // Spot-check the debit gate (constraint index 6): lhs = Var(2) (srcPost),
        // rhs = Add(Var(0), Mul(Const(-1), Var(4))) = srcPre + (-1)*amt. This confirms
        // the parser rebuilt the real nested AST (incl. the negative constant), not a
        // flattened mirror.
        let debit = &desc.constraints[6];
        assert_eq!(debit.lhs, LeanExpr::Var(2));
        assert_eq!(
            debit.rhs,
            LeanExpr::add(LeanExpr::Var(0), LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(4)))
        );

        // ---- Satisfying witness: the kT0/goodTurn/goodPost example from Transfer.lean ----
        // Pre: src(0)=100, dst(1)=5. Turn: amt=30, authorized, 0<=30<=100, src!=dst,
        // both live. Post: srcPost=70, dstPost=35. All six guard bits = 1.
        //   debit:  70 == 100 + (-1)*30        ✓
        //   credit: 35 == 5 + 30               ✓
        //   conserve: 70+35 == 100+5  (105)    ✓
        // Layout: [srcPre, dstPre, srcPost, dstPost, amt, auth, nonneg, avail, distinct, srcLive, dstLive]
        let good = [100i64, 5, 70, 35, 30, 1, 1, 1, 1, 1, 1];
        assert_eq!(good[2], good[0] - good[4]); // debit
        assert_eq!(good[3], good[1] + good[4]); // credit
        assert_eq!(good[2] + good[3], good[0] + good[1]); // conservation
        for &bit in &good[5..11] {
            assert_eq!(bit, 1);
        }

        let proof = prove_and_verify_descriptor(&desc, &good)
            .expect("the REAL Lean-emitted transfer circuit must prove+verify a conserving witness");
        verify_descriptor(&desc, &proof)
            .expect("re-verify of the satisfying transfer proof must succeed");

        // ---- Tampered witness: forge value (break conservation) ----
        // dstPost bumped 35 -> 36: src still debited 70 but dst credited an extra unit,
        // so 70+36 = 106 != 105. This is the Orchard-class value-forgery the
        // conservation gate forbids. (Credit gate also breaks: 36 != 5+30.)
        let forged_value = [100i64, 5, 70, 36, 30, 1, 1, 1, 1, 1, 1];
        assert_ne!(forged_value[2] + forged_value[3], forged_value[0] + forged_value[1]);

        let tampered = std::panic::catch_unwind(|| {
            // In debug builds the p3 prover panics on the violated constraint; in
            // release it returns a proof that verification then rejects. Either path
            // means the forgery is NOT accepted.
            let p = prove_descriptor(&desc, &forged_value)?;
            verify_descriptor(&desc, &p)
        });
        match tampered {
            Err(_) => {} // prover panicked on the broken gate: forgery rejected
            Ok(verify_result) => assert!(
                verify_result.is_err(),
                "TAMPERED (value-forging) transfer witness MUST be rejected, but a proof verified"
            ),
        }

        // ---- Tampered witness: drop authorization (authBit != 1) ----
        // A conserving transfer (70/35) but authBit = 0: an unauthorized move. The
        // authority gate (Var(5) == 1) must reject it.
        let forged_auth = [100i64, 5, 70, 35, 30, 0, 1, 1, 1, 1, 1];
        assert_eq!(forged_auth[2] + forged_auth[3], forged_auth[0] + forged_auth[1]); // conserves
        assert_ne!(forged_auth[5], 1); // but not authorized

        let tampered_auth = std::panic::catch_unwind(|| {
            let p = prove_descriptor(&desc, &forged_auth)?;
            verify_descriptor(&desc, &p)
        });
        match tampered_auth {
            Err(_) => {}
            Ok(verify_result) => assert!(
                verify_result.is_err(),
                "UNAUTHORIZED transfer witness MUST be rejected (authority gate broken), \
                 but a proof verified"
            ),
        }
    }

    /// The EXACT JSON string Lean's `Dregg2.Circuit.Transfer.transferDescriptorRangedJson`
    /// (`#eval transferDescriptorRangedJson`) emits for the RANGE-CHECKED `emittedTransferRanged`
    /// circuit: the verified `transferCircuit` PLUS the four balance-wire range checks
    /// (`vSrcPre/vDstPre/vSrcPost/vDstPost ∈ [0, 2³⁰)`). Copied verbatim from
    /// `lake build Dregg2.Circuit.Transfer`'s `#eval` output. Identical to
    /// `TRANSFER_DESCRIPTOR_JSON` except for the appended `"ranges":[…]` field.
    ///
    /// k = 30 (NOT 32): BabyBear's modulus is `p = 2³¹ − 2²⁷ + 1 = 2013265921`, with
    /// `2³⁰ < p < 2³¹`. A `k`-bit range with `2^k > p` is VACUOUS — every field element already
    /// has a `k`-bit decomposition — so it would reject nothing. `k = 30` is the largest
    /// power-of-two bound below `p`, making the gate NON-VACUOUS: residues in `[2³⁰, p)` have no
    /// 30-bit decomposition and are rejected. See `Transfer.balanceRangeBits`.
    const TRANSFER_DESCRIPTOR_RANGED_JSON: &str = r#"{"name":"dregg-transfer-v1","trace_width":11,"constraints":[{"lhs":{"t":"var","v":5},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":6},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":7},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":8},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":9},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":10},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":2},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}}},{"lhs":{"t":"var","v":3},"rhs":{"t":"add","l":{"t":"var","v":1},"r":{"t":"var","v":4}}},{"lhs":{"t":"add","l":{"t":"var","v":2},"r":{"t":"var","v":3}},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"var","v":1}}}],"ranges":[{"wire":0,"bits":30},{"wire":1,"bits":30},{"wire":2,"bits":30},{"wire":3,"bits":30}]}"#;

    /// **THE field-soundness acceptance test.** The RANGE-CHECKED Lean-emitted transfer
    /// descriptor drives the real Plonky3 prover with bit-decomposition range gates on the four
    /// balance wires (`[0, 2³⁰)`). An honest in-range witness proves+verifies; a witness whose
    /// balance is set to a value `≥ 2³⁰` (a value whose field image collides with a small honest
    /// residue but whose intended over-ℤ meaning exceeds the bound) is REJECTED by the range gate.
    /// This closes the `i64 → BabyBear` value-forgery hole: over `ℤ` the conservation gate is
    /// sound, but a wraparound balance smuggles value past it UNLESS the wire is range-bounded.
    #[test]
    fn lean_emitted_transfer_field_sound() {
        // ---- Parse the RANGE-CHECKED descriptor (the EXACT Lean-emitted bytes) ----
        let desc = parse_descriptor(TRANSFER_DESCRIPTOR_RANGED_JSON)
            .expect("range-checked transfer descriptor must parse");
        assert_eq!(desc.name, "dregg-transfer-v1");
        assert_eq!(desc.trace_width, 11);
        assert_eq!(desc.constraints.len(), 9);
        // Four range checks, one per balance wire (0,1,2,3), each 30 bits.
        assert_eq!(
            desc.ranges,
            vec![
                RangeSpec { wire: 0, bits: 30 },
                RangeSpec { wire: 1, bits: 30 },
                RangeSpec { wire: 2, bits: 30 },
                RangeSpec { wire: 3, bits: 30 },
            ]
        );
        // The full AIR trace is base 11 wires + 4*30 = 120 aux bit columns = 131 columns.
        assert_eq!(desc.air_width(), 11 + 4 * 30);

        // The bound is non-vacuous: 2^30 < p, so residues in [2^30, p) exist and are rejectable.
        assert!((1u64 << 30) < BABYBEAR_P as u64, "2^30 must be < p for the gate to bite");

        // ---- Honest in-range witness: kT0/goodTurn/goodPost (all balances small) ----
        // [srcPre, dstPre, srcPost, dstPost, amt, auth, nonneg, avail, distinct, srcLive, dstLive]
        let good = [100i64, 5, 70, 35, 30, 1, 1, 1, 1, 1, 1];
        // All four balances are well within [0, 2^30).
        for &b in &[good[0], good[1], good[2], good[3]] {
            assert!((0..(1i64 << 30)).contains(&b));
        }
        let proof = prove_and_verify_descriptor(&desc, &good)
            .expect("honest in-range transfer witness must prove+verify with range gates");
        verify_descriptor(&desc, &proof)
            .expect("re-verify of the range-checked satisfying proof must succeed");

        // ---- FORGED witness: a balance OUT OF [0, 2^30) (the wraparound the gate forbids) ----
        // Set srcPre = 2^30 and srcPost = 2^30 - amt so the arithmetic gates STILL hold in the
        // field (debit: srcPost = srcPre - amt; conservation: srcPost+dstPost = srcPre+dstPre),
        // isolating the RANGE gate as the SOLE possible rejector. 2^30 = 1073741824 is a valid
        // BabyBear element (< p) but lies OUTSIDE [0, 2^30): its 30-bit decomposition (the low 30
        // bits) recomposes to 0, not 2^30, so the recomposition gate `Σ bᵢ·2ⁱ = srcPre` FAILS.
        // (This is exactly the wraparound forgery: a colossal real balance whose field image the
        // over-ℤ-sound conservation gate cannot distinguish from an honest small one.)
        let two_pow_30: i64 = 1 << 30; // 1073741824: valid field element, but >= 2^30
        let amt = good[4];
        let forged_range = [
            two_pow_30,       // srcPre = 2^30  -> OUT OF [0, 2^30)
            good[1],          // dstPre  = 5
            two_pow_30 - amt, // srcPost = 2^30 - 30 (debit holds in-field)
            good[3],          // dstPost = 35
            amt,
            1, 1, 1, 1, 1, 1,
        ];
        // Sanity: the ARITHMETIC gates hold for this forgery — only the range gate can reject it.
        assert_eq!(forged_range[2], forged_range[0] - forged_range[4]); // debit
        assert_eq!(forged_range[3], forged_range[1] + forged_range[4]); // credit
        assert_eq!(
            forged_range[2] + forged_range[3],
            forged_range[0] + forged_range[1]
        ); // conservation
        assert!(forged_range[0] >= (1 << 30)); // but srcPre is OUT of [0, 2^30)

        let tampered = std::panic::catch_unwind(|| {
            // Debug: prover panics on the violated recomposition gate. Release: verify rejects.
            let p = prove_descriptor(&desc, &forged_range)?;
            verify_descriptor(&desc, &p)
        });
        match tampered {
            Err(_) => {} // prover panicked on the broken range gate: forgery rejected. Good.
            Ok(verify_result) => assert!(
                verify_result.is_err(),
                "OUT-OF-RANGE balance (>= 2^30) MUST be rejected by the bit-decomposition range \
                 gate, but a proof verified — the field-soundness hole is OPEN"
            ),
        }
    }

    /// The parser is faithful to the wire grammar on its own (independent of proving):
    /// round-tripping a hand-built descriptor through Lean-style JSON recovers it, and
    /// the tolerant parser accepts whitespace.
    #[test]
    fn parse_descriptor_basic() {
        // A 3-wire descriptor: Var(2) == Var(0) + Mul(Const(-1), Var(1)).
        let json = r#"{ "name" : "t" , "trace_width" : 3 , "constraints" : [
            { "lhs" : {"t":"var","v":2} ,
              "rhs" : {"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":1}}} } ] }"#;
        let d = parse_descriptor(json).expect("whitespace-tolerant parse");
        assert_eq!(d.name, "t");
        assert_eq!(d.trace_width, 3);
        assert_eq!(d.constraints.len(), 1);
        assert_eq!(d.constraints[0].lhs, LeanExpr::Var(2));
        assert_eq!(
            d.constraints[0].rhs,
            LeanExpr::add(LeanExpr::Var(0), LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(1)))
        );
        // Empty constraint list parses to an empty Vec.
        let empty = parse_descriptor(r#"{"name":"e","trace_width":1,"constraints":[]}"#)
            .expect("empty constraint list parses");
        assert!(empty.constraints.is_empty());
        // A malformed expr tag errors rather than panics.
        assert!(parse_descriptor(r#"{"name":"x","trace_width":1,"constraints":[{"lhs":{"t":"bogus"},"rhs":{"t":"const","v":0}}]}"#).is_err());
    }

    /// Negative i64 constants reduce correctly into BabyBear (no native sign).
    #[test]
    fn i64_to_babybear_handles_negatives() {
        assert_eq!(i64_to_babybear(0), BabyBear::new(0));
        assert_eq!(i64_to_babybear(5), BabyBear::new(5));
        // -1 ≡ p-1
        assert_eq!(i64_to_babybear(-1), BabyBear::new(BABYBEAR_P - 1));
        // -p ≡ 0
        assert_eq!(i64_to_babybear(-(BABYBEAR_P as i64)), BabyBear::new(0));
    }

    /// The interpreter computes the expected polynomial degrees (used to set the
    /// AIR's max_constraint_degree).
    #[test]
    fn descriptor_degree_is_correct() {
        let desc = transfer_test_descriptor();
        // conservation is degree 1 (only adds), bit gates degree 1 (var = const).
        assert_eq!(desc.max_degree(), 1);
    }
}
