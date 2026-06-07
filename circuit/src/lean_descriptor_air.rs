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
// PART 5 — The verifiable-execution beachhead: a public execute→prove→verify path.
// ============================================================================

/// The Lean-emitted full-state transfer circuit (`Dregg2.Circuit.StateCommit.stateDescriptorJson`):
/// the 9 transfer gates + 3 frame-forcing EQ gates over `RecordKernelState`, 20 wires. This is the
/// SOUND full-state circuit (`transfer_circuit_full_sound ⇒ TransferSpec`, the 18-field declarative
/// post-state spec) — NOT the two-balance projection. The witness's digest columns are filled by the
/// Lean witness generator `transferWitnessVec` (which runs the real executor `recKExec`).
pub const STATE_DESCRIPTOR_JSON_FULLSTATE: &str = r#"{"name":"dregg-transfer-fullstate-v1","trace_width":20,"constraints":[{"lhs":{"t":"var","v":5},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":6},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":7},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":8},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":9},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":10},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":2},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}}},{"lhs":{"t":"var","v":3},"rhs":{"t":"add","l":{"t":"var","v":1},"r":{"t":"var","v":4}}},{"lhs":{"t":"add","l":{"t":"var","v":2},"r":{"t":"var","v":3}},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"var","v":1}}},{"lhs":{"t":"var","v":13},"rhs":{"t":"var","v":14}},{"lhs":{"t":"var","v":15},"rhs":{"t":"var","v":16}},{"lhs":{"t":"var","v":18},"rhs":{"t":"var","v":19}}]}"#;

/// **`prove_executor_derived_transfer` — the demonstrable `execute_and_prove(transfer)` path.**
///
/// Takes a witness vector PRODUCED BY THE LEAN EXECUTOR (`Dregg2.Circuit.TransferWitness.
/// transferWitnessVec k t`, which runs `recKExec k t` and lays out the full-state assignment with the
/// concrete commitment-surface digest columns), parses the Lean-emitted full-state circuit, proves it
/// with the real Plonky3 prover, and verifies — returning the accepted `DreggProof`. A tampered /
/// forged witness (e.g. a third-cell-mint post-state) yields a non-equal frame-reuse digest pair, so
/// the prover/verifier REJECTS it (`Err`). This is the `execute → prove → verify → accept` gate for
/// ONE effect over the real executor state, the validated reference the other effects swarm from.
pub fn prove_executor_derived_transfer(witness: &[i64]) -> Result<DreggProof, String> {
    let desc = parse_descriptor(STATE_DESCRIPTOR_JSON_FULLSTATE)?;
    if witness.len() != desc.trace_width {
        return Err(format!(
            "executor witness length {} != full-state trace_width {}",
            witness.len(),
            desc.trace_width
        ));
    }
    prove_and_verify_descriptor(&desc, witness)
}

// ============================================================================
// PART 5b — The v2 verifiable-execution beachhead: `execute → prove → verify` for the
//           NON-CELL effect family (`EffectCommit2`/`EffectCommit2Dual`).
// ============================================================================
//
// Every `EffectCommit2` effect (`balanceA`/`burnA`/`bridgeFinalizeA`/`bridgeMintA`/`attenuateA`/…)
// emits the SAME wire descriptor shape — `Dregg2.Circuit.EffectCommit2.effectCircuit2 E`,
// `trace_width = 72`, four gates: `var 0 = 1` (guard bit), `66 = 67` (rest-frame), `68 = 69`
// (component-bind), `70 = 71` (log-bind). Only the AIR `name` differs per effect. The
// `EffectCommit2Dual` effects (`bridgeLockA`/`bridgeCancelA`/`cellDestroyA`) emit `trace_width = 74`
// with a fifth gate (`66=67`, `68=69`, `70=71` component pair 2, `72=73` log).
//
// The Lean witness generators (`Dregg2.Circuit.Witness.<effect>Witness.<effect>WitnessVec`) RUN the
// real executor and lay the satisfying full-state assignment out as a flat `&[i64]`, every digest
// column filled by a concrete commitment surface. The honest witness proves+verifies; a forged
// post-state (a tampered third cell / bystander mint / wrong post-component) breaks ONE EQ gate, a
// REAL UNSAT — the anti-ghost tooth realized end-to-end through the prover.

/// **`prove_executor_derived_v2` — the demonstrable `execute_and_prove(<v2 effect>)` path.**
///
/// Takes a witness vector PRODUCED BY THE LEAN EXECUTOR (`<effect>WitnessVec`, which runs the real
/// chained executor and lays out the full-state assignment with concrete-surface digest columns),
/// parses the Lean-emitted full-state circuit JSON, proves it with the real Plonky3 prover, and
/// verifies — returning the accepted `DreggProof`. A forged witness yields a non-equal EQ-gate pair,
/// so the prover/verifier REJECTS it (`Err`). The `execute → prove → verify → accept` gate for the
/// non-cell effect family, sharing the validated transfer reference's machinery.
pub fn prove_executor_derived_v2(descriptor_json: &str, witness: &[i64]) -> Result<DreggProof, String> {
    let desc = parse_descriptor(descriptor_json)?;
    if witness.len() != desc.trace_width {
        return Err(format!(
            "executor witness length {} != full-state trace_width {}",
            witness.len(),
            desc.trace_width
        ));
    }
    prove_and_verify_descriptor(&desc, witness)
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

    /// The EXACT JSON string Lean's `Dregg2.Circuit.StateCommit.stateDescriptorJson`
    /// (`#eval stateDescriptorJson`) emits for the REAL `emittedState` circuit — the verified
    /// `stateCircuit` (9 transfer gates + 3 frame-forcing EQ gates) serialized via
    /// `CircuitEmit.emitDescriptorJson`. Copied verbatim from `lake build Dregg2.Circuit.StateCommit`.
    ///
    /// Wire layout (StateCommit.lean §1b): 0..10 = Transfer wires; 11=preRoot 12=postRoot
    /// 13=restDigPre 14=restDigPost 15=frameDigPre 16=frameDigPost 17=movedDigPre
    /// 18=movedDigPost 19=movedDigExpected. Twelve gates: the nine transfer gates plus
    /// `restDigPre=restDigPost`, `frameDigPre=frameDigPost`, `movedDigPost=movedDigExpected`.
    const STATE_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-transfer-fullstate-v1","trace_width":20,"constraints":[{"lhs":{"t":"var","v":5},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":6},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":7},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":8},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":9},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":10},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":2},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}}},{"lhs":{"t":"var","v":3},"rhs":{"t":"add","l":{"t":"var","v":1},"r":{"t":"var","v":4}}},{"lhs":{"t":"add","l":{"t":"var","v":2},"r":{"t":"var","v":3}},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"var","v":1}}},{"lhs":{"t":"var","v":13},"rhs":{"t":"var","v":14}},{"lhs":{"t":"var","v":15},"rhs":{"t":"var","v":16}},{"lhs":{"t":"var","v":18},"rhs":{"t":"var","v":19}}]}"#;

    /// THE full-state swap acceptance test: the REAL Lean-emitted `stateCircuit` drives the
    /// Plonky3 prover. A satisfying conserving-transfer + frame-consistent witness proves+verifies;
    /// a tampered frame-reuse forgery (third-cell mint) is rejected by the `frameDigPre=frameDigPost`
    /// gate — the anti-ghost tooth `stateCircuit_rejects_third_cell` certifies in Lean.
    #[test]
    fn lean_emitted_state_roundtrip() {
        let desc = parse_descriptor(STATE_DESCRIPTOR_JSON)
            .expect("Lean-emitted full-state descriptor must parse");
        assert_eq!(desc.name, "dregg-transfer-fullstate-v1");
        assert_eq!(desc.trace_width, 20);
        assert_eq!(desc.constraints.len(), 12);

        // Honest witness: kT0/goodTurn/goodPost transfer + consistent digests.
        // Layout: [srcPre,dstPre,srcPost,dstPost,amt, auth..dstLive, preRoot,postRoot,
        //          restPre,restPost, framePre,framePost, movedPre,movedPost,movedExpected]
        let good = [
            100i64, 5, 70, 35, 30, // transfer wires 0..4
            1, 1, 1, 1, 1, 1,      // guard bits 5..10
            0, 0,                  // preRoot/postRoot (unconstrained by the 12 gates)
            1000, 1000,            // restDigPre = restDigPost
            2000, 2000,            // frameDigPre = frameDigPost
            0, 3000, 3000,         // movedDigPre (free), movedDigPost = movedDigExpected
        ];
        assert_eq!(good.len(), 20);
        assert_eq!(good[2], good[0] - good[4]);
        assert_eq!(good[3], good[1] + good[4]);
        assert_eq!(good[2] + good[3], good[0] + good[1]);
        assert_eq!(good[13], good[14]);
        assert_eq!(good[15], good[16]);
        assert_eq!(good[18], good[19]);

        let proof = prove_and_verify_descriptor(&desc, &good)
            .expect("honest full-state witness must prove+verify");
        verify_descriptor(&desc, &proof).expect("re-verify full-state proof");

        // Frame-reuse forgery: conserving transfer but frameDigPost != frameDigPre (third-cell mint).
        let forged_frame = [
            100, 5, 70, 35, 30, 1, 1, 1, 1, 1, 1, 0, 0, 1000, 1000, 2000, 2001, 0, 3000, 3000,
        ];
        assert_eq!(forged_frame[2] + forged_frame[3], forged_frame[0] + forged_frame[1]);
        assert_ne!(forged_frame[15], forged_frame[16]);

        let tampered = std::panic::catch_unwind(|| {
            let p = prove_descriptor(&desc, &forged_frame)?;
            verify_descriptor(&desc, &p)
        });
        match tampered {
            Err(_) => {}
            Ok(verify_result) => assert!(
                verify_result.is_err(),
                "FRAME-REUSE forgery (frameDigPost != frameDigPre) MUST be rejected"
            ),
        }
    }

    /// Range-checked full-state descriptor (balance wires ∈ [0, 2³⁰)).
    const STATE_DESCRIPTOR_RANGED_JSON: &str = r#"{"name":"dregg-transfer-fullstate-v1","trace_width":20,"constraints":[{"lhs":{"t":"var","v":5},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":6},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":7},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":8},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":9},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":10},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":2},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}}},{"lhs":{"t":"var","v":3},"rhs":{"t":"add","l":{"t":"var","v":1},"r":{"t":"var","v":4}}},{"lhs":{"t":"add","l":{"t":"var","v":2},"r":{"t":"var","v":3}},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"var","v":1}}},{"lhs":{"t":"var","v":13},"rhs":{"t":"var","v":14}},{"lhs":{"t":"var","v":15},"rhs":{"t":"var","v":16}},{"lhs":{"t":"var","v":18},"rhs":{"t":"var","v":19}}],"ranges":[{"wire":0,"bits":30},{"wire":1,"bits":30},{"wire":2,"bits":30},{"wire":3,"bits":30}]}"#;

    #[test]
    fn lean_emitted_state_field_sound() {
        let desc = parse_descriptor(STATE_DESCRIPTOR_RANGED_JSON)
            .expect("range-checked full-state descriptor must parse");
        assert_eq!(desc.ranges.len(), 4);
        assert_eq!(desc.air_width(), 20 + 4 * 30);

        let good = [
            100i64, 5, 70, 35, 30, 1, 1, 1, 1, 1, 1, 0, 0, 1000, 1000, 2000, 2000, 0, 3000, 3000,
        ];
        let proof = prove_and_verify_descriptor(&desc, &good)
            .expect("in-range full-state witness must prove+verify with range gates");
        verify_descriptor(&desc, &proof).expect("re-verify range-checked full-state proof");

        let two_pow_30: i64 = 1 << 30;
        let amt = good[4];
        let forged_range = [
            two_pow_30,
            good[1],
            two_pow_30 - amt,
            good[3],
            amt,
            1, 1, 1, 1, 1, 1,
            0, 0,
            1000, 1000,
            2000, 2000,
            0, 3000, 3000,
        ];
        assert!(forged_range[0] >= (1 << 30));
        assert_eq!(forged_range[2], forged_range[0] - forged_range[4]);

        let tampered = std::panic::catch_unwind(|| {
            let p = prove_descriptor(&desc, &forged_range)?;
            verify_descriptor(&desc, &p)
        });
        match tampered {
            Err(_) => {}
            Ok(verify_result) => assert!(
                verify_result.is_err(),
                "OUT-OF-RANGE balance on full-state circuit MUST be rejected by range gate"
            ),
        }
    }

    /// Lean-emitted `setFieldA` full-state circuit (`SetFieldCommit.setFieldDescriptorJson`).
    const SETFIELD_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-setfield-fullstate-v1","trace_width":16,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":1},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":2},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":3},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":6},"rhs":{"t":"var","v":7}},{"lhs":{"t":"var","v":8},"rhs":{"t":"var","v":9}},{"lhs":{"t":"var","v":11},"rhs":{"t":"var","v":12}},{"lhs":{"t":"var","v":14},"rhs":{"t":"var","v":15}}]}"#;

    #[test]
    fn lean_emitted_setfield_roundtrip() {
        let desc = parse_descriptor(SETFIELD_DESCRIPTOR_JSON)
            .expect("Lean-emitted setField descriptor must parse");
        assert_eq!(desc.name, "dregg-setfield-fullstate-v1");
        assert_eq!(desc.trace_width, 16);
        assert_eq!(desc.constraints.len(), 8);

        // Guard bits = 1; rest/frame/target/log pairs equal (SetFieldCommit wire layout).
        let good = [
            1i64, 1, 1, 1, // 0..3: caveat/auth/mem/live
            100, 101,      // 4..5: preRoot/postRoot (unconstrained)
            50, 50,        // 6..7: restPre/restPost
            60, 60,        // 8..9: framePre/framePost
            70, 70, 70,    // 10..12: targetPre/targetPost/targetExpected (gate: 11=12)
            90, 91, 91,    // 13..15: logPre/logPost/logExpected (gate: 14=15)
        ];
        assert_eq!(good.len(), 16);
        assert_eq!(good[6], good[7]);
        assert_eq!(good[8], good[9]);
        assert_eq!(good[11], good[12]);
        assert_eq!(good[14], good[15]);

        let proof = prove_and_verify_descriptor(&desc, &good)
            .expect("honest setField witness must prove+verify");
        verify_descriptor(&desc, &proof).expect("re-verify setField proof");

        // Frame forgery: framePost != framePre.
        let mut forged = good;
        forged[9] = 61;
        assert_ne!(forged[8], forged[9]);

        let tampered = std::panic::catch_unwind(|| {
            let p = prove_descriptor(&desc, &forged)?;
            verify_descriptor(&desc, &p)
        });
        match tampered {
            Err(_) => {}
            Ok(verify_result) => assert!(
                verify_result.is_err(),
                "setField FRAME forgery MUST be rejected"
            ),
        }
    }

    /// Lean `EffectInstances2.mintDescriptorJson` — the v2 mint effect circuit (4 gates, 72 wires).
    const MINT_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-mint-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_emitted_mint_roundtrip() {
        let desc = parse_descriptor(MINT_DESCRIPTOR_JSON).expect("mint descriptor must parse");
        assert_eq!(desc.name, "dregg-mint-v2");
        assert_eq!(desc.trace_width, 72);
        assert_eq!(desc.constraints.len(), 4);

        // Guard=1; rest/frame/component/log digest pairs equal (wires 66/67, 68/69, 70/71).
        let mut good = [0i64; 72];
        good[0] = 1;
        good[66] = 50;
        good[67] = 50;
        good[68] = 100;
        good[69] = 100;
        good[70] = 200;
        good[71] = 200;

        let proof = prove_and_verify_descriptor(&desc, &good)
            .expect("honest mint witness must prove+verify");
        verify_descriptor(&desc, &proof).expect("re-verify mint proof");

        // Log forgery: logPost != logExpected breaks the log gate (70 != 71).
        let mut forged = good;
        forged[71] = 201;
        let tampered = std::panic::catch_unwind(|| {
            let p = prove_descriptor(&desc, &forged)?;
            verify_descriptor(&desc, &p)
        });
        match tampered {
            Err(_) => {}
            Ok(verify_result) => assert!(
                verify_result.is_err(),
                "mint LOG forgery MUST be rejected"
            ),
        }
    }

    /// Lean `BurnA.burnDescriptorJson` — v2 burn effect circuit (4 gates, 72 wires).
    const BURN_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-burn-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_emitted_burn_roundtrip() {
        let desc = parse_descriptor(BURN_DESCRIPTOR_JSON).expect("burn descriptor must parse");
        assert_eq!(desc.name, "dregg-burn-v2");
        assert_eq!(desc.trace_width, 72);
        assert_eq!(desc.constraints.len(), 4);

        let mut good = [0i64; 72];
        good[0] = 1;
        good[66] = 50;
        good[67] = 50;
        good[68] = 100;
        good[69] = 100;
        good[70] = 200;
        good[71] = 200;

        let proof = prove_and_verify_descriptor(&desc, &good)
            .expect("honest burn witness must prove+verify");
        verify_descriptor(&desc, &proof).expect("re-verify burn proof");

        // Component forgery: compPost != compExpected breaks the bind gate (68 != 69).
        let mut forged = good;
        forged[69] = 101;
        let tampered = std::panic::catch_unwind(|| {
            let p = prove_descriptor(&desc, &forged)?;
            verify_descriptor(&desc, &p)
        });
        match tampered {
            Err(_) => {}
            Ok(verify_result) => assert!(
                verify_result.is_err(),
                "burn COMPONENT forgery MUST be rejected"
            ),
        }
    }

    /// Lean `Delegate.delegateEmitted` via `emitDescriptorJson` — v2 delegate circuit (4 gates, 72 wires).
    const DELEGATE_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-delegate-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_emitted_delegate_roundtrip() {
        let desc = parse_descriptor(DELEGATE_DESCRIPTOR_JSON)
            .expect("delegate descriptor must parse");
        assert_eq!(desc.name, "dregg-delegate-v2");
        assert_eq!(desc.trace_width, 72);
        assert_eq!(desc.constraints.len(), 4);

        let mut good = [0i64; 72];
        good[0] = 1;
        good[66] = 50;
        good[67] = 50;
        good[68] = 100;
        good[69] = 100;
        good[70] = 200;
        good[71] = 200;

        let proof = prove_and_verify_descriptor(&desc, &good)
            .expect("honest delegate witness must prove+verify");
        verify_descriptor(&desc, &proof).expect("re-verify delegate proof");

        // Rest-frame forgery: restPost != restPre breaks the rest gate (66 != 67).
        let mut forged = good;
        forged[67] = 51;
        let tampered = std::panic::catch_unwind(|| {
            let p = prove_descriptor(&desc, &forged)?;
            verify_descriptor(&desc, &p)
        });
        match tampered {
            Err(_) => {}
            Ok(verify_result) => assert!(
                verify_result.is_err(),
                "delegate REST forgery MUST be rejected"
            ),
        }
    }

    /// Lean `ExerciseA.exerciseAEmitted` via `emitDescriptorJson` — v1 hold-gate circuit (5 gates, 74 wires).
    const EXERCISE_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-exerciseA-v1","trace_width":74,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}}]}"#;

    #[test]
    fn lean_emitted_exercise_roundtrip() {
        let desc = parse_descriptor(EXERCISE_DESCRIPTOR_JSON)
            .expect("exerciseA descriptor must parse");
        assert_eq!(desc.name, "dregg-exerciseA-v1");
        assert_eq!(desc.trace_width, 74);
        assert_eq!(desc.constraints.len(), 5);

        // Guard=1; rest/frame/touched/log digest pairs equal (wires 66/67, 68/69, 70/71, 72/73).
        let mut good = [0i64; 74];
        good[0] = 1;
        good[66] = 50;
        good[67] = 50;
        good[68] = 60;
        good[69] = 60;
        good[70] = 70;
        good[71] = 70;
        good[72] = 200;
        good[73] = 200;

        let proof = prove_and_verify_descriptor(&desc, &good)
            .expect("honest exerciseA witness must prove+verify");
        verify_descriptor(&desc, &proof).expect("re-verify exerciseA proof");

        // Log forgery: logPost != logExpected breaks the log gate (72 != 73).
        let mut forged = good;
        forged[73] = 201;
        let tampered = std::panic::catch_unwind(|| {
            let p = prove_descriptor(&desc, &forged)?;
            verify_descriptor(&desc, &p)
        });
        match tampered {
            Err(_) => {}
            Ok(verify_result) => assert!(
                verify_result.is_err(),
                "exerciseA LOG forgery MUST be rejected"
            ),
        }
    }

    /// Lean `CoordinatedTurnEmit.coordinatedTurnDescriptorJson` — bilateral turn circuit (10 gates, 20 wires).
    const COORDINATED_TURN_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-coordinated-turn-v1","trace_width":20,"constraints":[{"lhs":{"t":"var","v":4},"rhs":{"t":"var","v":0}},{"lhs":{"t":"var","v":13},"rhs":{"t":"var","v":1}},{"lhs":{"t":"var","v":5},"rhs":{"t":"var","v":2}},{"lhs":{"t":"var","v":6},"rhs":{"t":"var","v":3}},{"lhs":{"t":"var","v":7},"rhs":{"t":"var","v":8}},{"lhs":{"t":"var","v":9},"rhs":{"t":"var","v":10}},{"lhs":{"t":"var","v":11},"rhs":{"t":"var","v":12}},{"lhs":{"t":"var","v":14},"rhs":{"t":"var","v":15}},{"lhs":{"t":"var","v":16},"rhs":{"t":"var","v":17}},{"lhs":{"t":"var","v":18},"rhs":{"t":"var","v":19}}]}"#;

    #[test]
    fn lean_emitted_coordinated_turn_roundtrip() {
        let desc = parse_descriptor(COORDINATED_TURN_DESCRIPTOR_JSON)
            .expect("coordinated-turn descriptor must parse");
        assert_eq!(desc.name, "dregg-coordinated-turn-v1");
        assert_eq!(desc.trace_width, 20);
        assert_eq!(desc.constraints.len(), 10);

        // Wire layout: pub 0..3; legA root/charter/binding 4..6 bound to pub; per-leg EQ pairs 7..19.
        let good = [
            100i64, 200, 300, 400, // pub: rootA, rootB, charterHash, bindingHash
            100, 300, 400,         // legA: legRootA, charterDig, bindingDig
            50, 50,                // legA rest pre/post
            60, 60,                // legA frame pre/post
            70, 70,                // legA moved post/expected
            200,                   // legB root (bound to pub rootB)
            80, 80,                // legB rest pre/post
            90, 90,                // legB frame pre/post
            100, 100,              // legB moved post/expected
        ];
        assert_eq!(good.len(), 20);
        assert_eq!(good[4], good[0]);
        assert_eq!(good[13], good[1]);
        assert_eq!(good[5], good[2]);
        assert_eq!(good[6], good[3]);
        assert_eq!(good[7], good[8]);
        assert_eq!(good[9], good[10]);
        assert_eq!(good[11], good[12]);
        assert_eq!(good[14], good[15]);
        assert_eq!(good[16], good[17]);
        assert_eq!(good[18], good[19]);

        let proof = prove_and_verify_descriptor(&desc, &good)
            .expect("honest coordinated-turn witness must prove+verify");
        verify_descriptor(&desc, &proof).expect("re-verify coordinated-turn proof");

        // Frame-reuse forgery on leg B: framePost != framePre (16 != 17).
        let mut forged = good;
        forged[17] = 91;
        assert_eq!(forged[16], forged[17] - 1);

        let tampered = std::panic::catch_unwind(|| {
            let p = prove_descriptor(&desc, &forged)?;
            verify_descriptor(&desc, &p)
        });
        match tampered {
            Err(_) => {}
            Ok(verify_result) => assert!(
                verify_result.is_err(),
                "coordinated-turn FRAME forgery MUST be rejected"
            ),
        }
    }

    /// Lean `Poseidon2Emit.poseidon2CompressWire` — Wave-4 sponge compress gadget (reuses
    /// `merkle_hash` + `transition` + two `pi_binding` boundaries; distinct AIR name).
    const POSEIDON2_COMPRESS_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-poseidon2-compress-v1","trace_width":6,"public_input_count":2,"constraints":[{"t":"merkle_hash","output_col":5,"current_col":0,"sib_cols":[1,2,3],"position_col":4},{"t":"transition","next_col":0,"local_col":5},{"t":"pi_binding_first","col":0,"pi_index":0},{"t":"pi_binding_last","col":5,"pi_index":1}]}"#;

    #[test]
    fn lean_emitted_poseidon2_compress_golden() {
        // Golden pin: byte-exact match to Lean `#guard poseidon2CompressWire`.
        assert_eq!(
            POSEIDON2_COMPRESS_DESCRIPTOR_JSON,
            r#"{"name":"dregg-poseidon2-compress-v1","trace_width":6,"public_input_count":2,"constraints":[{"t":"merkle_hash","output_col":5,"current_col":0,"sib_cols":[1,2,3],"position_col":4},{"t":"transition","next_col":0,"local_col":5},{"t":"pi_binding_first","col":0,"pi_index":0},{"t":"pi_binding_last","col":5,"pi_index":1}]}"#
        );
        assert!(POSEIDON2_COMPRESS_DESCRIPTOR_JSON.contains(r#""name":"dregg-poseidon2-compress-v1""#));
        assert!(POSEIDON2_COMPRESS_DESCRIPTOR_JSON.contains(r#""trace_width":6"#));
        assert!(POSEIDON2_COMPRESS_DESCRIPTOR_JSON.contains(r#""public_input_count":2"#));
        // Four structural constraints: merkle_hash, transition, pi_binding_first, pi_binding_last.
        assert_eq!(
            POSEIDON2_COMPRESS_DESCRIPTOR_JSON.matches(r#""t":"merkle_hash""#).count(),
            1
        );
        assert_eq!(
            POSEIDON2_COMPRESS_DESCRIPTOR_JSON.matches(r#""t":"transition""#).count(),
            1
        );
        assert_eq!(
            POSEIDON2_COMPRESS_DESCRIPTOR_JSON
                .matches(r#""t":"pi_binding_first""#)
                .count(),
            1
        );
        assert_eq!(
            POSEIDON2_COMPRESS_DESCRIPTOR_JSON
                .matches(r#""t":"pi_binding_last""#)
                .count(),
            1
        );
        // Constraint *forms* match Merkle membership (only the AIR name differs).
        let merkle_constraints = r#"{"t":"merkle_hash","output_col":5,"current_col":0,"sib_cols":[1,2,3],"position_col":4},{"t":"transition","next_col":0,"local_col":5},{"t":"pi_binding_first","col":0,"pi_index":0},{"t":"pi_binding_last","col":5,"pi_index":1}"#;
        assert!(POSEIDON2_COMPRESS_DESCRIPTOR_JSON.contains(merkle_constraints));
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

    // ========================================================================
    // THE VERIFIABLE-EXECUTION BEACHHEAD: execute → witness → prove → verify.
    //
    // Unlike `lean_emitted_state_roundtrip` (whose digest columns are hand-picked
    // magic numbers), the witness vectors HERE are computed BY THE LEAN EXECUTOR:
    // `Dregg2.Circuit.TransferWitness.transferWitnessVec kS0 goodTurnS` runs the real
    // record-cell executor (`recKExec`) and lays out the full-state witness with every
    // digest column filled by the concrete commitment surface (`compressNConcrete`/
    // `cmbConcrete`/…). These are the EXACT bytes Lean's `#guard honestWitnessJson ==`
    // / `forgedWitnessJson ==` goldens pin — copied verbatim. So this test proves the
    // SAME state transition the executor computed, end-to-end through the real Plonky3
    // prover, and demonstrates the anti-ghost rejection on a REAL forged post-state
    // (mint bystander cell 2: 50 → 999), not a hand-bumped digest.
    // ========================================================================

    /// The EXECUTOR-DERIVED honest witness for `kS0`/`goodTurnS` — the satisfying
    /// assignment Lean's `transferWitnessVec kS0 goodTurnS` produces (the executor
    /// committed `recKExec kS0 goodTurnS = some goodPostS`; the digest columns are the
    /// concrete-surface commitments of the REAL post-state). Wires 11/12 are the
    /// full-state ROOT commitments (large positional-Horner numbers, UNCONSTRAINED by
    /// the 12 gates — they reduce mod the BabyBear field harmlessly); the CONSTRAINED
    /// frame-EQ wires (13/14, 15/16, 18/19) are small and equal.
    const EXEC_HONEST_WITNESS: [i64; 20] = [
        100, 5, 70, 35, 30, // 0..4  transfer wires (src/dst pre/post + amt)
        1, 1, 1, 1, 1, 1, // 5..10 guard bits
        1000150000005000003, // 11 preRoot  (unconstrained)
        1000120000035000003, // 12 postRoot (unconstrained)
        3, 3, // 13/14 restDigPre = restDigPost   (rhConcrete = card + nullifiers.len)
        1000050, 1000050, // 15/16 frameDigPre = frameDigPost (untouched cell 2 sponge)
        100000005, // 17 movedDigPre (unconstrained)
        70000035, 70000035, // 18/19 movedDigPost = movedDigExpected (debit/credit leaves)
    ];

    /// The EXECUTOR-DERIVED FORGED witness — `transferWitnessVec` over the SAME pre/turn
    /// but the REAL `forgedThirdCell` post-state (bystander cell 2 minted 50 → 999). The
    /// only changed digest columns vs the honest witness are the post-root (12) and the
    /// frame-reuse post digest (16: 1000050 → 1000999): the minted cell perturbs the
    /// untouched-cell sponge. The frame-reuse gate `15 = 16` therefore FAILS — a REAL
    /// UNSAT — while the two MOVED balances still conserve (so the projection circuit
    /// would have passed it; the full-state circuit does not).
    const EXEC_FORGED_WITNESS: [i64; 20] = [
        100, 5, 70, 35, 30, 1, 1, 1, 1, 1, 1, //
        1000150000005000003, // 11 preRoot
        1001069000035000003, // 12 postRoot (now binds the minted cell)
        3, 3, // 13/14 rest still equal
        1000050, 1000999, // 15/16 frameDigPre != frameDigPost  ← the forgery shows up here
        100000005, 70000035, 70000035, // 17/18/19
    ];

    /// **THE BEACHHEAD TEST: execute → prove → verify, on the EXECUTOR-DERIVED witness.**
    /// The honest witness (computed by `transferWitnessVec` running the real executor)
    /// proves+verifies through the real Plonky3 prover on the Lean-emitted full-state
    /// circuit; the forged witness (the REAL third-cell-mint post-state) is REJECTED by
    /// the frame-reuse gate. This is the anti-ghost tooth `stateCircuit_rejects_third_cell`
    /// realized end-to-end through the prover, on a genuine forged state.
    #[test]
    fn lean_executor_derived_transfer() {
        let desc = parse_descriptor(STATE_DESCRIPTOR_JSON)
            .expect("Lean-emitted full-state descriptor must parse");
        assert_eq!(desc.trace_width, 20);
        assert_eq!(desc.constraints.len(), 12);

        // The executor-derived honest witness must satisfy the gates (mirror of Lean's
        // `#guard decide (satisfiedC (encodeSC kS0 goodTurnS goodPostS))`).
        let good = EXEC_HONEST_WITNESS;
        assert_eq!(good[2], good[0] - good[4], "debit");
        assert_eq!(good[3], good[1] + good[4], "credit");
        assert_eq!(good[2] + good[3], good[0] + good[1], "conserve");
        assert_eq!(good[13], good[14], "rest frame");
        assert_eq!(good[15], good[16], "untouched-cell frame");
        assert_eq!(good[18], good[19], "moved-cell bind");

        // EXECUTE → PROVE → VERIFY: the executor-derived witness proves+verifies.
        let proof = prove_and_verify_descriptor(&desc, &good)
            .expect("the EXECUTOR-DERIVED transfer witness must prove+verify");
        verify_descriptor(&desc, &proof)
            .expect("re-verify of the executor-derived full-state proof must succeed");

        // ANTI-GHOST: the REAL forged post-state (third-cell mint) is rejected. The two
        // moved balances still conserve, but the frame-reuse digest gate (15 = 16) fails.
        let forged = EXEC_FORGED_WITNESS;
        assert_eq!(
            forged[2] + forged[3],
            forged[0] + forged[1],
            "the forgery STILL conserves the two moved balances (the projection ghost)"
        );
        assert_ne!(
            forged[15], forged[16],
            "but the untouched-cell frame digest changed: the minted bystander shows up"
        );

        let tampered = std::panic::catch_unwind(|| {
            let p = prove_descriptor(&desc, &forged)?;
            verify_descriptor(&desc, &p)
        });
        match tampered {
            // Prover panicked on the broken frame-reuse gate: forgery rejected (real UNSAT).
            Err(_) => {}
            // Prover produced a proof: verification MUST reject it.
            Ok(verify_result) => assert!(
                verify_result.is_err(),
                "THIRD-CELL-MINT forgery (real executor-derived witness) MUST be rejected by \
                 the frame-reuse gate, but a proof verified — the anti-ghost tooth failed"
            ),
        }
    }

    // ========================================================================
    // THE WHOLE-TURN beachhead: compose per-effect proofs into ONE authenticated
    // full-turn proof for a chained transfer FOREST.
    //
    // A turn is a CHAIN of effects. The Lean `Dregg2.Circuit.TurnTransferWitness`
    // module composes TWO per-step `stateCircuit` blocks (the second offset by 20)
    // into one width-44 circuit, PLUS the gates the single-effect circuit was
    // MISSING: root-binding gates (force the formerly-free root wires 11/12 and
    // 31/32 to equal the concrete combiner `cmbConcrete(compressConcrete frame
    // moved) rest` of the step's digest children — a tampered post-root ⇒ UNSAT)
    // and chain gates (the post-state of step 0 IS the pre-state of step 1, via the
    // turn-independent full-cell sponge `allCellDig` carried on both sides + the
    // rest digest). `turnTransferWitnessVec kS0 [ta, tb]` runs the REAL chained
    // executor (`chainKernels` over `recKExec`) and lays out the satisfying
    // whole-turn witness. The forged variant mints a bystander cell 0 in the FINAL
    // post-state `k₂` — the second step's frame-reuse gate (35 = 36) breaks, a real
    // UNSAT for the WHOLE turn.
    // ========================================================================

    /// The Lean-emitted whole-turn circuit (`Dregg2.Circuit.TurnTransferWitness.
    /// turnStateDescriptorJson`): two transfer full-state blocks (step 1 offset 20),
    /// the two root-binding gates per step (closing the 11/12 root caveat), and the
    /// two chain gates (the shared kernel `k₁` flows through). 44 wires, 30 gates.
    const TURN_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-transfer-turn-v1","trace_width":44,"constraints":[{"lhs":{"t":"var","v":5},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":6},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":7},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":8},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":9},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":10},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":2},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}}},{"lhs":{"t":"var","v":3},"rhs":{"t":"add","l":{"t":"var","v":1},"r":{"t":"var","v":4}}},{"lhs":{"t":"add","l":{"t":"var","v":2},"r":{"t":"var","v":3}},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"var","v":1}}},{"lhs":{"t":"var","v":13},"rhs":{"t":"var","v":14}},{"lhs":{"t":"var","v":15},"rhs":{"t":"var","v":16}},{"lhs":{"t":"var","v":18},"rhs":{"t":"var","v":19}},{"lhs":{"t":"var","v":25},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":26},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":27},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":28},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":29},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":30},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":22},"rhs":{"t":"add","l":{"t":"var","v":20},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":24}}}},{"lhs":{"t":"var","v":23},"rhs":{"t":"add","l":{"t":"var","v":21},"r":{"t":"var","v":24}}},{"lhs":{"t":"add","l":{"t":"var","v":22},"r":{"t":"var","v":23}},"rhs":{"t":"add","l":{"t":"var","v":20},"r":{"t":"var","v":21}}},{"lhs":{"t":"var","v":33},"rhs":{"t":"var","v":34}},{"lhs":{"t":"var","v":35},"rhs":{"t":"var","v":36}},{"lhs":{"t":"var","v":38},"rhs":{"t":"var","v":39}},{"lhs":{"t":"var","v":11},"rhs":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":17}},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":13}}},{"lhs":{"t":"var","v":12},"rhs":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":18}},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":14}}},{"lhs":{"t":"var","v":31},"rhs":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":35},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":37}},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":33}}},{"lhs":{"t":"var","v":32},"rhs":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":36},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":38}},"r":{"t":"const","v":1000000}},"r":{"t":"var","v":34}}},{"lhs":{"t":"var","v":41},"rhs":{"t":"var","v":42}},{"lhs":{"t":"var","v":14},"rhs":{"t":"var","v":33}}]}"#;

    /// The EXECUTOR-DERIVED honest WHOLE-TURN witness (Lean `turnHonestWitnessJson`):
    /// `turnTransferWitnessVec kS0 [ta, tb]` ran the real chained executor
    /// (`recKExec kS0 ta = some k₁`, `recKExec k₁ tb = some k₂`). Layout: step-0
    /// block (0..19), step-1 block (20..39), then the four turn-independent
    /// full-cell chain digests (40: allCellDig k₀, 41: allCellDig k₁, 42:
    /// allCellDig k₁, 43: allCellDig k₂). The chain gate `41 = 42` holds (the shared
    /// kernel k₁ flows through); the root-binding gates pin 11/12 and 31/32.
    const TURN_HONEST_WITNESS: [i64; 44] = [
        // step 0: actor 0 transfers 30 from cell 0 → cell 1
        100, 5, 70, 35, 30, 1, 1, 1, 1, 1, 1, //
        1000150000005000003, // 11 preRoot  (NOW constrained = combine(15,17,13))
        1000120000035000003, // 12 postRoot (NOW constrained = combine(16,18,14))
        3, 3, 1000050, 1000050, 100000005, 70000035, 70000035, // 13..19
        // step 1: actor 1 transfers 10 from cell 1 → cell 2
        35, 50, 25, 60, 10, 1, 1, 1, 1, 1, 1, //
        1000105000050000003, // 31 preRoot  (constrained = combine(35,37,33))
        1000095000060000003, // 32 postRoot (constrained = combine(36,38,34))
        3, 3, 1000070, 1000070, 35000050, 25000060, 25000060, // 33..39
        // chain digests (turn-independent full-cell sponge)
        3000100000005000050, // 40 allCellDig k₀
        3000070000035000050, // 41 allCellDig k₁ (step-0 post)
        3000070000035000050, // 42 allCellDig k₁ (step-1 pre)  → 41 = 42 chain gate
        3000070000025000060, // 43 allCellDig k₂
    ];

    /// The EXECUTOR-DERIVED FORGED WHOLE-TURN witness (Lean `turnForgedWitnessJson`):
    /// the SAME chain, but step 1's FINAL post-state mints a bystander cell 0
    /// (50→... — value forged into a third cell of the final state). The two MOVED
    /// balances of step 1 still conserve, but the second step's frame-reuse digest
    /// gate (35 = 36) breaks (`1000070 != 1000999`): a REAL UNSAT for the WHOLE turn.
    const TURN_FORGED_WITNESS: [i64; 44] = [
        100, 5, 70, 35, 30, 1, 1, 1, 1, 1, 1, //
        1000150000005000003, 1000120000035000003, 3, 3, 1000050, 1000050, 100000005, 70000035,
        70000035, //
        35, 50, 25, 60, 10, 1, 1, 1, 1, 1, 1, //
        1000105000050000003, //
        1001024000060000003, // 32 forged postRoot (binds the minted cell 0)
        3, 3, 1000070, //
        1000999, // 36 frameDigPost != frameDigPre (35): the minted bystander shows up
        35000050, 25000060, 25000060, //
        3000100000005000050, 3000070000035000050, 3000070000035000050,
        3000999000025000060, // 43 forged final full-cell digest
    ];

    /// **THE WHOLE-TURN BEACHHEAD: execute the chain → prove → verify, ONE STARK
    /// proof for the whole transfer-forest turn.** The honest whole-turn witness
    /// (computed by `turnTransferWitnessVec` running the real chained executor)
    /// proves+verifies through the real Plonky3 prover on the Lean-emitted composed
    /// turn circuit — ONE proof binding BOTH effects + their root chain. The forged
    /// witness (the REAL final-state third-cell mint) is REJECTED by the second
    /// step's frame-reuse gate — the anti-ghost tooth realized end-to-end over the
    /// WHOLE TURN, on a genuine forged state.
    #[test]
    fn lean_executor_derived_turn() {
        let desc = parse_descriptor(TURN_DESCRIPTOR_JSON)
            .expect("Lean-emitted whole-turn descriptor must parse");
        assert_eq!(desc.name, "dregg-transfer-turn-v1");
        assert_eq!(desc.trace_width, 44);
        assert_eq!(desc.constraints.len(), 30);

        // The executor-derived honest whole-turn witness must satisfy the gates
        // (mirror of Lean's `#guard decide (satisfied turnStateCircuit …)`).
        let good = TURN_HONEST_WITNESS;
        // step 0 transfer relations:
        assert_eq!(good[2], good[0] - good[4], "step0 debit");
        assert_eq!(good[3], good[1] + good[4], "step0 credit");
        assert_eq!(good[13], good[14], "step0 rest frame");
        assert_eq!(good[15], good[16], "step0 untouched frame");
        assert_eq!(good[18], good[19], "step0 moved bind");
        // step 1 transfer relations (offset 20):
        assert_eq!(good[22], good[20] - good[24], "step1 debit");
        assert_eq!(good[23], good[21] + good[24], "step1 credit");
        assert_eq!(good[33], good[34], "step1 rest frame");
        assert_eq!(good[35], good[36], "step1 untouched frame");
        assert_eq!(good[38], good[39], "step1 moved bind");
        // ROOT-BINDING (the closed caveat): preRoot/postRoot = combine(frame,moved,rest).
        const M: i64 = 1_000_000;
        assert_eq!(
            good[11],
            (good[15] * M + good[17]) * M + good[13],
            "step0 preRoot bound to its digest children"
        );
        assert_eq!(
            good[32],
            (good[36] * M + good[38]) * M + good[34],
            "step1 postRoot bound to its digest children"
        );
        // CHAIN: step-0 post full-cell digest = step-1 pre full-cell digest.
        assert_eq!(good[41], good[42], "the shared kernel k₁ flows through the turn");
        assert_eq!(good[14], good[33], "rest digest chains across the boundary");

        // EXECUTE THE CHAIN → PROVE → VERIFY: ONE STARK proof for the whole turn.
        let proof = prove_and_verify_descriptor(&desc, &good)
            .expect("the EXECUTOR-DERIVED whole-turn witness must prove+verify (one proof)");
        verify_descriptor(&desc, &proof)
            .expect("re-verify of the executor-derived whole-turn proof must succeed");

        // ANTI-GHOST: the REAL forged FINAL post-state (third-cell mint in k₂) is
        // rejected. Step 1's two moved balances still conserve, but the frame-reuse
        // digest gate (35 = 36) fails — a real UNSAT over the WHOLE turn.
        let forged = TURN_FORGED_WITNESS;
        assert_eq!(
            forged[22] + forged[23],
            forged[20] + forged[21],
            "the forgery STILL conserves step 1's two moved balances (the projection ghost)"
        );
        assert_ne!(
            forged[35], forged[36],
            "but the step-1 untouched-cell frame digest changed: the minted bystander shows up"
        );

        let tampered = std::panic::catch_unwind(|| {
            let p = prove_descriptor(&desc, &forged)?;
            verify_descriptor(&desc, &p)
        });
        match tampered {
            // Prover panicked on the broken step-1 frame-reuse gate: forgery rejected.
            Err(_) => {}
            // Prover produced a proof: verification MUST reject it.
            Ok(verify_result) => assert!(
                verify_result.is_err(),
                "WHOLE-TURN final-state third-cell-mint forgery MUST be rejected by the \
                 step-1 frame-reuse gate, but a proof verified — the anti-ghost tooth failed"
            ),
        }
    }

    // ========================================================================
    // The v2 verifiable-execution beachhead tests (the non-cell effect family).
    //
    // Each test pastes the EXACT executor-derived witness bytes the Lean
    // `Dregg2.Circuit.Witness.<effect>Witness` goldens pin
    // (`<effect>HonestWitnessJson` / `<effect>ForgedWitnessJson`) and the
    // Lean-emitted descriptor (`<effect>DescriptorJson`), proves+verifies the
    // honest witness through the real Plonky3 prover, and asserts the forged
    // witness (a REAL tampered post-state) is REJECTED by a broken EQ gate.
    // ========================================================================

    /// Shared driver: prove+verify the honest v2 witness; assert the forged one
    /// is rejected (a real UNSAT on a broken EQ gate). `bind_pre`/`bind_post` are
    /// the wire indices of the gate the forgery breaks (for the documentation
    /// assert that the pair genuinely differs in the forged witness).
    fn v2_beachhead(
        desc_json: &str,
        expected_width: usize,
        honest: &[i64],
        forged: &[i64],
        broken_lo: usize,
        broken_hi: usize,
    ) {
        let desc = parse_descriptor(desc_json).expect("v2 descriptor must parse");
        assert_eq!(desc.trace_width, expected_width, "v2 trace width");
        assert_eq!(honest.len(), expected_width, "honest witness width");
        assert_eq!(forged.len(), expected_width, "forged witness width");

        // EXECUTE → PROVE → VERIFY: the executor-derived honest witness proves+verifies.
        let proof = prove_executor_derived_v2(desc_json, honest)
            .expect("the EXECUTOR-DERIVED v2 witness must prove+verify");
        verify_descriptor(&desc, &proof)
            .expect("re-verify of the executor-derived v2 proof must succeed");

        // ANTI-GHOST: the forged post-state breaks ONE EQ gate (a real UNSAT).
        assert_ne!(
            forged[broken_lo], forged[broken_hi],
            "the forged witness MUST break the EQ gate {} = {} (the tampered component shows up)",
            broken_lo, broken_hi
        );
        let tampered = std::panic::catch_unwind(|| {
            let p = prove_descriptor(&desc, forged)?;
            verify_descriptor(&desc, &p)
        });
        match tampered {
            // Prover panicked on the broken EQ gate: forgery rejected (real UNSAT).
            Err(_) => {}
            // Prover produced a proof: verification MUST reject it.
            Ok(verify_result) => assert!(
                verify_result.is_err(),
                "the v2 forgery (real executor-derived witness) MUST be rejected by the \
                 broken EQ gate, but a proof verified — the anti-ghost tooth failed"
            ),
        }
    }

    /// `dregg-balanceA-v2`: per-asset value movement (touched = `bal`). The forged
    /// post-state mints bystander cell 2's asset-0 balance 50 → 999; the
    /// component-bind gate `68 = 69` breaks (the moved balances still conserve).
    const BALANCEA_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-balanceA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_balance_a() {
        // Lean `balanceHonestWitnessJson` golden.
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 100000005000053, 70000035000054, 3, 3, 70000035000050, 70000035000050, 1, 1,
        ];
        // Lean `balanceForgedWitnessJson` golden (cell 2 minted 50 → 999): wire 68 changes.
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 100000005000053, 70000035001003, 3, 3, 70000035000999, 70000035000050, 1, 1,
        ];
        v2_beachhead(BALANCEA_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-burn-v2`: per-asset supply destruction (touched = `bal`). The forged
    /// post-state mints bystander cell 2 (50 → 999); the component-bind gate `68 = 69`
    /// breaks. Goldens pinned by Lean's `Dregg2.Circuit.Witness.BurnAWitness`.
    /// (Reuses the existing `BURN_DESCRIPTOR_JSON` const from the roundtrip test.)
    #[test]
    fn lean_executor_derived_burn_a() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 100000053, 70000054, 3, 3, 70000050, 70000050, 1, 1,
        ];
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 100000053, 70001003, 3, 3, 70000999, 70000050, 1, 1,
        ];
        v2_beachhead(BURN_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-bridgeMintA-v2`: bridge-INBOUND per-asset mint (touched = `bal`, credit).
    /// The forged post-state ALSO mints bystander cell 2 (50 → 999); the component-bind
    /// gate `68 = 69` breaks. Goldens pinned by Lean's
    /// `Dregg2.Circuit.Witness.BridgeMintAWitness`.
    const BRIDGE_MINT_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-bridgeMintA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_bridge_mint_a() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 100000053, 130000054, 3, 3, 130000050, 130000050, 1, 1,
        ];
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 100000053, 130001003, 3, 3, 130000999, 130000050, 1, 1,
        ];
        v2_beachhead(BRIDGE_MINT_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-bridgeFinalizeA-v2`: bridge-outbound no-credit RESOLVE (touched =
    /// `escrows`, a `listComponent`). The forged post-state leaves the finalized
    /// record id 7 UNresolved (a double-finalize laundering); the component-bind
    /// gate `68 = 69` breaks. Goldens pinned by Lean's
    /// `Dregg2.Circuit.Witness.BridgeFinalizeAWitness`.
    const BRIDGE_FINALIZE_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-bridgeFinalizeA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_bridge_finalize_a() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 2000705001000809103, 2000705101000809104, 2, 2,
            2000705101000809101, 2000705101000809101, 1, 1,
        ];
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 2000705001000809103, 2000705001000809104, 2, 2,
            2000705001000809101, 2000705101000809101, 1, 1,
        ];
        v2_beachhead(BRIDGE_FINALIZE_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-attenuateA-v2`: TOTAL authority self-narrowing (touched = `caps`, a
    /// `funcComponent`). Honest: label 0 narrows its idx-1 `node 9` cap to `[read]`.
    /// The forged post-state ALSO grants bystander label 1 a STOLEN `node 9` cap (a
    /// privilege escalation the attenuation never authorized); the component-bind gate
    /// `68 = 69` breaks. Goldens pinned by Lean's
    /// `Dregg2.Circuit.Witness.AttenuateAWitness`.
    const ATTENUATE_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-attenuateA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_attenuate_a() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 20105010900000002, 20105010900000003, 2, 2,
            20105010900000000, 20105010900000000, 1, 1,
        ];
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 20105010900000002, 20105010900010112, 2, 2,
            20105010900010109, 20105010900000000, 1, 1,
        ];
        v2_beachhead(ATTENUATE_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-delegate-v2`: the Granovetter unattenuated held-cap copy (touched =
    /// `kernel.caps`, a `funcComponent`). Honest: delegator 0 (holding `node 5`)
    /// grants recipient 1 the held cap to target 5. The forged post-state has
    /// recipient 1 STEAL an extra `node 9` cap on top of the honest grant; the
    /// component-bind gate `68 = 69` breaks (the rest frame + guard stay honest, so
    /// a projection circuit would have passed it). Goldens pinned by Lean's
    /// `Dregg2.Circuit.Witness.DelegateWitness.{descriptorJson, honest/forgedWitnessJson}`.
    /// (Reuses `DELEGATE_DESCRIPTOR_JSON` — the SAME Lean-emitted v2 circuit the
    /// hand-picked `lean_emitted_delegate_roundtrip` parses; the witness HERE is
    /// executor-derived, not hand-picked.)
    #[test]
    fn lean_executor_derived_delegate() {
        // Lean `DelegateWitness.honestWitnessJson` golden (recCDelegate post-state).
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 1015000000000003, 1015001016000003, 3, 3, 1015001015000000, 1015001015000000,
            1000000, 1000000,
        ];
        // Lean `DelegateWitness.forgedWitnessJson` golden (recipient steals `node 9`):
        // wire 68 (component-post digest) changes; 68 != 69.
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 1015000000000003, 1017019016000003, 3, 3, 1017019015000000, 1015001015000000,
            1000000, 1000000,
        ];
        v2_beachhead(DELEGATE_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-cellSealA-v2`: Live → Sealed lifecycle transition (touched =
    /// `kernel.lifecycle`, a `funcComponent`). Honest: actor 0 self-seals cell 0.
    /// The forged post-state ALSO flips a THIRD cell (2) to Sealed — a bystander
    /// lifecycle tamper; the component-bind gate `68 = 69` breaks. Goldens pinned by
    /// `Dregg2.Circuit.Witness.CellSealWitness.{sealDescriptorJson, seal*WitnessJson}`.
    const CELLSEAL_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-cellSealA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_cell_seal() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 3, 2000003, 3, 3, 1000000, 1000000, 1000000, 1000000,
        ];
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 3, 2000004, 3, 3, 1000001, 1000000, 1000000, 1000000,
        ];
        v2_beachhead(CELLSEAL_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-cellUnsealA-v2`: Sealed → Live (touched = `kernel.lifecycle`). Honest:
    /// actor 0 self-unseals cell 0 (it was Sealed). The forged post-state flips a
    /// THIRD cell (2) to Sealed; the component-bind gate `68 = 69` breaks. Goldens
    /// pinned by `CellSealWitness.{unsealDescriptorJson, unseal*WitnessJson}`.
    const CELLUNSEAL_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-cellUnsealA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_cell_unseal() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 1000003, 1000003, 3, 3, 0, 0, 1000000, 1000000,
        ];
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 1000003, 1000004, 3, 3, 1, 0, 1000000, 1000000,
        ];
        v2_beachhead(CELLUNSEAL_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-createSealPairA-v2`: the gated double c-list grant installing a
    /// sealer/unsealer keypair (touched = `kernel.caps`, a `funcComponent`). Honest:
    /// actor 0 (self-authority over sealerHolder 0) installs `sealerCap 7` at 0 and
    /// `unsealerCap 7` at 1. The forged post-state has a THIRD holder (cell 2) steal
    /// a `node 9` cap; the component-bind gate `68 = 69` breaks. Goldens pinned by
    /// `Dregg2.Circuit.Witness.CreateSealPairWitness.{descriptorJson, *WitnessJson}`.
    const CREATESEALPAIR_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-createSealPairA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_create_seal_pair() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 3, 1507001508000003, 3, 3, 1507001507000000, 1507001507000000, 1000000, 1000000,
        ];
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 3, 1507001508001022, 3, 3, 1507001507001019, 1507001507000000, 1000000, 1000000,
        ];
        v2_beachhead(CREATESEALPAIR_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-createEscrowA-v2` (DUAL-component, width 74, 5 gates): DEBIT `bal` at
    /// `(creator,asset)` AND PREPEND an unresolved `EscrowRecord` onto `escrows`.
    /// Honest: actor/creator 0 (self-authority, bal[0][0]=100) locks 30 of asset 0
    /// for recipient 1. The forged post-state ALSO mints a THIRD cell (2)'s bal
    /// 0 → 999; the comp1-bal gate `68 = 69` breaks (the escrow comp2 `70 = 71` + log
    /// stay honest). Goldens pinned by
    /// `Dregg2.Circuit.Witness.CreateEscrowWitness.{descriptorJson, *WitnessJson}`.
    const CREATEESCROW_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-createEscrowA-v2","trace_width":74,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}}]}"#;

    #[test]
    fn lean_executor_derived_create_escrow() {
        let honest: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 100000000000003, 70000002001033, 3, 3, 70000000000000, 70000000000000, 1001030,
            1001030, 1000000, 1000000,
        ];
        let forged: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 100000000000003, 70000002002032, 3, 3, 70000000000999, 70000000000000, 1001030,
            1001030, 1000000, 1000000,
        ];
        v2_beachhead(CREATEESCROW_DESCRIPTOR_JSON, 74, &honest, &forged, 68, 69);
    }

    // ========================================================================
    // The v1 verifiable-execution beachhead tests (the CELL/LOG effect family,
    // `EffectCommit`). Each emits the SAME 74-wire, 5-gate full-state circuit:
    // guard bit (`var 0 = 1`) + four frame-forcing EQ gates `66=67` (rest),
    // `68=69` (frame), `70=71` (touched), `72=73` (log). Only the AIR name differs.
    //
    // The witness bytes are pasted verbatim from the Lean goldens
    // `Dregg2.Circuit.Witness.<Effect>Witness.{honestWitnessJson, forged…Json}`
    // (computed by `<effect>WitnessVec`, which runs the real chained executor
    // `execFullA` and lays out the full-state assignment with concrete-surface
    // digest columns; the unconstrained roots 64/65 are zeroed for i64-safety).
    // ========================================================================

    /// Shared v1 driver: prove+verify the honest 74-wire witness through the real
    /// Plonky3 prover; assert EACH forged witness is rejected (a real UNSAT on the
    /// named broken EQ gate). `forgeries` pairs a label with `(witness, broken_lo,
    /// broken_hi)` — the EQ gate the forged post-state breaks.
    fn v1_beachhead(
        desc_json: &str,
        honest: &[i64],
        forgeries: &[(&str, &[i64], usize, usize)],
    ) {
        let desc = parse_descriptor(desc_json).expect("v1 descriptor must parse");
        assert_eq!(desc.trace_width, 74, "v1 trace width");
        assert_eq!(desc.constraints.len(), 5, "v1 gate count");
        assert_eq!(honest.len(), 74, "honest witness width");
        // The honest witness satisfies every gate.
        assert_eq!(honest[0], 1, "guard bit");
        assert_eq!(honest[66], honest[67], "rest frame");
        assert_eq!(honest[68], honest[69], "frame reuse");
        assert_eq!(honest[70], honest[71], "touched bind");
        assert_eq!(honest[72], honest[73], "log bind");

        // EXECUTE → PROVE → VERIFY: the executor-derived honest witness proves+verifies.
        let proof = prove_executor_derived_v2(desc_json, honest)
            .expect("the EXECUTOR-DERIVED v1 witness must prove+verify");
        verify_descriptor(&desc, &proof)
            .expect("re-verify of the executor-derived v1 proof must succeed");

        // ANTI-GHOST: each REAL forged post-state breaks ONE EQ gate (a real UNSAT).
        for (label, forged, lo, hi) in forgeries {
            assert_eq!(forged.len(), 74, "forged witness width [{label}]");
            assert_ne!(
                forged[*lo], forged[*hi],
                "forgery [{label}] MUST break the EQ gate {lo} = {hi}"
            );
            let tampered = std::panic::catch_unwind(|| {
                let p = prove_descriptor(&desc, forged)?;
                verify_descriptor(&desc, &p)
            });
            match tampered {
                Err(_) => {} // prover panicked on the broken gate: forgery rejected (real UNSAT)
                Ok(verify_result) => assert!(
                    verify_result.is_err(),
                    "v1 forgery [{label}] MUST be rejected by the broken EQ gate, but a proof verified"
                ),
            }
        }
    }

    /// `dregg-emitEventA-v1` (log-only): honest emit on cell 0. Forgeries: (F1) a
    /// tampered receipt row (actor 9 not 0) ⇒ log-bind gate `72=73` breaks; (F2) a
    /// minted bystander cell 2 (50 → 999) ⇒ frame-reuse gate `68=69` breaks.
    const EMITEVENT_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-emitEventA-v1","trace_width":74,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}}]}"#;

    #[test]
    fn lean_executor_derived_emit_event() {
        // Lean `EmitEventWitness.honestWitnessJson`.
        let honest: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 3000100000005000050, 3000100000005000050, 0, 0, 1000000, 1000000,
        ];
        // `forgedLogWitnessJson` (tampered receipt row): wire 72 != 73.
        let forged_log: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 3000100000005000050, 3000100000005000050, 0, 0, 1009000, 1000000,
        ];
        // `forgedCellWitnessJson` (minted bystander cell 2): wire 68 != 69.
        let forged_cell: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 3000100000005000050, 3000100000005000999, 0, 0, 1000000, 1000000,
        ];
        v1_beachhead(
            EMITEVENT_DESCRIPTOR_JSON,
            &honest,
            &[
                ("tampered receipt row", &forged_log, 72, 73),
                ("minted bystander cell", &forged_cell, 68, 69),
            ],
        );
    }

    /// `dregg-incrementNonceA-v1` (cell-touching monotone): actor 0 bumps cell 0's
    /// nonce to 7. Forgeries: (F1) minted bystander cell 2 (50 → 999) ⇒ frame-reuse
    /// gate `68=69` breaks; (F2) tampered receipt row ⇒ log-bind gate `72=73` breaks.
    /// (A wrong-nonce forgery is invisible to the balance-only toy leaf hash; the
    /// nonce soundness rides the abstract `cellLeafInjective` portal — see the Lean
    /// `IncrementNonceWitness` ANTI-GHOST NOTE.)
    const INCREMENT_NONCE_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-incrementNonceA-v1","trace_width":74,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}}]}"#;

    #[test]
    fn lean_executor_derived_increment_nonce() {
        // Lean `IncrementNonceWitness.honestWitnessJson`.
        let honest: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 2000005000050, 2000005000050, 1000100, 1000100, 1000000, 1000000,
        ];
        // `forgedCellWitnessJson` (minted bystander cell 2): wire 68 != 69.
        let forged_cell: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 2000005000050, 2000005000999, 1000100, 1000100, 1000000, 1000000,
        ];
        // `forgedLogWitnessJson` (tampered receipt row): wire 72 != 73.
        let forged_log: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 2000005000050, 2000005000050, 1000100, 1000100, 1009000, 1000000,
        ];
        v1_beachhead(
            INCREMENT_NONCE_DESCRIPTOR_JSON,
            &honest,
            &[
                ("minted bystander cell", &forged_cell, 68, 69),
                ("tampered receipt row", &forged_log, 72, 73),
            ],
        );
    }

    /// `dregg-makeSovereignA-v1` (commitment rebind): actor 0 rebinds cell 0 to a
    /// commitment-only record. Forgeries: (F1) the rebound cell installed with the
    /// WRONG value (balance 777) ⇒ touched-bind gate `70=71` breaks (the rebind MOVES
    /// the balance, so the touched gate is meaningful here); (F2) a minted bystander
    /// cell 2 (50 → 999) ⇒ frame-reuse gate `68=69` breaks.
    const MAKE_SOVEREIGN_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-makeSovereignA-v1","trace_width":74,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}}]}"#;

    #[test]
    fn lean_executor_derived_make_sovereign() {
        // Lean `MakeSovereignWitness.honestWitnessJson`.
        let honest: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 2000005000050, 2000005000050, 1000000, 1000000, 1000000, 1000000,
        ];
        // `forgedTouchedWitnessJson` (wrong rebound value): wire 70 != 71.
        let forged_touched: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 2000005000050, 2000005000050, 1000777, 1000000, 1000000, 1000000,
        ];
        // `forgedCellWitnessJson` (minted bystander cell 2): wire 68 != 69.
        let forged_cell: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 2000005000050, 2000005000999, 1000000, 1000000, 1000000, 1000000,
        ];
        v1_beachhead(
            MAKE_SOVEREIGN_DESCRIPTOR_JSON,
            &honest,
            &[
                ("wrong rebound value", &forged_touched, 70, 71),
                ("minted bystander cell", &forged_cell, 68, 69),
            ],
        );
    }

    /// `dregg-exerciseA-v1` (composite hold-gate, log-only outer layer): actor 0
    /// holds a `node 1` cap, exercises the edge to target 1 (kernel frozen, auth
    /// receipt prepended). Forgeries: (F1) a tampered receipt row ⇒ log-bind gate
    /// `72=73` breaks; (F2) a minted bystander cell 2 (50 → 999) ⇒ frame-reuse gate
    /// `68=69` breaks.
    const EXERCISE_HOLD_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-exerciseA-v1","trace_width":74,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}}]}"#;

    #[test]
    fn lean_executor_derived_exercise() {
        // Lean `ExerciseWitness.honestWitnessJson`.
        let honest: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 3000100000005000050, 3000100000005000050, 0, 0, 1000000, 1000000,
        ];
        // `forgedLogWitnessJson` (tampered auth receipt): wire 72 != 73.
        let forged_log: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 3000100000005000050, 3000100000005000050, 0, 0, 1009990, 1000000,
        ];
        // `forgedCellWitnessJson` (minted bystander cell 2): wire 68 != 69.
        let forged_cell: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 3000100000005000050, 3000100000005000999, 0, 0, 1000000, 1000000,
        ];
        v1_beachhead(
            EXERCISE_HOLD_DESCRIPTOR_JSON,
            &honest,
            &[
                ("tampered auth receipt", &forged_log, 72, 73),
                ("minted bystander cell", &forged_cell, 68, 69),
            ],
        );
    }

    /// `dregg-refusalA-v1`: the cell-state-audit refusal-slot write (v1 framework, width
    /// 74, 5 gates). Forged post-state mints bystander cell 2 (50 → 999): the frame-reuse
    /// gate `68 = 69` breaks while the refusal write + receipt log stay honest.
    const REFUSALA_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-refusalA-v1","trace_width":74,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}}]}"#;

    #[test]
    fn lean_executor_derived_refusal() {
        // Lean `RefusalWitness.honestWitnessJson` golden.
        let honest: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 2000005000050, 2000005000050, 1000100, 1000100, 1000000, 1000000,
        ];
        // `forgedCellWitnessJson` (minted bystander cell 2): wire 69 changes (68 != 69).
        let forged_cell: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 2000005000050, 2000005000999, 1000100, 1000100, 1000000, 1000000,
        ];
        v1_beachhead(
            REFUSALA_DESCRIPTOR_JSON,
            &honest,
            &[("minted bystander cell", &forged_cell, 68, 69)],
        );
    }

    /// `dregg-receiptArchiveA-v1`: the cell-state-audit lifecycle-slot write (v1 framework,
    /// width 74, 5 gates). Same shape as `refusalA` (single touched cell + growing receipt
    /// log), differing only in the written slot. Forged post-state mints bystander cell 2
    /// (50 → 999): the frame-reuse gate `68 = 69` breaks. Goldens from Lean
    /// `Dregg2.Circuit.Witness.ReceiptArchiveWitness.{honest,forgedCell}WitnessJson`.
    const RECEIPTARCHIVEA_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-receiptArchiveA-v1","trace_width":74,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}}]}"#;

    #[test]
    fn lean_executor_derived_receipt_archive() {
        let honest: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 2000005000050, 2000005000050, 1000100, 1000100, 1000000, 1000000,
        ];
        let forged_cell: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 3, 3, 2000005000050, 2000005000999, 1000100, 1000100, 1000000, 1000000,
        ];
        v1_beachhead(
            RECEIPTARCHIVEA_DESCRIPTOR_JSON,
            &honest,
            &[("minted bystander cell", &forged_cell, 68, 69)],
        );
    }

    /// `dregg-refreshDelegationA-v2`: the parent-c-list snapshot into `kernel.delegations`
    /// (a `funcComponent`, width 72). Honest: child 1 (parent 0 holding `[node 5]`) refreshes
    /// its delegation snapshot to `[node 5]`. The forged post-state TAMPERS the snapshot
    /// (child 1 steals an extra `node 9`): the component-bind gate `68 = 69` breaks while the
    /// rest frame + log stay honest. Goldens from Lean
    /// `Dregg2.Circuit.Witness.RefreshDelegationWitness.{honest,forged}WitnessJson`.
    const REFRESHDELEGATIONA_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-refreshDelegationA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_refresh_delegation() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 927922, 774219, 2, 2, 773953, 773953, 264, 264,
        ];
        // Forged: child 1's delegation snapshot tampered (stole node 9): wire 68 changes.
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 927922, 710615, 2, 2, 710349, 773953, 264, 264,
        ];
        v2_beachhead(REFRESHDELEGATIONA_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    // ========================================================================
    // Batch B6: ten more v2/v5 effects on the verifiable-execution beachhead.
    // Each pastes the EXACT executor-derived witness bytes the Lean
    // `Dregg2.Circuit.Witness.<Effect>Witness` goldens pin, the Lean-emitted v2
    // descriptor (4 gates, width 72), proves+verifies the honest witness, and
    // asserts the REAL forged post-state breaks the component-bind gate `68=69`.
    // ========================================================================

    /// `dregg-revokeDelegationA-v2`: the cap-graph `removeEdge` (touched = `kernel.caps`,
    /// a `funcComponent`). Honest: holder 0 (holding `[node 5, node 7]`) revokes the
    /// `node 5` cap conferring an edge to target 5, leaving `[node 7]`. The forged
    /// post-state FAILS to revoke (keeps `node 5`): the component-bind gate `68 = 69`
    /// breaks while the rest frame + log stay honest. Goldens from Lean
    /// `Dregg2.Circuit.Witness.RevokeDelegationWitness.{descriptorJson, honest/forgedWitnessJson}`.
    const REVOKE_DELEGATION_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-revokeDelegationA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_revoke_delegation() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 501156, 1170813, 2, 2, 1170548, 1170548, 263, 263,
        ];
        // Forged: holder 0 keeps the un-revoked `node 5` cap; wire 68 (post caps digest) differs.
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 501156, 501418, 2, 2, 501153, 1170548, 263, 263,
        ];
        v2_beachhead(REVOKE_DELEGATION_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-unsealA-v2`: the seal-box UNSEAL (touched = `kernel.caps`, a `funcComponent`).
    /// Honest: actor 0 (holding the unsealer cap `endpoint 7 [reply]`) unseals pair 7 from the
    /// store and grants the recovered payload `node 5` to recipient 1. The forged post-state
    /// DROPS the grant (recipient 1 stays empty): the component-bind gate `68 = 69` breaks while
    /// the rest frame + log stay honest. Goldens from Lean
    /// `Dregg2.Circuit.Witness.UnsealWitness.{descriptorJson, honest/forgedWitnessJson}`.
    const UNSEALA_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-unsealA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_unseal() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 97833, 1944132, 15, 15, 1943854, 1943854, 263, 263,
        ];
        // Forged: the unseal grant is dropped; wire 68 (post caps digest) differs.
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 97833, 98095, 15, 15, 97817, 1943854, 263, 263,
        ];
        v2_beachhead(UNSEALA_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-validateHandoffA-v2`: the 3-vat handoff = Granovetter unattenuated held-cap copy
    /// (touched = `kernel.caps`, a `funcComponent`, executor `recCDelegate`). Honest: intro 0
    /// (holding `node 5`) hands the held cap to recipient 1. The forged post-state has recipient 1
    /// STEAL an extra `node 9` cap; the component-bind gate `68 = 69` breaks. Goldens from Lean
    /// `Dregg2.Circuit.Witness.ValidateHandoffWitness.{descriptorJson, honest/forgedWitnessJson}`.
    const VALIDATE_HANDOFF_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-validateHandoffA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_validate_handoff() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 1672998, 1519294, 2, 2, 1519029, 1519029, 263, 263,
        ];
        // Forged: recipient 1 steals an extra `node 9`; wire 68 (post caps digest) differs.
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 1672998, 1455690, 2, 2, 1455425, 1519029, 263, 263,
        ];
        v2_beachhead(VALIDATE_HANDOFF_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-swissExportA-v2`: mint a CapTP sturdy ref (touched = `kernel.swiss`, a `listComponent`,
    /// FULL list equality). Honest: actor 0 self-exports sw 7 → target 1 (refcount 1). The forged
    /// post-state inserts the record with a double-counted `refcount := 2`; the component-bind gate
    /// `68 = 69` breaks. Goldens from Lean
    /// `Dregg2.Circuit.Witness.SwissExportWitness.{descriptorJson, honest/forgedWitnessJson}`.
    const SWISS_EXPORT_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-swissExportA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_swiss_export() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 4, 17139, 2, 2, 16874, 16874, 263, 263,
        ];
        // Forged: the inserted record carries refcount 2 (double-counted); wire 68 differs.
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 4, 17252, 2, 2, 16987, 16874, 263, 263,
        ];
        v2_beachhead(SWISS_EXPORT_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-swissHandoffA-v2`: the 3-vat handoff cert-bind (touched = `kernel.swiss`, a
    /// `listComponent`). Honest: introducer 0 binds cert 99 to the existing sw-7 entry and bumps its
    /// refcount to 2. The forged post-state bumps the refcount but does NOT bind the cert (cert stays
    /// `none`); the component-bind gate `68 = 69` breaks. Goldens from Lean
    /// `Dregg2.Circuit.Witness.SwissHandoffWitness.{descriptorJson, honest/forgedWitnessJson}`.
    const SWISS_HANDOFF_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-swissHandoffA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_swiss_handoff() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 16877, 29952, 2, 2, 29687, 29687, 263, 263,
        ];
        // Forged: the cert is NOT bound (cert stays none); wire 68 differs.
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 16877, 17252, 2, 2, 16987, 29687, 263, 263,
        ];
        v2_beachhead(SWISS_HANDOFF_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-sealA-v2`: the seal-box constructor (touched = `kernel.sealedBoxes`, a `listComponent`).
    /// Honest: actor 0 (holding the sealer cap for pid 5 + the payload `node 9`) seals `node 9` under
    /// pair 5. The forged post-state binds a SUBSTITUTED payload `node 42` in the box; the
    /// component-bind gate `68 = 69` breaks. Goldens from Lean
    /// `Dregg2.Circuit.Witness.SealWitness.{descriptorJson, honest/forgedWitnessJson}`.
    const SEALA_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-sealA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_seal() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 38, 30338, 36, 36, 30039, 30039, 263, 263,
        ];
        // Forged: the box binds a substituted payload (node 42 not node 9); wire 68 differs.
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 38, 40931, 36, 36, 40632, 30039, 263, 263,
        ];
        v2_beachhead(SEALA_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    // ========================================================================
    // Batch B3 (escrow + queue families): two v2-DUAL effects (width 74, 5 gates:
    // guard, rest 66/67, bind1 68/69, bind2 70/71, log 72/73) and two v2 queue-list
    // effects (width 72, 4 gates). Each pastes the EXACT executor-derived witness
    // bytes the Lean `Dregg2.Circuit.Witness.<Effect>` goldens pin, proves+verifies
    // the honest witness through the real Plonky3 prover, and asserts the REAL
    // forged post-state breaks a component-bind gate.
    // ========================================================================

    /// `dregg-releaseEscrowA-v2dual`: dual-component escrow settle (credit `bal` at the
    /// recipient + mark `escrows` resolved). Forged post mints the recipient credit (999,
    /// not the parked 30): the comp1-bind gate `68 = 69` breaks. Goldens from Lean
    /// `Dregg2.Circuit.Witness.ReleaseEscrowWitness.{honest,forged}WitnessJson`.
    const RELEASE_ESCROW_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-releaseEscrowA-v2dual","trace_width":74,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}}]}"#;

    #[test]
    fn lean_executor_derived_release_escrow() {
        let honest: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 344325, 1298045, 2, 2, 1281785, 1281785, 15995, 15995, 263, 263,
        ];
        let forged: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 344325, 694659, 2, 2, 678399, 1281785, 15995, 15995, 263, 263,
        ];
        v1_beachhead(
            RELEASE_ESCROW_DESCRIPTOR_JSON,
            &honest,
            &[("minted recipient credit", &forged, 68, 69)],
        );
    }

    /// `dregg-refundEscrowA-v2dual`: dual-component escrow refund (credit `bal` at the CREATOR
    /// + mark `escrows` resolved). Forged post mints the creator credit (999, not 30): the
    /// comp1-bind gate `68 = 69` breaks. Goldens from Lean
    /// `Dregg2.Circuit.Witness.RefundEscrowWitness.{honest,forged}WitnessJson`.
    const REFUND_ESCROW_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-refundEscrowA-v2dual","trace_width":74,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}}]}"#;

    #[test]
    fn lean_executor_derived_refund_escrow() {
        let honest: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 344325, 595622, 2, 2, 579362, 579362, 15995, 15995, 263, 263,
        ];
        let forged: [i64; 74] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 344325, 1904010, 2, 2, 1887750, 579362, 15995, 15995, 263, 263,
        ];
        v1_beachhead(
            REFUND_ESCROW_DESCRIPTOR_JSON,
            &honest,
            &[("minted creator credit", &forged, 68, 69)],
        );
    }

    /// `dregg-queueResizeA-v2`: balance-neutral FIFO queue re-cap (touched = `kernel.queues`,
    /// a `listComponent`). Forged post TAMPERS the buffer (a message dropped on the re-cap):
    /// the component-bind gate `68 = 69` breaks. Goldens from Lean
    /// `Dregg2.Circuit.Witness.QueueResizeWitness.{honest,forged}WitnessJson`.
    const QUEUE_RESIZE_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-queueResizeA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_queue_resize() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 16037, 16308, 1, 1, 16044, 16044, 263, 263,
        ];
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 16037, 16237, 1, 1, 15973, 16044, 263, 263,
        ];
        v2_beachhead(QUEUE_RESIZE_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

    /// `dregg-queuePipelineStepA-v2`: message-routing fan-out (touched = `kernel.queues`, a
    /// `listComponent`). Forged post DROPS the routed message (sink 11 stays empty): the
    /// component-bind gate `68 = 69` breaks. Goldens from Lean
    /// `Dregg2.Circuit.Witness.QueuePipelineStepWitness.{honest,forged}WitnessJson`.
    const QUEUE_PIPELINE_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-queuePipelineStepA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

    #[test]
    fn lean_executor_derived_queue_pipeline_step() {
        let honest: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 395231, 1557420, 3, 3, 1557154, 1557154, 263, 263,
        ];
        let forged: [i64; 72] = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 395231, 195352, 3, 3, 195086, 1557154, 263, 263,
        ];
        v2_beachhead(QUEUE_PIPELINE_DESCRIPTOR_JSON, 72, &honest, &forged, 68, 69);
    }

}
