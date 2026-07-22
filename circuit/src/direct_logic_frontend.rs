//! Checked finite-logic front end for the live descriptor IR-v2 relation.
//!
//! The source fragment is deliberately finite and executable.  Inputs and
//! bound variables range over `Bool` or a declared finite enumeration, terms
//! are variables/constants, and formulae contain equality, truth-table
//! predicates, Boolean connectives, and bounded quantifiers.  Quantifiers are
//! deterministically unrolled.  Enumeration inputs use an exact one-hot
//! encoding; the generated relation checks it with one linear sum-to-one gate
//! in addition to the per-column Booleanity gates.
//!
//! The target is the deployed [`EffectVmDescriptor2`] grammar.  Source atoms
//! occupy main-trace columns, receive always-on BabyBear Booleanity gates, and
//! the final always-on gate forces the exact Boolean polynomial to one.  The
//! emitted JSON follows Lean's `emitVmJson2` field/tag order for this restricted
//! descriptor face and is parsed and structurally checked before it is returned.
//!
//! This is an executable Rust compiler with differential tests.  It is not a
//! Rust-to-Lean refinement theorem; the corresponding Lean construction lives
//! in `Dregg2.Logic.FiniteLogicDescriptorIR2`.

use std::collections::BTreeSet;
use std::fmt;

use crate::descriptor_ir2::{
    EffectVmDescriptor2, TID_MAIN, TableDef2, TableSem, VmConstraint2, WindowExpr, WindowGateSpec,
    parse_vm_descriptor2,
};
use crate::field::BabyBear;

/// Version of the source encoding, compiler rules, and portable artifact.
pub const DIRECT_LOGIC_FRONTEND_VERSION: u32 = 1;

/// A source type.  `UnboundedInteger` is representable so adapters can fail
/// closed instead of silently truncating an unbounded source domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LogicType {
    Bool,
    Finite { cardinality: usize },
    UnboundedInteger,
}

impl LogicType {
    fn cardinality(&self) -> Result<usize, FrontendError> {
        match self {
            Self::Bool => Ok(2),
            Self::Finite { cardinality: 0 } => Err(FrontendError::EmptyFiniteDomain),
            Self::Finite { cardinality } => Ok(*cardinality),
            Self::UnboundedInteger => Err(FrontendError::UnboundedDomain),
        }
    }
}

/// A named free input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputDecl {
    pub name: String,
    pub ty: LogicType,
}

/// A finite term.  Bound variables use de Bruijn indices (`0` is innermost).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Input(usize),
    Bound(usize),
    Constant { ty: LogicType, value: usize },
}

/// An explicit finite predicate table.  Entries are row-major in argument
/// order: `index = (((a0 * |A1|) + a1) * |A2| + a2) ...`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateTable {
    pub name: String,
    pub argument_types: Vec<LogicType>,
    pub values: Vec<bool>,
}

/// Checked bounded first-order formula syntax.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
    Top,
    Bottom,
    Equal(Term, Term),
    Predicate {
        table: PredicateTable,
        arguments: Vec<Term>,
    },
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    ForAll {
        binder: LogicType,
        body: Box<Formula>,
    },
    Exists {
        binder: LogicType,
        body: Box<Formula>,
    },
}

/// A complete finite-logic compilation unit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogicProgram {
    pub inputs: Vec<InputDecl>,
    pub formula: Formula,
}

/// Concrete source values used by the reference evaluator and atom encoder.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LogicValue {
    Bool(bool),
    Finite(usize),
}

/// Explicit resource limits.  No truncation, early-exit witness, or implicit
/// widening occurs when a limit is exceeded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompileLimits {
    pub maximum_source_nodes: usize,
    pub maximum_atoms: usize,
    pub maximum_predicate_entries: usize,
    pub maximum_quantifier_instances: usize,
    pub maximum_expanded_nodes: usize,
}

impl Default for CompileLimits {
    fn default() -> Self {
        Self {
            maximum_source_nodes: 2_048,
            maximum_atoms: 4_096,
            maximum_predicate_entries: 65_536,
            maximum_quantifier_instances: 65_536,
            maximum_expanded_nodes: 250_000,
        }
    }
}

/// A source input's exact trace-column encoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputEncoding {
    pub name: String,
    pub ty: LogicType,
    pub first_atom: usize,
    pub atom_count: usize,
}

/// The Boolean graph retained beside the descriptor for transparent
/// differential evaluation.  Truth is represented by `true`/field one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoolExpr {
    Atom(usize),
    Constant(bool),
    Not(Box<BoolExpr>),
    And(Box<BoolExpr>, Box<BoolExpr>),
    Or(Box<BoolExpr>, Box<BoolExpr>),
}

impl BoolExpr {
    pub fn evaluate(&self, atoms: &[bool]) -> Result<bool, FrontendError> {
        match self {
            Self::Atom(index) => {
                atoms
                    .get(*index)
                    .copied()
                    .ok_or(FrontendError::AtomVectorTooShort {
                        required: index.saturating_add(1),
                        actual: atoms.len(),
                    })
            }
            Self::Constant(value) => Ok(*value),
            Self::Not(value) => Ok(!value.evaluate(atoms)?),
            Self::And(left, right) => Ok(left.evaluate(atoms)? && right.evaluate(atoms)?),
            Self::Or(left, right) => Ok(left.evaluate(atoms)? || right.evaluate(atoms)?),
        }
    }

    fn node_count(&self) -> usize {
        match self {
            Self::Atom(_) | Self::Constant(_) => 1,
            Self::Not(value) => 1 + value.node_count(),
            Self::And(left, right) | Self::Or(left, right) => {
                1 + left.node_count() + right.node_count()
            }
        }
    }
}

/// A checked portable artifact.  The wire image is canonical for compiler
/// version 1 and its digest is over those exact UTF-8 bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompiledLogicArtifact {
    descriptor: EffectVmDescriptor2,
    descriptor_json: String,
    descriptor_blake3: [u8; 32],
    source_blake3: [u8; 32],
    formula_relation: BoolExpr,
    inputs: Vec<InputEncoding>,
    logical_atom_count: usize,
}

impl CompiledLogicArtifact {
    pub fn descriptor(&self) -> &EffectVmDescriptor2 {
        &self.descriptor
    }

    pub fn descriptor_json(&self) -> &str {
        &self.descriptor_json
    }

    pub fn descriptor_bytes(&self) -> &[u8] {
        self.descriptor_json.as_bytes()
    }

    pub fn descriptor_blake3(&self) -> [u8; 32] {
        self.descriptor_blake3
    }

    pub fn descriptor_blake3_hex(&self) -> String {
        hex32(&self.descriptor_blake3)
    }

    pub fn source_blake3(&self) -> [u8; 32] {
        self.source_blake3
    }

    pub fn source_blake3_hex(&self) -> String {
        hex32(&self.source_blake3)
    }

    pub fn input_encodings(&self) -> &[InputEncoding] {
        &self.inputs
    }

    pub fn logical_atom_count(&self) -> usize {
        self.logical_atom_count
    }

    /// Formula polynomial before the separate input-encoding gates.  Use
    /// [`Self::relation_accepts_atoms`] to evaluate the complete relation.
    pub fn source_relation(&self) -> &BoolExpr {
        &self.formula_relation
    }

    /// Encode typed source inputs as the canonical trace row.  A descriptor
    /// with no logical atoms has one false padding column because the live AIR
    /// does not admit a zero-width main trace.
    pub fn encode_inputs(&self, values: &[LogicValue]) -> Result<Vec<bool>, FrontendError> {
        if values.len() != self.inputs.len() {
            return Err(FrontendError::InputCountMismatch {
                expected: self.inputs.len(),
                actual: values.len(),
            });
        }
        let mut atoms = vec![false; self.descriptor.trace_width];
        for (index, (encoding, value)) in self.inputs.iter().zip(values).enumerate() {
            match (&encoding.ty, value) {
                (LogicType::Bool, LogicValue::Bool(bit)) => {
                    atoms[encoding.first_atom] = *bit;
                }
                (LogicType::Finite { cardinality }, LogicValue::Finite(selected))
                    if *selected < *cardinality =>
                {
                    atoms[encoding.first_atom + selected] = true;
                }
                (LogicType::Finite { cardinality }, LogicValue::Finite(selected)) => {
                    return Err(FrontendError::InputValueOutOfRange {
                        input: index,
                        value: *selected,
                        cardinality: *cardinality,
                    });
                }
                _ => return Err(FrontendError::InputValueTypeMismatch { input: index }),
            }
        }
        Ok(atoms)
    }

    /// Canonical BabyBear row accepted directly by
    /// [`crate::descriptor_ir2::prove_vm_descriptor2`].  The returned row is
    /// the complete one-row witness for this row-local relation.
    pub fn trace_row(&self, values: &[LogicValue]) -> Result<Vec<BabyBear>, FrontendError> {
        Ok(self
            .encode_inputs(values)?
            .into_iter()
            .map(|bit| if bit { BabyBear::ONE } else { BabyBear::ZERO })
            .collect())
    }

    /// One-row trace wrapper for the live prover API.
    pub fn one_row_trace(
        &self,
        values: &[LogicValue],
    ) -> Result<Vec<Vec<BabyBear>>, FrontendError> {
        Ok(vec![self.trace_row(values)?])
    }

    /// Evaluate the complete compiled relation, including input one-hot
    /// validity.  This is a transparent oracle, not a proof verifier.
    pub fn relation_accepts_atoms(&self, atoms: &[bool]) -> Result<bool, FrontendError> {
        if atoms.len() != self.descriptor.trace_width {
            return Err(FrontendError::AtomCountMismatch {
                expected: self.descriptor.trace_width,
                actual: atoms.len(),
            });
        }
        for encoding in &self.inputs {
            if let LogicType::Finite { cardinality } = encoding.ty {
                let selected = (0..cardinality)
                    .filter(|offset| atoms[encoding.first_atom + offset])
                    .count();
                if selected != 1 {
                    return Ok(false);
                }
            }
        }
        self.formula_relation.evaluate(atoms)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrontendError {
    EmptyFiniteDomain,
    UnboundedDomain,
    DuplicateInputName(String),
    SourceTooLarge {
        nodes: usize,
        maximum: usize,
    },
    TooManyAtoms {
        atoms: usize,
        maximum: usize,
    },
    PredicateTooLarge {
        entries: usize,
        maximum: usize,
    },
    PredicateShapeMismatch {
        expected: usize,
        actual: usize,
    },
    PredicateArityMismatch {
        expected: usize,
        actual: usize,
    },
    QuantifierExpansionTooLarge {
        instances: usize,
        maximum: usize,
    },
    ExpandedRelationTooLarge {
        nodes: usize,
        maximum: usize,
    },
    InputOutOfRange {
        index: usize,
        available: usize,
    },
    BoundVariableOutOfRange {
        index: usize,
        depth: usize,
    },
    ConstantOutOfRange {
        value: usize,
        cardinality: usize,
    },
    TypeMismatch {
        expected: LogicType,
        actual: LogicType,
    },
    InputCountMismatch {
        expected: usize,
        actual: usize,
    },
    InputValueTypeMismatch {
        input: usize,
    },
    InputValueOutOfRange {
        input: usize,
        value: usize,
        cardinality: usize,
    },
    AtomVectorTooShort {
        required: usize,
        actual: usize,
    },
    AtomCountMismatch {
        expected: usize,
        actual: usize,
    },
    InternalWireDrift(String),
}

impl fmt::Display for FrontendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for FrontendError {}

#[derive(Clone, Debug)]
struct BoundValue {
    ty: LogicType,
    value: usize,
}

struct Lowering<'a> {
    limits: &'a CompileLimits,
    inputs: Vec<InputEncoding>,
    bounds: Vec<BoundValue>,
    quantifier_instances: usize,
    construction_steps: usize,
}

impl Lowering<'_> {
    fn spend(&mut self, amount: usize) -> Result<(), FrontendError> {
        self.construction_steps = self.construction_steps.saturating_add(amount);
        if self.construction_steps > self.limits.maximum_expanded_nodes {
            return Err(FrontendError::ExpandedRelationTooLarge {
                nodes: self.construction_steps,
                maximum: self.limits.maximum_expanded_nodes,
            });
        }
        Ok(())
    }

    fn term_bits(&mut self, term: &Term) -> Result<(LogicType, Vec<BoolExpr>), FrontendError> {
        self.spend(1)?;
        match term {
            Term::Input(index) => {
                let encoding = self
                    .inputs
                    .get(*index)
                    .ok_or(FrontendError::InputOutOfRange {
                        index: *index,
                        available: self.inputs.len(),
                    })?;
                let bits = match encoding.ty {
                    LogicType::Bool => {
                        let atom = BoolExpr::Atom(encoding.first_atom);
                        vec![not(atom.clone()), atom]
                    }
                    LogicType::Finite { cardinality } => (0..cardinality)
                        .map(|offset| BoolExpr::Atom(encoding.first_atom + offset))
                        .collect(),
                    LogicType::UnboundedInteger => return Err(FrontendError::UnboundedDomain),
                };
                Ok((encoding.ty.clone(), bits))
            }
            Term::Bound(index) => {
                let depth = self.bounds.len();
                let bound = depth
                    .checked_sub(index.saturating_add(1))
                    .and_then(|position| self.bounds.get(position))
                    .ok_or(FrontendError::BoundVariableOutOfRange {
                        index: *index,
                        depth,
                    })?;
                let cardinality = bound.ty.cardinality()?;
                Ok((
                    bound.ty.clone(),
                    (0..cardinality)
                        .map(|value| BoolExpr::Constant(value == bound.value))
                        .collect(),
                ))
            }
            Term::Constant { ty, value } => {
                let cardinality = ty.cardinality()?;
                if *value >= cardinality {
                    return Err(FrontendError::ConstantOutOfRange {
                        value: *value,
                        cardinality,
                    });
                }
                Ok((
                    ty.clone(),
                    (0..cardinality)
                        .map(|candidate| BoolExpr::Constant(candidate == *value))
                        .collect(),
                ))
            }
        }
    }

    fn formula(&mut self, formula: &Formula) -> Result<BoolExpr, FrontendError> {
        self.spend(1)?;
        match formula {
            Formula::Top => Ok(BoolExpr::Constant(true)),
            Formula::Bottom => Ok(BoolExpr::Constant(false)),
            Formula::Equal(left, right) => {
                let (left_ty, left_bits) = self.term_bits(left)?;
                let (right_ty, right_bits) = self.term_bits(right)?;
                require_same_type(&left_ty, &right_ty)?;
                Ok(any(left_bits
                    .into_iter()
                    .zip(right_bits)
                    .map(|(l, r)| and(l, r))))
            }
            Formula::Predicate { table, arguments } => {
                if table.argument_types.len() != arguments.len() {
                    return Err(FrontendError::PredicateArityMismatch {
                        expected: table.argument_types.len(),
                        actual: arguments.len(),
                    });
                }
                let mut expected_entries = 1usize;
                let mut argument_bits = Vec::with_capacity(arguments.len());
                for (expected_ty, term) in table.argument_types.iter().zip(arguments) {
                    let cardinality = expected_ty.cardinality()?;
                    expected_entries = expected_entries.saturating_mul(cardinality);
                    let (actual_ty, bits) = self.term_bits(term)?;
                    require_same_type(expected_ty, &actual_ty)?;
                    argument_bits.push(bits);
                }
                if expected_entries > self.limits.maximum_predicate_entries {
                    return Err(FrontendError::PredicateTooLarge {
                        entries: expected_entries,
                        maximum: self.limits.maximum_predicate_entries,
                    });
                }
                if table.values.len() != expected_entries {
                    return Err(FrontendError::PredicateShapeMismatch {
                        expected: expected_entries,
                        actual: table.values.len(),
                    });
                }
                let cards: Vec<usize> = table
                    .argument_types
                    .iter()
                    .map(LogicType::cardinality)
                    .collect::<Result<_, _>>()?;
                let mut rows = Vec::new();
                for (flat, value) in table.values.iter().enumerate() {
                    if !value {
                        continue;
                    }
                    let tuple = decode_row_major(flat, &cards);
                    rows.push(all(tuple
                        .into_iter()
                        .enumerate()
                        .map(|(i, selected)| argument_bits[i][selected].clone())));
                }
                Ok(any(rows))
            }
            Formula::Not(value) => Ok(not(self.formula(value)?)),
            Formula::And(left, right) => Ok(and(self.formula(left)?, self.formula(right)?)),
            Formula::Or(left, right) => Ok(or(self.formula(left)?, self.formula(right)?)),
            Formula::ForAll { binder, body } => self.quantifier(binder, body, true),
            Formula::Exists { binder, body } => self.quantifier(binder, body, false),
        }
    }

    fn quantifier(
        &mut self,
        binder: &LogicType,
        body: &Formula,
        universal: bool,
    ) -> Result<BoolExpr, FrontendError> {
        let cardinality = binder.cardinality()?;
        self.quantifier_instances = self.quantifier_instances.saturating_add(cardinality);
        if self.quantifier_instances > self.limits.maximum_quantifier_instances {
            return Err(FrontendError::QuantifierExpansionTooLarge {
                instances: self.quantifier_instances,
                maximum: self.limits.maximum_quantifier_instances,
            });
        }
        let mut instances = Vec::with_capacity(cardinality);
        for value in 0..cardinality {
            self.bounds.push(BoundValue {
                ty: binder.clone(),
                value,
            });
            let instance = self.formula(body);
            self.bounds.pop();
            instances.push(instance?);
        }
        Ok(if universal {
            all(instances)
        } else {
            any(instances)
        })
    }
}

/// Compile a finite program to a live IR-v2 descriptor and stable wire image.
pub fn compile_logic_program(
    program: &LogicProgram,
    limits: &CompileLimits,
) -> Result<CompiledLogicArtifact, FrontendError> {
    let source_nodes = formula_node_count(&program.formula);
    if source_nodes > limits.maximum_source_nodes {
        return Err(FrontendError::SourceTooLarge {
            nodes: source_nodes,
            maximum: limits.maximum_source_nodes,
        });
    }

    let mut names = BTreeSet::new();
    let mut inputs = Vec::with_capacity(program.inputs.len());
    let mut next_atom = 0usize;
    for input in &program.inputs {
        if !names.insert(input.name.clone()) {
            return Err(FrontendError::DuplicateInputName(input.name.clone()));
        }
        let atom_count = match input.ty {
            LogicType::Bool => 1,
            LogicType::Finite { .. } => input.ty.cardinality()?,
            LogicType::UnboundedInteger => return Err(FrontendError::UnboundedDomain),
        };
        next_atom = next_atom.saturating_add(atom_count);
        if next_atom > limits.maximum_atoms {
            return Err(FrontendError::TooManyAtoms {
                atoms: next_atom,
                maximum: limits.maximum_atoms,
            });
        }
        inputs.push(InputEncoding {
            name: input.name.clone(),
            ty: input.ty.clone(),
            first_atom: next_atom - atom_count,
            atom_count,
        });
    }

    let mut lowering = Lowering {
        limits,
        inputs: inputs.clone(),
        bounds: Vec::new(),
        quantifier_instances: 0,
        construction_steps: 0,
    };
    let formula_relation = lowering.formula(&program.formula)?;
    let expanded_nodes = formula_relation.node_count();
    if expanded_nodes > limits.maximum_expanded_nodes {
        return Err(FrontendError::ExpandedRelationTooLarge {
            nodes: expanded_nodes,
            maximum: limits.maximum_expanded_nodes,
        });
    }

    let source_bytes = canonical_source_bytes(program);
    let source_blake3 = *blake3::hash(&source_bytes).as_bytes();
    let name = format!(
        "dregg-direct-logic-v{}-{}",
        DIRECT_LOGIC_FRONTEND_VERSION,
        hex32(&source_blake3)
    );
    let trace_width = next_atom.max(1);
    let finite_input_count = inputs
        .iter()
        .filter(|input| matches!(input.ty, LogicType::Finite { .. }))
        .count();
    let mut constraints = Vec::with_capacity(trace_width + finite_input_count + 1);
    for atom in 0..trace_width {
        constraints.push(VmConstraint2::WindowGate(WindowGateSpec {
            body: binary_body(atom),
            on_transition: false,
        }));
    }
    for input in &inputs {
        let LogicType::Finite { cardinality } = input.ty else {
            continue;
        };
        let sum = sum_window(
            (0..cardinality)
                .map(|offset| WindowExpr::Loc(input.first_atom + offset))
                .collect(),
        );
        constraints.push(VmConstraint2::WindowGate(WindowGateSpec {
            body: WindowExpr::Add(Box::new(sum), Box::new(WindowExpr::Const(-1))),
            on_transition: false,
        }));
    }
    constraints.push(VmConstraint2::WindowGate(WindowGateSpec {
        body: WindowExpr::Add(
            Box::new(bool_expr_to_window(&formula_relation)),
            Box::new(WindowExpr::Const(-1)),
        ),
        on_transition: false,
    }));
    let descriptor = EffectVmDescriptor2 {
        name,
        trace_width,
        public_input_count: 0,
        tables: vec![TableDef2 {
            id: TID_MAIN,
            name: "main".to_string(),
            arity: trace_width,
            sem: TableSem::Main,
        }],
        constraints,
        hash_sites: Vec::new(),
        ranges: Vec::new(),
    };
    let descriptor_json = canonical_descriptor_json(&descriptor)?;
    let reparsed =
        parse_vm_descriptor2(&descriptor_json).map_err(FrontendError::InternalWireDrift)?;
    if reparsed != descriptor {
        return Err(FrontendError::InternalWireDrift(
            "canonical wire did not round-trip to the compiled descriptor".to_string(),
        ));
    }
    let descriptor_blake3 = *blake3::hash(descriptor_json.as_bytes()).as_bytes();
    Ok(CompiledLogicArtifact {
        descriptor,
        descriptor_json,
        descriptor_blake3,
        source_blake3,
        formula_relation,
        inputs,
        logical_atom_count: next_atom,
    })
}

/// Transparent source evaluator, independent of descriptor construction.
pub fn evaluate_logic_program(
    program: &LogicProgram,
    inputs: &[LogicValue],
) -> Result<bool, FrontendError> {
    if inputs.len() != program.inputs.len() {
        return Err(FrontendError::InputCountMismatch {
            expected: program.inputs.len(),
            actual: inputs.len(),
        });
    }
    for (index, (decl, value)) in program.inputs.iter().zip(inputs).enumerate() {
        validate_value(index, &decl.ty, value)?;
    }
    eval_formula(program, &program.formula, inputs, &mut Vec::new())
}

fn validate_value(index: usize, ty: &LogicType, value: &LogicValue) -> Result<(), FrontendError> {
    match (ty, value) {
        (LogicType::Bool, LogicValue::Bool(_)) => Ok(()),
        (LogicType::Finite { cardinality }, LogicValue::Finite(value)) if *value < *cardinality => {
            Ok(())
        }
        (LogicType::Finite { cardinality }, LogicValue::Finite(value)) => {
            Err(FrontendError::InputValueOutOfRange {
                input: index,
                value: *value,
                cardinality: *cardinality,
            })
        }
        (LogicType::UnboundedInteger, _) => Err(FrontendError::UnboundedDomain),
        _ => Err(FrontendError::InputValueTypeMismatch { input: index }),
    }
}

fn eval_formula(
    program: &LogicProgram,
    formula: &Formula,
    inputs: &[LogicValue],
    bounds: &mut Vec<BoundValue>,
) -> Result<bool, FrontendError> {
    match formula {
        Formula::Top => Ok(true),
        Formula::Bottom => Ok(false),
        Formula::Equal(left, right) => {
            let (left_ty, left_value) = eval_term(program, left, inputs, bounds)?;
            let (right_ty, right_value) = eval_term(program, right, inputs, bounds)?;
            require_same_type(&left_ty, &right_ty)?;
            Ok(left_value == right_value)
        }
        Formula::Predicate { table, arguments } => {
            if table.argument_types.len() != arguments.len() {
                return Err(FrontendError::PredicateArityMismatch {
                    expected: table.argument_types.len(),
                    actual: arguments.len(),
                });
            }
            let mut flat = 0usize;
            let mut expected_entries = 1usize;
            for (expected_ty, term) in table.argument_types.iter().zip(arguments) {
                let cardinality = expected_ty.cardinality()?;
                expected_entries = expected_entries.saturating_mul(cardinality);
                let (actual_ty, value) = eval_term(program, term, inputs, bounds)?;
                require_same_type(expected_ty, &actual_ty)?;
                flat = flat.saturating_mul(cardinality).saturating_add(value);
            }
            if table.values.len() != expected_entries {
                return Err(FrontendError::PredicateShapeMismatch {
                    expected: expected_entries,
                    actual: table.values.len(),
                });
            }
            Ok(table.values[flat])
        }
        Formula::Not(value) => Ok(!eval_formula(program, value, inputs, bounds)?),
        Formula::And(left, right) => {
            let left = eval_formula(program, left, inputs, bounds)?;
            let right = eval_formula(program, right, inputs, bounds)?;
            Ok(left && right)
        }
        Formula::Or(left, right) => {
            let left = eval_formula(program, left, inputs, bounds)?;
            let right = eval_formula(program, right, inputs, bounds)?;
            Ok(left || right)
        }
        Formula::ForAll { binder, body } => {
            let cardinality = binder.cardinality()?;
            for value in 0..cardinality {
                bounds.push(BoundValue {
                    ty: binder.clone(),
                    value,
                });
                let result = eval_formula(program, body, inputs, bounds);
                bounds.pop();
                if !result? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Formula::Exists { binder, body } => {
            let cardinality = binder.cardinality()?;
            for value in 0..cardinality {
                bounds.push(BoundValue {
                    ty: binder.clone(),
                    value,
                });
                let result = eval_formula(program, body, inputs, bounds);
                bounds.pop();
                if result? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
    }
}

fn eval_term(
    program: &LogicProgram,
    term: &Term,
    inputs: &[LogicValue],
    bounds: &[BoundValue],
) -> Result<(LogicType, usize), FrontendError> {
    match term {
        Term::Input(index) => {
            let decl = program
                .inputs
                .get(*index)
                .ok_or(FrontendError::InputOutOfRange {
                    index: *index,
                    available: program.inputs.len(),
                })?;
            let value = inputs.get(*index).ok_or(FrontendError::InputOutOfRange {
                index: *index,
                available: inputs.len(),
            })?;
            Ok((
                decl.ty.clone(),
                match value {
                    LogicValue::Bool(value) => usize::from(*value),
                    LogicValue::Finite(value) => *value,
                },
            ))
        }
        Term::Bound(index) => {
            let depth = bounds.len();
            let value = depth
                .checked_sub(index.saturating_add(1))
                .and_then(|position| bounds.get(position))
                .ok_or(FrontendError::BoundVariableOutOfRange {
                    index: *index,
                    depth,
                })?;
            Ok((value.ty.clone(), value.value))
        }
        Term::Constant { ty, value } => {
            let cardinality = ty.cardinality()?;
            if *value >= cardinality {
                return Err(FrontendError::ConstantOutOfRange {
                    value: *value,
                    cardinality,
                });
            }
            Ok((ty.clone(), *value))
        }
    }
}

fn require_same_type(expected: &LogicType, actual: &LogicType) -> Result<(), FrontendError> {
    if expected == actual {
        Ok(())
    } else {
        Err(FrontendError::TypeMismatch {
            expected: expected.clone(),
            actual: actual.clone(),
        })
    }
}

fn not(value: BoolExpr) -> BoolExpr {
    match value {
        BoolExpr::Constant(value) => BoolExpr::Constant(!value),
        BoolExpr::Not(inner) => *inner,
        other => BoolExpr::Not(Box::new(other)),
    }
}

fn and(left: BoolExpr, right: BoolExpr) -> BoolExpr {
    match (left, right) {
        (BoolExpr::Constant(false), _) | (_, BoolExpr::Constant(false)) => {
            BoolExpr::Constant(false)
        }
        (BoolExpr::Constant(true), value) | (value, BoolExpr::Constant(true)) => value,
        (left, right) if left == right => left,
        (left, right) => BoolExpr::And(Box::new(left), Box::new(right)),
    }
}

fn or(left: BoolExpr, right: BoolExpr) -> BoolExpr {
    match (left, right) {
        (BoolExpr::Constant(true), _) | (_, BoolExpr::Constant(true)) => BoolExpr::Constant(true),
        (BoolExpr::Constant(false), value) | (value, BoolExpr::Constant(false)) => value,
        (left, right) if left == right => left,
        (left, right) => BoolExpr::Or(Box::new(left), Box::new(right)),
    }
}

fn all(values: impl IntoIterator<Item = BoolExpr>) -> BoolExpr {
    reduce_balanced(values.into_iter().collect(), true, and)
}

fn any(values: impl IntoIterator<Item = BoolExpr>) -> BoolExpr {
    reduce_balanced(values.into_iter().collect(), false, or)
}

fn reduce_balanced(
    mut values: Vec<BoolExpr>,
    identity: bool,
    combine: fn(BoolExpr, BoolExpr) -> BoolExpr,
) -> BoolExpr {
    if values.is_empty() {
        return BoolExpr::Constant(identity);
    }
    while values.len() > 1 {
        let mut next = Vec::with_capacity(values.len().div_ceil(2));
        let mut iter = values.into_iter();
        while let Some(left) = iter.next() {
            next.push(match iter.next() {
                Some(right) => combine(left, right),
                None => left,
            });
        }
        values = next;
    }
    values.pop().expect("nonempty by construction")
}

fn decode_row_major(mut flat: usize, cards: &[usize]) -> Vec<usize> {
    let mut out = vec![0; cards.len()];
    for index in (0..cards.len()).rev() {
        out[index] = flat % cards[index];
        flat /= cards[index];
    }
    out
}

fn binary_body(atom: usize) -> WindowExpr {
    WindowExpr::Mul(
        Box::new(WindowExpr::Loc(atom)),
        Box::new(WindowExpr::Add(
            Box::new(WindowExpr::Loc(atom)),
            Box::new(WindowExpr::Const(-1)),
        )),
    )
}

fn sum_window(mut values: Vec<WindowExpr>) -> WindowExpr {
    if values.is_empty() {
        return WindowExpr::Const(0);
    }
    while values.len() > 1 {
        let mut next = Vec::with_capacity(values.len().div_ceil(2));
        let mut iter = values.into_iter();
        while let Some(left) = iter.next() {
            next.push(match iter.next() {
                Some(right) => WindowExpr::Add(Box::new(left), Box::new(right)),
                None => left,
            });
        }
        values = next;
    }
    values.pop().expect("nonempty by construction")
}

fn bool_expr_to_window(expr: &BoolExpr) -> WindowExpr {
    match expr {
        BoolExpr::Atom(index) => WindowExpr::Loc(*index),
        BoolExpr::Constant(value) => WindowExpr::Const(i64::from(*value)),
        BoolExpr::Not(value) => WindowExpr::Add(
            Box::new(WindowExpr::Const(1)),
            Box::new(WindowExpr::Mul(
                Box::new(WindowExpr::Const(-1)),
                Box::new(bool_expr_to_window(value)),
            )),
        ),
        BoolExpr::And(left, right) => WindowExpr::Mul(
            Box::new(bool_expr_to_window(left)),
            Box::new(bool_expr_to_window(right)),
        ),
        BoolExpr::Or(left, right) => {
            let left = bool_expr_to_window(left);
            let right = bool_expr_to_window(right);
            WindowExpr::Add(
                Box::new(WindowExpr::Add(
                    Box::new(left.clone()),
                    Box::new(right.clone()),
                )),
                Box::new(WindowExpr::Mul(
                    Box::new(WindowExpr::Const(-1)),
                    Box::new(WindowExpr::Mul(Box::new(left), Box::new(right))),
                )),
            )
        }
    }
}

fn formula_node_count(formula: &Formula) -> usize {
    match formula {
        Formula::Top | Formula::Bottom => 1,
        Formula::Equal(left, right) => 1 + term_node_count(left) + term_node_count(right),
        Formula::Predicate { arguments, .. } => 1 + arguments.len(),
        Formula::Not(value) => 1 + formula_node_count(value),
        Formula::And(left, right) | Formula::Or(left, right) => {
            1 + formula_node_count(left) + formula_node_count(right)
        }
        Formula::ForAll { body, .. } | Formula::Exists { body, .. } => 1 + formula_node_count(body),
    }
}

fn term_node_count(_term: &Term) -> usize {
    1
}

fn canonical_source_bytes(program: &LogicProgram) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(b"dregg-direct-logic-source\0");
    put_u64(&mut out, u64::from(DIRECT_LOGIC_FRONTEND_VERSION));
    put_u64(&mut out, program.inputs.len() as u64);
    for input in &program.inputs {
        put_bytes(&mut out, input.name.as_bytes());
        put_type(&mut out, &input.ty);
    }
    put_formula(&mut out, &program.formula);
    out
}

fn put_formula(out: &mut Vec<u8>, formula: &Formula) {
    match formula {
        Formula::Top => out.push(0),
        Formula::Bottom => out.push(1),
        Formula::Equal(left, right) => {
            out.push(2);
            put_term(out, left);
            put_term(out, right);
        }
        Formula::Predicate { table, arguments } => {
            out.push(3);
            put_bytes(out, table.name.as_bytes());
            put_u64(out, table.argument_types.len() as u64);
            for ty in &table.argument_types {
                put_type(out, ty);
            }
            put_u64(out, table.values.len() as u64);
            for value in &table.values {
                out.push(u8::from(*value));
            }
            put_u64(out, arguments.len() as u64);
            for term in arguments {
                put_term(out, term);
            }
        }
        Formula::Not(value) => {
            out.push(4);
            put_formula(out, value);
        }
        Formula::And(left, right) => {
            out.push(5);
            put_formula(out, left);
            put_formula(out, right);
        }
        Formula::Or(left, right) => {
            out.push(6);
            put_formula(out, left);
            put_formula(out, right);
        }
        Formula::ForAll { binder, body } => {
            out.push(7);
            put_type(out, binder);
            put_formula(out, body);
        }
        Formula::Exists { binder, body } => {
            out.push(8);
            put_type(out, binder);
            put_formula(out, body);
        }
    }
}

fn put_term(out: &mut Vec<u8>, term: &Term) {
    match term {
        Term::Input(index) => {
            out.push(0);
            put_u64(out, *index as u64);
        }
        Term::Bound(index) => {
            out.push(1);
            put_u64(out, *index as u64);
        }
        Term::Constant { ty, value } => {
            out.push(2);
            put_type(out, ty);
            put_u64(out, *value as u64);
        }
    }
}

fn put_type(out: &mut Vec<u8>, ty: &LogicType) {
    match ty {
        LogicType::Bool => out.push(0),
        LogicType::Finite { cardinality } => {
            out.push(1);
            put_u64(out, *cardinality as u64);
        }
        LogicType::UnboundedInteger => out.push(2),
    }
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_bytes(out: &mut Vec<u8>, value: &[u8]) {
    put_u64(out, value.len() as u64);
    out.extend_from_slice(value);
}

fn canonical_descriptor_json(descriptor: &EffectVmDescriptor2) -> Result<String, FrontendError> {
    if descriptor.tables.len() != 1
        || descriptor.tables[0].id != TID_MAIN
        || descriptor.tables[0].sem != TableSem::Main
        || !descriptor.hash_sites.is_empty()
        || !descriptor.ranges.is_empty()
        || descriptor
            .constraints
            .iter()
            .any(|constraint| !matches!(constraint, VmConstraint2::WindowGate(_)))
    {
        return Err(FrontendError::InternalWireDrift(
            "restricted direct-logic serializer received an unsupported descriptor face".into(),
        ));
    }
    let table = &descriptor.tables[0];
    let mut out = format!(
        "{{\"name\":\"{}\",\"ir\":2,\"trace_width\":{},\"public_input_count\":{},\"tables\":[{{\"id\":{},\"name\":\"main\",\"arity\":{},\"sem\":\"main\"}}],\"constraints\":[",
        descriptor.name,
        descriptor.trace_width,
        descriptor.public_input_count,
        table.id,
        table.arity,
    );
    for (index, constraint) in descriptor.constraints.iter().enumerate() {
        if index != 0 {
            out.push(',');
        }
        let VmConstraint2::WindowGate(window) = constraint else {
            unreachable!("checked above")
        };
        out.push_str("{\"t\":\"window_gate\",\"on_transition\":");
        out.push_str(if window.on_transition {
            "true"
        } else {
            "false"
        });
        out.push_str(",\"body\":");
        put_window_json(&mut out, &window.body);
        out.push('}');
    }
    out.push_str("],\"hash_sites\":[],\"ranges\":[]}");
    Ok(out)
}

fn put_window_json(out: &mut String, expression: &WindowExpr) {
    match expression {
        WindowExpr::Loc(column) => out.push_str(&format!("{{\"t\":\"loc\",\"c\":{column}}}")),
        WindowExpr::Nxt(column) => out.push_str(&format!("{{\"t\":\"nxt\",\"c\":{column}}}")),
        WindowExpr::Const(value) => out.push_str(&format!("{{\"t\":\"const\",\"v\":{value}}}")),
        WindowExpr::Add(left, right) => {
            out.push_str("{\"t\":\"add\",\"l\":");
            put_window_json(out, left);
            out.push_str(",\"r\":");
            put_window_json(out, right);
            out.push('}');
        }
        WindowExpr::Mul(left, right) => {
            out.push_str("{\"t\":\"mul\",\"l\":");
            put_window_json(out, left);
            out.push_str(",\"r\":");
            put_window_json(out, right);
            out.push('}');
        }
    }
}

fn hex32(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(&mut out, "{byte:02x}").expect("writing to String cannot fail");
    }
    out
}
