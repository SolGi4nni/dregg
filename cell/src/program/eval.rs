use super::*;

impl CellProgram {
    /// Evaluate the program's constraints against the new (post-transition) state.
    ///
    /// For transition variants (`Immutable`, `WriteOnce`, `Monotonic`,
    /// `StrictMonotonic`, `BoundedBy`, `FieldDelta`, `FieldDeltaInRange`,
    /// `SumEqualsAcross`, `MonotonicSequence`, `AllowedTransitions`),
    /// `old_state` is required to compare the field value before and after
    /// the transition. On the cell-initialization path (`old_state == None`
    /// AND `new_state.nonce == 0`), transition variants are permitted to
    /// initialize the field.
    ///
    /// For contextual variants (`FieldGteHeight`, `FieldLteHeight`,
    /// `TemporalGate`, `SenderAuthorized`, `RateLimit`, `RateLimitBySum`,
    /// `PreimageGate`, `TemporalPredicate`, `BoundDelta`), `ctx` supplies
    /// the runtime context. `ctx` may be omitted for purely static checks;
    /// in that case the contextual variants surface
    /// `ProgramError::MissingContextField`.
    pub fn evaluate(
        &self,
        new_state: &CellState,
        old_state: Option<&CellState>,
        ctx: Option<&EvalContext>,
    ) -> Result<(), ProgramError> {
        // Legacy entry-point: callers that don't have a TransitionMeta
        // fall through to a `wildcard` meta (matches only `Always`
        // guards). New `Cases` programs that depend on method or
        // effect-kind guards should use `evaluate_with_meta`.
        self.evaluate_with_meta(new_state, old_state, ctx, &TransitionMeta::wildcard())
    }

    /// Evaluate the program with a [`TransitionMeta`] in scope.
    ///
    /// Used by the executor for `Cases` programs: each case's guard is
    /// matched against the (cell, action) pair, and only the matching
    /// cases' constraints fire. When *no* case matches, the program
    /// default-denies; when multiple cases match, their constraints AND
    /// together.
    ///
    /// `Predicate(_)` and `None` programs are unaffected by `meta`
    /// (they ignore the action-level signals).
    pub fn evaluate_with_meta(
        &self,
        new_state: &CellState,
        old_state: Option<&CellState>,
        ctx: Option<&EvalContext>,
        meta: &TransitionMeta,
    ) -> Result<(), ProgramError> {
        self.evaluate_full(new_state, old_state, ctx, meta, &WitnessBundle::empty())
    }

    /// Full-fat evaluation: per-transition context + witness bundle.
    ///
    /// Used by the executor (Cav-Codex Block 2) to dispatch witnessed
    /// predicates through a registered verifier, populate
    /// `SenderAuthorized` Merkle-membership witnesses, resolve
    /// `PreimageGate` reveals, and surface `Custom` predicate proofs.
    ///
    /// Callers without a witness bundle should use
    /// [`Self::evaluate_with_meta`] (which forwards an empty bundle);
    /// callers without action-level meta and without witnesses can use
    /// [`Self::evaluate`].
    pub fn evaluate_full(
        &self,
        new_state: &CellState,
        old_state: Option<&CellState>,
        ctx: Option<&EvalContext>,
        meta: &TransitionMeta,
        witnesses: &WitnessBundle<'_>,
    ) -> Result<(), ProgramError> {
        match self {
            CellProgram::None => Ok(()),
            CellProgram::Predicate(constraints) => {
                for constraint in constraints {
                    evaluate_constraint_full(
                        constraint, new_state, old_state, ctx, meta, witnesses,
                    )?;
                }
                Ok(())
            }
            CellProgram::Cases(cases) => {
                // Track matches separately for invariant cases (Always /
                // SlotChanged) and operation-binding cases (MethodIs /
                // EffectKindIs / boolean composition over those).
                //
                // Cav-Codex Block 4 default-deny: if the program defines
                // at least one operation-binding case, an action whose
                // dispatch matches NONE of them is rejected as
                // `NoTransitionCaseMatched`, even when invariant cases
                // still match. Without this carve-out, an `Always`
                // invariants case silently absorbs unknown methods —
                // the executor would only ever enforce the universal
                // invariants on a `cipherclerk_drain_funds` symbol and
                // the program's whole purpose (operation discrimination)
                // would erode. See the
                // `unknown_method_default_denied` tests in
                // `starbridge-subscription`,
                // `starbridge-governed-namespace`, and
                // `dregg-storage-templates::cap_inbox_tests`.
                let mut any_matched = false;
                let mut any_dispatch_case = false;
                let mut any_dispatch_matched = false;
                for case in cases {
                    let is_dispatch = case.guard.is_method_dispatching();
                    if is_dispatch {
                        any_dispatch_case = true;
                    }
                    if case.guard.matches(meta, old_state, new_state) {
                        any_matched = true;
                        if is_dispatch {
                            any_dispatch_matched = true;
                        }
                        for constraint in &case.constraints {
                            evaluate_constraint_full(
                                constraint, new_state, old_state, ctx, meta, witnesses,
                            )?;
                        }
                    }
                }
                if !any_matched {
                    // No case at all applied — pure default-deny.
                    return Err(ProgramError::NoTransitionCaseMatched);
                }
                if any_dispatch_case && !any_dispatch_matched {
                    // Program defines operation-binding cases but the
                    // action's dispatch matched none of them.
                    return Err(ProgramError::NoTransitionCaseMatched);
                }
                Ok(())
            }
            CellProgram::Circuit { circuit_hash } => Err(ProgramError::CircuitProofRequired {
                circuit_hash: *circuit_hash,
            }),
        }
    }

    /// Backwards-compatible two-arg evaluation: equivalent to
    /// `evaluate(new, old, None)`. Use the three-arg form to support
    /// contextual variants (`SenderAuthorized`, `TemporalGate`, etc.).
    pub fn evaluate_static(
        &self,
        new_state: &CellState,
        old_state: Option<&CellState>,
    ) -> Result<(), ProgramError> {
        self.evaluate(new_state, old_state, None)
    }

    /// Returns true if this program is `None` (backward-compatible no-op).
    pub fn is_none(&self) -> bool {
        matches!(self, CellProgram::None)
    }

    /// Returns true if this program requires proof authorization for state transitions.
    pub fn requires_proof(&self) -> bool {
        matches!(self, CellProgram::Circuit { .. })
    }

    /// Sugar: lift a list of constraints into a single `Always`-guarded
    /// case. Equivalent to `CellProgram::Predicate(constraints)` but
    /// uses the new `Cases` shape (so callers can mix in extra cases
    /// later without restructuring).
    pub fn always(constraints: Vec<StateConstraint>) -> Self {
        CellProgram::Cases(vec![TransitionCase {
            guard: TransitionGuard::Always,
            constraints,
        }])
    }
}

// ============================================================================
// Per-variant evaluators
// ============================================================================

fn check_index(index: u8) -> Result<usize, ProgramError> {
    let idx = index as usize;
    if idx >= STATE_SLOTS {
        return Err(ProgramError::InvalidFieldIndex { index });
    }
    Ok(idx)
}

/// Select the **unique** witness blob whose kind is in `kinds`.
///
/// SECURITY (audit item 4): the previous evaluator selected the *first*
/// blob of a matching kind (`witnesses.blobs.iter().find(..)`). When an
/// action carries several proofs of the same wire kind (e.g. two
/// `ProofBytes` blobs — one for a `Renounced` non-membership proof and
/// one for a `TemporalPredicate`), a first-of-kind scan can bind the
/// *wrong* proof to a predicate, letting a submitter cross-match a valid
/// proof for predicate A against predicate B.
///
/// The `StateConstraint` variants that need a proof
/// (`SenderAuthorized`, `Renounced`, `Custom`) do not carry an explicit
/// `proof_witness_index` field, so we cannot bind by index without a
/// schema/commitment break. Instead we bind by *uniqueness*: the action
/// must carry exactly one blob of the expected kind(s). Ambiguity (more
/// than one candidate) fails **closed** — there is no first-of-kind
/// cross-match window. Predicates that need to disambiguate multiple
/// same-kind proofs must migrate to the typed
/// [`StateConstraint::Witnessed`] variant, whose
/// [`crate::predicate::WitnessedPredicate::proof_witness_index`] names
/// the blob explicitly.
///
/// Returns the index of the unique blob and a reference to it.
fn unique_blob_of_kinds<'a>(
    witnesses: &WitnessBundle<'a>,
    kinds: &[WitnessKindTag],
) -> Result<(usize, &'a WitnessBlobView<'a>), UniqueBlobError> {
    let mut found: Option<(usize, &WitnessBlobView<'_>)> = None;
    for (i, b) in witnesses.blobs.iter().enumerate() {
        if kinds.contains(&b.kind) {
            if found.is_some() {
                return Err(UniqueBlobError::Ambiguous);
            }
            found = Some((i, b));
        }
    }
    found.ok_or(UniqueBlobError::Missing)
}

/// Outcome of [`unique_blob_of_kinds`].
enum UniqueBlobError {
    /// No blob of the requested kind(s) is present.
    Missing,
    /// More than one blob of the requested kind(s) is present — the
    /// binding is ambiguous and we fail closed rather than guess.
    Ambiguous,
}

/// Evaluate a single constraint with no witness bundle (legacy entry).
/// Forwards to [`evaluate_constraint_full`] with an empty bundle so
/// witness-dependent variants surface the same `WitnessedPredicateRequiresExecutor` /
/// `WitnessedPredicateWitnessMissing` sentinel as before.
///
/// Retained for backwards-compatibility with callers that hold a
/// constraint without a witness bundle; the `AnyOf` evaluator now goes
/// through [`evaluate_simple_constraint`] so the Heyting-fragment `Not`
/// short-circuit can fire.
#[allow(dead_code)]
fn evaluate_constraint(
    constraint: &StateConstraint,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
) -> Result<(), ProgramError> {
    evaluate_constraint_full(
        constraint,
        new_state,
        old_state,
        ctx,
        &TransitionMeta::wildcard(),
        &WitnessBundle::empty(),
    )
}

/// Evaluate a single constraint against the cell state with a witness
/// bundle in scope (Cav-Codex Block 2). When the bundle carries a
/// matching witness for `SenderAuthorized`, `PreimageGate`,
/// `RateLimit`, `Witnessed`, `TemporalPredicate`, or `Custom`, the
/// evaluator dispatches to the registered verifier or uses the
/// witness payload directly. Otherwise it falls through to the
/// legacy fail-closed sentinel.
fn evaluate_constraint_full(
    constraint: &StateConstraint,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
    meta: &TransitionMeta,
    witnesses: &WitnessBundle<'_>,
) -> Result<(), ProgramError> {
    match constraint {
        StateConstraint::FieldEquals { index, value } => {
            let idx = check_index(*index)?;
            if new_state.fields[idx] != *value {
                return violated(constraint, format!("field[{idx}] != expected value"));
            }
            Ok(())
        }
        StateConstraint::FieldGte { index, value } => {
            let idx = check_index(*index)?;
            if !field_gte(&new_state.fields[idx], value) {
                return violated(constraint, format!("field[{idx}] < minimum value"));
            }
            Ok(())
        }
        StateConstraint::FieldLte { index, value } => {
            let idx = check_index(*index)?;
            if !field_lte(&new_state.fields[idx], value) {
                return violated(constraint, format!("field[{idx}] > maximum value"));
            }
            Ok(())
        }
        StateConstraint::FieldLteField {
            left_index,
            right_index,
        } => {
            let left = check_index(*left_index)?;
            let right = check_index(*right_index)?;
            if !field_lte(&new_state.fields[left], &new_state.fields[right]) {
                return violated(
                    constraint,
                    format!("field[{left}] > field[{right}] in post-state"),
                );
            }
            Ok(())
        }
        StateConstraint::FieldLteOther {
            index,
            other,
            delta,
        } => {
            let i = check_index(*index)?;
            let o = check_index(*other)?;
            // `new[index] <= new[other] + delta`, signed: read both slots as
            // big-endian u64 lifted to i128 (mirrors Lean `fieldOf` + the
            // integration harness `field_i128`), add the signed `delta` on the
            // right. Fail-closed on violation.
            let lhs = field_to_u64(&new_state.fields[i]) as i128;
            let rhs = field_to_u64(&new_state.fields[o]) as i128 + *delta as i128;
            if lhs > rhs {
                return violated(
                    constraint,
                    format!("field[{i}] = {lhs} > field[{o}] + {delta} = {rhs} in post-state"),
                );
            }
            Ok(())
        }
        StateConstraint::SumEquals { indices, value } => {
            let mut sum: u64 = 0;
            for &idx in indices {
                let i = check_index(idx)?;
                sum = sum
                    .checked_add(field_to_u64(&new_state.fields[i]))
                    .ok_or_else(|| ProgramError::ConstraintViolated {
                        constraint: constraint.clone(),
                        description: format!(
                            "overflow computing sum of fields {indices:?}: u64 addition overflowed"
                        ),
                    })?;
            }
            let expected = field_to_u64(value);
            if sum != expected {
                return violated(
                    constraint,
                    format!("sum of fields {indices:?} = {sum}, expected {expected}"),
                );
            }
            Ok(())
        }

        StateConstraint::Immutable { index } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    if new_state.fields[idx] != old.fields[idx] {
                        return violated(
                            constraint,
                            format!("field[{idx}] was mutated but is marked immutable"),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::WriteOnce { index } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    // Permitted: old slot was zero (first write) OR
                    // new == old (no change).
                    let old_zero = old.fields[idx] == FIELD_ZERO;
                    let unchanged = new_state.fields[idx] == old.fields[idx];
                    if !(old_zero || unchanged) {
                        return violated(
                            constraint,
                            format!("field[{idx}] is write-once and was already set"),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::Monotonic { index } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    if !field_gte(&new_state.fields[idx], &old.fields[idx]) {
                        return violated(
                            constraint,
                            format!("field[{idx}] decreased; Monotonic requires new >= old"),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::StrictMonotonic { index } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    if !field_gt(&new_state.fields[idx], &old.fields[idx]) {
                        return violated(
                            constraint,
                            format!(
                                "field[{idx}] did not strictly increase; StrictMonotonic requires new > old"
                            ),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::BoundedBy {
            index,
            witness_index,
        } => {
            let idx = check_index(*index)?;
            let widx = check_index(*witness_index)?;
            let changed = match old_state {
                Some(old) => new_state.fields[idx] != old.fields[idx],
                None => new_state.fields[idx] != FIELD_ZERO,
            };
            if changed {
                let armed = new_state.fields[widx] != FIELD_ZERO;
                if !armed {
                    return violated(
                        constraint,
                        format!(
                            "field[{idx}] changed but witness field[{widx}] is zero (BoundedBy)"
                        ),
                    );
                }
            }
            Ok(())
        }

        StateConstraint::FieldDelta { index, delta } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    let expected = field_add(&old.fields[idx], delta);
                    if new_state.fields[idx] != expected {
                        return violated(constraint, format!("field[{idx}] != old + delta"));
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::FieldDeltaInRange {
            index,
            min_delta,
            max_delta,
        } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    let lower = field_add(&old.fields[idx], min_delta);
                    let upper = field_add(&old.fields[idx], max_delta);
                    if !(field_gte(&new_state.fields[idx], &lower)
                        && field_lte(&new_state.fields[idx], &upper))
                    {
                        return violated(
                            constraint,
                            format!("field[{idx}] outside [old+min_delta, old+max_delta]"),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::FieldGteHeight { index, offset } => {
            let idx = check_index(*index)?;
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "block_height",
            })?;
            let height = ctx.block_height as i128;
            let bound = (height + (*offset as i128)).max(0) as u64;
            let value = field_to_u64(&new_state.fields[idx]);
            if value < bound {
                return violated(
                    constraint,
                    format!(
                        "field[{idx}] = {value} < block_height({}) + {} = {bound}",
                        ctx.block_height, offset
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::FieldLteHeight { index, offset } => {
            let idx = check_index(*index)?;
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "block_height",
            })?;
            let height = ctx.block_height as i128;
            let bound = (height + (*offset as i128)).max(0) as u64;
            let value = field_to_u64(&new_state.fields[idx]);
            if value > bound {
                return violated(
                    constraint,
                    format!(
                        "field[{idx}] = {value} > block_height({}) + {} = {bound}",
                        ctx.block_height, offset
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::SumEqualsAcross {
            input_fields,
            output_fields,
        } => {
            let old = match old_state {
                Some(o) => o,
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: 0,
                        });
                    }
                    return Ok(());
                }
            };
            let mut new_in: u64 = 0;
            let mut old_in: u64 = 0;
            let mut new_out: u64 = 0;
            for &idx in input_fields {
                let i = check_index(idx)?;
                new_in = new_in
                    .checked_add(field_to_u64(&new_state.fields[i]))
                    .ok_or_else(|| viol(constraint, "input sum overflow"))?;
                old_in = old_in
                    .checked_add(field_to_u64(&old.fields[i]))
                    .ok_or_else(|| viol(constraint, "input sum overflow"))?;
            }
            for &idx in output_fields {
                let i = check_index(idx)?;
                new_out = new_out
                    .checked_add(field_to_u64(&new_state.fields[i]))
                    .ok_or_else(|| viol(constraint, "output sum overflow"))?;
            }
            let rhs = old_in
                .checked_add(new_out)
                .ok_or_else(|| viol(constraint, "rhs overflow"))?;
            if new_in != rhs {
                return violated(
                    constraint,
                    format!(
                        "SumEqualsAcross: sum(new[in])={new_in} != sum(old[in])({old_in}) + sum(new[out])({new_out})"
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::SenderAuthorized { set } => {
            let ctx = ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let sender = ctx
                .sender
                .as_ref()
                .ok_or(ProgramError::MissingContextField { field: "sender" })?;
            // Cav-Codex Block 2: enforce membership by dispatching to the
            // witnessed-predicate registry against the appropriate
            // commitment (slot root or blinded commitment). The action
            // MUST carry a `MerklePath` (PublicRoot) or `ProofBytes`
            // (BlindedSet) witness blob.
            //
            // SECURITY (audit item 4): the blob is bound by *uniqueness*,
            // not first-of-kind — see `unique_blob_of_kinds`. If the
            // action carries more than one MerklePath/ProofBytes blob the
            // binding is ambiguous and we fail closed.
            let (commitment, kind) = match set {
                AuthorizedSet::PublicRoot { set_root_index } => {
                    let idx = check_index(*set_root_index)?;
                    (
                        new_state.fields[idx],
                        crate::predicate::WitnessedPredicateKind::MerkleMembership,
                    )
                }
                AuthorizedSet::BlindedSet { commitment } => (
                    *commitment,
                    crate::predicate::WitnessedPredicateKind::BlindedSet,
                ),
                AuthorizedSet::CredentialSet {
                    issuer_cell,
                    credential_schema_id,
                } => (
                    AuthorizedSet::credential_set_commitment(issuer_cell, credential_schema_id),
                    crate::predicate::WitnessedPredicateKind::BlindedSet,
                ),
            };
            // Require a witness blob and a registry. If neither is
            // present the constraint surfaces a structural sentinel so
            // tests / fail-closed callers can still match on the
            // `MissingContextField` shape, but real executor calls
            // MUST configure both.
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::SenderMembershipWitnessMissing);
            };
            // Bind the unique MerklePath / ProofBytes witness blob by
            // uniqueness. Ambiguity or absence fails closed.
            let (blob_idx, blob) = unique_blob_of_kinds(
                witnesses,
                &[WitnessKindTag::MerklePath, WitnessKindTag::ProofBytes],
            )
            .map_err(|e| match e {
                UniqueBlobError::Missing => ProgramError::SenderMembershipWitnessMissing,
                UniqueBlobError::Ambiguous => ProgramError::WitnessedPredicateRejected {
                    kind_name: "SenderAuthorized",
                    reason: "ambiguous membership witness: action carries more than one \
                             MerklePath/ProofBytes blob; bind explicitly via Witnessed { wp }"
                        .into(),
                },
            })?;
            // Build a placeholder WitnessedPredicate to feed the registry,
            // binding the explicit proof witness index we resolved.
            let wp = crate::predicate::WitnessedPredicate {
                kind,
                commitment,
                input_ref: InputRef::Sender,
                proof_witness_index: blob_idx,
            };
            let input = PredicateInput::Sender(sender);
            registry.verify(&wp, &input, blob.bytes).map_err(|e| {
                ProgramError::WitnessedPredicateRejected {
                    kind_name: match kind {
                        crate::predicate::WitnessedPredicateKind::MerkleMembership => {
                            "MerkleMembership"
                        }
                        crate::predicate::WitnessedPredicateKind::BlindedSet => "BlindedSet",
                        _ => "Witnessed",
                    },
                    reason: e.to_string(),
                }
            })?;
            Ok(())
        }

        StateConstraint::Renounced { set } => {
            // Dual of SenderAuthorized: verify the sender is *not* in
            // the named sorted-leaf set by dispatching the
            // NonMembership verifier.
            let ctx = ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let sender = ctx
                .sender
                .as_ref()
                .ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let commitment = match set {
                RenouncedSet::PublicRoot { set_root_index } => {
                    let idx = check_index(*set_root_index)?;
                    new_state.fields[idx]
                }
                RenouncedSet::BlindedSet { commitment } => *commitment,
            };
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::SenderMembershipWitnessMissing);
            };
            // The non-membership neighbor witness is a ProofBytes blob
            // (96 bytes — see `NonMembershipNeighborProof`). Bind by
            // uniqueness (audit item 4): ambiguity/absence fails closed.
            let (blob_idx, blob) = unique_blob_of_kinds(witnesses, &[WitnessKindTag::ProofBytes])
                .map_err(|e| match e {
                UniqueBlobError::Missing => ProgramError::SenderMembershipWitnessMissing,
                UniqueBlobError::Ambiguous => ProgramError::WitnessedPredicateRejected {
                    kind_name: "NonMembership",
                    reason: "ambiguous non-membership witness: action carries more than one \
                                 ProofBytes blob; bind explicitly via Witnessed { wp }"
                        .into(),
                },
            })?;
            let wp = crate::predicate::WitnessedPredicate {
                kind: crate::predicate::WitnessedPredicateKind::NonMembership,
                commitment,
                input_ref: InputRef::Sender,
                proof_witness_index: blob_idx,
            };
            let input = PredicateInput::Sender(sender);
            registry.verify(&wp, &input, blob.bytes).map_err(|e| {
                ProgramError::WitnessedPredicateRejected {
                    kind_name: "NonMembership",
                    reason: e.to_string(),
                }
            })?;
            Ok(())
        }

        StateConstraint::CapabilityUniqueness { cap_set_root_slot } => {
            let _ = check_index(*cap_set_root_slot)?;
            // SECURITY (audit item 1): structural "exactly one / no
            // duplicate live capability" cannot be decided from
            // `(old_state, new_state)` alone — the scalar evaluator only
            // sees the 16 state-slot field values, NOT the cell's actual
            // `CapabilitySet`. The cap-set root in
            // `slot[cap_set_root_slot]` is an opaque 32-byte commitment;
            // verifying that it encodes a unique cap requires the real
            // capability list, which is only reachable from the executor.
            //
            // The previous implementation bounds-checked the slot and
            // returned `Ok(())` — a silent no-op that let a cell *declare*
            // NFT-uniqueness while enforcing nothing. We now fail
            // **closed**: any caller that reaches this scalar path without
            // the executor's cap-set enforcement gets a rejection. The
            // executor (`execute_tree::validate_capability_uniqueness`)
            // is the only place this constraint is genuinely enforced; it
            // binds the declared root slot to
            // `compute_canonical_capability_root(&cell.capabilities)` and
            // rejects duplicate cap entries.
            Err(ProgramError::CapabilityUniquenessRequiresExecutor {
                cap_set_root_slot: *cap_set_root_slot,
            })
        }

        StateConstraint::RateLimit { max_per_epoch, .. } => {
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "sender_epoch_count",
            })?;
            // SECURITY (audit item 2): the count MUST come from the
            // executor's authoritative per-(cell, sender, epoch) counter,
            // surfaced as `ctx.sender_epoch_count`. The executor wires
            // this in `execute_tree::state_constraint_context_count`.
            //
            // The previous implementation fell back to a `RateLimitCount`
            // witness blob carried by the action itself when the ctx
            // count was zero. That fallback was *bypassable*: the action's
            // own signer chose the value, so a submitter could attest
            // `count = 0` on every action and never trip the limit. The
            // self-attested fallback is removed — there is no submitter-
            // controlled path to the count. A `RateLimitCount` witness
            // blob (if present) is informational only and is NOT trusted
            // here.
            let count = ctx.sender_epoch_count;
            if count >= *max_per_epoch {
                return violated(
                    constraint,
                    format!(
                        "sender has {} mutations this epoch, max is {}",
                        count, max_per_epoch
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::RateLimitBySum {
            slot_index,
            max_sum_per_epoch,
            ..
        } => {
            // Window-sum is supplied through the per-(cell, slot, window)
            // running sum tracked by the executor; that pre-aggregated
            // value comes in via `ctx.sender_epoch_count` repurposed as
            // the running per-window sum when the executor wires this
            // variant. Until then, evaluate the delta-bound directly: the
            // per-turn increment must not exceed the cap.
            let idx = check_index(*slot_index)?;
            let new_val = field_to_u64(&new_state.fields[idx]);
            let old_val = old_state.map(|o| field_to_u64(&o.fields[idx])).unwrap_or(0);
            let delta = new_val.saturating_sub(old_val);
            let prior_window_sum = ctx.map(|c| c.sender_epoch_count as u64).unwrap_or(0);
            let window_sum = prior_window_sum.saturating_add(delta);
            if window_sum > *max_sum_per_epoch {
                return violated(
                    constraint,
                    format!(
                        "slot[{idx}] window_sum={window_sum} (prior={prior_window_sum}, delta={delta}) exceeds max_sum_per_epoch={max_sum_per_epoch}"
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::TemporalGate {
            not_before,
            not_after,
        } => {
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "block_height",
            })?;
            if let Some(nb) = not_before
                && ctx.block_height < *nb
            {
                return violated(
                    constraint,
                    format!("height {} < not_before {nb}", ctx.block_height),
                );
            }
            if let Some(na) = not_after
                && ctx.block_height > *na
            {
                return violated(
                    constraint,
                    format!("height {} > not_after {na}", ctx.block_height),
                );
            }
            Ok(())
        }

        StateConstraint::PreimageGate {
            commitment_index,
            hash_kind,
        } => {
            let idx = check_index(*commitment_index)?;
            // Cav-Codex Block 2: prefer the witness blob over the
            // ctx-side preimage (the witness blob is the canonical
            // carrier). Fall back to `ctx.revealed_preimage` for
            // backwards compatibility with callers that haven't moved
            // to witness_blobs yet.
            let preimage = witnesses
                .blobs
                .iter()
                .find_map(|b| {
                    if b.kind == WitnessKindTag::Preimage32 && b.bytes.len() == 32 {
                        let mut buf = [0u8; 32];
                        buf.copy_from_slice(b.bytes);
                        Some(buf)
                    } else {
                        None
                    }
                })
                .or_else(|| ctx.and_then(|c| c.revealed_preimage))
                .ok_or(ProgramError::PreimageWitnessMissing)?;
            let expected = new_state.fields[idx];
            let hash = hash_preimage32(hash_kind, &preimage);
            if hash != expected {
                return violated(constraint, "preimage does not match commitment".into());
            }
            Ok(())
        }

        StateConstraint::KeyRotationGate {
            digest_slot,
            current_slot,
            last_rotated_slot,
            cooling_period,
            hash_kind,
        } => {
            let d = check_index(*digest_slot)?;
            let c = check_index(*current_slot)?;
            let r = check_index(*last_rotated_slot)?;
            // Resolve the pre-state rotation registers. A fresh cell
            // (init path: no old state, nonce == 0) reads as all-zero;
            // any other missing-old case is fail-closed.
            let zeros;
            let old_fields: &[FieldElement; STATE_SLOTS] = match old_state {
                Some(old) => &old.fields,
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *digest_slot,
                        });
                    }
                    zeros = [FIELD_ZERO; STATE_SLOTS];
                    &zeros
                }
            };
            let unchanged = new_state.fields[d] == old_fields[d]
                && new_state.fields[c] == old_fields[c]
                && new_state.fields[r] == old_fields[r];
            if unchanged {
                // Not a rotation event: the gate only guards the
                // rotation registers.
                return Ok(());
            }
            if old_fields[d] == FIELD_ZERO {
                // INCEPTION (KERI `icp`): nothing was pre-committed yet, so
                // the first commitment is installed without a preimage. The
                // chain must START: a zero digest is the unborn sentinel.
                if new_state.fields[d] == FIELD_ZERO {
                    return violated(
                        constraint,
                        "inception must commit a nonzero next-keys digest".into(),
                    );
                }
                // A nonzero inception stamp must not be future-dated.
                if new_state.fields[r] != FIELD_ZERO {
                    let height = ctx
                        .ok_or(ProgramError::MissingContextField {
                            field: "block_height",
                        })?
                        .block_height;
                    let stamp = field_to_u64(&new_state.fields[r]);
                    if stamp > height {
                        return violated(
                            constraint,
                            format!("inception stamp {stamp} is future-dated (height {height})"),
                        );
                    }
                }
                return Ok(());
            }
            // ROTATION (KERI `rot`). NOTE: `old_fields[c]` — the current,
            // exposed key set — is deliberately never read here
            // (`rotate_current_keys_irrelevant`): holding the current keys
            // contributes nothing toward rotating.
            let height = ctx
                .ok_or(ProgramError::MissingContextField {
                    field: "block_height",
                })?
                .block_height;
            // 1. The preimage EXHIBIT against the PRE-state register.
            let preimage = witnesses
                .blobs
                .iter()
                .find_map(|b| {
                    if b.kind == WitnessKindTag::Preimage32 && b.bytes.len() == 32 {
                        let mut buf = [0u8; 32];
                        buf.copy_from_slice(b.bytes);
                        Some(buf)
                    } else {
                        None
                    }
                })
                .or_else(|| ctx.and_then(|c| c.revealed_preimage))
                .ok_or(ProgramError::PreimageWitnessMissing)?;
            if hash_preimage32(hash_kind, &preimage) != old_fields[d] {
                return violated(
                    constraint,
                    "rotation does not exhibit the preimage of the committed next-keys digest"
                        .into(),
                );
            }
            // 2. The presented key set is INSTALLED.
            if new_state.fields[c] != preimage {
                return violated(
                    constraint,
                    "rotation must install the exhibited key-set commitment as current".into(),
                );
            }
            // 3. The forward chain: the fresh next-commitment rides the
            //    same turn.
            if new_state.fields[d] == FIELD_ZERO {
                return violated(
                    constraint,
                    "rotation must commit a fresh nonzero next-keys digest (the chain)".into(),
                );
            }
            // 4. The cooling window (cooledSince lastRotatedAt period).
            let last = field_to_u64(&old_fields[r]);
            if last.saturating_add(*cooling_period) > height {
                return violated(
                    constraint,
                    format!(
                        "rotation inside the cooling window: last rotation at {last}, \
                         period {cooling_period}, height {height}"
                    ),
                );
            }
            // 5. The rotation stamps its own height (the next window's
            //    anchor).
            if field_to_u64(&new_state.fields[r]) != height
                || new_state.fields[r][..24] != [0u8; 24]
            {
                return violated(
                    constraint,
                    format!("rotation must stamp the current height {height}"),
                );
            }
            Ok(())
        }

        StateConstraint::MonotonicSequence { seq_index } => {
            let idx = check_index(*seq_index)?;
            match old_state {
                Some(old) => {
                    let old_seq = field_to_u64(&old.fields[idx]);
                    let new_seq = field_to_u64(&new_state.fields[idx]);
                    if new_seq != old_seq.wrapping_add(1) {
                        return violated(
                            constraint,
                            format!("seq[{idx}]: expected {} got {}", old_seq + 1, new_seq),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *seq_index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::AllowedTransitions {
            slot_index,
            allowed,
        } => {
            let idx = check_index(*slot_index)?;
            let new_v = new_state.fields[idx];
            let old_v = old_state.map(|o| o.fields[idx]).unwrap_or(FIELD_ZERO);
            let ok = allowed.iter().any(|(o, n)| *o == old_v && *n == new_v);
            if !ok {
                return violated(
                    constraint,
                    format!("transition on slot[{idx}] is not in the allow-list"),
                );
            }
            Ok(())
        }

        // The sealed-escrow atomic-swap gate (the Lean `SettleGate`,
        // `metatheory/Dregg2/Deos/SealedEscrow.lean` §6), evaluated over the
        // field-mirrored leg-status slots. Both legs must be `Deposited` (1)
        // before AND `Consumed` (2) after — the atomic both-or-none transition.
        // A partial/half-open settle (one leg left `Deposited`) fails this
        // conjunction: there is no accepting witness with only one leg moving.
        // Status codes mirror `crate::escrow_sealed::LegStatus` (Empty/Deposited/
        // Consumed = 0/1/2), read off the u64 lane so the slot mirror is the
        // small status integer.
        StateConstraint::SettleEscrow {
            leg_a_index,
            leg_b_index,
        } => {
            const DEPOSITED: u64 = 1;
            const CONSUMED: u64 = 2;
            let a = check_index(*leg_a_index)?;
            let b = check_index(*leg_b_index)?;
            let Some(old) = old_state else {
                return Err(ProgramError::TransitionCheckRequiresOldState {
                    constraint: constraint.clone(),
                    index: *leg_a_index,
                });
            };
            let before_a = field_to_u64(&old.fields[a]);
            let before_b = field_to_u64(&old.fields[b]);
            let after_a = field_to_u64(&new_state.fields[a]);
            let after_b = field_to_u64(&new_state.fields[b]);
            if before_a != DEPOSITED || before_b != DEPOSITED {
                return violated(
                    constraint,
                    format!(
                        "SettleEscrow: both legs must be Deposited before settle \
                         (leg A slot[{a}]={before_a}, leg B slot[{b}]={before_b})"
                    ),
                );
            }
            if after_a != CONSUMED || after_b != CONSUMED {
                return violated(
                    constraint,
                    format!(
                        "SettleEscrow: both legs must be Consumed after settle \
                         (leg A slot[{a}]={after_a}, leg B slot[{b}]={after_b})"
                    ),
                );
            }
            Ok(())
        }

        // The standing-obligation per-period discharge gate (the Lean
        // `DischargeGate`, `metatheory/Dregg2/Deos/StandingObligation.lean` §6b),
        // evaluated over the field-mirrored schedule slots. Across the (old, new)
        // transition the discharge must be DUE (block height ≥ the committed due
        // block), the `next_due` cursor must ADVANCE by exactly one period, and the
        // discharged total must advance by EXACTLY the schedule amount. An early /
        // wrong-amount / non-advanced step fails this conjunction: there is no
        // accepting witness that skips the due block, under/over-pays, or leaves the
        // one-shot cursor un-advanced.
        StateConstraint::DischargeObligation {
            cursor_slot,
            due_slot,
            amount_slot,
            period,
            amount,
        } => {
            let cs = check_index(*cursor_slot)?;
            let ds = check_index(*due_slot)?;
            let as_ = check_index(*amount_slot)?;
            let Some(old) = old_state else {
                return Err(ProgramError::TransitionCheckRequiresOldState {
                    constraint: constraint.clone(),
                    index: *cursor_slot,
                });
            };
            let clock = ctx
                .ok_or(ProgramError::MissingContextField {
                    field: "block_height",
                })?
                .block_height;
            let cursor_before = field_to_u64(&old.fields[cs]);
            let cursor_after = field_to_u64(&new_state.fields[cs]);
            let due_block = field_to_u64(&old.fields[ds]);
            let total_before = field_to_u64(&old.fields[as_]);
            let total_after = field_to_u64(&new_state.fields[as_]);
            // DUE: the schedule clock has reached the committed due block.
            if clock < due_block {
                return violated(
                    constraint,
                    format!(
                        "DischargeObligation: not yet due (clock {clock} < due block {due_block})"
                    ),
                );
            }
            // ADVANCED: the one-shot cursor advances by exactly one period.
            let expected_cursor = cursor_before.wrapping_add(u64::from(*period));
            if cursor_after != expected_cursor {
                return violated(
                    constraint,
                    format!(
                        "DischargeObligation: cursor must advance one period \
                         (slot[{cs}] expected {expected_cursor}, got {cursor_after})"
                    ),
                );
            }
            // EXACT: the discharged total advances by exactly the schedule amount.
            let expected_total = total_before.wrapping_add(u64::from(*amount));
            if total_after != expected_total {
                return violated(
                    constraint,
                    format!(
                        "DischargeObligation: amount must be exact \
                         (slot[{as_}] expected total {expected_total}, got {total_after})"
                    ),
                );
            }
            Ok(())
        }

        // The share-vault no-dilution deposit gate (the Lean `VaultDepositGate`,
        // `metatheory/Dregg2/Deos/Vault.lean` §6b), evaluated over the field-mirrored
        // `total_assets` / `total_shares` counter slots. Across the (old, new)
        // transition the committed total_assets must advance by the deposit `d > 0`,
        // the committed total_shares must advance by `m > 0` minted shares (the
        // zero-mint / inflation-attack tooth), and NO existing holder may be diluted
        // (`before_assets·m ≤ before_shares·d`, the no-dilution floor). A zero-mint /
        // diluting / non-conserving step fails this conjunction: there is no accepting
        // witness that mints nothing, dilutes the existing holders, or conjures pooled
        // value. The deposit `d` and minted `m` are the across-transition deltas of the
        // two slots (no per-deposit constant); products in `u128` so they cannot wrap.
        StateConstraint::VaultDeposit {
            assets_slot,
            shares_slot,
        } => {
            let as_ = check_index(*assets_slot)?;
            let ss = check_index(*shares_slot)?;
            let Some(old) = old_state else {
                return Err(ProgramError::TransitionCheckRequiresOldState {
                    constraint: constraint.clone(),
                    index: *assets_slot,
                });
            };
            let before_assets = field_to_u64(&old.fields[as_]);
            let after_assets = field_to_u64(&new_state.fields[as_]);
            let before_shares = field_to_u64(&old.fields[ss]);
            let after_shares = field_to_u64(&new_state.fields[ss]);
            // CONSERVING + GENUINE DEPOSIT: total_assets advances by a positive deposit.
            if after_assets <= before_assets {
                return violated(
                    constraint,
                    format!(
                        "VaultDeposit: total_assets must advance by a positive deposit \
                         (slot[{as_}] before {before_assets}, after {after_assets})"
                    ),
                );
            }
            let d = after_assets - before_assets;
            // THE INFLATION-ATTACK TOOTH: a positive deposit must mint positive shares.
            if after_shares <= before_shares {
                return violated(
                    constraint,
                    format!(
                        "VaultDeposit: inflation-attack rejection — a positive deposit must mint positive shares \
                         (slot[{ss}] before {before_shares}, after {after_shares})"
                    ),
                );
            }
            let m = after_shares - before_shares;
            // THE NO-DILUTION FLOOR: before_assets·m ≤ before_shares·d (the existing
            // price-per-share never decreases). u128 so the products cannot overflow.
            if u128::from(before_assets) * u128::from(m) > u128::from(before_shares) * u128::from(d)
            {
                return violated(
                    constraint,
                    format!(
                        "VaultDeposit: dilution — minting {m} shares for a deposit of {d} dilutes the existing holders \
                         (before_assets·m = {} > before_shares·d = {})",
                        u128::from(before_assets) * u128::from(m),
                        u128::from(before_shares) * u128::from(d)
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::TemporalPredicate {
            dsl_hash,
            witness_index,
        } => {
            // Cav-Codex Block 2: dispatch through the witnessed-predicate
            // registry using the `Temporal` kind. The `witness_index`
            // names which witness blob is the input.
            //
            // SECURITY (audit item 4): the proof bytes are bound by an
            // *explicit* index — the blob immediately following the input
            // (`witness_index + 1`) — instead of a first-of-kind
            // ProofBytes scan. A first-of-kind scan could cross-match a
            // proof intended for a different predicate (e.g. a `Renounced`
            // ProofBytes blob) to this temporal predicate. The proof slot
            // is deterministic and must be ProofBytes, else we fail closed.
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::TemporalPredicateWitnessMissing {
                    dsl_hash: *dsl_hash,
                });
            };
            let input_idx = *witness_index as usize;
            let input_blob =
                witnesses
                    .blob(input_idx)
                    .ok_or(ProgramError::TemporalPredicateWitnessMissing {
                        dsl_hash: *dsl_hash,
                    })?;
            let proof_idx = input_idx + 1;
            let proof_blob = witnesses
                .blob(proof_idx)
                .filter(|b| b.kind == WitnessKindTag::ProofBytes)
                .ok_or(ProgramError::WitnessedPredicateRejected {
                    kind_name: "Temporal",
                    reason: "TemporalPredicate proof must be a ProofBytes blob at \
                         witness_index + 1 (explicit binding); none found"
                        .into(),
                })?;
            let wp = crate::predicate::WitnessedPredicate {
                kind: crate::predicate::WitnessedPredicateKind::Temporal,
                commitment: *dsl_hash,
                input_ref: InputRef::Witness { index: input_idx },
                proof_witness_index: proof_idx,
            };
            let input = PredicateInput::Bytes(input_blob.bytes);
            registry.verify(&wp, &input, proof_blob.bytes).map_err(|e| {
                ProgramError::WitnessedPredicateRejected {
                    kind_name: "Temporal",
                    reason: e.to_string(),
                }
            })
        }

        StateConstraint::BoundDelta { peer_cell, .. } => {
            // Cross-cell binding is verified by γ.2's cross-cell match
            // loop in the turn executor (post-effect, pre-commit). The
            // per-cell evaluator does not have peer-cell state in scope;
            // it surfaces a sentinel error the executor maps to the
            // cross-cell path.
            Err(ProgramError::BoundDeltaNotWired {
                peer_cell: *peer_cell,
            })
        }

        StateConstraint::AnyOf { variants } => {
            if variants.is_empty() {
                return violated(constraint, "AnyOf with no variants".into());
            }
            let mut last_err: Option<ProgramError> = None;
            for v in variants {
                match evaluate_simple_constraint(v, new_state, old_state, ctx, meta, witnesses) {
                    Ok(()) => return Ok(()),
                    Err(e) => last_err = Some(e),
                }
            }
            Err(
                last_err.unwrap_or_else(|| ProgramError::ConstraintViolated {
                    constraint: constraint.clone(),
                    description: "no AnyOf branch satisfied".into(),
                }),
            )
        }

        // ─── Witnessed branches under ⊔ (§11.3, the AnyOfBound rung) ───
        // Mirrors the proven Lean `evalConstraint_anyOfBound_iff` (admits IFF
        // SOME branch admits) + `anyOfBound_stripped_proof_branch_fails` (a
        // witnessed branch with an absent/invalid proof FAILS — it cannot
        // masquerade as a no-proof branch). Each branch CALLS the executor's
        // existing evaluator (LAW #1 — no new semantics): the cheap `Simple`
        // leg through `evaluate_simple_constraint`; the `Witnessed` leg by
        // dispatching the EXACT same `ObservedFieldEquals` verification (so the
        // witnessed branch's anti-strip behaviour IS the standalone atom's —
        // missing blob / forged `at_root` / no authority all fail closed, and
        // the per-branch `proof_witness_index` keeps the audit-item-4 binding).
        StateConstraint::AnyOfBound { branches } => {
            if branches.is_empty() {
                return violated(constraint, "AnyOfBound with no branches".into());
            }
            let mut last_err: Option<ProgramError> = None;
            for branch in branches {
                let result = match branch {
                    BoundBranch::Simple(c) => {
                        evaluate_simple_constraint(c, new_state, old_state, ctx, meta, witnesses)
                    }
                    BoundBranch::Witnessed {
                        local_field,
                        source_cell,
                        source_field,
                        at_root,
                        proof_witness_index,
                    } => {
                        // The witnessed leg IS the cross-cell verified-observation
                        // atom — dispatch the same proven arm, so a stripped proof
                        // closes THIS branch exactly as it refuses the standalone
                        // `ObservedFieldEquals`.
                        let observed = StateConstraint::ObservedFieldEquals {
                            local_field: *local_field,
                            source_cell: *source_cell,
                            source_field: *source_field,
                            at_root: *at_root,
                            proof_witness_index: *proof_witness_index,
                        };
                        evaluate_constraint_full(
                            &observed, new_state, old_state, ctx, meta, witnesses,
                        )
                    }
                };
                match result {
                    Ok(()) => return Ok(()),
                    Err(e) => last_err = Some(e),
                }
            }
            Err(
                last_err.unwrap_or_else(|| ProgramError::ConstraintViolated {
                    constraint: constraint.clone(),
                    description: "no AnyOfBound branch satisfied".into(),
                }),
            )
        }

        // ─── TYPED dig/sym field atoms (mirrors Lean `PredAlgebra` typed atoms) ───
        // The untyped 8-slot substrate has no leaf-type distinction: a `sym` is
        // the u64 lane (`field_to_u64`), a `dig` is the full 32-byte field. So the
        // sym/dig EQUALITY/MEMBERSHIP arms read the appropriate lane; `DigFieldEq`
        // is the genuinely-new full-field cross-slot equality (owner-match).
        StateConstraint::SymEq { index, sym } => {
            let idx = check_index(*index)?;
            let v = field_to_u64(&new_state.fields[idx]);
            if v != *sym {
                return violated(constraint, format!("sym field[{idx}] = {v} != {sym}"));
            }
            Ok(())
        }

        StateConstraint::SymMemberOf { index, set } => {
            let idx = check_index(*index)?;
            let v = field_to_u64(&new_state.fields[idx]);
            if !set.contains(&v) {
                return violated(
                    constraint,
                    format!("sym field[{idx}] = {v} not in enum set"),
                );
            }
            Ok(())
        }

        StateConstraint::DigEq { index, digest } => {
            let idx = check_index(*index)?;
            // Full 32-byte digest equality (NOT the u64 lane): a cell-reference /
            // commitment is pinned by its whole hash.
            if new_state.fields[idx] != *digest {
                return violated(constraint, format!("dig field[{idx}] != expected digest"));
            }
            Ok(())
        }

        StateConstraint::DigFieldEq {
            left_index,
            right_index,
        } => {
            let left = check_index(*left_index)?;
            let right = check_index(*right_index)?;
            // Full 32-byte cross-slot equality — the owner-match tooth. Distinct
            // from `FieldLteField` (a u64-lane ordering): this is digest EQUALITY.
            if new_state.fields[left] != new_state.fields[right] {
                return violated(
                    constraint,
                    format!("dig field[{left}] != dig field[{right}] (owner-match failed)"),
                );
            }
            Ok(())
        }

        // ─── Policy-combinator core (mirrors Lean `Exec.Program`) ───
        StateConstraint::MemberOf { index, set } => {
            let idx = check_index(*index)?;
            let v = field_to_u64(&new_state.fields[idx]);
            if !set.contains(&v) {
                return violated(constraint, format!("field[{idx}] = {v} not in allowlist"));
            }
            Ok(())
        }

        StateConstraint::PrefixOf {
            seg_indices,
            prefix,
        } => {
            // Fail-closed: a path shorter than the queried prefix cannot match.
            if prefix.len() > seg_indices.len() {
                return violated(constraint, "path shorter than prefix".into());
            }
            for (k, want) in prefix.iter().enumerate() {
                let idx = check_index(seg_indices[k])?;
                let got = field_to_u64(&new_state.fields[idx]);
                if got != *want {
                    return violated(
                        constraint,
                        format!("path segment {k} = {got}, prefix wants {want}"),
                    );
                }
            }
            Ok(())
        }

        StateConstraint::InRangeTwoSided { index, lo, hi } => {
            let idx = check_index(*index)?;
            let v = field_to_u64(&new_state.fields[idx]);
            if !(v >= *lo && v <= *hi) {
                return violated(
                    constraint,
                    format!("field[{idx}] = {v} outside [{lo}, {hi}]"),
                );
            }
            Ok(())
        }

        StateConstraint::DeltaBounded { index, d } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    let delta = field_delta_i128(&old.fields[idx], &new_state.fields[idx]);
                    if delta.unsigned_abs() > (*d as u128) {
                        return violated(
                            constraint,
                            format!("|field[{idx}] delta| = {} > {d}", delta.unsigned_abs()),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::AffineLe { terms, c } => {
            let sum = affine_sum(terms, new_state)?;
            if sum > (*c as i128) {
                return violated(constraint, format!("affine sum {sum} > {c}"));
            }
            Ok(())
        }

        StateConstraint::AffineEq { terms, c } => {
            let sum = affine_sum(terms, new_state)?;
            if sum != (*c as i128) {
                return violated(constraint, format!("affine sum {sum} != {c}"));
            }
            Ok(())
        }

        StateConstraint::Reachable {
            from_index,
            to_label,
            edges,
        } => {
            let idx = check_index(*from_index)?;
            let from = field_to_u64(&new_state.fields[idx]);
            if !reachable_closure(edges, from, *to_label) {
                return violated(
                    constraint,
                    format!("label {from} does not reach {to_label} in DAG"),
                );
            }
            Ok(())
        }

        StateConstraint::ClearanceDominates {
            actor_label_index,
            box_index,
            root_index,
            edges,
        } => {
            let actor_idx = check_index(*actor_label_index)?;
            let box_idx = check_index(*box_index)?;
            let root_idx = check_index(*root_index)?;
            // The slot-consulting tooth: the carried graph MUST commit to the
            // root stored in `new[root_index]`, else a turn could walk an
            // over-permissive (or entirely substituted) graph. Recompute the
            // canonical commitment and compare to the stored root — FAIL CLOSED
            // on mismatch BEFORE the dominance walk.
            let committed = clearance_graph_root(edges);
            if committed != new_state.fields[root_idx] {
                return violated(
                    constraint,
                    format!(
                        "clearance graph commitment does not match stored root in slot {root_idx} \
                         (carried graph is not the committed one)"
                    ),
                );
            }
            // The proved-sound `dominatesD` walk: the actor's clearance label
            // must dominate the required compartment label (both read from
            // post-state slots) in the (now root-verified) graph.
            let actor = new_state.fields[actor_idx];
            let box_label = new_state.fields[box_idx];
            if !dominates_closure(edges, actor, box_label) {
                return violated(
                    constraint,
                    format!(
                        "actor clearance label in slot {actor_idx} does not dominate the required \
                         compartment label in slot {box_idx} in the clearance graph"
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::AllOf { variants } => {
            for v in variants {
                evaluate_simple_constraint(v, new_state, old_state, ctx, meta, witnesses)?;
            }
            Ok(())
        }

        StateConstraint::Witnessed { wp } => {
            let kind_name: &'static str = match wp.kind {
                crate::predicate::WitnessedPredicateKind::Dfa => "Dfa",
                crate::predicate::WitnessedPredicateKind::Temporal => "Temporal",
                crate::predicate::WitnessedPredicateKind::MerkleMembership => "MerkleMembership",
                crate::predicate::WitnessedPredicateKind::NonMembership => "NonMembership",
                crate::predicate::WitnessedPredicateKind::BlindedSet => "BlindedSet",
                crate::predicate::WitnessedPredicateKind::BridgePredicate => "BridgePredicate",
                crate::predicate::WitnessedPredicateKind::PedersenEquality => "PedersenEquality",
                crate::predicate::WitnessedPredicateKind::Custom { .. } => "Custom",
            };
            // Cav-Codex Block 2: dispatch through the registry when one
            // is supplied. Resolve the InputRef to a PredicateInput and
            // read the proof bytes from `witnesses.blobs[wp.proof_witness_index]`.
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::WitnessedPredicateRequiresExecutor { kind_name });
            };
            let proof_blob = witnesses.blob(wp.proof_witness_index).ok_or(
                ProgramError::WitnessedPredicateRejected {
                    kind_name,
                    reason: format!(
                        "witness_blobs has no entry at proof_witness_index {}",
                        wp.proof_witness_index
                    ),
                },
            )?;
            // Resolve input ref. For Slot we hand a 32-byte slot value;
            // for Witness we hand the bytes; for Sender we hand the
            // sender pk; for PublicInput we cannot synthesize without
            // the proof's PI vec (caller must use a more specialized
            // path); for SigningMessage we fall through to Bytes.
            //
            // For Sender we need to extend the lifetime of the sender
            // pk reference; we resolve the sender outside the match
            // so the &[u8; 32] borrow is valid for the call.
            let sender_ref: Option<&[u8; 32]> = match &wp.input_ref {
                InputRef::Sender => Some(
                    ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?
                        .sender
                        .as_ref()
                        .ok_or(ProgramError::MissingContextField { field: "sender" })?,
                ),
                _ => None,
            };
            let input: PredicateInput<'_> = match &wp.input_ref {
                InputRef::Slot { index } => {
                    let idx = check_index(*index)?;
                    PredicateInput::Slot(&new_state.fields[idx])
                }
                InputRef::Witness { index } => {
                    let b =
                        witnesses
                            .blob(*index)
                            .ok_or(ProgramError::WitnessedPredicateRejected {
                                kind_name,
                                reason: format!(
                                    "witness_blobs has no entry at input_ref index {index}"
                                ),
                            })?;
                    PredicateInput::Bytes(b.bytes)
                }
                InputRef::PublicInput { .. } => {
                    return Err(ProgramError::WitnessedPredicateRejected {
                        kind_name,
                        reason: "InputRef::PublicInput unsupported in cell-program evaluator"
                            .into(),
                    });
                }
                InputRef::Sender => PredicateInput::Sender(sender_ref.unwrap()),
                InputRef::SigningMessage => {
                    // Caller passes the signing message as a Cleartext
                    // blob; pick the first one.
                    let b = witnesses
                        .blobs
                        .iter()
                        .find(|b| b.kind == WitnessKindTag::Cleartext)
                        .ok_or(ProgramError::WitnessedPredicateRejected {
                            kind_name,
                            reason: "InputRef::SigningMessage needs a Cleartext witness blob"
                                .into(),
                        })?;
                    PredicateInput::Bytes(b.bytes)
                }
            };
            registry.verify(wp, &input, proof_blob.bytes).map_err(|e| {
                ProgramError::WitnessedPredicateRejected {
                    kind_name,
                    reason: e.to_string(),
                }
            })
        }

        StateConstraint::Custom { ir_hash, .. } => {
            // Cav-Codex Block 2: require an attached `custom_program_proof`
            // (a ProofBytes witness blob whose verifier is registered
            // against the declared `ir_hash` as a `Custom { vk_hash }`
            // kind). When no registry is supplied or no matching
            // verifier is registered, fall through to the legacy
            // fail-closed sentinel.
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::CustomConstraintUnevaluable { ir_hash: *ir_hash });
            };
            // SECURITY (audit item 4): bind the proof blob by uniqueness,
            // not first-of-kind. If the action carries more than one
            // ProofBytes blob the binding is ambiguous (a proof for some
            // other predicate could be cross-matched here) and we fail
            // closed. Apps needing multiple same-kind proofs migrate to
            // the typed `Witnessed { wp }` variant.
            let (proof_idx, proof_blob) =
                unique_blob_of_kinds(witnesses, &[WitnessKindTag::ProofBytes]).map_err(|e| {
                    ProgramError::CustomProgramProofRejected {
                        ir_hash: *ir_hash,
                        reason: match e {
                            UniqueBlobError::Missing => {
                                "no ProofBytes witness blob carried for Custom predicate".into()
                            }
                            UniqueBlobError::Ambiguous => {
                                "ambiguous Custom proof: action carries more than one ProofBytes \
                                 blob; bind explicitly via Witnessed { wp }"
                                    .to_string()
                            }
                        },
                    }
                })?;
            let wp = crate::predicate::WitnessedPredicate {
                kind: crate::predicate::WitnessedPredicateKind::Custom { vk_hash: *ir_hash },
                commitment: *ir_hash,
                input_ref: InputRef::Slot { index: 0 },
                proof_witness_index: proof_idx,
            };
            // Input: hand the entire new_state as Slot(0) reference;
            // custom verifiers are expected to fold whatever they need
            // out of the PI / proof itself.
            let input = PredicateInput::Slot(&new_state.fields[0]);
            registry.verify(&wp, &input, proof_blob.bytes).map_err(|e| {
                ProgramError::CustomProgramProofRejected {
                    ir_hash: *ir_hash,
                    reason: match e {
                        WitnessedPredicateError::KindNotRegistered { .. } => {
                            format!("no verifier registered for ir_hash {:02x?}", ir_hash)
                        }
                        other => other.to_string(),
                    },
                }
            })
        }

        // ─── Turn-context atoms (CELL-PROGRAM-LANGUAGE.md §3) ───
        StateConstraint::SenderIs { pk } => {
            let ctx = ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let sender = ctx
                .sender
                .as_ref()
                .ok_or(ProgramError::MissingContextField { field: "sender" })?;
            if sender != pk {
                return violated(
                    constraint,
                    "turn sender is not the bound identity (SenderIs)".into(),
                );
            }
            Ok(())
        }

        StateConstraint::SenderInSlot { index } => {
            let idx = check_index(*index)?;
            let ctx = ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let sender = ctx
                .sender
                .as_ref()
                .ok_or(ProgramError::MissingContextField { field: "sender" })?;
            if sender != &new_state.fields[idx] {
                return violated(
                    constraint,
                    format!("turn sender does not match the identity held in slot[{idx}]"),
                );
            }
            Ok(())
        }

        StateConstraint::BalanceGte { min } => {
            let bal = new_state.balance();
            // SIGNED balance (THE EPOCH §5): any negative balance is below
            // every u64 floor.
            if bal < 0 || (bal as u64) < *min {
                return violated(
                    constraint,
                    format!("cell balance {bal} < required minimum {min}"),
                );
            }
            Ok(())
        }

        StateConstraint::BalanceLte { max } => {
            let bal = new_state.balance();
            // A negative balance satisfies every u64 ceiling.
            if bal >= 0 && (bal as u64) > *max {
                return violated(
                    constraint,
                    format!("cell balance {bal} > allowed maximum {max}"),
                );
            }
            Ok(())
        }

        // ─── Turn-context atoms (apps gaps 3/4): the Lean twins
        //     `senderMemberOf` / `balanceDeltaLe` / `balanceDeltaGe` /
        //     `affineDeltaLe`. Each mirrors its admit-characterization in
        //     `metatheory/Dregg2/Exec/Program.lean`. ───
        StateConstraint::SenderMemberOf { members } => {
            // Mirrors `evalSimpleCtx_senderMemberOf_iff`: admits IFF the
            // context carries a sender AND that sender ∈ members. No sender
            // (system turn / no context) ⇒ MissingContextField (fail-closed);
            // a sender off the board ⇒ ConstraintViolated.
            let ctx = ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let sender = ctx
                .sender
                .as_ref()
                .ok_or(ProgramError::MissingContextField { field: "sender" })?;
            if !members.contains(sender) {
                return violated(
                    constraint,
                    "turn sender is not a member of the bound id-set (SenderMemberOf)".into(),
                );
            }
            Ok(())
        }

        StateConstraint::BalanceDeltaLte { max } => {
            // Mirrors `evalSimpleCtx_balanceDeltaLe_iff`: admits IFF BOTH the
            // pre- and post-turn sealed balances are present AND
            // `new.balance − old.balance <= max`. The pre-turn balance is the
            // executor's `old_state` (the already-plumbed `balanceBefore`); an
            // absent pre-state fails closed (a rate gate needs both endpoints).
            // Balances are SIGNED i64 (THE EPOCH §5); the delta is computed in
            // i128 to avoid overflow, and `max` (signed) is compared in i128.
            let old = old_state.ok_or(ProgramError::TransitionCheckRequiresOldState {
                constraint: constraint.clone(),
                index: 0,
            })?;
            let delta = new_state.balance() as i128 - old.balance() as i128;
            if delta > (*max as i128) {
                return violated(
                    constraint,
                    format!("per-turn balance change {delta} > allowed maximum {max}"),
                );
            }
            Ok(())
        }

        StateConstraint::BalanceDeltaGte { min } => {
            // Mirrors `evalSimpleCtx_balanceDeltaGe_iff`: admits IFF BOTH the
            // pre- and post-turn sealed balances are present AND
            // `new.balance − old.balance >= min`. Absent pre-state ⇒ fail-closed.
            let old = old_state.ok_or(ProgramError::TransitionCheckRequiresOldState {
                constraint: constraint.clone(),
                index: 0,
            })?;
            let delta = new_state.balance() as i128 - old.balance() as i128;
            if delta < (*min as i128) {
                return violated(
                    constraint,
                    format!("per-turn balance change {delta} < required minimum {min}"),
                );
            }
            Ok(())
        }

        StateConstraint::AffineDeltaLe { terms, c } => {
            // Mirrors `evalConstraint_affineDeltaLe_iff`: admits IFF every
            // term-slot reads on BOTH old and new AND
            // `Σ kᵢ·(new[fᵢ] − old[fᵢ]) <= c`. Absent pre-state (no old_state)
            // ⇒ the delta is not evaluable ⇒ fail-closed; a bad slot index ⇒
            // InvalidFieldIndex (inside `affine_delta_sum`).
            let old = old_state.ok_or(ProgramError::TransitionCheckRequiresOldState {
                constraint: constraint.clone(),
                index: 0,
            })?;
            let sum = affine_delta_sum(terms, old, new_state)?;
            if sum > (*c as i128) {
                return violated(constraint, format!("affine delta sum {sum} > {c}"));
            }
            Ok(())
        }

        // ─── Heap-keyed atom (THE ROTATION's app-state lane) ───
        StateConstraint::HeapField { key, atom } => {
            evaluate_heap_atom(constraint, *key, atom, new_state, old_state)
        }

        // ─── Cross-KEY heap relation: new[key] <= new[other_key] + delta ───
        StateConstraint::HeapFieldLteOther {
            key,
            other_key,
            delta,
        } => {
            // Read BOTH operands from the post-state heap (get_field_ext: keys
            // < STATE_SLOTS are registers, >= STATE_SLOTS the fields_map).
            // FAIL CLOSED if EITHER key is absent — a cross-key bound over an
            // unborn key is unevaluable (stricter than the Lean FIELD_ZERO
            // default; the executor only ever tightens). Same i128 + signed
            // delta comparison as StateConstraint::FieldLteOther.
            let lhs = match new_state.get_field_ext(*key) {
                Some(ref x) => field_to_u64(x) as i128,
                None => {
                    return violated(
                        constraint,
                        format!("heap[{key}] absent post-state (HeapFieldLteOther fails closed)"),
                    );
                }
            };
            let rhs = match new_state.get_field_ext(*other_key) {
                Some(ref x) => field_to_u64(x) as i128 + *delta as i128,
                None => {
                    return violated(
                        constraint,
                        format!(
                            "heap[{other_key}] absent post-state (HeapFieldLteOther fails closed)"
                        ),
                    );
                }
            };
            if lhs > rhs {
                return violated(
                    constraint,
                    format!(
                        "heap[{key}] = {lhs} > heap[{other_key}] + {delta} = {rhs} in post-state"
                    ),
                );
            }
            Ok(())
        }

        // ─── Program-readable delegation_epoch (the channels closure lane) ───
        StateConstraint::DelegationEpochEquals { index } => {
            let idx = check_index(*index)?;
            // Fail-closed: only the executor's per-cell program-check loop
            // stamps the epoch (`TransitionMeta::with_delegation_epoch`);
            // every legacy/wildcard meta surfaces the sentinel.
            let epoch = meta
                .delegation_epoch
                .ok_or(ProgramError::MissingContextField {
                    field: "delegation_epoch",
                })?;
            // Full 32-byte equality against the canonical encoding — a slot
            // with garbage upper limbs and a matching low limb is refused.
            if new_state.fields[idx] != field_from_u64(epoch) {
                return violated(
                    constraint,
                    format!(
                        "slot[{idx}] != delegation_epoch ({epoch}): the epoch slot diverged \
                         from the capability-freshness counter (DelegationEpochEquals)"
                    ),
                );
            }
            Ok(())
        }

        // ─── Count-≥ / order-statistic atom (in-program M-of-N) ───
        StateConstraint::CountGe {
            threshold,
            set_commitment_slot,
        } => {
            let idx = check_index(*set_commitment_slot)?;
            // The witness re-exhibits the FULL element set every turn (the
            // anti-AffineLe design: nothing accumulates in state, so no
            // counter slot can fake M). Bind by uniqueness, fail closed on
            // ambiguity — the `unique_blob_of_kinds` discipline.
            let (_, blob) = unique_blob_of_kinds(witnesses, &[WitnessKindTag::Cleartext]).map_err(
                |e| match e {
                    UniqueBlobError::Missing => ProgramError::MissingContextField {
                        field: "count-ge set-exhibit witness (Cleartext)",
                    },
                    UniqueBlobError::Ambiguous => ProgramError::WitnessedPredicateRejected {
                        kind_name: "CountGe",
                        reason: "ambiguous: more than one Cleartext witness blob; \
                                 the set exhibit cannot be bound"
                            .to_string(),
                    },
                },
            )?;
            let elements: Vec<[u8; 32]> = postcard::from_bytes(blob.bytes).map_err(|_| {
                ProgramError::WitnessedPredicateRejected {
                    kind_name: "CountGe",
                    reason: "set-exhibit blob is not a postcard Vec<[u8;32]>".to_string(),
                }
            })?;
            // Distinctness is structural: duplicates collapse in the set
            // (a duplicate-padded exhibit dedupes to the SAME committed set,
            // so the commitment still binds and the count stays honest).
            let set: std::collections::BTreeSet<[u8; 32]> = elements.into_iter().collect();
            let commitment = count_ge_set_commitment(&set);
            if new_state.fields[idx] != commitment {
                return violated(
                    constraint,
                    format!("exhibited set does not open the commitment in slot[{idx}] (CountGe)"),
                );
            }
            if (set.len() as u64) < (*threshold as u64) {
                return violated(
                    constraint,
                    format!(
                        "exhibited set has {} distinct element(s) < threshold {threshold} (CountGe)",
                        set.len()
                    ),
                );
            }
            Ok(())
        }

        // ─── Cross-cell verified observation (§11.2) ───
        StateConstraint::ObservedFieldEquals {
            local_field,
            source_cell,
            source_field,
            at_root,
            proof_witness_index,
        } => {
            // Mirrors the proven `evalConstraintCtx_observedFieldEquals_iff`:
            // admits IFF the host `FinalizedRootAuthority` confirms `at_root`
            // is `source_cell`'s genuine FINALIZED commitment AND opens
            // `source_field` to `v`, AND `new[local_field] == v`. Every other
            // path fails CLOSED.
            let idx = check_index(*local_field)?;
            // Fail-closed without a host authority: no channel to the peer's
            // real finalized roots ⇒ a self-fabricated `at_root` is
            // indistinguishable from a genuine one, so REJECT (the Lean
            // empty-`observedFields` carrier; the `IssuerRootAuthority`
            // BlindedSet posture). This is the anti-forge tooth.
            let Some(authority) = witnesses.finalized_roots else {
                return Err(ProgramError::WitnessedPredicateRequiresExecutor {
                    kind_name: "ObservedFieldEquals",
                });
            };
            // The Merkle-open proof rides in the witness at the bound index
            // (named, not first-of-kind — no cross-match window). Its absence
            // is fail-closed: the portal cannot have opened a root the prover
            // did not supply a proof for.
            let _proof = witnesses.blob(*proof_witness_index).ok_or(
                ProgramError::WitnessedPredicateRejected {
                    kind_name: "ObservedFieldEquals",
                    reason: format!(
                        "no Merkle-open witness blob at proof_witness_index {proof_witness_index} \
                         (cross-cell finalized read cannot be opened)"
                    ),
                },
            )?;
            // Recompute against the receipt chain: the host opens the peer's
            // finalized field, rejecting a forged `at_root` / a field never
            // finalized at that root (fail-closed inside the authority).
            let observed = authority
                .observe_finalized_field(source_cell, at_root, *source_field)
                .map_err(|reason| ProgramError::WitnessedPredicateRejected {
                    kind_name: "ObservedFieldEquals",
                    reason,
                })?;
            // The binding is real: `new[local_field]` MUST equal the peer's
            // finalized value (the mismatch tooth — a turn cannot diverge its
            // local field from the observed finalized value).
            if new_state.fields[idx] != observed {
                return violated(
                    constraint,
                    format!(
                        "slot[{idx}] != the finalized value of source_field {source_field} on the \
                         peer cell at the observed root (ObservedFieldEquals)"
                    ),
                );
            }
            Ok(())
        }

        // ─── Aggregate-over-a-collection gate (the heap/layout rung) ───
        StateConstraint::CollectionAggregate {
            collection_id,
            stride,
            fuel,
            pred,
        } => {
            // Read the named collection out of the cell's `(collection_id,
            // key)` heap (the `Value.collectionField` mirror). The anchor
            // (the predicate's key/read offset) drives the `readIndexed`
            // truncation. Fail-closed: an absent collection (element 0's
            // anchor not present, or a zero stride) REJECTS — an aggregate
            // over an absent collection is unevaluable
            // (`collectionAggregate_absent_refuses`).
            let anchor = pred.anchor_offset();
            let Some(coll) = read_collection(new_state, *collection_id, *stride, *fuel, anchor)
            else {
                return violated(
                    constraint,
                    format!(
                        "collection {collection_id} is absent/empty (CollectionAggregate fails \
                         closed: no collection to aggregate)"
                    ),
                );
            };
            // Evaluate the aggregate (`CollPred.eval` / `mOfNDistinct`).
            if pred.eval(&coll) {
                Ok(())
            } else {
                violated(
                    constraint,
                    format!(
                        "aggregate over collection {collection_id} ({} element(s)) refuses \
                         (CollectionAggregate)",
                        coll.len()
                    ),
                )
            }
        }

        // ─── Aggregate over the EXECUTOR-REACHABLE user-field map (the
        //     `fields_map` twin of CollectionAggregate; the `_RECORD-LAYER-
        //     UPGRADE.md` deliverable). Same fail-closed shape, same CollPred
        //     evaluator — only the read source is the map, not the heap. ───
        StateConstraint::FieldsCollectionAggregate {
            base,
            stride,
            fuel,
            pred,
        } => {
            let anchor = pred.anchor_offset();
            let Some(coll) = read_collection_fields(new_state, *base, *stride, *fuel, anchor)
            else {
                return violated(
                    constraint,
                    format!(
                        "fields-map collection at base {base} is absent/empty \
                         (FieldsCollectionAggregate fails closed: no collection to aggregate)"
                    ),
                );
            };
            if pred.eval(&coll) {
                Ok(())
            } else {
                violated(
                    constraint,
                    format!(
                        "aggregate over fields-map collection at base {base} ({} element(s)) \
                         refuses (FieldsCollectionAggregate)",
                        coll.len()
                    ),
                )
            }
        }

        // ─── Register-reading temporal atoms (the proven `TemporalAlgebra`
        //     family). Each honors the discharged Lean semantics
        //     (`TemporalAtom.eval` / `EventAtom.eval`,
        //     `metatheory/Dregg2/Authority/TemporalAlgebra{,2}.lean`): read the
        //     COMMITTED PRE-state register (`old_state`; absent ⇒ 0 ⇒
        //     `FIELD_ZERO`), fail closed. ───
        StateConstraint::RateBound { counter_index, k } => {
            let idx = check_index(*counter_index)?;
            // Lean `TemporalAtom.rateBound`: admit iff `fieldOf counter rec < k`
            // over the committed PRE-state record.
            let count = old_state.map(|o| field_to_u64(&o.fields[idx])).unwrap_or(0);
            if count >= *k {
                return violated(
                    constraint,
                    format!("rate counter field[{idx}] = {count} not < k = {k}"),
                );
            }
            Ok(())
        }

        StateConstraint::CooledSince { staged_at, period } => {
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "block_height",
            })?;
            // Lean `TemporalAtom.cooledSince` ≡ `afterHeight (staged_at + period)`.
            let boundary = staged_at.saturating_add(*period);
            if ctx.block_height < boundary {
                return violated(
                    constraint,
                    format!(
                        "height {} < cooled boundary staged_at({staged_at}) + period({period}) = {boundary}",
                        ctx.block_height
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::UntilEvent { flag_index } => {
            let idx = check_index(*flag_index)?;
            // Lean `EventAtom.untilEvent`: admit WHILE the pre-state flag reads 0.
            let flag = old_state.map(|o| field_to_u64(&o.fields[idx])).unwrap_or(0);
            if flag != 0 {
                return violated(
                    constraint,
                    format!(
                        "event flag field[{idx}] already set ({flag} != 0); UntilEvent (U) closed"
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::SinceEvent { flag_index } => {
            let idx = check_index(*flag_index)?;
            // Lean `EventAtom.sinceEvent`: admit only SINCE the pre-state flag
            // is set (absent ⇒ 0 ⇒ refuse, fail-closed).
            let flag = old_state.map(|o| field_to_u64(&o.fields[idx])).unwrap_or(0);
            if flag == 0 {
                return violated(
                    constraint,
                    format!("event flag field[{idx}] not yet set; SinceEvent (S) fails closed"),
                );
            }
            Ok(())
        }

        StateConstraint::ChallengeWindow {
            challenge_index,
            staged_at,
            period,
        } => {
            let idx = check_index(*challenge_index)?;
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "block_height",
            })?;
            // Lean `TemporalAtom.challengeWindow`: window elapsed AND no
            // challenge filed (pre-state challenge register reads 0).
            let boundary = staged_at.saturating_add(*period);
            if ctx.block_height < boundary {
                return violated(
                    constraint,
                    format!(
                        "challenge window not elapsed: height {} < staged_at({staged_at}) + period({period}) = {boundary}",
                        ctx.block_height
                    ),
                );
            }
            let challenge = old_state.map(|o| field_to_u64(&o.fields[idx])).unwrap_or(0);
            if challenge != 0 {
                return violated(
                    constraint,
                    format!(
                        "challenge filed (field[{idx}] = {challenge} != 0); settlement refused"
                    ),
                );
            }
            Ok(())
        }
    }
}

/// Domain tag for [`count_ge_set_commitment`].
const COUNT_GE_SET_DOMAIN: &str = "dregg-countge-set-v1";

/// Canonical openable commitment over a `CountGe` element set: BLAKE3
/// (derive-key domain) over the length-prefixed SORTED 32-byte elements —
/// the same openable sorted-set shape as the channel membership root
/// (`blueprint::channel_member_root`) and the mailbox sender set. An empty
/// set commits to a nonzero value distinct from the all-zero unborn slot.
pub fn count_ge_set_commitment(elements: &std::collections::BTreeSet<[u8; 32]>) -> FieldElement {
    let mut hasher = blake3::Hasher::new_derive_key(COUNT_GE_SET_DOMAIN);
    hasher.update(&(elements.len() as u64).to_le_bytes());
    for e in elements {
        hasher.update(e);
    }
    *hasher.finalize().as_bytes()
}

/// Evaluate a [`HeapAtom`] lifted over heap `key` against the
/// `Option`-valued heap reads of `(old, new)`.
///
/// **Lean twin (the semantics):** `Dregg2.Exec.evalHeap` =
/// `evalSimple (HeapAtom.lift k a)` (`metatheory/Dregg2/Exec/Program.lean`);
/// the per-arm behavior below implements exactly the `evalHeap_*_iff`
/// characterizations and the `evalHeap_*_absent_*` /
/// `evalHeap_immutable_pinned` / `evalHeap_writeOnce_frozen` absence
/// theorems. A missing `old_state` is the Lean EMPTY RECORD: every old
/// key reads `None`. There is deliberately NO `(old_state = None,
/// nonce = 0)` init escape and NO `TransitionCheckRequiresOldState`
/// sentinel here — heap absence has total, fail-closed-coherent
/// semantics of its own (first-write-free where the theorem says so,
/// refuse everywhere else).
///
/// Reads go through [`CellState::get_field_ext`]: keys `< STATE_SLOTS`
/// resolve to the fixed registers (always present when a state exists),
/// keys `>= STATE_SLOTS` to the committed `fields_map` heap.
fn evaluate_heap_atom(
    constraint: &StateConstraint,
    key: u64,
    atom: &HeapAtom,
    new_state: &CellState,
    old_state: Option<&CellState>,
) -> Result<(), ProgramError> {
    let old_v: Option<FieldElement> = old_state.and_then(|s| s.get_field_ext(key));
    let new_v: Option<FieldElement> = new_state.get_field_ext(key);
    match atom {
        // ── post-state atoms: fail closed on an absent post-state key ──
        HeapAtom::Equals { value } => match new_v {
            Some(x) if x == *value => Ok(()),
            Some(_) => violated(constraint, format!("heap[{key}] != expected value")),
            // Absent ≠ present-zero on the heap (evalHeap_equals_absent_refuses).
            None => violated(
                constraint,
                format!("heap[{key}] absent post-state (Equals)"),
            ),
        },
        HeapAtom::Gte { value } => match new_v {
            Some(ref x) if field_gte(x, value) => Ok(()),
            Some(_) => violated(constraint, format!("heap[{key}] < minimum value")),
            None => violated(constraint, format!("heap[{key}] absent post-state (Gte)")),
        },
        HeapAtom::Lte { value } => match new_v {
            Some(ref x) if field_lte(x, value) => Ok(()),
            Some(_) => violated(constraint, format!("heap[{key}] > maximum value")),
            None => violated(constraint, format!("heap[{key}] absent post-state (Lte)")),
        },
        HeapAtom::MemberOf { set } => match new_v {
            Some(ref x) if set.contains(&field_to_u64(x)) => Ok(()),
            Some(ref x) => violated(
                constraint,
                format!("heap[{key}] = {} not in allowlist", field_to_u64(x)),
            ),
            None => violated(
                constraint,
                format!("heap[{key}] absent post-state (MemberOf)"),
            ),
        },
        HeapAtom::InRangeTwoSided { lo, hi } => match new_v {
            Some(ref x) => {
                let v = field_to_u64(x);
                if v >= *lo && v <= *hi {
                    Ok(())
                } else {
                    violated(
                        constraint,
                        format!("heap[{key}] = {v} outside [{lo}, {hi}]"),
                    )
                }
            }
            None => violated(
                constraint,
                format!("heap[{key}] absent post-state (InRangeTwoSided)"),
            ),
        },

        // ── immutable: first write free, then pinned (erasure refused) ──
        HeapAtom::Immutable => match old_v {
            // evalHeap_immutable_absent_old_admits: the first write is free.
            None => Ok(()),
            // evalHeap_immutable_pinned: admission ⇔ post-state holds the
            // SAME value — a flip OR an erasure (new absent) refuses
            // (evalHeap_immutable_erase_refused).
            Some(a) => {
                if new_v == Some(a) {
                    Ok(())
                } else {
                    violated(
                        constraint,
                        format!("heap[{key}] is pinned (Immutable) and was mutated or erased"),
                    )
                }
            }
        },

        // ── writeOnce: absent/zero-old free, nonzero freezes ──
        HeapAtom::WriteOnce => match old_v {
            // evalHeap_writeOnce_absent_admits / _zero_admits.
            None => Ok(()),
            Some(a) if a == FIELD_ZERO => Ok(()),
            // evalHeap_writeOnce_frozen: admission ⇔ unchanged.
            Some(a) => {
                if new_v == Some(a) {
                    Ok(())
                } else {
                    violated(
                        constraint,
                        format!("heap[{key}] is write-once and was already set"),
                    )
                }
            }
        },

        // ── relational atoms: BOTH sides must be present (no init escape) ──
        HeapAtom::Monotonic => match (old_v, new_v) {
            (Some(ref a), Some(ref b)) if field_gte(b, a) => Ok(()),
            (Some(_), Some(_)) => violated(
                constraint,
                format!("heap[{key}] decreased; Monotonic requires new >= old"),
            ),
            // evalHeap_monotonic_absent_old/new_refuses.
            _ => violated(
                constraint,
                format!("heap[{key}] absent pre- or post-state (Monotonic fails closed)"),
            ),
        },
        HeapAtom::StrictMonotonic => match (old_v, new_v) {
            (Some(ref a), Some(ref b)) if field_gt(b, a) => Ok(()),
            (Some(_), Some(_)) => violated(
                constraint,
                format!("heap[{key}] did not strictly increase (StrictMonotonic)"),
            ),
            _ => violated(
                constraint,
                format!("heap[{key}] absent pre- or post-state (StrictMonotonic fails closed)"),
            ),
        },
        HeapAtom::DeltaBounded { d } => match (old_v, new_v) {
            (Some(ref a), Some(ref b)) => {
                let delta = field_delta_i128(a, b);
                if delta.unsigned_abs() > (*d as u128) {
                    violated(
                        constraint,
                        format!("|heap[{key}] delta| = {} > {d}", delta.unsigned_abs()),
                    )
                } else {
                    Ok(())
                }
            }
            _ => violated(
                constraint,
                format!("heap[{key}] absent pre- or post-state (DeltaBounded fails closed)"),
            ),
        },
        HeapAtom::DeltaEquals { d } => match (old_v, new_v) {
            // Both present (NO init/nonce escape — an absent old OR new
            // refuses, exactly like DeltaBounded / the Lean `fieldDelta`
            // both-present match). EXACT signed delta: `new - old == d`.
            (Some(ref a), Some(ref b)) => {
                let delta = field_delta_i128(a, b);
                if delta == *d as i128 {
                    Ok(())
                } else {
                    violated(
                        constraint,
                        format!("heap[{key}] delta = {delta} != {d} (DeltaEquals)"),
                    )
                }
            }
            _ => violated(
                constraint,
                format!("heap[{key}] absent pre- or post-state (DeltaEquals fails closed)"),
            ),
        },
    }
}

fn violated(constraint: &StateConstraint, description: String) -> Result<(), ProgramError> {
    Err(ProgramError::ConstraintViolated {
        constraint: constraint.clone(),
        description,
    })
}

fn viol(constraint: &StateConstraint, description: &str) -> ProgramError {
    ProgramError::ConstraintViolated {
        constraint: constraint.clone(),
        description: description.to_string(),
    }
}

/// Lift a non-`Not` `SimpleStateConstraint` into the full
/// `StateConstraint` enum so the same evaluator can handle the lattice
/// of static / transition / contextual variants.
///
/// `Not` is *not* lifted: it has no corresponding `StateConstraint`
/// variant and is dispatched directly by
/// [`evaluate_simple_constraint`], which short-circuits on the inner
/// constraint's acceptance bit. Calling `lift_simple` on a `Not` is a
/// programming error and panics — callers must go through
/// [`evaluate_simple_constraint`] instead.
fn lift_simple(s: &SimpleStateConstraint) -> StateConstraint {
    match s {
        SimpleStateConstraint::FieldEquals { index, value } => StateConstraint::FieldEquals {
            index: *index,
            value: *value,
        },
        SimpleStateConstraint::FieldGte { index, value } => StateConstraint::FieldGte {
            index: *index,
            value: *value,
        },
        SimpleStateConstraint::FieldLte { index, value } => StateConstraint::FieldLte {
            index: *index,
            value: *value,
        },
        SimpleStateConstraint::WriteOnce { index } => StateConstraint::WriteOnce { index: *index },
        SimpleStateConstraint::Immutable { index } => StateConstraint::Immutable { index: *index },
        SimpleStateConstraint::Monotonic { index } => StateConstraint::Monotonic { index: *index },
        SimpleStateConstraint::StrictMonotonic { index } => {
            StateConstraint::StrictMonotonic { index: *index }
        }
        SimpleStateConstraint::BoundedBy {
            index,
            witness_index,
        } => StateConstraint::BoundedBy {
            index: *index,
            witness_index: *witness_index,
        },
        SimpleStateConstraint::FieldGteHeight { index, offset } => {
            StateConstraint::FieldGteHeight {
                index: *index,
                offset: *offset,
            }
        }
        SimpleStateConstraint::FieldLteHeight { index, offset } => {
            StateConstraint::FieldLteHeight {
                index: *index,
                offset: *offset,
            }
        }
        SimpleStateConstraint::TemporalGate {
            not_before,
            not_after,
        } => StateConstraint::TemporalGate {
            not_before: *not_before,
            not_after: *not_after,
        },
        SimpleStateConstraint::Not(_) => {
            // The Heyting-fragment Not has no equivalent
            // StateConstraint variant — it is dispatched inline by
            // evaluate_simple_constraint. lift_simple must not be
            // called on a Not.
            panic!(
                "lift_simple invoked on SimpleStateConstraint::Not; \
                 route through evaluate_simple_constraint instead"
            );
        }
        SimpleStateConstraint::SenderIs { pk } => StateConstraint::SenderIs { pk: *pk },
        SimpleStateConstraint::SenderInSlot { index } => {
            StateConstraint::SenderInSlot { index: *index }
        }
        SimpleStateConstraint::BalanceGte { min } => StateConstraint::BalanceGte { min: *min },
        SimpleStateConstraint::BalanceLte { max } => StateConstraint::BalanceLte { max: *max },
        SimpleStateConstraint::PreimageGate {
            commitment_index,
            hash_kind,
        } => StateConstraint::PreimageGate {
            commitment_index: *commitment_index,
            hash_kind: *hash_kind,
        },
        SimpleStateConstraint::HeapField { key, atom } => StateConstraint::HeapField {
            key: *key,
            atom: atom.clone(),
        },
        SimpleStateConstraint::DelegationEpochEquals { index } => {
            StateConstraint::DelegationEpochEquals { index: *index }
        }
        SimpleStateConstraint::CountGe {
            threshold,
            set_commitment_slot,
        } => StateConstraint::CountGe {
            threshold: *threshold,
            set_commitment_slot: *set_commitment_slot,
        },
        SimpleStateConstraint::SenderMemberOf { members } => StateConstraint::SenderMemberOf {
            members: members.clone(),
        },
        SimpleStateConstraint::BalanceDeltaLte { max } => {
            StateConstraint::BalanceDeltaLte { max: *max }
        }
        SimpleStateConstraint::BalanceDeltaGte { min } => {
            StateConstraint::BalanceDeltaGte { min: *min }
        }
    }
}

/// Evaluate a `SimpleStateConstraint` directly — handles the Heyting
/// `Not` short-circuit inline, falls back to `lift_simple` +
/// `evaluate_constraint_full` for the lattice variants.
///
/// **Acceptance semantics for `Not`:**
/// - Inner `Ok(())` (inner accepts) → `Not` rejects (returns
///   `ConstraintViolated`).
/// - Inner `Err(ProgramError::ConstraintViolated { .. })` (inner
///   rejects on its own terms) → `Not` accepts (`Ok(())`).
/// - Inner returns any other error (`MissingContextField`,
///   `InvalidFieldIndex`, `TransitionCheckRequiresOldState`,
///   `WitnessedPredicateRequiresExecutor`, etc.) → `Not` propagates
///   the same error. This preserves the fail-closed contract: an
///   unevaluable predicate is unevaluable under negation, not
///   vacuously satisfied.
fn evaluate_simple_constraint(
    s: &SimpleStateConstraint,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
    meta: &TransitionMeta,
    witnesses: &WitnessBundle<'_>,
) -> Result<(), ProgramError> {
    match s {
        SimpleStateConstraint::Not(inner) => {
            let lifted_inner = lift_simple(inner);
            match evaluate_constraint_full(
                &lifted_inner,
                new_state,
                old_state,
                ctx,
                meta,
                witnesses,
            ) {
                // Inner accepted ⇒ Not rejects.
                Ok(()) => Err(ProgramError::ConstraintViolated {
                    constraint: lifted_inner.clone(),
                    description: format!(
                        "Not({:?}): inner constraint accepted; negation rejects",
                        inner
                    ),
                }),
                // Inner rejected on its own terms ⇒ Not accepts.
                Err(ProgramError::ConstraintViolated { .. }) => Ok(()),
                // Inner unevaluable (missing ctx, bad index,
                // transition-needs-old-state, witness/registry
                // missing, …) ⇒ propagate, do NOT accept. Fail-closed.
                Err(other) => Err(other),
            }
        }
        other => {
            let lifted = lift_simple(other);
            evaluate_constraint_full(&lifted, new_state, old_state, ctx, meta, witnesses)
        }
    }
}

/// Hash a 32-byte preimage under the named [`HashKind`] — the shared
/// digest function behind [`StateConstraint::PreimageGate`] and
/// [`StateConstraint::KeyRotationGate`].
///
/// `Poseidon2` is the STARK-native hash: it runs the exact audited
/// `dregg_circuit::poseidon2` sponge (`hash_bytes`, the same width-16 BabyBear
/// permutation the whole circuit verifies, KAT-locked to Plonky3's
/// `default_babybear_poseidon2_16`) over the preimage bytes, then encodes the
/// resulting field element into the 32-byte slot word via
/// [`crate::felt_to_bytes32`] — the SAME felt→bytes encoding the capability
/// root uses. So a Poseidon2-gated slot commitment computed here equals the
/// circuit's `hash_bytes(preimage)` digest bit-for-bit (see the cross-crate KAT
/// `cell::tests::poseidon2_hash_matches_circuit`).
fn hash_preimage32(hash_kind: &HashKind, preimage: &[u8; 32]) -> [u8; 32] {
    match hash_kind {
        HashKind::Blake3 => *blake3::hash(preimage).as_bytes(),
        HashKind::Poseidon2 => {
            crate::felt_to_bytes32(dregg_circuit::poseidon2::hash_bytes(preimage))
        }
    }
}

// ============================================================================
// Field arithmetic / comparisons
// ============================================================================

/// Interpret a field element as a big-endian u64 (last 8 bytes).
pub(crate) fn field_to_u64(field: &FieldElement) -> u64 {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&field[24..32]);
    u64::from_be_bytes(bytes)
}

fn field_delta_i128(old: &FieldElement, new: &FieldElement) -> i128 {
    field_to_u64(new) as i128 - field_to_u64(old) as i128
}

/// Check one `BoundDelta` pair against concrete local and peer state snapshots.
///
/// The ordinary cell-side evaluator still returns `BoundDeltaNotWired` because
/// it does not have peer state in scope. The executor's multi-cell pass and
/// system-level tests use this helper once both old/new cell states are known.
pub fn bound_delta_pair_matches(
    local_old: &CellState,
    local_new: &CellState,
    local_slot: u8,
    peer_old: &CellState,
    peer_new: &CellState,
    peer_slot: u8,
    relation: DeltaRelation,
) -> Result<bool, ProgramError> {
    let local_idx = check_index(local_slot)?;
    let peer_idx = check_index(peer_slot)?;
    let local_delta = field_delta_i128(&local_old.fields[local_idx], &local_new.fields[local_idx]);
    let peer_delta = field_delta_i128(&peer_old.fields[peer_idx], &peer_new.fields[peer_idx]);
    Ok(match relation {
        DeltaRelation::Equal => local_delta == peer_delta,
        DeltaRelation::EqualAndOpposite => local_delta + peer_delta == 0,
    })
}

/// `Σ kᵢ·new[fᵢ]` over named slots (big-endian u64 lifted to i128). Fail-closed on a
/// bad slot index. Mirrors Lean `Exec.affineSum`.
fn affine_sum(terms: &[(i64, u8)], state: &CellState) -> Result<i128, ProgramError> {
    let mut sum: i128 = 0;
    for (k, idx) in terms {
        let i = check_index(*idx)?;
        let x = field_to_u64(&state.fields[i]) as i128;
        sum += (*k as i128) * x;
    }
    Ok(sum)
}

/// `Σ kᵢ·(new[fᵢ] − old[fᵢ])` over named slots — the affine combination of the per-field
/// DELTAS across the `(old, new)` transition (big-endian u64 lifted to i128 on each side).
/// Fail-closed on a bad slot index. Mirrors Lean `Exec.affineDeltaSum` (the reader behind
/// `affineDeltaLe`): the genuine multi-field rate gate the single-field `DeltaBounded` /
/// `FieldDelta` cannot express.
fn affine_delta_sum(
    terms: &[(i64, u8)],
    old_state: &CellState,
    new_state: &CellState,
) -> Result<i128, ProgramError> {
    let mut sum: i128 = 0;
    for (k, idx) in terms {
        let i = check_index(*idx)?;
        let delta = field_delta_i128(&old_state.fields[i], &new_state.fields[i]);
        sum += (*k as i128) * delta;
    }
    Ok(sum)
}

/// Fuel-bounded reflexive-transitive reachability over `(dominator, dominated)` edges
/// (`a` reaches `b`). Mirrors Lean `ClearanceGraph.dominatesFuel`/`dominatesD`: fuel =
/// `edges.len() + 1` bounds the search depth on a finite graph.
fn reachable_closure(edges: &[(u64, u64)], a: u64, b: u64) -> bool {
    fn go(edges: &[(u64, u64)], a: u64, b: u64, fuel: usize) -> bool {
        if fuel == 0 {
            return false;
        }
        if a == b {
            return true;
        }
        edges
            .iter()
            .any(|(src, mid)| *src == a && go(edges, *mid, b, fuel - 1))
    }
    go(edges, a, b, edges.len() + 1)
}

/// Fuel-bounded reflexive-transitive reachability over FULL-FIELD
/// `(dominator, dominated)` edges (`a` dominates `b`). The 32-byte-label twin
/// of [`reachable_closure`]; it IS the proved-sound Lean
/// `ClearanceGraph.dominatesFuel`/`dominatesD`
/// (`metatheory/Dregg2/Authority/ClearanceGraph.lean:46,53`) realised over the
/// untyped felt substrate, fuel = `edges.len() + 1` bounding the search depth on
/// a finite graph. Reflexive: `a == b ⇒ true` (an actor holding exactly the box
/// label is cleared).
fn dominates_closure(
    edges: &[(FieldElement, FieldElement)],
    a: FieldElement,
    b: FieldElement,
) -> bool {
    fn go(
        edges: &[(FieldElement, FieldElement)],
        a: FieldElement,
        b: FieldElement,
        fuel: usize,
    ) -> bool {
        if fuel == 0 {
            return false;
        }
        if a == b {
            return true;
        }
        edges
            .iter()
            .any(|(src, mid)| *src == a && go(edges, *mid, b, fuel - 1))
    }
    go(edges, a, b, edges.len() + 1)
}

/// Canonical commitment of a clearance graph (a SET of `(dominator, dominated)`
/// edges) to a 32-byte [`FieldElement`] root, for [`StateConstraint::ClearanceDominates`].
///
/// Domain-separated BLAKE3 over the LEX-SORTED, deduplicated edge bytes — the
/// same BLAKE3 family the apps hash their labels with (`field_from_bytes`), so a
/// mandate cell can pin this value in its `clearance_graph_root` slot and the
/// executor recomputes it on every touching turn. ORDER-INDEPENDENT (the graph
/// is a set; sorting + dedup means two edge lists denoting the same graph commit
/// to the same root), so reordering edges does NOT change the root, and a
/// duplicate edge does not. The leading `len` is bound (length-extension /
/// concatenation ambiguity), then each 64-byte `dominator || dominated` edge.
pub fn clearance_graph_root(edges: &[(FieldElement, FieldElement)]) -> FieldElement {
    let mut canon: Vec<[u8; 64]> = edges
        .iter()
        .map(|(hi, lo)| {
            let mut buf = [0u8; 64];
            buf[..32].copy_from_slice(hi);
            buf[32..].copy_from_slice(lo);
            buf
        })
        .collect();
    canon.sort_unstable();
    canon.dedup();
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"dregg.clearance-graph-root.v1");
    hasher.update(&(canon.len() as u64).to_be_bytes());
    for edge in &canon {
        hasher.update(edge);
    }
    *hasher.finalize().as_bytes()
}

/// Compare two field elements as unsigned big-endian: a >= b.
pub(crate) fn field_gte(a: &FieldElement, b: &FieldElement) -> bool {
    a >= b
}

/// Compare two field elements as unsigned big-endian: a <= b.
pub(crate) fn field_lte(a: &FieldElement, b: &FieldElement) -> bool {
    field_gte(b, a)
}

/// Compare two field elements as unsigned big-endian: a > b strictly.
fn field_gt(a: &FieldElement, b: &FieldElement) -> bool {
    a > b
}

/// Field addition modulo the byte-array representation (u64 lane in last 8
/// bytes). For decrements, encode `delta` as the additive inverse. See
/// `SLOT-CAVEATS-EVALUATION.md` §8 question 6.
fn field_add(a: &FieldElement, b: &FieldElement) -> FieldElement {
    let av = field_to_u64(a);
    let bv = field_to_u64(b);
    let s = av.wrapping_add(bv);
    let mut out = *a;
    out[24..32].copy_from_slice(&s.to_be_bytes());
    out
}

/// Helper: create a FieldElement from a u64 (big-endian in last 8 bytes).
pub fn field_from_u64(val: u64) -> FieldElement {
    let mut f = FIELD_ZERO;
    f[24..32].copy_from_slice(&val.to_be_bytes());
    f
}

/// Alias for `field_from_u64` — explicit big-endian naming for clarity at call sites.
pub fn field_from_u64_be(val: u64) -> FieldElement {
    field_from_u64(val)
}
