from pathlib import Path

helpers = r'''
theorem sgmWF_of_mandate_cell_eq {k k' : RecordKernelState}
    (hc : k'.cell mandateCell = k.cell mandateCell) (hcav : k'.slotCaveats mandateCell = k.slotCaveats mandateCell)
    (hwf : sgmWF k) : sgmWF k' := by
  rcases hwf with ⟨hvol, hprog⟩
  refine ⟨?_, ?_⟩
  · unfold sgmVolumeBound sgmVolumeSpent
    rw [show sgmVolumeSpent k' = sgmVolumeSpent k from by simp [sgmVolumeSpent, hc]]
    exact hvol
  · simpa [hcav] using hprog

theorem sgmInBucket_of_mandate_cell_eq {k k' : RecordKernelState} (bucket : Int)
    (hc : k'.cell mandateCell = k.cell mandateCell) (hcav : k'.slotCaveats mandateCell = k.slotCaveats mandateCell)
    (hb : sgmInBucket k bucket) : sgmInBucket k' bucket := by
  rcases hb with ⟨hanchor, hprog⟩
  refine ⟨?_, ?_⟩
  · unfold sgmAnchorIs sgmAnchor
    rw [show sgmAnchor k' = sgmAnchor k from by simp [sgmAnchor, hc]]
    exact hanchor
  · simpa [hcav] using hprog

theorem sgmVolumeSpent_writeField_ne {k k' : RecordKernelState} {f : FieldName} {target : CellId} {v : Value}
    (h : k' = writeField k f target v) (hf : f ≠ volumeSpentSlot) :
    sgmVolumeSpent k' = sgmVolumeSpent k := by
  subst h; unfold sgmVolumeSpent writeField
  by_cases ht : target = mandateCell
  · subst ht; simp only [if_pos rfl, fieldOf]
    congr 1
    simpa [Value.field] using field_setField_ne f volumeSpentSlot (k.cell mandateCell) v hf
  · simp only [if_neg (Ne.symm ht)]

theorem sgmAnchor_writeField_ne {k k' : RecordKernelState} {f : FieldName} {target : CellId} {v : Value}
    (h : k' = writeField k f target v) (hf : f ≠ commitmentAnchorSlot) :
    sgmAnchor k' = sgmAnchor k := by
  subst h; unfold sgmAnchor writeField
  by_cases ht : target = mandateCell
  · subst ht; simp only [if_pos rfl, fieldOf]
    congr 1
    simpa [Value.field] using field_setField_ne f commitmentAnchorSlot (k.cell mandateCell) v hf
  · simp only [if_neg (Ne.symm ht)]

theorem sgmVolumeBound_of_spent_eq {k k' : RecordKernelState}
    (hv : sgmVolumeSpent k' = sgmVolumeSpent k) (hb : sgmVolumeBound k = true) :
    sgmVolumeBound k' = true := by
  unfold sgmVolumeBound at *; simpa [hv] using hb

theorem sgmAnchorIs_of_anchor_eq {k k' : RecordKernelState} (bucket : Int)
    (ha : sgmAnchor k' = sgmAnchor k) (hb : sgmAnchorIs k bucket = true) :
    sgmAnchorIs k' bucket = true := by
  unfold sgmAnchorIs at *; simpa [ha] using hb

theorem caveatsAdmit_volume_bounded (k : RecordKernelState) (actor : CellId) (newSpent : Int)
    (hprog : sgmMandateProgramOK k)
    (h : caveatsAdmit k volumeSpentSlot actor mandateCell newSpent = true) :
    sgmVolumeBound (writeField k volumeSpentSlot mandateCell (.int newSpent)) = true := by
  rcases hprog with rfl
  unfold sgmVolumeBound sgmVolumeSpent caveatsAdmit mandateCaveats at h ⊢
  simp only [fieldOf, writeField, if_pos rfl, List.filter, List.all, SlotCaveat.field,
    SlotCaveat.eval, beq_self_eq_true, decide_eq_true_eq] at h ⊢
  exact h.2

theorem caveatsAdmit_anchor_unchanged (k : RecordKernelState) (actor : CellId) (newAnchor : Int)
    (hprog : sgmMandateProgramOK k)
    (h : caveatsAdmit k commitmentAnchorSlot actor mandateCell newAnchor = true) :
    newAnchor = sgmAnchor k := by
  rcases hprog with rfl
  unfold sgmAnchor caveatsAdmit mandateCaveats at h ⊢
  simp only [fieldOf, List.filter, List.all, SlotCaveat.field, SlotCaveat.eval, beq_self_eq_true,
    decide_eq_true_eq] at h
  exact h

theorem sgmWF_setFieldA_preserved (s s' : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (h : execFullA s (.setFieldA actor cell f v) = some s') (hwf : sgmWF s.kernel) : sgmWF s'.kernel := by
  simp only [execFullA] at h
  obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq h)
  have hk : s'.kernel = writeField s.kernel f cell (.int v) := by simpa using hs'.symm
  by_cases hmc : cell = mandateCell
  · subst hmc
    by_cases hv : f = volumeSpentSlot
    · subst hv; rw [hk]; rcases hwf with ⟨_, hprog⟩
      exact ⟨caveatsAdmit_volume_bounded s.kernel actor v hprog (stateStepGuarded_admits h), hprog⟩
    · rw [hk]; rcases hwf with ⟨hvol, hprog⟩
      exact ⟨sgmVolumeBound_of_spent_eq (sgmVolumeSpent_writeField_ne rfl hv) hvol, hprog⟩
  · exact sgmWF_of_mandate_cell_eq (by rw [hk]; exact writeField_cell_other s.kernel f cell (.int v) (Ne.symm hmc)) rfl hwf

theorem sgmInBucket_setFieldA_preserved (s s' : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (bucket : Int) (h : execFullA s (.setFieldA actor cell f v) = some s') (hb : sgmInBucket s.kernel bucket) :
    sgmInBucket s'.kernel bucket := by
  simp only [execFullA] at h
  obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq h)
  have hk : s'.kernel = writeField s.kernel f cell (.int v) := by simpa using hs'.symm
  by_cases hmc : cell = mandateCell
  · subst hmc
    by_cases ha : f = commitmentAnchorSlot
    · subst ha
      rcases hb with ⟨hanchor, hprog⟩
      have hunchanged := caveatsAdmit_anchor_unchanged s.kernel actor v hprog (stateStepGuarded_admits h)
      rw [hk]; refine ⟨?_, hprog⟩
      unfold sgmAnchorIs sgmAnchor at hanchor ⊢; simpa [hunchanged] using hanchor
    · rw [hk]; rcases hb with ⟨hanchor, hprog⟩
      exact ⟨sgmAnchorIs_of_anchor_eq bucket (sgmAnchor_writeField_ne rfl ha) hanchor, hprog⟩
  · exact sgmInBucket_of_mandate_cell_eq bucket (by rw [hk]; exact writeField_cell_other s.kernel f cell (.int v) (Ne.symm hmc)) rfl hb

'''

exec_wf = Path('/tmp/sgm_exec_clean.txt').read_text()
exec_wf = exec_wf.replace(
    '| setFieldA actor cell f v =>\n      exact sgmWF_setFieldA_preserved s s\' actor cell f v h hwf',
    '| setFieldA actor cell f v =>\n      exact sgmWF_setFieldA_preserved s s\' actor cell f v h hwf')

exec_inner = '''
theorem execInnerA_sgmWF_preserved (s s' : RecChainedState) (inner : List FullActionA)
    (h : execInnerA s inner = some s') (hwf : sgmWF s.kernel) : sgmWF s'.kernel := by
  cases inner with
  | nil => simp only [execInnerA, Option.some.injEq] at h; subst h; exact hwf
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact execInnerA_sgmWF_preserved s1 s' rest h (execFullA_sgmWF_preserved s s1 a ha hwf)

theorem execFullTurnA_sgmWF_preserved :
    ∀ (s s' : RecChainedState) (actions : List FullActionA),
      execFullTurnA s actions = some s' → sgmWF s.kernel → sgmWF s'.kernel := by
  intro s s' actions
  induction actions generalizing s with
  | nil => intro h hwf; simpa [execFullTurnA] using hwf
  | cons a rest ih =>
      intro h hwf
      simp only [execFullTurnA] at h
      cases hs : execFullA s a with
      | none => simp [hs] at h
      | some s1 =>
          rw [hs] at h
          cases ht : execFullTurnA s1 s' rest with
          | none => simp [ht] at h
          | some s2 => rw [ht] at h; subst h; exact ih s2 (execFullA_sgmWF_preserved s s1 a hs hwf) ht

theorem execFullForestA_sgmWF_preserved (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') (hwf : sgmWF s.kernel) : sgmWF s'.kernel := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_sgmWF_preserved s s' (lowerForestA f) h hwf

theorem sgmWF_traj_carries (s s' : RecChainedState) (cf : FullForestA)
    (h : execFullForestA s cf = some s') (hwf : sgmWF s.kernel) : sgmWF s'.kernel :=
  execFullForestA_sgmWF_preserved s s' cf h hwf
'''

def adapt_bucket(text: str) -> str:
    t = text
    t = t.replace('execFullA_sgmWF_preserved', 'execFullA_sgmInBucket_preserved bucket')
    t = t.replace('execInnerA_sgmWF_preserved', 'execInnerA_sgmInBucket_preserved bucket')
    t = t.replace('execFullTurnA_sgmWF_preserved', 'execFullTurnA_sgmInBucket_preserved bucket')
    t = t.replace('execFullForestA_sgmWF_preserved', 'execFullForestA_sgmInBucket_preserved')
    t = t.replace('sgmWF_traj_carries', 'sgmBucket_traj_carries')
    t = t.replace('sgmWF_of_mandate_cell_eq', 'sgmInBucket_of_mandate_cell_eq bucket')
    t = t.replace('sgmWF_setFieldA_preserved', 'sgmInBucket_setFieldA_preserved bucket')
    t = t.replace('sgmWF s.kernel', 'sgmInBucket s.kernel bucket')
    t = t.replace("sgmWF s'.kernel", "sgmInBucket s'.kernel bucket")
    t = t.replace('sgmWF s1.kernel', 'sgmInBucket s1.kernel bucket')
    t = t.replace('(hwf : sgmWF s.kernel)', '(hb : sgmInBucket s.kernel bucket)')
    t = t.replace(' hwf)', ' hb)')
    t = t.replace(' hwf ', ' hb ')
    t = t.replace(' hwf\n', ' hb\n')
    t = t.replace(' hwf1', ' hb1')
    t = t.replace(' hwf,', ' hb,')
    t = t.replace('using hwf', 'using hb')
    t = t.replace('exact hwf', 'exact hb')
    t = t.replace('theorem execFullA_sgmInBucket_preserved bucket (s s\' : RecChainedState) (fa : FullActionA)',
                  'theorem execFullA_sgmInBucket_preserved (bucket : Int) (s s\' : RecChainedState) (fa : FullActionA)')
    t = t.replace('theorem execInnerA_sgmInBucket_preserved bucket (s s\' : RecChainedState) (inner : List FullActionA)',
                  'theorem execInnerA_sgmInBucket_preserved (bucket : Int) (s s\' : RecChainedState) (inner : List FullActionA)')
    t = t.replace('theorem execFullTurnA_sgmInBucket_preserved bucket :',
                  'theorem execFullTurnA_sgmInBucket_preserved (bucket : Int) :')
    t = t.replace('theorem execFullForestA_sgmInBucket_preserved (s s\' : RecChainedState) (f : FullForestA)',
                  'theorem execFullForestA_sgmInBucket_preserved (s s\' : RecChainedState) (f : FullForestA) (bucket : Int)')
    t = t.replace('theorem sgmBucket_traj_carries (s s\' : RecChainedState) (cf : FullForestA)',
                  'theorem sgmBucket_traj_carries (s s\' : RecChainedState) (cf : FullForestA) (bucket : Int)')
    t = t.replace('execFullForestA_sgmInBucket_preserved s s\' cf h hwf',
                  'execFullForestA_sgmInBucket_preserved s s\' cf bucket h hb')
    t = t.replace('execFullTurnA_sgmInBucket_preserved bucket s s\' (lowerForestA f) h hwf',
                  'execFullTurnA_sgmInBucket_preserved bucket s s\' (lowerForestA f) h hb')
    t = t.replace('execFullTurnA_sgmInBucket_preserved bucket s s\' (lowerForestA f) h hb',
                  'execFullTurnA_sgmInBucket_preserved bucket s s\' (lowerForestA f) h hb')
    t = t.replace('sgmBucket_traj_carries (s s\' : RecChainedState) (cf : FullForestA) (bucket : Int)\n    (h : execFullForestA s cf = some s\') (hb : sgmInBucket s.kernel bucket) : sgmInBucket s\'.kernel bucket :=\n  execFullForestA_sgmInBucket_preserved s s\' cf h hwf',
                  'sgmBucket_traj_carries (s s\' : RecChainedState) (cf : FullForestA) (bucket : Int)\n    (h : execFullForestA s cf = some s\') (hb : sgmInBucket s.kernel bucket) :\n    sgmInBucket s\'.kernel bucket :=\n  execFullForestA_sgmInBucket_preserved s s\' cf bucket h hb')
    return t

exec_bucket = adapt_bucket(exec_wf + exec_inner.replace('theorem execInnerA_sgmWF_preserved', 'theorem execInnerA_sgmInBucket_preserved (bucket : Int)').replace('execFullA_sgmWF_preserved', 'execFullA_sgmInBucket_preserved bucket').replace('execFullTurnA_sgmWF_preserved', 'execFullTurnA_sgmInBucket_preserved bucket').replace('execFullForestA_sgmWF_preserved', 'execFullForestA_sgmInBucket_preserved').replace('sgmWF_traj_carries', 'sgmBucket_traj_carries_PLACEHOLDER'))

# simpler: only adapt exec_wf for bucket + separate inner/turn/forest/bucket tail
bucket_wf = adapt_bucket(exec_wf)
bucket_tail = '''
theorem execInnerA_sgmInBucket_preserved (bucket : Int) (s s' : RecChainedState) (inner : List FullActionA)
    (h : execInnerA s inner = some s') (hb : sgmInBucket s.kernel bucket) : sgmInBucket s'.kernel bucket := by
  cases inner with
  | nil => simp only [execInnerA, Option.some.injEq] at h; subst h; exact hb
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact execInnerA_sgmInBucket_preserved bucket s1 s' rest h (execFullA_sgmInBucket_preserved bucket s s1 a ha hb)

theorem execFullTurnA_sgmInBucket_preserved (bucket : Int) :
    ∀ (s s' : RecChainedState) (actions : List FullActionA),
      execFullTurnA s actions = some s' → sgmInBucket s.kernel bucket → sgmInBucket s'.kernel bucket := by
  intro s s' actions
  induction actions generalizing s with
  | nil => intro h hb; simpa [execFullTurnA] using hb
  | cons a rest ih =>
      intro h hb
      simp only [execFullTurnA] at h
      cases hs : execFullA s a with
      | none => simp [hs] at h
      | some s1 =>
          rw [hs] at h
          cases ht : execFullTurnA s1 s' rest with
          | none => simp [ht] at h
          | some s2 => rw [ht] at h; subst h; exact ih s2 (execFullA_sgmInBucket_preserved bucket s s1 a hs hb) ht

theorem execFullForestA_sgmInBucket_preserved (s s' : RecChainedState) (f : FullForestA) (bucket : Int)
    (h : execFullForestA s f = some s') (hb : sgmInBucket s.kernel bucket) :
    sgmInBucket s'.kernel bucket := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_sgmInBucket_preserved bucket s s' (lowerForestA f) h hb

theorem sgmBucket_traj_carries (s s' : RecChainedState) (cf : FullForestA) (bucket : Int)
    (h : execFullForestA s cf = some s') (hb : sgmInBucket s.kernel bucket) :
    sgmInBucket s'.kernel bucket :=
  execFullForestA_sgmInBucket_preserved s s' cf bucket h hb
'''

mid = helpers + exec_wf + '\n' + exec_inner + '\n' + bucket_wf + '\n' + bucket_tail

src = Path('/Users/ember/dev/breadstuffs/metatheory/Dregg2/Apps/StorageGatewayMandate.lean').read_text()
start = src.index('/-- Hatchery carry')
end = src.index('/-! ## §C — Stingray volume-budget demo')
Path('/Users/ember/dev/breadstuffs/metatheory/Dregg2/Apps/StorageGatewayMandate.lean').write_text(src[:start] + mid + '\n' + src[end:])
print('ok')