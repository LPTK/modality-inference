import ModalityInference.ComparisonJointAssemblyReification
import ModalityInference.Proofs.ComparisonJointAssemblyGroup
import ModalityInference.Proofs.ComparisonTupleWitness
import ModalityInference.Proofs.ComparisonJointModeWitness

namespace ModalityInference.ComparisonJointAssemblyReification

open ComparisonPropagation ComparisonJointAssembly ComparisonControls SymbolicModes

noncomputable def projectWorld (allowed : List ModVar) (world : Nat → Bool) (i : Nat) : Bool :=
  if atomVariable i ∈ allowed then world i else false

@[simp] theorem projectExpression_eval (allowed : List ModVar) (e : BoolExpr) (world : Nat → Bool) :
    (projectExpression allowed e).eval world = e.eval (projectWorld allowed world) := by
  simp only [projectExpression, SymbolicCNF.substitute_eval]
  congr 1
  funext i
  by_cases hi : atomVariable i ∈ allowed <;> simp [projectAtom, projectWorld, hi, BoolExpr.eval]

theorem projectExpression_atoms {allowed : List ModVar} {e : BoolExpr} {v : Nat}
    (h : v ∈ (projectExpression allowed e).atoms) :
    v ∈ e.atoms ∧ atomVariable v ∈ allowed := by
  obtain ⟨w, hw, hv⟩ := SymbolicCNF.substitute_atoms h
  unfold projectAtom at hv
  split at hv
  · have he : v = w := by simpa [BoolExpr.atoms] using hv
    subst v
    exact ⟨hw, by simpa using ‹allowed.contains (atomVariable w) = true›⟩
  · simp [BoolExpr.atoms] at hv

theorem run_modes_atoms {fuel : Nat} {side : Nat → Bool} {flex : List Nat}
    {count heads : Nat} {input : ComparisonJointGroup.Input} {result : Result input count flex}
    (h : ComparisonJointAssembly.run fuel side flex count heads input = .success result)
    {v w : Nat} (hw : w ∈ (result.solution.modes.substitute v).atoms) :
    side w = side v ∧ (v ∈ flex → w ∉ flex) := by
  obtain ⟨solution, hs, rfl⟩ := run_solution h
  unfold ComparisonJointGuarded.run at hs
  cases hr : CNFPropagation.solve fuel (ComparisonJointGuarded.query side flex (compile side count heads input)) with
  | exhausted | rejected => simp [hr, bind, RunResult.bind] at hs
  | success assignment =>
    simp only [hr, bind, RunResult.bind, pure, RunResult.success.injEq] at hs
    cases hs
    exact ComparisonJointModes.witness_atoms
      (ComparisonJointGuarded.modeClauses_supported side true _)
      (ComparisonJointGuarded.modeClauses_supported side false _) hw

theorem rebase_positive {heads : Nat} {embedding : Fin selectors → Fin constants}
    {clauses : CNF} (h : Positive clauses) : Positive (rebase heads embedding clauses) := by
  intro clause hc literal hl
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hc
  obtain ⟨value, hv, rfl⟩ := List.mem_map.mp hl
  exact h original ho value hv

theorem rebase_atoms {heads : Nat} {embedding : Fin selectors → Fin constants}
    {clauses : CNF} {v : Nat} (h : v ∈ CNFPropagation.atoms (rebase heads embedding clauses)) :
    ∃ w ∈ CNFPropagation.atoms clauses, v = rebaseAtom heads embedding w := by
  obtain ⟨clause, hc, polarity, hl⟩ := CNFPropagation.mem_atoms.mp h
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hc
  obtain ⟨value, hv, he⟩ := List.mem_map.mp hl
  exact ⟨value.1, CNFPropagation.mem_atoms.mpr ⟨original, ho, value.2, hv⟩,
    (congrArg Prod.fst he).symm⟩

theorem values_parameter (allowed : List ModVar) (result : Result input count flex)
    (embedding : Fin selectors → Fin (constantCount input)) (i : Nat) :
    values allowed result (parameter embedding i) =
      if hi : i < selectors then .const result.solution.constants[embedding ⟨i, hi⟩]
      else projectExpression allowed (result.solution.modes.substitute (i - selectors)) := by
  by_cases hi : i < selectors
  · simp [parameter, values, hi, (embedding ⟨i, hi⟩).isLt]
  · simp [parameter, values, hi, show ¬constantCount input + (i - selectors) < constantCount input by omega]

theorem scalars_rebase {b : Basis} (result : Result input count flex)
    (embedding : Fin selectors → Fin (constantCount input)) {i : Nat} (hi : b.heads.length ≤ i) :
    scalars b result (rebaseAtom b.heads.length embedding i) =
      if (i - b.heads.length) % 2 == 0 then
        values b.modes result (parameter embedding ((i - b.heads.length) / 2))
      else .imp (values b.modes result (parameter embedding ((i - b.heads.length) / 2))) (.const false) := by
  have hr : (i - b.heads.length) % 2 < 2 := Nat.mod_lt _ (by decide)
  simp [scalars, rebaseAtom, ComparisonTupleWitness.signed, Nat.not_lt.mpr hi, Nat.add_assoc,
    show (2 * parameter embedding ((i - b.heads.length) / 2) + (i - b.heads.length) % 2) / 2 =
      parameter embedding ((i - b.heads.length) / 2) by omega]

theorem rebase_coordinate_supported {fuel : Nat} {flex : List Nat} {b : Basis}
    {input : ComparisonJointGroup.Input} {result : Result input count flex}
    (h : ComparisonJointAssembly.run fuel ModalSynthesis.locality flex count b.heads.length input = .success result)
    {component : Bool} {axis : Axis}
    (haxis : ∀ v, ModalSynthesis.locality v = component → axis.Supports v)
    (embedding : Fin selectors → Fin (constantCount input)) {clauses : CNF}
    (hkeep : ∀ i ∈ CNFPropagation.atoms clauses,
      ComparisonJointAxisSummary.keep ModalSynthesis.locality component b.heads.length selectors i = true) :
    ComparisonTupleWitness.CoordinateSupported b axis (scalars b result)
      (rebase b.heads.length embedding clauses) := by
  intro v hv hvhead
  obtain ⟨i, hi, rfl⟩ := rebase_atoms hv
  have hih : b.heads.length ≤ i := by
    by_contra hn
    have hh : i < b.heads.length := by omega
    simp [rebaseAtom, hh] at hvhead
    omega
  rw [scalars_rebase result embedding hih]
  have hvalue : ComparisonTupleReification.Supported b axis
      (values b.modes result (parameter embedding ((i - b.heads.length) / 2))) := by
    rw [values_parameter]
    split
    · simp [ComparisonTupleReification.Supported, BoolExpr.atoms]
    · rename_i hn
      have hk : ModalSynthesis.locality ((i - b.heads.length) / 2 - selectors) = component := by
        simpa [ComparisonJointAxisSummary.keep, Nat.not_lt.mpr hih, hn] using hkeep i hi
      intro w hw
      obtain ⟨hw, hm⟩ := projectExpression_atoms hw
      exact ⟨haxis w ((run_modes_atoms h hw).1.trans hk), hm⟩
  split
  · exact hvalue
  · simpa [ComparisonTupleReification.Supported, BoolExpr.atoms] using hvalue

theorem world_rebase (b : Basis) (result : Result input count flex)
    (embedding : Fin selectors → Fin (constantCount input))
    (heads : CompareTy → Bool) (world : Nat → Bool) :
    (ComparisonTupleCNF.world b heads (scalars b result) world ∘ rebaseAtom b.heads.length embedding) =
      ComparisonSelectorPropagation.select b.heads.length
        (ComparisonJointAxisSummary.parameterWorld embedding result.choice
          (result.strategy (projectWorld b.modes world)))
        (basisValue b.heads heads) := by
  funext i
  by_cases hi : i < b.heads.length
  · simp [rebaseAtom, ComparisonTupleCNF.world, hi, ComparisonSelectorPropagation.select,
      basisValue]
  · have hr : ¬rebaseAtom b.heads.length embedding i < b.heads.length := by
      simp only [rebaseAtom, hi, ↓reduceIte]
      omega
    simp only [Function.comp_apply, ComparisonTupleCNF.world, hr, ↓reduceDIte,
      scalars_rebase result embedding (by omega : b.heads.length ≤ i),
      ComparisonSelectorPropagation.select, hi, ↓reduceIte, ComparisonSelectorPropagation.fixedValue]
    by_cases hj : (i - b.heads.length) / 2 < selectors <;> split <;>
      simp [values_parameter, hj, BoolExpr.eval, ComparisonJointAxisSummary.parameterWorld,
        ComparisonJointAxisSummary.decode, Result.choice, Result.strategy]

theorem rebase_holds (b : Basis) (result : Result input count flex)
    (embedding : Fin selectors → Fin (constantCount input))
    (heads : CompareTy → Bool) (world : Nat → Bool) (clauses : CNF) :
    CNFHolds (ComparisonTupleCNF.world b heads (scalars b result) world)
      (rebase b.heads.length embedding clauses) ↔
    CNFHolds (ComparisonSelectorPropagation.select b.heads.length
      (ComparisonJointAxisSummary.parameterWorld embedding result.choice
        (result.strategy (projectWorld b.modes world)))
      (basisValue b.heads heads)) clauses := by
  rw [rebase, rename_correct, world_rebase]

theorem nominal_holds {b : Basis} (result : Result input count flex)
    {clauses : CNF} (hs : Supported (List.range b.heads.length) clauses)
    (heads : CompareTy → Bool) (world : Nat → Bool) :
    CNFHolds (ComparisonTupleCNF.world b heads (scalars b result) world) clauses ↔
      CNFHolds (basisValue b.heads heads) clauses := by
  apply CNFPropagation.holds_congr
  intro i hi
  have hh : i < b.heads.length := List.mem_range.mp (hs i hi)
  simp [ComparisonTupleCNF.world, basisValue, hh]

theorem leaf_complete {fuel : Nat} {flex : List Nat} {b : Basis}
    {input : ComparisonJointGroup.Input} {result : Result input count flex}
    (hl : ComparisonJointHorn.Linear (· < 4 * count) input.locality)
    (ho : ComparisonJointHorn.Linear (· < 4 * count) input.other)
    (hr : ComparisonJointAssembly.run fuel ModalSynthesis.locality flex count b.heads.length input = .success result)
    (i : Fin count) :
    ∃ generated : ComparisonControls.Generated b,
      leaf b result i = some generated.term ∧ ComparisonTupleReification.Total generated ∧
      ∀ heads η,
        ComparisonJointGroup.Compatible (result.state b.heads.length (basisValue b.heads heads)
          (projectWorld b.modes (encodeModes η))) →
        ∀ coordinate, ComparisonTupleReification.observe coordinate heads η generated =
          result.state b.heads.length (basisValue b.heads heads)
            (projectWorld b.modes (encodeModes η)) (ComparisonJointGroup.state coordinate i) := by
  have hp := (run_compiled hr).1
  obtain ⟨hlocal, hother⟩ := run_coordinates hl ho hr
  have sl := rebase_coordinate_supported hr
    (component := true) (axis := .locality)
    (fun v hv => by simpa [Axis.Supports, ModalSynthesis.locality] using hv)
    (localityEmbedding input) (hlocal.2.2.1 (ComparisonJointGroup.state .locality i))
  have sf := rebase_coordinate_supported hr
    (component := false) (axis := .affinity)
    (fun v hv => by simpa [Axis.Supports, ModalSynthesis.locality] using hv)
    (otherEmbedding input) (hother.2.2.1 (ComparisonJointGroup.state .affinity i))
  have su := rebase_coordinate_supported hr
    (component := false) (axis := .uniqueness)
    (fun v hv => by simpa [Axis.Supports, ModalSynthesis.locality] using hv)
    (otherEmbedding input) (hother.2.2.1 (ComparisonJointGroup.state .uniqueness i))
  obtain ⟨generated, hg, ht, he⟩ := ComparisonTupleWitness.reconstructWith_complete
    (hp.1 i) (hp.2.1 i) (hp.2.2.2 i) (hp.2.2.1 i)
    (ComparisonTupleCNF.positive_headPositive (rebase_positive (hlocal.1 (ComparisonJointGroup.state .locality i))))
    (ComparisonTupleCNF.positive_headPositive (rebase_positive (hother.1 (ComparisonJointGroup.state .affinity i))))
    (ComparisonTupleCNF.positive_headPositive (rebase_positive (hother.1 (ComparisonJointGroup.state .uniqueness i))))
    sl sf su
  refine ⟨generated, hg, ht, ?_⟩
  intro heads η hcompatible
  have ep : CNFHolds (ComparisonTupleCNF.world b heads (scalars b result) (encodeModes η))
      result.solution.types[i] ↔
      result.state b.heads.length (basisValue b.heads heads) (projectWorld b.modes (encodeModes η))
        (ComparisonJointGroup.state .unaffected i) = true := by
    rw [Result.state_unaffected]
    exact (nominal_holds result (hp.2.1 i) heads _).trans (ComparisonJointProgram.values_true _ _ _).symm
  have el : CNFHolds (ComparisonTupleCNF.world b heads (scalars b result) (encodeModes η))
      (rebase b.heads.length (localityEmbedding input) result.locality[ComparisonJointGroup.state .locality i]) ↔
      result.state b.heads.length (basisValue b.heads heads) (projectWorld b.modes (encodeModes η))
        (ComparisonJointGroup.state .locality i) = true := by
    rw [rebase_holds, Result.state_locality]
    exact (ComparisonJointProgram.values_true _ _ _).symm
  have ef : CNFHolds (ComparisonTupleCNF.world b heads (scalars b result) (encodeModes η))
      (rebase b.heads.length (otherEmbedding input) result.other[ComparisonJointGroup.state .affinity i]) ↔
      result.state b.heads.length (basisValue b.heads heads) (projectWorld b.modes (encodeModes η))
        (ComparisonJointGroup.state .affinity i) = true := by
    rw [rebase_holds, Result.state_affinity]
    exact (ComparisonJointProgram.values_true _ _ _).symm
  have eu : CNFHolds (ComparisonTupleCNF.world b heads (scalars b result) (encodeModes η))
      (rebase b.heads.length (otherEmbedding input) result.other[ComparisonJointGroup.state .uniqueness i]) ↔
      result.state b.heads.length (basisValue b.heads heads) (projectWorld b.modes (encodeModes η))
        (ComparisonJointGroup.state .uniqueness i) = true := by
    rw [rebase_holds, Result.state_uniqueness]
    exact (ComparisonJointProgram.values_true _ _ _).symm
  have he := he heads η
    (fun hv => ep.mpr (hcompatible.1 i (el.mp hv)))
    (fun hv => ep.mpr (hcompatible.2.1 i (ef.mp hv)))
    (fun hv => eu.mpr (hcompatible.2.2 i (ep.mp hv)))
  intro coordinate
  cases coordinate
  · exact Bool.eq_iff_iff.mpr (he.1.trans ep)
  · exact Bool.eq_iff_iff.mpr (he.2.1.trans el)
  · exact Bool.eq_iff_iff.mpr (he.2.2.1.trans ef)
  · exact Bool.eq_iff_iff.mpr (he.2.2.2.trans eu)

/-- Every actual assembled leaf has one finite type realizing all four
coordinates. Its symbolic coefficients share one projected input valuation. -/
theorem group_leaf_complete {prepareFuel fuel : Nat} {flex : List Nat} {b : Basis}
    {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {input : ComparisonJointGroup.Input} {result : Result input g.leaves.length flex}
    (hp : ComparisonJointGroup.prepare prepareFuel assumptions required g = .success input)
    (hr : ComparisonJointAssembly.run fuel ModalSynthesis.locality flex g.leaves.length g.heads.length input = .success result)
    (hheads : b.heads.length = g.heads.length) (i : Fin g.leaves.length) :
    ∃ generated : ComparisonControls.Generated b,
      leaf b result i = some generated.term ∧ ComparisonTupleReification.Total generated ∧
      ∀ heads η coordinate,
        ComparisonTupleReification.observe coordinate heads η generated =
          result.state g.heads.length (basisValue b.heads heads)
            (projectWorld b.modes (encodeModes η)) (ComparisonJointGroup.state coordinate i) := by
  have hr' : ComparisonJointAssembly.run fuel ModalSynthesis.locality flex g.leaves.length b.heads.length input =
      .success result := by simpa only [hheads] using hr
  have hlinear := ComparisonJointGroup.prepare_linear hp
  obtain ⟨generated, hg, ht, he⟩ := leaf_complete hlinear.2.1 hlinear.2.2 hr' i
  refine ⟨generated, hg, ht, ?_⟩
  intro heads η coordinate
  have hc := run_compatible hp hr (basisValue b.heads heads) (projectWorld b.modes (encodeModes η))
  simpa only [hheads] using he heads η (by simpa only [hheads] using hc) coordinate

/-- Common-shape, defined basis heads and their original identifier support
are preserved by the actual returned type, without enlarging the allowed modes. -/
theorem group_leaf_properties {prepareFuel fuel : Nat} {flex : List Nat} {b : Basis}
    {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {input : ComparisonJointGroup.Input} {result : Result input g.leaves.length flex}
    (hp : ComparisonJointGroup.prepare prepareFuel assumptions required g = .success input)
    (hr : ComparisonJointAssembly.run fuel ModalSynthesis.locality flex g.leaves.length g.heads.length input = .success result)
    (hheads : b.heads.length = g.heads.length) (i : Fin g.leaves.length)
    {Δ : Bounds} {shape : ComparisonShape} {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hh : ∀ a ∈ b.heads, a.WellShaped Δ ∧ ComparisonShape.Equivalent Δ a.shape shape)
    (hd : ∀ a ∈ b.heads, a.DefinedUnder Δ)
    (hP : ∀ a ∈ b.heads, ComparisonInterpolation.Supports P Q a)
    (hQ : ∀ v ∈ b.modes, Q v) :
    ∃ t, leaf b result i = some t ∧ t.WellShaped Δ ∧
      ComparisonShape.Equivalent Δ t.shape shape ∧ t.DefinedUnder Δ ∧
      ComparisonInterpolation.Supports P Q t := by
  obtain ⟨generated, hg, ht, _⟩ := group_leaf_complete hp hr hheads i
  have hs := ComparisonTupleReification.shaped generated hh
  exact ⟨generated.term, hg, hs.1, hs.2, ht.definedUnder hd,
    ComparisonTupleReification.supports generated P Q hP hQ⟩

theorem projectElimination_substitute (allowed : List ModVar) (solution : Elimination flex) (v : Nat) :
    (projectElimination allowed solution).substitute v =
      if v ∈ flex then projectExpression allowed (solution.substitute v) else .atom v := by
  cases hi : ConcreteBackend.atomFin flex v with
  | none =>
    have hn : v ∉ flex := by
      intro hv
      obtain ⟨i, he⟩ := HornPropagation.atomFin_exists hv
      simp [hi] at he
    simp [Elimination.substitute, projectElimination, hi, hn]
  | some i =>
    have hv : v ∈ flex := by
      rw [← ConcreteBackend.atomFin_lookup hi]
      exact List.getElem_mem i.isLt
    simp [Elimination.substitute, projectElimination, hi, hv, Vector.get]

theorem projectElimination_atoms {allowed : List ModVar} {solution : Elimination flex} {v w : Nat}
    (h : w ∈ ((projectElimination allowed solution).substitute v).atoms) :
    w ∈ (solution.substitute v).atoms := by
  rw [projectElimination_substitute] at h
  by_cases hv : v ∈ flex
  · exact (projectExpression_atoms (by simpa [hv] using h)).1
  · have hn : ConcreteBackend.atomFin flex v = none := by
      cases hi : ConcreteBackend.atomFin flex v with
      | none => rfl
      | some i => exact False.elim (hv (by rw [← ConcreteBackend.atomFin_lookup hi]; exact List.getElem_mem i.isLt))
    simpa [hv, Elimination.substitute, hn] using h

theorem projectElimination_flexible {allowed : List ModVar} {solution : Elimination flex}
    {v : Nat} (hv : v ∈ flex) (world : Nat → Bool) :
    ((projectElimination allowed solution).substitute v).eval world =
      (solution.substitute v).eval (projectWorld allowed world) := by
  simp [projectElimination_substitute, hv]

theorem projectElimination_allowed {allowed : List ModVar} {solution : Elimination flex}
    {v : Nat} (hv : atomVariable v ∈ allowed) (world : Nat → Bool) :
    ((projectElimination allowed solution).substitute v).eval world =
      (solution.substitute v).eval (projectWorld allowed world) := by
  by_cases hf : v ∈ flex
  · exact projectElimination_flexible hf world
  · have hn : ConcreteBackend.atomFin flex v = none := by
      cases hi : ConcreteBackend.atomFin flex v with
      | none => rfl
      | some i => exact False.elim (hf (by rw [← ConcreteBackend.atomFin_lookup hi]; exact List.getElem_mem i.isLt))
    simp [Elimination.substitute, hn, BoolExpr.eval, projectWorld, hv]

end ModalityInference.ComparisonJointAssemblyReification
