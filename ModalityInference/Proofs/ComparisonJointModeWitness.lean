import ModalityInference.Proofs.ComparisonJointModes
import ModalityInference.Proofs.SchemeModeSynthesis

/-! Finite modality substitutions for the joint selector solution. The returned
source action preserves its exact domain and satisfies both component clauses
under the original shared selector assignment. -/
namespace ModalityInference.ComparisonJointModes

open ModalSynthesis

/-- Flexible images contain only coordinates present in their original component. -/
theorem image_atoms_origin {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    {σ : Nat → Bool} {v w : Nat} (hv : v ∈ flex)
    (h : w ∈ (image side (prepare side flex locality other) σ v).atoms) :
    2 * w ∈ CNFPropagation.atoms (if side v then locality else other) := by
  obtain ⟨u, hu, hw⟩ := SymbolicCNF.substitute_atoms h
  rw [prepare_part] at hu
  have hup : 2 * v ∈ pivots side (side v) flex := mem_pivots.mpr ⟨hv, rfl⟩
  have hua := (SymbolicCNF.solve_atoms hup hu).1
  have hus : selector u = false := by
    cases hs : selector u with
    | false => rfl
    | true => simp [decode, hs, BoolExpr.atoms] at hw
  have hwu : w = u / 2 := by simpa [decode, hus, BoolExpr.atoms] using hw
  have hu : u = 2 * w := by
    simp only [selector, beq_eq_false_iff_ne] at hus
    omega
  exact hu ▸ hua

theorem witness_atoms_origin {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    {σ : Nat → Bool} {v w : Nat} (hv : v ∈ flex)
    (h : w ∈ ((witness side flex (prepare side flex locality other) σ).substitute v).atoms) :
    2 * w ∈ CNFPropagation.atoms (if side v then locality else other) := by
  rw [witness_substitute] at h
  exact image_atoms_origin hv h

theorem reify_excludes {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    (hl : ComponentSupported side true locality) (ho : ComponentSupported side false other)
    {σ : Nat → Bool} {v : Nat} (hv : v ∈ flex) {axis m}
    (hr : SymbolicModes.reify axis
      ((witness side flex (prepare side flex locality other) σ).substitute v) = some m)
    {w : ModVar} (hw : ∀ a < 3, w.atomIndex a ∈ flex) : w ∉ m.vars := by
  intro hm
  obtain ⟨i, hi, he⟩ := SymbolicModes.reify_variables hr w hm
  apply (witness_atoms hl ho hi).2 hv
  have ha := hw (i % 3) (Nat.mod_lt _ (by decide))
  rwa [← he, SymbolicSchemeModes.atomVariable_reencode] at ha

/-- Reified images cannot mention any eliminated source modality. -/
theorem mode_excludes {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    (hl : ComponentSupported side true locality) (ho : ComponentSupported side false other)
    {σ : Nat → Bool} {v m}
    (hm : (witness side flex (prepare side flex locality other) σ).mode v = some m)
    (hv : ∀ a < 3, v.atomIndex a ∈ flex) {w : ModVar}
    (hw : ∀ a < 3, w.atomIndex a ∈ flex) : w ∉ m.vars := by
  let result := witness side flex (prepare side flex locality other) σ
  change result.mode v = some m at hm
  cases hlocal : SymbolicModes.reify .locality (result.substitute (v.atomIndex 0)) <;>
    cases ha : SymbolicModes.reify .affinity (result.substitute (v.atomIndex 1)) <;>
    cases hu : SymbolicModes.reify .uniqueness (result.substitute (v.atomIndex 2)) <;>
    simp [SymbolicModes.Elimination.mode, hlocal, ha, hu] at hm
  cases hm
  simp only [ModExpr.vars, Finset.mem_union, not_or]
  exact ⟨reify_excludes hl ho (hv 0 (by decide)) hlocal hw,
    reify_excludes hl ho (hv 1 (by decide)) ha hw,
    reify_excludes hl ho (hv 2 (by decide)) hu hw⟩

theorem assemble_excludes {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    (hl : ComponentSupported side true locality) (ho : ComponentSupported side false other)
    {σ : Nat → Bool} {parameters action key v}
    (ha : SymbolicSchemeModes.assemble
      (witness side flex (prepare side flex locality other) σ) parameters = some action)
    (hv : parameters.lookup key = some v)
    (hcoords : ∀ a < 3, v.atomIndex a ∈ flex) {w : ModVar}
    (hw : ∀ a < 3, w.atomIndex a ∈ flex) : w ∉ (action.mode (.flex key)).vars :=
  mode_excludes hl ho (SymbolicSchemeModes.assemble_action ha hv) hcoords hw

/-- Assembly has exactly the requested source-mode domain and no type entries. -/
theorem assemble_domain {modeIds : List Nat} {locality other : CNF}
    {σ : Nat → Bool} {action}
    (ha : SymbolicSchemeModes.assemble
      (witness ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds)
        (prepare ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds) locality other) σ)
      (SchemeModeSynthesis.parameters modeIds) = some action) :
    action.types = [] ∧ action.modes.map Prod.fst = modeIds := by
  have hd := SymbolicSchemeModes.assemble_domain ha
  exact ⟨hd.1, by simpa [SchemeModeSynthesis.parameters, List.map_map, Function.comp_def] using hd.2⟩

/-- The actual finite mode substitution satisfies both scalar components at
all interpretations, using the same constant selector solution as the type side. -/
theorem assemble_actual {modeIds : List Nat} {localPart other : CNF}
    (hl : ComponentSupported locality true localPart) (ho : ComponentSupported locality false other)
    {σ : Nat → Bool} {action}
    (hq : CNFHolds σ
      (prepare locality (SchemeModeSynthesis.atoms modeIds) localPart other).query)
    (ha : SymbolicSchemeModes.assemble
      (witness locality (SchemeModeSynthesis.atoms modeIds)
        (prepare locality (SchemeModeSynthesis.atoms modeIds) localPart other) σ)
      (SchemeModeSynthesis.parameters modeIds) = some action)
    (η : ModVar → Mode) :
    ∃ τ : ModVar → Mode,
      (∀ v, (action.mode v).eval (some ∘ η) = some (τ v)) ∧
      CNFHolds (encode σ (encodeModes τ)) localPart ∧
      CNFHolds (encode σ (encodeModes τ)) other := by
  let images := witness locality (SchemeModeSynthesis.atoms modeIds)
    (prepare locality (SchemeModeSynthesis.atoms modeIds) localPart other) σ
  refine ⟨projectedModes (fun i => (images.substitute i).eval (encodeModes η)),
    SchemeModeSynthesis.assemble_eval ha η, ?_⟩
  rw [SchemeModeSynthesis.encodeModes_projectedModes]
  exact witness_sound hl ho hq (encodeModes η)

/-- A satisfying selector assignment always has a finite, globally total mode
action realizing both components with exactly the required source domain. -/
theorem query_finite_witness {modeIds : List Nat} {localPart other : CNF}
    (hl : ComponentSupported locality true localPart) (ho : ComponentSupported locality false other)
    {σ : Nat → Bool}
    (hq : CNFHolds σ
      (prepare locality (SchemeModeSynthesis.atoms modeIds) localPart other).query) :
    ∃ action : Substitution,
      action.types = [] ∧ action.modes.map Prod.fst = modeIds ∧
      (∀ η v, (action.mode v).WellFormed η) ∧
      ∀ η, ∃ τ : ModVar → Mode,
        (∀ v, (action.mode v).eval (some ∘ η) = some (τ v)) ∧
        CNFHolds (encode σ (encodeModes τ)) localPart ∧
        CNFHolds (encode σ (encodeModes τ)) other := by
  obtain ⟨action, ha⟩ := witness_assembles (flex := SchemeModeSynthesis.atoms modeIds)
    hl ho σ (SchemeModeSynthesis.parameters modeIds)
  have hd := assemble_domain ha
  exact ⟨action, hd.1, hd.2, SymbolicSchemeModes.assemble_wellFormed ha,
    assemble_actual hl ho hq ha⟩

end ModalityInference.ComparisonJointModes
