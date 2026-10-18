import ModalityInference.ComparisonSelectedBases
import ModalityInference.Proofs.ComparisonShapeSelectors
import ModalityInference.Proofs.ComparisonSelectedRealizer

/-! The prepared finite branch family retains exact shared-selector shapes,
computable input-name support, and the corresponding structural bases. -/

namespace ModalityInference.ComparisonSelectedBases

open ComparisonShapeSelectors ComparisonShapeRetraction ComparisonControls

@[simp] theorem mem_inputNames (p : SchemePreparation.Prepared) (v : TypeVar) :
    v∈inputNames p ↔ v∈ComparisonWitnessRestriction.inputTypes p := by
  simp only [inputNames, List.mem_dedup, List.mem_append,
    TypeExpr.mem_typeVariables, Bounds.mem_typeVariables,
    ComparisonWitnessRestriction.inputTypes, Finset.mem_union]

@[simp] theorem mem_inputModes (p : SchemePreparation.Prepared) (v : ModVar) :
    v∈inputModes p ↔ v∈ComparisonWitnessRestriction.inputModes p := by
  simp only [inputModes, List.mem_dedup, List.mem_append,
    TypeExpr.mem_modeVariables, Bounds.mem_modeVariables,
    ComparisonWitnessRestriction.inputModes, Finset.mem_union]

theorem layout_scope {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {v : TypeVar} (hv : v∈inputNames p)
    {w : TypeVar} (hw : w∈(solved.resolveAll v).vars) :
    w∈(layout first p solved).parameters := by
  exact ofTemplates_scope
    (List.mem_map.mpr ⟨v, input_mem_anchorNames p solved ((mem_inputNames p v).mp hv), rfl⟩) hw

theorem layout_encode {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {ρ : TypeVar → ComparisonShape}
    (hρ : ∀v, ρ v∈shapeChoices p solved) :
    (layout first p solved).theory.eval ((layout first p solved).encode ρ)=true :=
  Layout.theory_encode (fun v _ => hρ v)

theorem bases_origin {layout : Layout} {names : List TypeVar} {modes : List ModVar}
    {fixed : TypeVar → ComparisonShape} {s : ComparisonShape} {branch : Branch}
    (h : branch∈bases layout names modes fixed s) :
    ∃raw∈layout.branches s, branch.shape=raw.shape.subst fixed ∧ branch.guard=raw.guard ∧
      ComparisonStructuralBasis.basis names modes fixed branch.shape = some branch.basis := by
  obtain ⟨raw, hr, hout⟩ := List.mem_filterMap.mp h
  cases hb : ComparisonStructuralBasis.basis names modes fixed (raw.shape.subst fixed) with
  | none => simp [hb] at hout
  | some b =>
    simp only [hb, Option.map_some, Option.some.injEq] at hout
    subst branch
    exact ⟨raw, hr, rfl, rfl, hb⟩

theorem bases_insert {layout : Layout} {names : List TypeVar} {modes : List ModVar}
    {fixed : TypeVar → ComparisonShape} {s : ComparisonShape}
    {raw : ComparisonShapeSelectors.Branch} (hr : raw∈layout.branches s) {b : Basis}
    (hb : ComparisonStructuralBasis.basis names modes fixed (raw.shape.subst fixed)=some b) :
    ({shape := raw.shape.subst fixed, guard := raw.guard, basis := b} : Branch)∈
      bases layout names modes fixed s := by
  exact List.mem_filterMap.mpr ⟨raw, hr, by simp only [hb, Option.map_some]⟩

theorem bases_sound {layout : Layout} {world : Nat → Bool}
    (h : layout.theory.eval world=true) {names : List TypeVar} {modes : List ModVar}
    {fixed : TypeVar → ComparisonShape} {s : ComparisonShape}
    (hscope : ∀v∈s.vars, v∈layout.parameters) {branch : Branch}
    (hb : branch∈bases layout names modes fixed s) (hg : branch.guard.eval world=true) :
    branch.shape=(s.subst (layout.decode world)).subst fixed ∧
      ComparisonStructuralBasis.basis names modes fixed branch.shape=some branch.basis := by
  obtain ⟨raw, hr, hs, he, hb⟩ := bases_origin hb
  refine ⟨?_, hb⟩
  rw [hs, (Layout.branches_decoded h s hscope).1 raw hr (he ▸ hg)]

theorem bases_encoded_complete {layout : Layout} {ρ : TypeVar → ComparisonShape}
    (hρ : ∀v∈layout.parameters, ρ v∈layout.choices) {names : List TypeVar} {modes : List ModVar}
    {fixed : TypeVar → ComparisonShape} {s : ComparisonShape}
    (hscope : ∀v∈s.vars, v∈layout.parameters) {b : Basis}
    (hb : ComparisonStructuralBasis.basis names modes fixed ((s.subst ρ).subst fixed)=some b) :
    ∃branch∈bases layout names modes fixed s,
      branch.guard.eval (layout.encode ρ)=true ∧
      branch.shape=(s.subst ρ).subst fixed ∧ branch.basis=b := by
  obtain ⟨raw, hr, hg, hs⟩ := (Layout.branches_encoded hρ s hscope).2
  refine ⟨_, bases_insert hr (by simpa only [hs] using hb), hg, ?_, rfl⟩
  exact congrArg (ComparisonShape.subst fixed) hs

theorem bases_enabled_unique {layout : Layout} {world : Nat → Bool}
    (h : layout.theory.eval world=true) {names : List TypeVar} {modes : List ModVar}
    {fixed : TypeVar → ComparisonShape} {s : ComparisonShape}
    (hscope : ∀v∈s.vars, v∈layout.parameters) {a b : Branch}
    (ha : a∈bases layout names modes fixed s) (hb : b∈bases layout names modes fixed s)
    (hga : a.guard.eval world=true) (hgb : b.guard.eval world=true) :
    a.shape=b.shape ∧ a.basis=b.basis := by
  obtain ⟨hsa, hba⟩ := bases_sound h hscope ha hga
  obtain ⟨hsb, hbb⟩ := bases_sound h hscope hb hgb
  have he := hsa.trans hsb.symm
  exact ⟨he, Option.some.inj (hba.symm.trans ((congrArg
    (ComparisonStructuralBasis.basis names modes fixed) he).trans hbb))⟩

theorem bases_atoms {layout : Layout} {names : List TypeVar} {modes : List ModVar}
    {fixed : TypeVar → ComparisonShape} {s : ComparisonShape}
    (hscope : ∀v∈s.vars, v∈layout.parameters) {branch : Branch}
    (hb : branch∈bases layout names modes fixed s) :
    ∀n∈branch.guard.atoms, layout.first≤n ∧ n<layout.next := by
  obtain ⟨raw, hr, _, he, _⟩ := bases_origin hb
  rw [he]
  exact layout.branches_atoms s hscope raw hr

theorem prepared_sound {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool}
    (h : (layout first p solved).theory.eval world=true) {v : TypeVar}
    (hv : v∈inputNames p) {branch : Branch} (hb : branch∈prepared first p solved v)
    (hg : branch.guard.eval world=true) :
    branch.shape=((solved.resolveAll v).subst ((layout first p solved).decode world)).subst solved.fixedShapes ∧
      ComparisonStructuralBasis.basis (inputNames p) (inputModes p) solved.fixedShapes branch.shape=
        some branch.basis :=
  bases_sound h (fun _ => layout_scope hv) hb hg

theorem prepared_encoded_complete {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {ρ : TypeVar → ComparisonShape}
    (hρ : ∀v, ρ v∈shapeChoices p solved) {v : TypeVar} (hv : v∈inputNames p) {b : Basis}
    (hb : ComparisonStructuralBasis.basis (inputNames p) (inputModes p) solved.fixedShapes
      (((solved.resolveAll v).subst ρ).subst solved.fixedShapes)=some b) :
    ∃branch∈prepared first p solved v,
      branch.guard.eval ((layout first p solved).encode ρ)=true ∧
      branch.shape=((solved.resolveAll v).subst ρ).subst solved.fixedShapes ∧ branch.basis=b :=
  bases_encoded_complete (fun v _ => hρ v) (fun _ => layout_scope hv) hb

theorem prepared_atoms {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {v : TypeVar} (hv : v∈inputNames p)
    {branch : Branch} (hb : branch∈prepared first p solved v) :
    ∀n∈branch.guard.atoms, first≤n ∧ n<(layout first p solved).next :=
  bases_atoms (fun _ => layout_scope hv) hb

end ModalityInference.ComparisonSelectedBases
