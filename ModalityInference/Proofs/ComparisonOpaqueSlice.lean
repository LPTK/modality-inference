import ModalityInference.Proofs.ComparisonOpaqueGrammar
import ModalityInference.Proofs.ComparisonOpaqueObserver

namespace ModalityInference.ComparisonOpaqueObserver

open ComparisonControls ComparisonInterpolation

/-- Fix the modality environment while leaving all rigid type generators free. -/
def freeze (η : ModVar → Mode) (a : CompareTy) : CompareTy :=
  a.subst CompareTy.var (ModExpr.const ∘ η)

@[simp] theorem complete_constants (η θ : ModVar → Mode) (m : ModExpr) :
    (m.subst (ModExpr.const ∘ η)).complete θ = m.complete η := by
  induction m <;> simp_all [ModExpr.subst, ModExpr.complete, Function.comp_def]

@[simp] theorem freeze_shape (η : ModVar → Mode) (a : CompareTy) :
    (freeze η a).shape = a.shape := by
  induction a <;> simp_all [freeze, CompareTy.subst, CompareTy.shape]

theorem freeze_wellShaped {Δ : Bounds} {a : CompareTy} (ha : a.WellShaped Δ)
    (η : ModVar → Mode) : (freeze η a).WellShaped Δ :=
  (a.wellShaped_subst_modes_iff _).mpr ha

theorem freeze_support (η : ModVar → Mode) (a : CompareTy)
    (modes : ModVar → Prop) : Supports (fun _ => True) modes (freeze η a) := by
  induction a <;> simp_all only [freeze, CompareTy.subst, Supports, true_and]
  case modal a m ih =>
    exact ModExpr.support_subst m (ModExpr.const ∘ η) (fun _ _ w hw => by
      simp only [Function.comp_apply, ModExpr.vars, Finset.notMem_empty] at hw)

@[simp] theorem freeze_value (c : Coordinate) (η θ : ModVar → Mode)
    (heads : TypeVar → Bool) (a : CompareTy) :
    value c θ heads (freeze η a) = value c η heads a := by
  induction a <;> simp_all [freeze, CompareTy.subst, value, complete_constants]

theorem freeze_defined {a : CompareTy} {η : ModVar → Mode}
    (hd : ModeModels a.wellFormedBounds η) (θ : ModVar → Mode) :
    ModeModels (freeze η a).wellFormedBounds θ := by
  induction a <;> simp only [CompareTy.wellFormedBounds, ModeModels, List.mem_append,
    or_imp, forall_and, List.mem_singleton, forall_eq, ModeSatisfies] at hd
  all_goals simp only [freeze, CompareTy.subst, CompareTy.wellFormedBounds, ModeModels,
    List.mem_append, or_imp, forall_and, List.mem_singleton, forall_eq, ModeSatisfies]
  case modal a m ih =>
    exact ⟨ih hd.1, by simpa [ModExpr.WellFormed, ModExpr.eval_subst, ModExpr.eval,
      Function.comp_def] using hd.2⟩
  case prod a b iha ihb | sum a b iha ihb | fn a b iha ihb |
      join a b iha ihb | meet a b iha ihb => exact ⟨iha hd.1, ihb hd.2⟩
  all_goals simp

theorem modalWith_value (c : Coordinate) (modeAtom : Nat → Nat) (σ : Nat → Bool)
    (e : BoolExpr) (m : ModExpr) (hm : m.WellFormed (projectedModes (σ ∘ modeAtom))) :
    (c.modalWith modeAtom e m).eval σ =
      applyMode c (e.eval σ) (m.complete (projectedModes (σ ∘ modeAtom))) := by
  have hg := (m.project_defined (σ ∘ modeAtom)).mpr hm
  have he := m.project_correct (σ ∘ modeAtom)
  rw [Projection.eval, hg] at he
  have hc := ModExpr.complete_of_eval he.symm
  rw [hc]
  cases c <;> simp [Coordinate.modalWith, SymbolicCNF.substitute_eval, BoolExpr.eval,
    applyMode, Function.comp_def]

theorem generated_formula_value {b : Basis} (e : ComparisonControls.Generated b)
    (headAtom modeAtom : Nat → Nat) (c : Coordinate) (σ : Nat → Bool)
    (heads : TypeVar → Bool)
    (hh : ∀a∈b.heads, value c (projectedModes (σ ∘ modeAtom)) heads a =
      σ (headAtom (b.heads.idxOf a)))
    (hd : ModeModels e.term.wellFormedBounds (projectedModes (σ ∘ modeAtom))) :
    (e.formula headAtom modeAtom c).eval σ =
      value c (projectedModes (σ ∘ modeAtom)) heads e.term := by
  induction e with
  | head a ha => exact (hh a ha).symm
  | join a d iha ihd | meet a d iha ihd =>
    have hp : ModeModels a.term.wellFormedBounds (projectedModes (σ ∘ modeAtom)) ∧
        ModeModels d.term.wellFormedBounds (projectedModes (σ ∘ modeAtom)) := by
      simpa only [ComparisonControls.Generated.term, CompareTy.wellFormedBounds, ModeModels,
        List.mem_append, or_imp, forall_and] using hd
    simp only [ComparisonControls.Generated.formula, ComparisonControls.Generated.term, value, BoolExpr.eval, iha hp.1, ihd hp.2]
  | modal a m hm ih =>
    have hp : ModeModels a.term.wellFormedBounds (projectedModes (σ ∘ modeAtom)) ∧
        m.WellFormed (projectedModes (σ ∘ modeAtom)) := by
      simpa only [ComparisonControls.Generated.term, CompareTy.wellFormedBounds, ModeModels,
        List.mem_append, or_imp, forall_and, List.mem_singleton, forall_eq,
        ModeSatisfies] using hd
    simp only [ComparisonControls.Generated.formula, ComparisonControls.Generated.term, value, modalWith_value _ _ _ _ _ hp.2, ih hp.1]

/-- At any fixed modality environment, every well-shaped opaque image admits
an exact finite-head generated expression. Its labels have no free mode names. -/
theorem frozen_generated_of_shape {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (hφ : ComparisonShape.Models Δ φ) {s : TypeVar} {b : Basis} {a : CompareTy}
    (hs : a.WellShaped Δ) (ha : a.shape.subst φ = .var s)
    (hh : ∀v, φ v = .var s → .var v ∈ b.heads) (η : ModVar → Mode) :
    ∃e : ComparisonControls.Generated b, e.term = freeze η a :=
  generated_of_shape hφ (freeze_wellShaped hs η) (by simpa using ha) hh
    (freeze_support η a _)

/-- A fixed-mode slice of an arbitrary collected opaque image is represented by
one positive polynomial over the executable basis. No support restriction is
imposed on the original witness's modality expressions. -/
theorem collected_slice_representable {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    (hshape : ComparisonShapeSolver.prepare fuel p = .success (.solved shapes))
    (h : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hscope : ∀v∈p.assumptions.typeVars, ComparisonShapeSolver.sourceAllowed p v = false)
    (hfresh : ∀leaf∈templates.leaves,
      ∀v∈p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    {g : ComparisonGroups.Group} (hg : g ∈ groups) {first : TypeVar} {rest : List TypeVar}
    (hheads : g.heads = first :: rest) {a : CompareTy}
    (hs : a.WellShaped p.assumptions)
    (ha : ComparisonShape.Equivalent p.assumptions a.shape (.var g.shapeClass))
    (η : ModVar → Mode) :
    let basis := ComparisonElimination.groupBasis p.assumptions reduced.modes g first rest
    ∃e : ComparisonControls.Generated basis, e.term = freeze η a ∧
      ∃clauses, Polynomial basis clauses ∧
      ∀basisAtom headAtom modeAtom coordinate σ,
        (basis.theoryAt basisAtom headAtom modeAtom coordinate).eval σ = true →
        (CNFHolds (σ ∘ basisAtom) clauses ↔
          (e.formula headAtom modeAtom coordinate).eval σ = true) := by
  obtain ⟨e, he⟩ := ComparisonGroups.collect_generated hshape h hscope hfresh hg hheads
    (freeze_wellShaped hs η) (by simpa using ha) (freeze_support η a _)
  exact ⟨e, he, e.representable⟩

/-- The polynomial represents the original image on the chosen mode slice,
for every Boolean assignment to its opaque heads and every coordinate kind. -/
theorem collected_slice_polynomial {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    (hshape : ComparisonShapeSolver.prepare fuel p = .success (.solved shapes))
    (h : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hscope : ∀v∈p.assumptions.typeVars, ComparisonShapeSolver.sourceAllowed p v = false)
    (hfresh : ∀leaf∈templates.leaves,
      ∀v∈p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    {g : ComparisonGroups.Group} (hg : g ∈ groups) {first : TypeVar} {rest : List TypeVar}
    (hheads : g.heads = first :: rest) {a : CompareTy}
    (hs : a.WellShaped p.assumptions)
    (ha : ComparisonShape.Equivalent p.assumptions a.shape (.var g.shapeClass))
    (η : ModVar → Mode) (hd : ModeModels a.wellFormedBounds η) :
    let basis := ComparisonElimination.groupBasis p.assumptions reduced.modes g first rest
    ∃clauses, Polynomial basis clauses ∧
      ∀basisAtom headAtom modeAtom coordinate σ,
        (basis.theoryAt basisAtom headAtom modeAtom coordinate).eval σ = true →
        (CNFHolds (σ ∘ basisAtom) clauses ↔
          value coordinate η (fun v => σ (headAtom (basis.heads.idxOf (.var v)))) a = true) := by
  obtain ⟨e, he, clauses, hp, hclauses⟩ :=
    collected_slice_representable hshape h hscope hfresh hg hheads hs ha η
  refine ⟨clauses, hp, ?_⟩
  intro basisAtom headAtom modeAtom coordinate σ ht
  rw [hclauses _ _ _ _ _ ht]
  have hh := generated_formula_value e headAtom modeAtom coordinate σ
    (fun v => σ (headAtom ((ComparisonElimination.groupBasis
      p.assumptions reduced.modes g first rest).heads.idxOf (.var v))))
    (by
      intro t hm
      change t ∈ CompareTy.var first :: rest.map CompareTy.var at hm
      rcases List.mem_cons.mp hm with rfl | hm
      · rfl
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
        rfl)
    (by rw [he]; exact freeze_defined hd _)
  simpa only [he, freeze_value] using (congrArg (· = true) hh).to_iff

end ModalityInference.ComparisonOpaqueObserver
