import ModalityInference.Proofs.SolverShape

/-! Successful finite-shape checking produces a shape model. -/
namespace ModalityInference
namespace SolverShape

def PairModels (ρ : TypeVar → Ty) (ps : List (Ty × Ty)) : Prop :=
  ∀ a b, (a, b) ∈ ps → a.shapeUnder ρ = b.shapeUnder ρ

@[simp] theorem pairModels_cons {ρ a b ps} :
    PairModels ρ ((a, b) :: ps) ↔ a.shapeUnder ρ = b.shapeUnder ρ ∧ PairModels ρ ps := by
  simp [PairModels, or_imp, forall_and]

theorem pairModels_replace {ρ : TypeVar → Ty} {v t ps}
    (hv : v ∉ t.typeVars)
    (h : PairModels ρ (ps.map fun (a, b) =>
      (a.subst (ShapePairs.replace v t) ModExpr.var, b.subst (ShapePairs.replace v t) ModExpr.var))) :
    ∃ η, PairModels η ((.var v, t) :: ps) := by
  let η := fun w => (ShapePairs.replace v t w).shapeUnder ρ
  refine ⟨η, pairModels_cons.mpr ⟨?_, ?_⟩⟩
  · have ht : t.shapeUnder η = t.shapeUnder ρ := by
      apply t.shapeUnder_congr
      intro w hw
      have hne : w ≠ v := fun he => hv (he ▸ hw)
      simp [η, ShapePairs.replace, hne, TypeExpr.shapeUnder]
    rw [ht]
    simp [TypeExpr.shapeUnder, η, ShapePairs.replace]
  · intro a b hab
    simpa only [TypeExpr.shapeUnder_subst] using h _ _ (List.mem_map_of_mem hab)

theorem checkShapePairs_model {fuel ps} (h : checkShapePairs fuel ps = .success ()) :
    ∃ ρ, PairModels ρ ps := by
  induction fuel generalizing ps with
  | zero => cases h
  | succ fuel ih =>
    cases ps with
    | nil => exact ⟨fun _ => .unit, by simp [PairModels]⟩
    | cons p ps =>
      obtain ⟨a, b⟩ := p
      simp only [checkShapePairs] at h
      split at h
      · obtain rfl : a = b := by simpa only [beq_iff_eq] using ‹(a == b) = true›
        obtain ⟨ρ, hρ⟩ := ih h
        exact ⟨ρ, pairModels_cons.mpr ⟨rfl, hρ⟩⟩
      · repeat' split at h
        all_goals try cases h
        case h_1.isFalse =>
          rename_i x y v hne hocc
          obtain ⟨ρ, hρ⟩ := ih h
          exact pairModels_replace (by simpa using hocc) hρ
        case h_2.isFalse =>
          rename_i x y v hnv hne hocc
          obtain ⟨ρ, hρ⟩ := ih h
          obtain ⟨η, hη⟩ := pairModels_replace (by simpa using hocc) hρ
          exact ⟨η, pairModels_cons.mpr ⟨(pairModels_cons.mp hη).1.symm, (pairModels_cons.mp hη).2⟩⟩
        all_goals obtain ⟨ρ, hρ⟩ := ih h
        all_goals simp only [pairModels_cons] at hρ ⊢
        all_goals exact ⟨ρ, by simp [TypeExpr.shapeUnder, hρ]⟩

theorem checkShapes_model {fuel cs} (h : checkShapes fuel cs = .success ()) :
    ∃ ρ, Models ρ cs := by
  obtain ⟨ρ, hρ⟩ := checkShapePairs_model h
  refine ⟨ρ, fun c hc => ?_⟩
  cases c
  case mode | defined => trivial
  case sub a b | equiv a b =>
    have hh := hρ a.eraseModes b.eraseModes (List.mem_filterMap.mpr ⟨_, hc, rfl⟩)
    simpa only [TypeExpr.shapeUnder_eraseModes] using hh
  case equal v a =>
    have hh := hρ (.var v) a.eraseModes (List.mem_filterMap.mpr ⟨_, hc, rfl⟩)
    simpa only [TypeExpr.shapeUnder_eraseModes, TypeExpr.shapeUnder] using hh

end SolverShape
end ModalityInference
