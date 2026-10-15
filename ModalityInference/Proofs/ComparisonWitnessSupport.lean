import ModalityInference.Proofs.ComparisonModeRestriction
import ModalityInference.Proofs.ComparisonTypeRestriction

/-! Public comparison intervals admit witnesses whose type and modality names
come from their declared assumptions and endpoints. This restricts identifiers
without imposing definedness on the interval or its witness. -/

namespace ModalityInference.ComparisonWitnessSupport

theorem restrict_interval {Δ : Bounds} {a b : Ty} {w : CompareTy}
    (hal : AlgebraSubtype Δ (.ofTy a) w) (hru : AlgebraSubtype Δ w (.ofTy b)) :
    let types := Δ.typeVars ∪ a.typeVars ∪ b.typeVars
    let modes := Δ.modVars ∪ a.modVars ∪ b.modVars
    let c := (w.subst CompareTy.var (ComparisonModeRestriction.restrict modes)).subst
      (ComparisonTypeRestriction.restrict types) ModExpr.var
    AlgebraSubtype Δ (.ofTy a) c ∧ AlgebraSubtype Δ c (.ofTy b) ∧
      ComparisonInterpolation.Supports (fun v => v ∈ types) (fun v => v ∈ modes) c := by
  dsimp only
  have hm := ComparisonModeRestriction.restrict_interval hal hru
  have ht := ComparisonTypeRestriction.restrict_interval hm.1 hm.2.1
  exact ⟨ht.1, ht.2.1, ComparisonTypeRestriction.restrict_support _ hm.2.2⟩

theorem interval_supported {Δ : Bounds} {a b : Ty} {w : CompareTy}
    (hal : AlgebraSubtype Δ (.ofTy a) w) (hru : AlgebraSubtype Δ w (.ofTy b)) :
    ∃ c, AlgebraSubtype Δ (.ofTy a) c ∧ AlgebraSubtype Δ c (.ofTy b) ∧
      ComparisonInterpolation.Supports
        (fun v => v ∈ Δ.typeVars ∪ a.typeVars ∪ b.typeVars)
        (fun v => v ∈ Δ.modVars ∪ a.modVars ∪ b.modVars) c :=
  ⟨_, restrict_interval hal hru⟩

end ModalityInference.ComparisonWitnessSupport
