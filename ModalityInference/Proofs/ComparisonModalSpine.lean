import ModalityInference.ComparisonModalSpine
import ModalityInference.Proofs.ComparisonPartialModes

namespace ModalityInference.ComparisonModalSpine

theorem factor_support {base target : Ty} {ms : List ModExpr}
    (h : factor base target = some ms) :
    ∀ m ∈ ms, m.vars ⊆ target.modVars := by
  induction target generalizing ms with
  | modal a n ih =>
    simp only [factor] at h
    split at h
    · cases h; simp
    · cases hf : factor base a with
      | none => simp [hf] at h
      | some rest =>
        simp only [hf, Option.map_some, Option.some.injEq] at h
        subst ms
        intro m hm v hv
        rcases List.mem_cons.mp hm with rfl | hm
        · exact Finset.mem_union_right _ hv
        · exact Finset.mem_union_left _ (ih hf m hm hv)
  | _ =>
    simp only [factor] at h
    split at h
    · cases h; simp
    · contradiction

theorem factor_recompose_support {base target : Ty} {ms : List ModExpr}
    (h : factor base target = some ms) :
    (ComparisonPartialModes.recompose ms).vars ⊆ target.modVars :=
  ComparisonPartialModes.recompose_support ms (factor_support h)

theorem factor_spec {base target : Ty} {ms : List ModExpr}
    (h : factor base target = some ms) : act ms base = target := by
  induction target generalizing ms with
  | modal a n ih =>
    simp only [factor] at h
    split at h
    · next he =>
      cases h
      exact (beq_iff_eq.mp he).symm
    · cases hf : factor base a with
      | none => simp [hf] at h
      | some rest =>
        simp only [hf, Option.map_some, Option.some.injEq] at h
        subst ms
        exact congrArg (fun t : Ty => (TypeExpr.modal t n : Ty)) (ih hf)
  | _ =>
    simp only [factor] at h
    split at h
    · next he =>
      cases h
      exact (beq_iff_eq.mp he).symm
    · contradiction

end ModalityInference.ComparisonModalSpine
