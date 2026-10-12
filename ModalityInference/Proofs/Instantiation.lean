import ModalityInference.Proofs.Annotations
import ModalityInference.Declarative
import ModalityInference.Semantics

/-! Explicit scheme/value instantiation and its runtime-erasure contract. -/
namespace ModalityInference

theorem TypeExpr.wellFormedBounds_spec (ρ : GroundAssignment) (t : Ty) :
    ModeModels t.wellFormedBounds ρ.modes ↔ (t.realize ρ).isSome = true := by
  induction t <;>
    simp_all [TypeExpr.wellFormedBounds, ModeModels, ModeSatisfies,
      List.mem_append, or_imp, forall_and, TypeExpr.realize]
  all_goals simp [Option.isSome_bind, Option.any_eq_true, Option.isSome_iff_exists,
    ModExpr.WellFormed]

theorem instantiationGuards_spec (ρ : GroundAssignment) (types : List Ty)
    (modes : List ModExpr) :
    ModeModels (instantiationGuards types modes) ρ.modes ↔
      (∀ t ∈ types, (t.realize ρ).isSome = true) ∧
      (∀ m ∈ modes, m.WellFormed ρ.modes) := by
  simp only [← TypeExpr.wellFormedBounds_spec]
  simp [instantiationGuards, ModeModels, List.mem_append, or_imp, forall_and,
    ModeSatisfies]
  exact fun _ => ⟨fun h t ht c hc => h c t ht hc, fun h c t ht hc => h t ht c hc⟩

theorem SchemeValue.instantiate_spec {p : SchemeValue} {types modes r}
    (h : p.instantiate types modes = .success r) :
    Instantiates p.scheme r.substitution ∧
      r.bounds = r.substitution.bounds p.scheme.bounds ++ instantiationGuards types modes ∧
      r.type = r.substitution.ty p.scheme.body ∧
      r.value = p.value.substCapturedTypes r.substitution := by
  simp only [SchemeValue.instantiate] at h
  split at h <;> simp [bind, pure, RunResult.bind] at h
  split at h <;> simp at h
  cases h
  simp_all [Instantiates, List.map_fst_zip]

theorem SchemeValue.instantiate_erasure {p : SchemeValue} {types modes r}
    (h : p.instantiate types modes = .success r) : ValueErasure p.value r.value := by
  rw [(SchemeValue.instantiate_spec h).2.2.2]
  exact p.value.substCapturedTypes_erasure _

end ModalityInference
