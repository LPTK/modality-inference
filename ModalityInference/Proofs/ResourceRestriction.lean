import ModalityInference.Proofs.TypingScope
import ModalityInference.Proofs.ResourceWorlds

/-! Restricting usage and trimming unused runtime captures preserve the same
resource evidence for every retained binding. -/
namespace ModalityInference

@[simp] theorem Context.restrict_present {Γ : Context} {used : Finset Nat} {i : Nat} {s : Scheme} :
    (Γ.restrict used)[i]? = some (some s) ↔ i ∈ used ∧ Γ[i]? = some (some s) := by
  simp only [Context.restrict, List.getElem?_mapIdx]
  cases Γ[i]? <;> split_ifs <;> simp_all

theorem trimEnvironment_lookup {γ : Environment} {used : Finset Nat} {i : Nat} {v : Value}
    (h : γ[i]? = some v) (hi : i ∈ used) : (trimEnvironment γ used)[i]? = some v := by
  simp [trimEnvironment, List.getElem?_mapIdx, h, hi]

theorem ResourceEnvironmentInterpretation.restrict {ρ w Γ γ reserved}
    (h : ResourceEnvironmentInterpretation ρ w Γ γ reserved) (used : Finset Nat) :
    ResourceEnvironmentInterpretation ρ w (Γ.restrict used) γ reserved :=
  ⟨fun i s hi => h.1 i s (Context.restrict_present.mp hi).2,
   fun i j s t hij hi hj => h.2 i j s t hij
      (Context.restrict_present.mp hi).2 (Context.restrict_present.mp hj).2⟩

theorem ResourceEnvironmentInterpretation.trim {ρ w γ reserved used} {Γ : Context}
    (h : ResourceEnvironmentInterpretation ρ w (Γ.restrict used) γ reserved) :
    ResourceEnvironmentInterpretation ρ w (Γ.restrict used) (trimEnvironment γ used) reserved :=
  ⟨fun i s hi =>
    let ⟨v, hv, hs⟩ := h.1 i s hi
    ⟨v, trimEnvironment_lookup hv (Context.restrict_present.mp hi).1, hs⟩,
   h.2⟩

theorem ContextResources.restrict_subset (Γ : Context) (used : Finset Nat)
    (reserved : Nat → Resources) :
    ContextResources (Γ.restrict used) reserved ⊆ ContextResources Γ reserved :=
  fun _ ⟨i, s, hi, hl⟩ => ⟨i, s, (Context.restrict_present.mp hi).2, hl⟩

end ModalityInference
