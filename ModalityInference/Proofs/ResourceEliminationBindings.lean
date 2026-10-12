import ModalityInference.Proofs.ResourceRegions

/-! Extending an interpreted environment with split's credit and two fields.
The restriction accounts for all three binders without changing their indices. -/
namespace ModalityInference

/-- The reserves of the credit, first field, second field, and original context. -/
def splitReserves (r₀ r₁ r₂ : Resources) (tail : Nat → Resources) : Nat → Resources :=
  fun
  | 0 => r₀
  | i + 1 => match i with
    | 0 => r₁
    | j + 1 => match j with
      | 0 => r₂
      | k + 1 => tail k

theorem Context.split_restrict_lookup (body : AnnotatedTerm) (Γ : Context)
    (s₀ s₁ s₂ : Scheme) (i : Nat) (s : Scheme)
    (hi : (Context.restrict (some s₀ :: some s₁ :: some s₂ :: Γ) body.freeVars)[i]? = some (some s)) :
    (some s₀ :: some s₁ :: some s₂ :: Γ.restrict (body.freeVars 3))[i]? = some (some s) := by
  obtain ⟨hu, he⟩ := Context.restrict_present.mp hi
  rcases i with _ | (_ | (_ | i))
  · exact he
  · exact he
  · exact he
  · apply Context.restrict_present.mpr
    exact ⟨(body.mem_freeVars_add 0 3 i).mpr (by simpa [Nat.add_assoc] using hu), he⟩

theorem ResourceEnvironmentInterpretation.split_used {Γ : Context} {ρ w γ tail s₀ s₁ s₂ v₀ v₁ v₂ r₀ r₁ r₂}
    (body : AnnotatedTerm)
    (h₀ : ResourceSchemeInterpretation ρ w s₀ v₀ r₀)
    (h₁ : ResourceSchemeInterpretation ρ w s₁ v₁ r₁)
    (h₂ : ResourceSchemeInterpretation ρ w s₂ v₂ r₂)
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ.restrict (body.freeVars 3)) γ tail)
    (h₀₁ : Disjoint r₀ r₁) (h₀₂ : Disjoint r₀ r₂) (h₁₂ : Disjoint r₁ r₂)
    (hd : Disjoint (r₀ ∪ r₁ ∪ r₂) (ContextResources (Γ.restrict (body.freeVars 3)) tail)) :
    ResourceEnvironmentInterpretation ρ w
      (Context.restrict (some s₀ :: some s₁ :: some s₂ :: Γ) body.freeVars) (v₀ :: v₁ :: v₂ :: γ)
      (splitReserves r₀ r₁ r₂ tail) := by
  simp only [Set.disjoint_union_left] at hd
  have htwo := hγ.cons h₂ hd.2
  have hone := htwo.cons h₁ (by
    simpa only [ContextResources.cons] using Set.disjoint_union_right.mpr ⟨h₁₂, hd.1.2⟩)
  have hzero := hone.cons h₀ (by
    simpa only [ContextResources.cons] using
      Set.disjoint_union_right.mpr ⟨h₀₁, Set.disjoint_union_right.mpr ⟨h₀₂, hd.1.1⟩⟩)
  exact hzero.of_lookup (Context.split_restrict_lookup body Γ s₀ s₁ s₂)

theorem ContextResources.split_used_subset (body : AnnotatedTerm) (Γ : Context)
    (s₀ s₁ s₂ : Scheme) (r₀ r₁ r₂ : Resources) (tail : Nat → Resources) :
    ContextResources (Context.restrict (some s₀ :: some s₁ :: some s₂ :: Γ) body.freeVars)
      (splitReserves r₀ r₁ r₂ tail) ⊆
    (r₀ ∪ r₁ ∪ r₂) ∪ ContextResources (Γ.restrict (body.freeVars 3)) tail := by
  rintro l ⟨i, s, hi, hl⟩
  have hi' := Context.split_restrict_lookup body Γ s₀ s₁ s₂ i s hi
  rcases i with _ | (_ | (_ | i))
  · exact Or.inl (Or.inl (Or.inl hl))
  · exact Or.inl (Or.inl (Or.inr hl))
  · exact Or.inl (Or.inr hl)
  · exact Or.inr ⟨i, s, hi', hl⟩

end ModalityInference
