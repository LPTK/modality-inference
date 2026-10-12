import ModalityInference.Proofs.ResourceDefinitions

/-! Split contexts using the actual free-variable sets and preserve disjointness
when each component additionally owns fresh resources from its own branch. -/
namespace ModalityInference

theorem ResourceEnvironmentInterpretation.restrict_used {ρ w γ reserved U V} {Γ : Context}
    (h : ResourceEnvironmentInterpretation ρ w (Γ.restrict U) γ reserved) (hsub : V ⊆ U) :
    ResourceEnvironmentInterpretation ρ w (Γ.restrict V) γ reserved :=
  h.of_lookup fun _ _ hi => let ⟨hu, he⟩ := Context.restrict_present.mp hi
    Context.restrict_present.mpr ⟨hsub hu, he⟩

theorem ContextResources.restrict_mono (Γ : Context) (reserved : Nat → Resources)
    {U V : Finset Nat} (hsub : V ⊆ U) :
    ContextResources (Γ.restrict V) reserved ⊆ ContextResources (Γ.restrict U) reserved :=
  ContextResources.of_lookup _ fun _ _ hi => let ⟨hu, he⟩ := Context.restrict_present.mp hi
    Context.restrict_present.mpr ⟨hsub hu, he⟩

theorem ContextJoin.resource_used {ρ w Γ Γ₁ Γ₂ γ Δ reserved X Y}
    (hΔ : GroundModels ρ Δ) (h : ContextJoin Δ Γ₁ Γ₂ Γ)
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ.restrict (X ∪ Y)) γ reserved) :
    ∃ left right,
      ResourceEnvironmentInterpretation ρ w (Γ₁.restrict X) γ left ∧
      ResourceEnvironmentInterpretation ρ w (Γ₂.restrict Y) γ right ∧
      ContextResources (Γ₁.restrict X) left ⊆ ContextResources (Γ.restrict (X ∪ Y)) reserved ∧
      ContextResources (Γ₂.restrict Y) right ⊆ ContextResources (Γ.restrict (X ∪ Y)) reserved ∧
      Disjoint (ContextResources (Γ₁.restrict X) left) (ContextResources (Γ₂.restrict Y) right) := by
  obtain ⟨left, right, hleft, hright, hl, hr, hd⟩ := (h.restrict (X ∪ Y)).resource_semantics hΔ hγ
  have hsl := ContextResources.restrict_mono Γ₁ left (Finset.subset_union_left (s₁ := X) (s₂ := Y))
  have hsr := ContextResources.restrict_mono Γ₂ right (Finset.subset_union_right (s₁ := X) (s₂ := Y))
  exact ⟨left, right, hleft.restrict_used Finset.subset_union_left,
    hright.restrict_used Finset.subset_union_right, hsl.trans hl, hsr.trans hr,
    hd.mono hsl hsr⟩

theorem World.Compatible.separate_branches {w : World} {s γ}
    (hs : w.Compatible s γ) {left right first second : Resources} {k i j : Nat}
    (hleft : ∀ l ∈ left, EnvironmentReferences γ l)
    (hright : ∀ l ∈ right, EnvironmentReferences γ l) (hd : Disjoint left right)
    (hi : i < k) (hj : j < k) (hij : i ≠ j)
    (hf : first ⊆ left ∪ {l | (s.branch k i).FreshLocation l})
    (hg : second ⊆ right ∪ {l | (s.branch k j).FreshLocation l}) :
    Disjoint first second := by
  apply Set.disjoint_left.mpr
  intro l hl hr
  rcases hf hl with hl | hl <;> rcases hg hr with hr | hr
  · exact Set.disjoint_left.mp hd hl hr
  · exact hs.2.2.2 l (hleft l hl) (Supplies.fresh_branch hr)
  · exact hs.2.2.2 l (hright l hr) (Supplies.fresh_branch hl)
  · exact Set.disjoint_left.mp (s.fresh_branch_disjoint hs.1 hi hj hij) hl hr

end ModalityInference
