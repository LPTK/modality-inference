import ModalityInference.Proofs.ResourceSplitting

/-! The application step of the fundamental theorem. Three disjoint allocation
branches separate the function, argument, and call; no typed reference is lost. -/
namespace ModalityInference

theorem Typing.resource_app {Δ f x a b} {Γ Γ₁ Γ₂ : Context}
    (hx : Typing Δ Γ₂ x a) (hj : ContextJoin Δ Γ₁ Γ₂ Γ) {ρ} (hΔ : GroundModels ρ Δ)
    (ihf : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w (Γ₁.restrict f.freeVars) γ reserved →
      (TypeExpr.fn a b).realize ρ = some ground →
      ResourceSemanticEvaluation w γ f ground (ContextResources (Γ₁.restrict f.freeVars) reserved))
    (ihx : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w (Γ₂.restrict x.freeVars) γ reserved →
      a.realize ρ = some ground →
      ResourceSemanticEvaluation w γ x ground (ContextResources (Γ₂.restrict x.freeVars) reserved))
    {w γ reserved ground}
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ.restrict (Term.app f x).freeVars) γ reserved)
    (ha : b.realize ρ = some ground) :
    ResourceSemanticEvaluation w γ (.app f x) ground
      (ContextResources (Γ.restrict (Term.app f x).freeVars) reserved) := by
  obtain ⟨domain, hdomain⟩ := Option.isSome_iff_exists.mp (hx.realize_defined hΔ)
  have hfn : (TypeExpr.fn a b).realize ρ = some (.fn domain ground Mode.identity) := by
    simp [TypeExpr.realize, hdomain, ha]
  obtain ⟨left, right, hleft, hright, hl, hr, hd⟩ := hj.resource_used
    (X := f.freeVars) (Y := x.freeVars) hΔ hγ
  intro supplies hsup
  obtain ⟨vf, rf, hef, hvf, hrf⟩ := ihf hleft hfn
    (supplies.branch 3 0) (hsup.branch (by decide) 0)
  obtain ⟨vx, rx, hex, hvx, hrx⟩ := ihx hright hdomain
    (supplies.branch 3 1) (hsup.branch (by decide) 1)
  have hsep := hsup.separate_branches hleft.references hright.references hd
    (by decide) (by decide) (by decide) hrf hrx
  cases vf <;> simp only [ResourceInterpretation, GroundTy.mode, Mode.compose_identity, and_false] at hvf
  rename_i δ captured body
  have hδ : w.Compatible (supplies.branch 3 2) δ :=
    (((hsup.branch (by decide) 2).empty).cons
      (hef.not_fresh_branch (j := 2) hsup (by decide) (by decide) (by decide))).of_references
        (fun l he => ⟨.closure δ captured body, by simp, References.closure_iff.mpr he⟩)
  obtain ⟨result, resources, hebody, hri, hres⟩ := hvf.2.2.2.2 w vx rx
    (fun v hv l hl => hvf.1 l (.closure hv hl)) hvx hsep (supplies.branch 3 2)
    (hδ.cons (hex.not_fresh_branch hsup (by decide) (by decide) (by decide)))
  exact ⟨result, resources, .app hef hex hebody, hri,
    hres.trans (Set.union_subset
      (Set.union_subset
        (hrf.trans (Set.union_subset_union hl (fun _ h => Supplies.fresh_branch h)))
        (hrx.trans (Set.union_subset_union hr (fun _ h => Supplies.fresh_branch h))))
      (fun _ h => Or.inr (Supplies.fresh_branch h)))⟩

end ModalityInference
