import ModalityInference.Proofs.ResourceProducts

/-! Reuse consumes a unique credit, preserves its locality constraint, and
separates the reused cell from both fields using all three context components. -/
namespace ModalityInference

theorem Typing.resource_reuse {Δ t u v a b m k} {Γ Γ₁ Γ₂ Γ₃ Γ₂₃ : Context}
    (h23 : ContextJoin Δ Γ₂ Γ₃ Γ₂₃) (h1 : ContextJoin Δ Γ₁ Γ₂₃ Γ)
    (hunique : Submode Δ k (.const Mode.uniqueOnly))
    (hkm : Submode Δ (.compose k (.const Mode.many)) m) {ρ} (hΔ : GroundModels ρ Δ)
    (iht : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w (Γ₁.restrict t.freeVars) γ reserved →
      (TypeExpr.modal .credit k).realize ρ = some ground →
      ResourceSemanticEvaluation w γ t ground (ContextResources (Γ₁.restrict t.freeVars) reserved))
    (ihu : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w (Γ₂.restrict u.freeVars) γ reserved →
      (TypeExpr.modal a m).realize ρ = some ground →
      ResourceSemanticEvaluation w γ u ground (ContextResources (Γ₂.restrict u.freeVars) reserved))
    (ihv : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w (Γ₃.restrict v.freeVars) γ reserved →
      (TypeExpr.modal b m).realize ρ = some ground →
      ResourceSemanticEvaluation w γ v ground (ContextResources (Γ₃.restrict v.freeVars) reserved))
    {w γ reserved ground}
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ.restrict (Term.reuse t u v).freeVars) γ reserved)
    (ha : (TypeExpr.modal (.prod a b) m).realize ρ = some ground) :
    ResourceSemanticEvaluation w γ (.reuse t u v) ground
      (ContextResources (Γ.restrict (Term.reuse t u v).freeVars) reserved) := by
  cases ha' : a.realize ρ <;> cases hb' : b.realize ρ <;>
    cases hm' : m.eval (some ∘ ρ.modes) <;>
    simp [TypeExpr.realize, ha', hb', hm', GroundTy.modal] at ha
  rename_i firstTy secondTy q
  subst ground
  obtain ⟨p, _, hk', he, hpu⟩ := hunique.denote hΔ.modeModels
  simp only [ModExpr.eval, Option.some.injEq] at he
  subst_vars
  have hp : p.unique = true := ((Mode.le_iff _ _).mp hpu).2.2 rfl
  have hpq : (p.compose Mode.many).le q = true := by
    have hh := hkm.denote hΔ.modeModels
    simpa [ModExpr.Below, ModExpr.eval, hk', hm'] using hh
  simp only [Term.freeVars, Finset.union_assoc] at hγ ⊢
  obtain ⟨creditR, fieldsR, hcredit, hfields, hc, hf, hd⟩ :=
    h1.resource_used (X := t.freeVars) (Y := u.freeVars ∪ v.freeVars) hΔ hγ
  obtain ⟨left, right, hleft, hright, hl, hr, hdfields⟩ := h23.resource_used hΔ hfields
  intro supplies hsup
  obtain ⟨vc, rc, hec, hvc, hrc⟩ := iht (ground := .credit p) hcredit
    (by simp [TypeExpr.realize, hk', GroundTy.modal])
    (supplies.branch 3 0) (hsup.branch (by decide) 0)
  obtain ⟨x, first, hex, hx, hfirst⟩ := ihu (ground := firstTy.modal q) hleft
    (by simp [TypeExpr.realize, ha', hm'])
    (supplies.branch 3 1) (hsup.branch (by decide) 1)
  obtain ⟨y, second, hey, hy, hsecond⟩ := ihv (ground := secondTy.modal q) hright
    (by simp [TypeExpr.realize, hb', hm'])
    (supplies.branch 3 2) (hsup.branch (by decide) 2)
  cases vc <;> simp only [ResourceInterpretation, GroundTy.mode, Mode.compose_identity, and_false] at hvc
  rename_i l
  have hcell : cellResources q l ⊆ rc := by
    rw [hvc.2.2.2]
    exact cellResources_mono (fun _ => hp) l
  have hcx := (hsup.separate_branches hcredit.references hleft.references
    (hd.mono Set.Subset.rfl hl) (by decide) (by decide) (by decide) hrc hfirst).mono
      hcell Set.Subset.rfl
  have hcy := (hsup.separate_branches hcredit.references hright.references
    (hd.mono Set.Subset.rfl hr) (by decide) (by decide) (by decide) hrc hsecond).mono
      hcell Set.Subset.rfl
  have hxy := hsup.separate_branches hleft.references hright.references hdfields
    (by decide) (by decide) (by decide) hfirst hsecond
  have hlocal : q.isLocal = true ∨ HeapLocation l :=
    hvc.2.2.1.imp (fun he => ((Mode.le_iff _ _).mp hpq).1
      (by simpa [Mode.compose, Mode.many] using he)) id
  refine ⟨_, _, .reuse hec hex hey,
    ResourceInterpretation.pair (hvc.1 _ .credit) hlocal
      (by simpa using ResourceInterpretation.modal_iff.mp hx)
      (by simpa using ResourceInterpretation.modal_iff.mp hy) hcx hcy hxy, ?_⟩
  exact Set.union_subset
    (Set.union_subset
      (hcell.trans (hrc.trans (Set.union_subset_union hc (fun _ h => Supplies.fresh_branch h))))
      (hfirst.trans (Set.union_subset_union (hl.trans hf) (fun _ h => Supplies.fresh_branch h))))
    (hsecond.trans (Set.union_subset_union (hr.trans hf) (fun _ h => Supplies.fresh_branch h)))

end ModalityInference
