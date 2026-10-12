import ModalityInference.Proofs.ResourceEliminationBindings

/-! Resource-safe product and sum elimination with the original usage routing. -/
namespace ModalityInference

theorem Typing.resource_split {Δ t u a b m} {c : Ty} {Γ Γ₁ Γ₂ : Context}
    (ht : Typing Δ Γ₁ t (.modal (.prod a b) m))
    (hj : ContextJoin Δ Γ₁ Γ₂ Γ) {ρ} (hΔ : GroundModels ρ Δ)
    (iht : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w (Γ₁.restrict t.freeVars) γ reserved →
      (TypeExpr.modal (.prod a b) m).realize ρ = some ground →
      ResourceSemanticEvaluation w γ t ground (ContextResources (Γ₁.restrict t.freeVars) reserved))
    (ihu : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w
        (Context.restrict (some (Scheme.mono (.modal .credit m)) ::
          some (Scheme.mono (.modal a m)) :: some (Scheme.mono (.modal b m)) :: Γ₂) u.freeVars)
        γ reserved →
      c.realize ρ = some ground →
      ResourceSemanticEvaluation w γ u ground (ContextResources
        (Context.restrict (some (Scheme.mono (.modal .credit m)) ::
          some (Scheme.mono (.modal a m)) :: some (Scheme.mono (.modal b m)) :: Γ₂) u.freeVars) reserved))
    {w γ reserved ground}
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ.restrict (Term.split t u).freeVars) γ reserved)
    (ha : c.realize ρ = some ground) :
    ResourceSemanticEvaluation w γ (.split t u) ground
      (ContextResources (Γ.restrict (Term.split t u).freeVars) reserved) := by
  have hdefined := ht.realize_defined hΔ
  cases ha' : a.realize ρ <;> cases hb' : b.realize ρ <;>
    cases hm' : m.eval (some ∘ ρ.modes) <;>
    simp [TypeExpr.realize, ha', hb', hm'] at hdefined
  rename_i firstTy secondTy n
  obtain ⟨left, right, hleft, hright, hl, hr, hd⟩ :=
    hj.resource_used (X := t.freeVars) (Y := u.freeVars 3) hΔ hγ
  intro supplies hsup
  obtain ⟨v, owned, he, hv, ho⟩ := iht (ground := .prod firstTy secondTy n) hleft
    (by simp [TypeExpr.realize, ha', hb', hm', GroundTy.modal])
    (supplies.branch 2 0) (hsup.branch (by decide) 0)
  have hsep := hsup.separate_branches (j := 1) hleft.references hright.references hd
    (by decide) (by decide) (by decide) ho (fun _ h => Or.inl h)
  cases v <;> simp only [ResourceInterpretation, GroundTy.mode, Mode.compose_identity, and_false] at hv
  rename_i l x y
  obtain ⟨first, second, hx, hy, hcx, hcy, hxy, rfl⟩ := hv.2.2.2
  have hcredit : ResourceSchemeInterpretation ρ w (Scheme.mono (.modal .credit m))
      (.credit l) (cellResources n l) :=
    .mono (by simp [TypeExpr.realize, hm', GroundTy.modal])
      (.credit (hv.1 _ .pairCell) hv.2.2.1)
  have hfirst : ResourceSchemeInterpretation ρ w (Scheme.mono (.modal a m)) x first :=
    .mono (ground := firstTy.modal n) (by simp [TypeExpr.realize, ha', hm'])
      (ResourceInterpretation.modal_iff.mpr (by simpa using hx))
  have hsecond : ResourceSchemeInterpretation ρ w (Scheme.mono (.modal b m)) y second :=
    .mono (ground := secondTy.modal n) (by simp [TypeExpr.realize, hb', hm'])
      (ResourceInterpretation.modal_iff.mpr (by simpa using hy))
  have henv := ResourceEnvironmentInterpretation.split_used u
    hcredit hfirst hsecond hright hcx hcy hxy hsep
  have hnot := he.not_fresh_branch (j := 1) hsup (by decide) (by decide) (by decide)
  have hcompatible : w.Compatible (supplies.branch 2 1) (.credit l :: x :: y :: γ) :=
    (((hsup.branch (by decide) 1).cons (fun k hk => hnot k (.pairRight hk))).cons
      (fun k hk => hnot k (.pairLeft hk))).cons
        (fun k hk => by cases hk; exact hnot _ .pairCell)
  obtain ⟨result, resources, heres, hri, hres⟩ := ihu henv ha _ hcompatible
  refine ⟨result, resources, .split he heres, hri, ?_⟩
  exact hres.trans (Set.union_subset
    ((ContextResources.split_used_subset u Γ₂ _ _ _ _ _ _ _).trans
      (Set.union_subset
        (ho.trans (Set.union_subset_union hl (fun _ h => Supplies.fresh_branch h)))
        (fun _ h => Or.inl (hr h))))
    (fun _ h => Or.inr (Supplies.fresh_branch h)))

theorem Typing.resource_case {Δ t u v a b m} {c : Ty} {Γ Γ₁ Γ₂ : Context}
    (ht : Typing Δ Γ₁ t (.modal (.sum a b) m))
    (hj : ContextJoin Δ Γ₁ Γ₂ Γ) {ρ} (hΔ : GroundModels ρ Δ)
    (iht : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w (Γ₁.restrict t.freeVars) γ reserved →
      (TypeExpr.modal (.sum a b) m).realize ρ = some ground →
      ResourceSemanticEvaluation w γ t ground (ContextResources (Γ₁.restrict t.freeVars) reserved))
    (ihu : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w
        (Context.restrict (some (Scheme.mono (.modal a m)) :: Γ₂) u.freeVars) γ reserved →
      c.realize ρ = some ground →
      ResourceSemanticEvaluation w γ u ground (ContextResources
        (Context.restrict (some (Scheme.mono (.modal a m)) :: Γ₂) u.freeVars) reserved))
    (ihv : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w
        (Context.restrict (some (Scheme.mono (.modal b m)) :: Γ₂) v.freeVars) γ reserved →
      c.realize ρ = some ground →
      ResourceSemanticEvaluation w γ v ground (ContextResources
        (Context.restrict (some (Scheme.mono (.modal b m)) :: Γ₂) v.freeVars) reserved))
    {w γ reserved ground}
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ.restrict (Term.case t u v).freeVars) γ reserved)
    (ha : c.realize ρ = some ground) :
    ResourceSemanticEvaluation w γ (.case t u v) ground
      (ContextResources (Γ.restrict (Term.case t u v).freeVars) reserved) := by
  have hdefined := ht.realize_defined hΔ
  cases ha' : a.realize ρ <;> cases hb' : b.realize ρ <;>
    cases hm' : m.eval (some ∘ ρ.modes) <;>
    simp [TypeExpr.realize, ha', hb', hm'] at hdefined
  rename_i firstTy secondTy n
  simp only [Term.freeVars, Finset.union_assoc] at hγ ⊢
  obtain ⟨left, right, hleft, hright, hl, hr, hd⟩ :=
    hj.resource_used (X := t.freeVars) (Y := u.freeVars 1 ∪ v.freeVars 1) hΔ hγ
  intro supplies hsup
  obtain ⟨scrut, owned, he, hscrut, ho⟩ := iht (ground := .sum firstTy secondTy n) hleft
    (by simp [TypeExpr.realize, ha', hb', hm', GroundTy.modal])
    (supplies.branch 3 0) (hsup.branch (by decide) 0)
  have hsep := hsup.separate_branches (j := 1) hleft.references hright.references hd
    (by decide) (by decide) (by decide) ho (fun _ h => Or.inl h)
  cases scrut <;> simp only [ResourceInterpretation, GroundTy.mode, Mode.compose_identity, and_false] at hscrut
  case inl x =>
    have hsub := ContextResources.restrict_mono Γ₂ right
      (Finset.subset_union_left (s₁ := u.freeVars 1) (s₂ := v.freeVars 1))
    have hpayload : ResourceSchemeInterpretation ρ w (Scheme.mono (.modal a m)) x owned :=
      .mono (ground := firstTy.modal n) (by simp [TypeExpr.realize, ha', hm'])
        (ResourceInterpretation.modal_iff.mpr (by simpa using hscrut.2.2))
    have henv := ResourceEnvironmentInterpretation.cons_used u hpayload
      (hright.restrict_used Finset.subset_union_left) (hsep.mono Set.Subset.rfl hsub)
    have hnot := he.not_fresh_branch (j := 1) hsup (by decide) (by decide) (by decide)
    obtain ⟨result, resources, heres, hri, hres⟩ := ihu henv ha _
      ((hsup.branch (by decide) 1).cons (fun l hl => hnot l (.inl hl)))
    refine ⟨result, resources, .caseLeft he heres, hri, ?_⟩
    exact hres.trans (Set.union_subset
      ((ContextResources.cons_used_subset u Γ₂ _ owned right).trans
        (Set.union_subset
          (ho.trans (Set.union_subset_union hl (fun _ h => Supplies.fresh_branch h)))
          (fun _ h => Or.inl (hr (hsub h)))))
      (fun _ h => Or.inr (Supplies.fresh_branch h)))
  case inr x =>
    have hsub := ContextResources.restrict_mono Γ₂ right
      (Finset.subset_union_right (s₁ := u.freeVars 1) (s₂ := v.freeVars 1))
    have hpayload : ResourceSchemeInterpretation ρ w (Scheme.mono (.modal b m)) x owned :=
      .mono (ground := secondTy.modal n) (by simp [TypeExpr.realize, hb', hm'])
        (ResourceInterpretation.modal_iff.mpr (by simpa using hscrut.2.2))
    have henv := ResourceEnvironmentInterpretation.cons_used v hpayload
      (hright.restrict_used Finset.subset_union_right) (hsep.mono Set.Subset.rfl hsub)
    have hnot := he.not_fresh_branch (j := 2) hsup (by decide) (by decide) (by decide)
    obtain ⟨result, resources, heres, hri, hres⟩ := ihv henv ha _
      ((hsup.branch (by decide) 2).cons (fun l hl => hnot l (.inr hl)))
    refine ⟨result, resources, .caseRight he heres, hri, ?_⟩
    exact hres.trans (Set.union_subset
      ((ContextResources.cons_used_subset v Γ₂ _ owned right).trans
        (Set.union_subset
          (ho.trans (Set.union_subset_union hl (fun _ h => Supplies.fresh_branch h)))
          (fun _ h => Or.inl (hr (hsub h)))))
      (fun _ h => Or.inr (Supplies.fresh_branch h)))

end ModalityInference
