import ModalityInference.Proofs.SolverFlexible

/-! Whole-type assumptions need not expose their component constraints. -/
namespace ModalityInference.PrincipalAmbient

def variableHead : Ty → Bool
  | .var _ => true
  | .modal a _ => variableHead a
  | _ => false

theorem subtype_variableHead {Δ a b} (h : Subtype Δ a b)
    (hΔ : ∀ x y, Constraint.sub x y ∈ Δ → variableHead x = variableHead y) :
    variableHead a = variableHead b := by
  induction h
  all_goals first | rfl | exact hΔ _ _ ‹_› | exact Eq.trans ‹_› ‹_› | exact ‹_›

def bounds : Bounds :=
  [.sub (.prod (.var (.flex 0)) .unit) (.prod .unit .unit)]

theorem flexible : bounds.Flexible := by
  simp [bounds, Constraint.Flexible, TypeExpr.Flexible]

theorem not_residual : ¬ Residual bounds := by
  simp [Residual, bounds, TypeExpr.outer]

theorem succeeds : ∃ result, solve 50 bounds = .success result ∧
    result.substitution.type (.flex 0) = .modal .unit (.var (.flex 0)) :=
  ⟨_, rfl, rfl⟩

theorem no_variable_unit (m : ModExpr) :
    ¬ Subtype bounds (.var (.flex 0)) (.modal .unit m) :=
  fun h => Bool.noConfusion (subtype_variableHead h (by simp [bounds, variableHead]))

theorem symbolic_solution : Solution bounds bounds {} := by
  change EntailsAll bounds bounds
  simp only [EntailsAll, bounds, List.mem_singleton, forall_eq, Entails,
    TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, List.nil_append, ModeModels,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact .bound (List.mem_singleton_self _)

theorem no_type_factorization {σ : Substitution}
    (hσ : σ.type (.flex 0) = .modal .unit (.var (.flex 0))) :
    ¬ ∃ τ : Substitution, Subtype bounds (.var (.flex 0)) (τ.ty (σ.type (.flex 0))) := by
  rintro ⟨τ, hτ⟩
  exact no_variable_unit _ (by simpa [hσ, Substitution.ty, TypeExpr.subst] using hτ)

theorem satisfiable : BoundsSatisfiable bounds := by
  refine ⟨{types := [(0, .unit)]}, rfl, rfl, ?_⟩
  change EntailsAll [] [.sub (.prod .unit .unit) (.prod .unit .unit)]
  simpa [EntailsAll, Entails, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]
    using (Subtype.refl (Δ := []) (a := .prod .unit .unit))

/-- The former solver principality obligation, with unrestricted ambient bounds. -/
def UnrestrictedPrincipality : Prop :=
  ∀ {fuel cs result Δ θ}, solve fuel cs = .success result → Solution cs Δ θ →
    ∃ τ : Substitution, EntailsAll Δ (τ.bounds result.bounds) ∧
      (∀ v ∈ cs.typeVars,
        Subtype Δ (θ.type v) (τ.ty (result.substitution.type v)) ∧
        Subtype Δ (τ.ty (result.substitution.type v)) (θ.type v)) ∧
      (∀ v ∈ cs.modVars,
        Submode Δ (θ.mode v) ((result.substitution.mode v).subst τ.mode) ∧
        Submode Δ ((result.substitution.mode v).subst τ.mode) (θ.mode v))

theorem no_unrestricted_principality : ¬ UnrestrictedPrincipality := by
  intro hp
  obtain ⟨result, hs, hr⟩ := succeeds
  obtain ⟨τ, _, ht, _⟩ := hp hs symbolic_solution
  exact no_type_factorization hr ⟨τ, (ht (.flex 0) (by decide)).1⟩

end ModalityInference.PrincipalAmbient
