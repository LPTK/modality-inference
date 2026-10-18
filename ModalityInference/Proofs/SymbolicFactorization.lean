import ModalityInference.Proofs.SymbolicSteps

namespace ModalityInference.SymbolicSolver

structure Witness (scope : Scope) (s : SolverState) (Δ : Bounds)
    (θ τ : Substitution) : Prop where
  wellFormed : τ.WellFormedUnder Δ
  models : Models Δ τ s
  types : ∀v ∈ scope.types, (τ.ty (s.substitution.type v)).DefinedUnder Δ ∧
    TypeEquivalent Δ (θ.type v) (τ.ty (s.substitution.type v))
  modes : ∀v ∈ scope.modes,
    Submode Δ (θ.mode v) ((s.substitution.mode v).subst τ.mode) ∧
    Submode Δ ((s.substitution.mode v).subst τ.mode) (θ.mode v)

def Factors (scope : Scope) (s : SolverState) (Δ : Bounds) (θ : Substitution) : Prop :=
  ∃τ, Witness scope s Δ θ τ

theorem Witness.same_substitution {scope s t Δ θ τ} (h : Witness scope s Δ θ τ)
    (he : t.substitution = s.substitution) (hm : Models Δ τ t) : Witness scope t Δ θ τ :=
  ⟨h.wellFormed, hm, he ▸ h.types, he ▸ h.modes⟩

theorem initial {scope cs Δ θ nt nm} (hθ : θ.WellFormedUnder Δ)
    (hcs : Solution cs Δ θ) :
    Factors scope {pending := cs, nextType := nt, nextMode := nm} Δ θ := by
  refine ⟨θ, hθ, ?_, ?_, ?_⟩
  · intro c hc
    exact hcs _ (List.mem_map.mpr ⟨c, by simpa using hc, rfl⟩)
  · intro v _
    have hv : ({} : Substitution).type v = .var v := by cases v <;> rfl
    change (θ.ty (({} : Substitution).type v)).DefinedUnder Δ ∧ _
    rw [hv]
    simpa [Substitution.ty, TypeExpr.subst, Substitution.type] using
      (show (θ.type v).DefinedUnder Δ ∧ TypeEquivalent Δ (θ.type v) (θ.type v)
        from ⟨hθ.types v, .refl, .refl⟩)
  · intro v _
    cases v <;> exact ⟨.refl (hθ.modes _), .refl (hθ.modes _)⟩

theorem stepType_factors {scope θ Δ s a b t} (hΔ : Residual Δ) (hs : s.Fresh)
    (ha : a.Bounded s.nextType s.nextMode) (hb : b.Bounded s.nextType s.nextMode)
    (hscope : scope.Bounded s.nextType s.nextMode) (he : stepType s a b = .success t)
    (hm : Factors scope {s with pending := .sub a b :: s.pending} Δ θ) :
    Factors scope t Δ θ := by
  obtain ⟨σ, hw⟩ := hm
  have hc := hw.models (.sub a b) (by simp)
  have hbase : Models Δ σ s := fun c hc => hw.models c (List.mem_cons_of_mem _ hc)
  obtain ⟨τ, hτ, hm, hagree⟩ := stepType_models hΔ hs hw.wellFormed ha hb hbase hc he
  refine ⟨τ, hτ, hm, ?_, ?_⟩
  · intro v hv
    rw [stepType_substitution he, hagree.ty (hs.substitution.type v (hscope.1 v hv))]
    exact hw.types v hv
  · intro v hv
    rw [stepType_substitution he, hagree.mode (hs.substitution.mode v (hscope.2 v hv))]
    exact hw.modes v hv

theorem stepMode_factors {scope θ Δ s a b t} (hΔ : Residual Δ)
    (he : stepMode s a b = .success t)
    (hm : Factors scope {s with pending := .mode a b :: s.pending} Δ θ) :
    Factors scope t Δ θ := by
  obtain ⟨σ, hw⟩ := hm
  have hc := hw.models (.mode a b) (by simp)
  have hbase : Models Δ σ s := fun c hc => hw.models c (List.mem_cons_of_mem _ hc)
  exact ⟨σ, hw.same_substitution
    (show t.substitution = s.substitution from stepMode_substitution he)
    (stepMode_models hΔ hbase hc he)⟩

theorem singleType_modes (σ : Substitution) (n : Nat) (a : Ty) :
    (σ.compose ({types := [(n, a)]} : Substitution)).mode = σ.mode := by
  funext v
  rw [Substitution.mode_compose]
  cases v <;> rfl

theorem singleType_solution {cs Δ : Bounds} {σ : Substitution} {n : Nat} {a : Ty}
    (hw : σ.WellFormedUnder Δ) (he : Entails Δ (σ.constraint (.equal (.flex n) a)))
    (hs : Solution cs Δ σ) :
    Solution (({types := [(n, a)]} : Substitution).bounds (cs ++ a.wellFormedBounds)) Δ σ := by
  let one : Substitution := {types := [(n, a)]}
  let τ := σ.compose one
  have ha : (σ.ty a).DefinedUnder Δ := ((σ.constraint_subst_entails _ Δ).mp he).2.2.2
  have ht : τ.WellFormedUnder Δ := singleType_wellFormed hw ha
  have hm : τ.mode = σ.mode := singleType_modes σ n a
  have hs' : Solution cs Δ τ := solution_equivalent ht (singleType_equivalent he) hm.symm hs
  have ha' : (τ.ty a).DefinedUnder Δ := by
    change (a.subst τ.type τ.mode).DefinedUnder Δ
    rw [hm]
    exact type_subst_defined a ht.types ha
  change EntailsAll Δ (σ.bounds (one.bounds (cs ++ a.wellFormedBounds)))
  rw [Substitution.bounds_compose]
  exact Solution.append.mpr ⟨hs', ha'.subst_guards⟩

theorem substitute_factors {scope θ Δ n a} {s : SolverState}
    (hk : n ∉ s.substitution.types.map Prod.fst)
    (hm : Factors scope {s with pending := .equal (.flex n) a :: s.pending} Δ θ) :
    Factors scope
      {pending := ({types := [(n, a)]} : Substitution).bounds
          (s.pending ++ s.bounds ++ a.wellFormedBounds)
       bounds := [], substitution := s.substitution.extendType n a} Δ θ := by
  obtain ⟨σ, hw⟩ := hm
  have hc := hw.models (.equal (.flex n) a) (by simp)
  have hbase : Models Δ σ s := fun c hc => hw.models c (List.mem_cons_of_mem _ hc)
  let one : Substitution := {types := [(n, a)]}
  let τ := σ.compose one
  have hτ : τ.WellFormedUnder Δ := singleType_wellFormed hw.wellFormed
    (((σ.constraint_subst_entails _ Δ).mp hc).2.2.2)
  have hmode : τ.mode = σ.mode := singleType_modes σ n a
  refine ⟨σ, hw.wellFormed, ?_, ?_, ?_⟩
  · apply Models.of_solution
    simpa only [List.append_nil] using singleType_solution hw.wellFormed hc hbase.solution
  · intro v hv
    change (σ.ty ((s.substitution.extendType n a).type v)).DefinedUnder Δ ∧ _
    rw [Substitution.extendType_type hk, Substitution.ty_compose]
    obtain ⟨hd, hl, hr⟩ := hw.types v hv
    have heq : TypeEquivalent Δ (σ.ty (s.substitution.type v)) (τ.ty (s.substitution.type v)) := by
      change TypeEquivalent Δ ((s.substitution.type v).subst σ.type σ.mode)
        ((s.substitution.type v).subst τ.type τ.mode)
      rw [hmode]
      exact type_subst_equivalent _ (singleType_equivalent hc) hd
    have hdef : (τ.ty (s.substitution.type v)).DefinedUnder Δ := by
      change ((s.substitution.type v).subst τ.type τ.mode).DefinedUnder Δ
      rw [hmode]
      exact type_subst_defined _ hτ.types hd
    exact ⟨hdef, hl.trans heq.1, heq.2.trans hr⟩
  · exact hw.modes

end ModalityInference.SymbolicSolver
