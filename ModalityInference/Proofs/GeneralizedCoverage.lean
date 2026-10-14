import ModalityInference.Proofs.GroundPrincipality
import ModalityInference.Proofs.GeneralizationTransport
import ModalityInference.Proofs.GenerationEventualCovers
import ModalityInference.Proofs.SolverCompleteness
import ModalityInference.Proofs.GenerationEventualFuel
import ModalityInference.Proofs.GenerationSupplies

/-! Ground solver factorization gives coverage of closed generalized schemes. -/
namespace ModalityInference

theorem GroundFactorization.type {scope cs σ ρ a b}
    (h : GroundFactorization scope cs σ ρ) (ha : a.Scoped scope)
    (hb : a.realize ρ = some b) :
    ∃ η t, GroundModels η cs ∧ (σ.ty a).realize η = some t ∧
      Subtype [] t.reify b.reify ∧ Subtype [] b.reify t.reify := by
  obtain ⟨η, hm, htypes, hmodes⟩ := h
  have ht : ∀ v ∈ a.typeVars,
      (σ.type v).realize η = some ((σ.ground η).types v) := by
    intro v hv
    obtain ⟨t, ht, _, _⟩ := htypes v (ha.1 hv)
    simp [Substitution.ground, ht]
  have he : ∀ v ∈ a.typeVars, (ρ.types v).Equivalent ((σ.ground η).types v) := by
    intro v hv
    obtain ⟨t, ht, hl, hr⟩ := htypes v (ha.1 hv)
    simpa [Substitution.ground, ht] using
      (And.intro (GroundOrder.of_subtype hr) (GroundOrder.of_subtype hl) :
        (ρ.types v).Equivalent t)
  have heq : ∀ v ∈ a.modVars, ρ.modes v = (σ.ground η).modes v := by
    intro v hv
    simp [Substitution.ground, hmodes v (ha.2 hv)]
  obtain ⟨t, ht', hsub⟩ := (a.realize_equivalent he heq).some_left hb
  refine ⟨η, t, hm, ?_, hsub.2.to_subtype, hsub.1.to_subtype⟩
  exact (a.realize_subst_congr ht (fun v hv =>
    (hmodes v (ha.2 hv)).trans (congrArg some (heq v hv)))).trans ht'

theorem Scheme.generalize_closed {cs : Bounds} {a : Ty}
    (hc : cs.Flexible) (ha : a.Flexible) :
    (generalize cs a).freeTypes = ∅ ∧ (generalize cs a).freeModes = ∅ := by
  constructor
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hv, hn⟩ := (Scheme.mem_freeTypes_iff _ v).mp hv
    have hflex : ∃ n, v = .flex n := hv.elim
      (fun h => (a.flexible_iff.mp ha).1 v h)
      (fun h => (cs.flexible_iff.mp hc).1 v h)
    obtain ⟨n, rfl⟩ := hflex
    exact hn (List.mem_map.mpr ⟨n, Scheme.generalize_typeParams.mpr
      (Finset.mem_union.mpr hv), rfl⟩)
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hv, hn⟩ := (Scheme.mem_freeModes_iff _ v).mp hv
    have hflex : ∃ n, v = .flex n := hv.elim
      (fun h => (a.flexible_iff.mp ha).2 v h)
      (fun h => (cs.flexible_iff.mp hc).2 v h)
    obtain ⟨n, rfl⟩ := hflex
    exact hn (List.mem_map.mpr ⟨n, Scheme.generalize_modParams.mpr
      (Finset.mem_union.mpr hv), rfl⟩)

theorem Scheme.generalize_ground {cs : Bounds} {a : Ty} {η : GroundAssignment}
    (hc : cs.Flexible) (ha : a.Flexible) (hη : GroundModels η cs)
    (ρ : GroundAssignment) :
    GroundInstantiates ρ (generalize cs a) ((generalize cs a).rebase ρ η) ∧
      (generalize cs a).body.realize ((generalize cs a).rebase ρ η) = a.realize η := by
  have hi : GroundInstantiates η (generalize cs a) η :=
    ⟨fun _ _ => rfl, fun _ _ => rfl, hη⟩
  exact hi.rebase (by simp [(generalize_closed hc ha).1])
    (by simp [(generalize_closed hc ha).2])

theorem SchemeCovers.generalize_factorization {scope cs residual σ a rhsBounds rhsType}
    (hscope : a.Scoped scope) (hr : residual.Flexible) (ha : (σ.ty a).Flexible)
    (hcover : ∀ η b, GroundModels η rhsBounds → rhsType.realize η = some b →
      ∃ ρ t, GroundModels ρ cs ∧ a.realize ρ = some t ∧ Subtype [] t.reify b.reify)
    (hfactor : ∀ ρ, GroundModels ρ cs → GroundFactorization scope residual σ ρ)
    (ρ τ : GroundAssignment) :
    SchemeCovers ρ τ (Scheme.generalize residual (σ.ty a))
      (Scheme.generalize rhsBounds rhsType) := by
  intro η b hη hb
  obtain ⟨ξ, t, hξ, ht, hsub⟩ := hcover η b hη.2.2 hb
  obtain ⟨ζ, u, hζ, hu, hut, _⟩ := (hfactor ξ hξ).type hscope ht
  obtain ⟨hi, he⟩ := Scheme.generalize_ground hr ha hζ ρ
  exact ⟨_, u, hi, he.trans hu, hut.trans hsub⟩

theorem solveFrom_generalize_covers {cs : Bounds} {nt nm fuel result a rhsBounds rhsType}
    (hc : cs.Bounded nt nm) (hf : cs.Flexible) (ha : a.Bounded nt nm) (hfa : a.Flexible)
    (hr : solveFrom fuel nt nm cs = .success result)
    (hcover : ∀ η b, GroundModels η rhsBounds → rhsType.realize η = some b →
      ∃ ξ t, GroundModels ξ cs ∧ a.realize ξ = some t ∧ Subtype [] t.reify b.reify)
    (ρ τ : GroundAssignment) :
    SchemeCovers ρ τ (Scheme.generalize result.bounds (result.substitution.ty a))
      (Scheme.generalize rhsBounds rhsType) := by
  have hflex := solveFrom_flexible hf hr
  apply SchemeCovers.generalize_factorization (scope := ⟨a.typeVars, a.modVars⟩)
    ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩ hflex.1 (hflex.2.ty hfa) hcover
  intro ξ hξ
  exact solveFrom_ground_factorization hc hf ((a.bounded_iff nt nm).mp ha) hr hξ

theorem generate_success_unique {n k Γ t s r q}
    (hr : generate n Γ t s = .success r) (hq : generate k Γ t s = .success q) : r = q :=
  RunResult.success.inj ((generate_monotone hr (max n k) (Nat.le_max_left _ _)).symm.trans
    (generate_monotone hq (max n k) (Nat.le_max_right _ _)))

theorem generate_generalize_covers {nt nm n fuel rhs r result rhsBounds rhsType}
    (hg : generate n [] rhs {nextType := nt, nextMode := nm} = .success r)
    (hr : solveFrom fuel r.state.nextType r.state.nextMode r.state.constraints = .success result)
    (hcover : ∀ η b, GroundModels η rhsBounds → rhsType.realize η = some b →
      ∃ k q ξ t,
        generate k [] rhs {nextType := nt, nextMode := nm} = .success q ∧
        GroundModels ξ q.state.constraints ∧ q.type.realize ξ = some t ∧
        Subtype [] t.reify b.reify)
    (ρ τ : GroundAssignment) :
    SchemeCovers ρ τ (Scheme.generalize result.bounds (result.substitution.ty r.type))
      (Scheme.generalize rhsBounds rhsType) := by
  have hb := generate_bounded hg (AlgorithmicContext.bounded_nil _ _) (Bounds.bounded_nil _ _)
  have hf := generate_flexible hg AlgorithmicContext.flexible_nil Bounds.flexible_nil
  apply solveFrom_generalize_covers hb.2 hf.2 hb.1 hf.1 hr
  intro η b hη hb
  obtain ⟨k, q, ξ, t, hq, hξ, ht, hsub⟩ := hcover η b hη hb
  cases generate_success_unique hg hq
  exact ⟨ξ, t, hξ, ht, hsub⟩

end ModalityInference
