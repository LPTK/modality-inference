import ModalityInference.Proofs.GenerationCompletenessBase
import ModalityInference.Proofs.GenerationEventualSharing

/-! Context coverage for monomorphic bindings and fresh symbolic locks. -/
namespace ModalityInference

theorem GenerationReady.mono {A s a} (hs : GenerationReady A s)
    (ha : a.Bounded s.nextType s.nextMode) (hf : a.Flexible) :
    GenerationReady (.binding (some (Scheme.mono a)) :: A) s := by
  refine ⟨?_, ?_, ?_, hs.constraintsBounded, hs.constraintsFlexible⟩
  · simpa [ContextEntry.Bounded, Scheme.Bounded, Scheme.mono] using And.intro ha hs.contextBounded
  · simpa [ContextEntry.Flexible, Scheme.Flexible, Scheme.mono] using And.intro hf hs.contextFlexible
  · simpa [Scheme.ModParamsBounded, Scheme.mono] using hs.parametersBounded

theorem SchemeCovers.mono {ρ τ : GroundAssignment} {a b : Ty} {x y : GroundTy}
    (ha : a.realize ρ = some x) (hb : b.realize τ = some y)
    (hxy : Subtype [] x.reify y.reify) : SchemeCovers ρ τ (.mono a) (.mono b) := by
  intro η ground hi ht
  have he : η = τ := GroundInstantiates.mono_iff.mp hi
  subst η
  have he : ground = y := Option.some.inj (ht.symm.trans hb)
  subst ground
  exact ⟨ρ, x, GroundInstantiates.mono_iff.mpr rfl, ha, hxy⟩

theorem AlgorithmicContextCovers.binding {ρ τ A Γ source target used tailUsed}
    (hc : AlgorithmicContextCovers ρ τ A Γ tailUsed)
    (hs : SchemeCovers ρ τ source target)
    (hi : ∀ i, i + 1 ∈ used → i ∈ tailUsed) :
    AlgorithmicContextCovers ρ τ (.binding (some source) :: A)
      (some target :: Γ) used := by
  intro i hm s hl
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
    cases hl
    exact ⟨source, .here, hs⟩
  | succ i =>
    obtain ⟨s', hs', hc'⟩ := hc i (hi i hm) s (by simpa using hl)
    exact ⟨s', .there hs', hc'⟩

theorem Lookup.modParamsBounded {Γ i s nm} (hl : Lookup Γ i s)
    (hΓ : Γ.ModParamsBounded nm) : s.ModParamsBounded nm := by
  induction hl
  case here => exact hΓ _ List.mem_cons_self
  case there hl ih => exact ih (fun s hs => hΓ s (List.mem_cons_of_mem _ hs))
  case locked hl ih => exact ih (fun s hs => hΓ s (List.mem_cons_of_mem _ hs))

theorem AlgorithmicContextCovers.lock {ρ τ Δ A Γ captured used m n p}
    (hc : AlgorithmicContextCovers ρ τ A Γ used)
    (hp : A.ModParamsBounded p) (hΔ : GroundModels τ Δ)
    (hl : Lock Δ m Γ captured)
    (hs : ρ.modes (.flex p) = n) (hm : m.eval (some ∘ τ.modes) = some n) :
    AlgorithmicContextCovers ρ τ (.lock (.var (.flex p)) :: A) captured used := by
  intro i hi target ht
  obtain ⟨scheme, hscheme, rfl, hfb, hfm, hfuture⟩ := hl.kept ht
  obtain ⟨source, hsource, hcover⟩ := hc i hi scheme hscheme
  refine ⟨source.lock (.var (.flex p)), .locked hsource, ?_⟩
  apply hcover.lock hΔ hfb hfm
  · intro k hk hv
    have hk := hsource.modParamsBounded hp k hk
    simp only [ModExpr.vars, Finset.mem_singleton, ModVar.flex.injEq] at hv
    omega
  · exact congrArg some hs
  · exact hm
  · exact hfuture

end ModalityInference
