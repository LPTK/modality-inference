import ModalityInference.Proofs.ResourceBindings

/-! The lambda step of the fundamental theorem. The body induction hypothesis is
explicit; capture liveness, globality, affinity and resource bounds are proved. -/
namespace ModalityInference

theorem Typing.resource_lam {Δ t a b m} {Γ captured : Context}
    (hbody : Typing Δ (some (Scheme.mono a) :: captured) t b)
    (hlock : Lock Δ m Γ captured) {ρ} (hΔ : GroundModels ρ Δ)
    (ih : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w
        (Context.restrict (some (Scheme.mono a) :: captured) t.freeVars) γ reserved →
      b.realize ρ = some ground →
      ResourceSemanticEvaluation w γ t ground
        (ContextResources (Context.restrict (some (Scheme.mono a) :: captured) t.freeVars) reserved))
    {w γ reserved ground}
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ.restrict (t.freeVars 1)) γ reserved)
    (ha : (TypeExpr.modal (.fn a b) m).realize ρ = some ground) :
    ResourceSemanticEvaluation w γ (.lam (captured.restrict (t.freeVars 1)) t) ground
      (ContextResources (Γ.restrict (t.freeVars 1)) reserved) := by
  cases ha' : a.realize ρ <;> cases hb' : b.realize ρ <;>
    cases hm' : m.eval (some ∘ ρ.modes) <;>
    simp [TypeExpr.realize, ha', hb', hm', GroundTy.modal] at ha
  rename_i domain codomain n
  subst ground
  have hused : ∀ i ∈ t.freeVars 1,
      ∃ s, captured[i]? = some (some s) ∧ s.Realizable ρ := by
    intro i hi
    simpa using hbody.freeVars_realizable hΔ ((t.mem_freeVars_add 0 1 i).mp hi)
  let capR : Nat → Resources := if n.once then reserved else fun _ => ∅
  have hcap : ResourceEnvironmentInterpretation ρ w
      (captured.restrict (t.freeVars 1)) γ capR := by
    cases hn : n.once <;> simp only [capR, hn, Bool.false_eq_true, ↓reduceIte]
    · exact (hlock.restrict _).resource_many_semantics hΔ hγ hm' hn
    · exact ((hlock.restrict _).resource_semantics hΔ hγ).1
  refine fun _ _ => ⟨_, ContextResources (captured.restrict (t.freeVars 1)) capR, .lam, ?_, ?_⟩
  case refine_1 =>
    simp only [ResourceInterpretation, GroundTy.mode, Mode.compose_identity]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    case refine_5 =>
      intro w' x argument hlive hx hsep supplies hsup
      obtain ⟨result, resources, he, hv, hr⟩ := ih
        (ResourceEnvironmentInterpretation.cons_used t
          (.mono ha' hx) (hcap.trim.reworld hlive) hsep.symm) hb' supplies hsup
      exact ⟨result, resources, he, hv, fun l hl => (hr hl).elim
        (fun hc => Or.inl ((ContextResources.cons_used_subset t captured
          (Scheme.mono a) argument capR hc).elim Or.inr Or.inl)) Or.inr⟩
    case refine_1 =>
      exact fun l hl => let ⟨v, hv, href⟩ := References.closure_iff.mp hl
        hcap.trim_valid hused v hv l href
    case refine_2 =>
      exact fun l hl => References.closure_iff.mpr (hcap.trim.references l hl)
    case refine_3 => exact hlock.trim_global hcap hused hm'
    case refine_4 =>
      intro hn
      simp [ContextResources, capR, hn]
  case refine_2 =>
    cases hn : n.once <;> simp only [capR, hn, Bool.false_eq_true, ↓reduceIte]
    · simp [ContextResources]
    · exact fun _ hl => Or.inl (((hlock.restrict _).resource_semantics hΔ hγ).2 hl)

end ModalityInference
