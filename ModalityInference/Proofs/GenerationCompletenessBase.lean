import ModalityInference.Proofs.GenerationCompletenessFresh
import ModalityInference.Proofs.GenerationHygiene
import ModalityInference.Proofs.GenerationEventualFuel
import ModalityInference.Proofs.GenerationEventualCovers

/-! The ground completeness invariant records an executable generation together
with a model extending the previously allocated identifiers. -/
namespace ModalityInference

structure GenerationReady (Γ : AlgorithmicContext) (s : InferenceState) : Prop where
  contextBounded : Γ.Bounded s.nextType s.nextMode
  contextFlexible : Γ.Flexible
  parametersBounded : Γ.ModParamsBounded s.nextMode
  constraintsBounded : s.constraints.Bounded s.nextType s.nextMode
  constraintsFlexible : s.constraints.Flexible

theorem GenerationReady.restate {Γ s t} (h : GenerationReady Γ s)
    (ht : s.nextType ≤ t.nextType) (hm : s.nextMode ≤ t.nextMode)
    (hb : t.constraints.Bounded t.nextType t.nextMode) (hf : t.constraints.Flexible) :
    GenerationReady Γ t :=
  ⟨h.contextBounded.mono ht hm, h.contextFlexible, h.parametersBounded.mono hm, hb, hf⟩

theorem GenerationReady.advance {Γ Γ' s r fuel t} (h : GenerationReady Γ s)
    (hg : generate fuel Γ' t s = .success r)
    (hb : Γ'.Bounded s.nextType s.nextMode) (hf : Γ'.Flexible) :
    GenerationReady Γ r.state :=
  h.restate (generate_counters hg).1 (generate_counters hg).2
    (generate_bounded hg hb h.constraintsBounded).2
    (generate_flexible hg hf h.constraintsFlexible).2

theorem GenerationReady.split {Γ s} (h : GenerationReady Γ s) (X Y : Finset Nat) :
    GenerationReady (splitContext X Y Γ).1 s ∧
      GenerationReady (splitContext X Y Γ).2 s :=
  ⟨⟨(splitContext_bounded h.contextBounded X Y).1,
    (splitContext_flexible h.contextFlexible X Y).1,
    (splitContext_modParamsBounded h.parametersBounded X Y).1,
    h.constraintsBounded, h.constraintsFlexible⟩,
   ⟨(splitContext_bounded h.contextBounded X Y).2,
    (splitContext_flexible h.contextFlexible X Y).2,
    (splitContext_modParamsBounded h.parametersBounded X Y).2,
    h.constraintsBounded, h.constraintsFlexible⟩⟩

def GroundGenerates (Γ : AlgorithmicContext) (t : RawTerm) (s : InferenceState)
    (ρ : GroundAssignment) (target : GroundTy) : Prop :=
  ∃ fuel r η ground, generate fuel Γ t s = .success r ∧
    GroundModels η r.state.constraints ∧
    SolverGround.AgreesBelow η ρ s.nextType s.nextMode ∧
    r.type.realize η = some ground ∧ Subtype [] ground.reify target.reify

def GroundTypingComplete (Δ : Bounds) (Γ : Context) (t : AnnotatedTerm) (a : Ty) : Prop :=
  ∀ A s ρ τ b, GenerationReady A s → GroundModels τ Δ →
    AlgorithmicContextCovers ρ τ A Γ t.freeVars → GroundModels ρ s.constraints →
    a.realize τ = some b → GroundGenerates A t.erase s ρ b

theorem GroundGenerates.weaken {Γ t s ρ a b}
    (h : GroundGenerates Γ t s ρ a) (hab : Subtype [] a.reify b.reify) :
    GroundGenerates Γ t s ρ b := by
  obtain ⟨fuel, r, η, ground, hr, hm, ha, ht, hs⟩ := h
  exact ⟨fuel, r, η, ground, hr, hm, ha, ht, hs.trans hab⟩

theorem GroundGenerates.result_eq {Γ t s ρ a fuel r}
    (h : GroundGenerates Γ t s ρ a) (hr : generate fuel Γ t s = .success r) :
    ∃ η ground, GroundModels η r.state.constraints ∧
      SolverGround.AgreesBelow η ρ s.nextType s.nextMode ∧
      r.type.realize η = some ground ∧ Subtype [] ground.reify a.reify := by
  obtain ⟨n, q, η, ground, hq, hm, ha, ht, hs⟩ := h
  have he : q = r := by
    have hq' := generate_monotone hq _ (Nat.le_max_left n fuel)
    have hr' := generate_monotone hr _ (Nat.le_max_right n fuel)
    exact RunResult.success.inj (hq'.symm.trans hr')
  subst q
  exact ⟨η, ground, hm, ha, ht, hs⟩

end ModalityInference
