import ModalityInference.Proofs.ResourceEliminations

/-! Fundamental soundness for every constructor of the corrected core language.
Ownership evidence belongs to a ground instance, independently of runtime
annotations. The stronger induction uses exactly the bindings read by the term;
the ordinary full-environment theorem follows by resource weakening. -/
namespace ModalityInference

/-- Fundamental induction, including polymorphic variables, trimmed closures,
closed definitions, allocation, reuse, eliminations, and regions. -/
theorem Typing.resource_semantic_used {Δ Γ t a} (ht : Typing Δ Γ t a)
    {ρ w γ reserved ground} (hΔ : GroundModels ρ Δ)
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ.restrict t.freeVars) γ reserved)
    (ha : a.realize ρ = some ground) :
    ResourceSemanticEvaluation w γ t ground (ContextResources (Γ.restrict t.freeVars) reserved) := by
  induction ht generalizing ρ w γ reserved ground
  case lam Δ Γ captured t a b m harg hm hlock hbody ih =>
    exact hbody.resource_lam hlock hΔ (ih hΔ) hγ ha
  case defn Δ Γ rhs body a b rhsBounds hrhs hsat hbody ihr ihb =>
    have ihg : ∀ {ρ w ground}, GroundModels ρ rhsBounds → a.realize ρ = some ground →
        ResourceSemanticEvaluation w [] rhs ground ∅ := by
      intro ρ w ground hm hg
      simpa using ihr (γ := []) (reserved := fun _ => ∅) hm .nil hg
    exact hrhs.resource_defn hsat ihg (ihb hΔ) hγ ha
  case app Δ Γ Γ₁ Γ₂ f x a b hj hf hx ihf ihx =>
    exact hx.resource_app hj hΔ (ihf hΔ) (ihx hΔ) hγ ha
  case pair Δ Γ Γ₁ Γ₂ a b t u m hj ht hu iht ihu =>
    exact Typing.resource_pair hj hΔ (iht hΔ) (ihu hΔ) hγ ha
  case stackPair Δ Γ Γ₁ Γ₂ a b t u m n hj ht hu hmn hlocal iht ihu =>
    exact Typing.resource_stackPair hj hmn hlocal hΔ (iht hΔ) (ihu hΔ) hγ ha
  case reuse Δ Γ Γ₁ Γ₂ Γ₃ Γ₂₃ t u v a b m k h23 h1 ht hu hv hunique hkm iht ihu ihv =>
    exact Typing.resource_reuse h23 h1 hunique hkm hΔ (iht hΔ) (ihu hΔ) (ihv hΔ) hγ ha
  case region Δ Γ t a ht ih =>
    exact Typing.resource_region (ih hΔ) hγ ha
  case split Δ Γ Γ₁ Γ₂ a b c t u m hj ht hu iht ihu =>
    exact ht.resource_split hj hΔ (iht hΔ) (ihu hΔ) hγ ha
  case case Δ Γ Γ₁ Γ₂ a b c t u v m hj ht hu hv iht ihu ihv =>
    exact ht.resource_case hj hΔ (iht hΔ) (ihu hΔ) (ihv hΔ) hγ ha
  case var Δ Γ i s σ hi hσ hbounds hdefined =>
    exact hγ.instantiated_lookup hΔ
      (Context.restrict_present.mpr ⟨by simp [Term.freeVars], hi⟩) hσ hbounds ha
  case unit Δ Γ m hdefined =>
    cases hm : m.eval (some ∘ ρ.modes) <;>
      simp [TypeExpr.realize, hm, GroundTy.modal] at ha
    subst ground
    refine fun _ _ => ⟨.unit, ∅, .unit, ?_, Set.empty_subset _⟩
    simp only [ResourceInterpretation]
    refine ⟨?_, ?_, trivial⟩
    · exact fun _ h => nomatch h
    · simp
  case subs Δ Γ Γ' t a b ht hctx hty ih =>
    obtain ⟨source, hs⟩ := Option.isSome_iff_exists.mp (ht.realize_defined hΔ)
    obtain ⟨henv, hsub⟩ := (hctx.restrict t.freeVars).resource_semantics hΔ hγ
    intro supplies hsup
    obtain ⟨v, owned, he, hv, ho⟩ := ih hΔ henv hs supplies hsup
    obtain ⟨target, htarget, hri⟩ := hty.resource_semantic hΔ hs ha hv
    exact ⟨v, target, he, hri, htarget.trans
      (ho.trans (Set.union_subset_union hsub Set.Subset.rfl))⟩
  case inl Δ Γ a b t m hdefined ht ih =>
    cases ha' : a.realize ρ <;> cases hb' : b.realize ρ <;>
      cases hm' : m.eval (some ∘ ρ.modes) <;>
      simp [TypeExpr.realize, ha', hb', hm', GroundTy.modal] at ha
    rename_i firstTy secondTy n
    subst ground
    intro supplies hsup
    obtain ⟨x, owned, he, hv, ho⟩ := ih (ground := firstTy.modal n) hΔ hγ
      (by simp [TypeExpr.realize, ha', hm']) supplies hsup
    refine ⟨.inl x, owned, .inl he, ?_, ho⟩
    simp only [ResourceInterpretation, GroundTy.mode, Mode.compose_identity]
    refine ⟨?_, fun l hl => .inl (hv.references l hl), ?_⟩
    · intro l hl
      cases hl with | inl hl => exact hv.valid l hl
    · simpa using ResourceInterpretation.modal_iff.mp hv
  case inr Δ Γ a b t m hdefined ht ih =>
    cases ha' : a.realize ρ <;> cases hb' : b.realize ρ <;>
      cases hm' : m.eval (some ∘ ρ.modes) <;>
      simp [TypeExpr.realize, ha', hb', hm', GroundTy.modal] at ha
    rename_i firstTy secondTy n
    subst ground
    intro supplies hsup
    obtain ⟨x, owned, he, hv, ho⟩ := ih (ground := secondTy.modal n) hΔ hγ
      (by simp [TypeExpr.realize, hb', hm']) supplies hsup
    refine ⟨.inr x, owned, .inr he, ?_, ho⟩
    simp only [ResourceInterpretation, GroundTy.mode, Mode.compose_identity]
    refine ⟨?_, fun l hl => .inr (hv.references l hl), ?_⟩
    · intro l hl
      cases hl with | inr hl => exact hv.valid l hl
    · simpa using ResourceInterpretation.modal_iff.mp hv

/-- Full-context soundness for the complete corrected declarative system. -/
theorem Typing.resource_semantic {Δ Γ t a} (ht : Typing Δ Γ t a)
    {ρ w γ reserved ground} (hΔ : GroundModels ρ Δ)
    (hγ : ResourceEnvironmentInterpretation ρ w Γ γ reserved)
    (ha : a.realize ρ = some ground) :
    ResourceSemanticEvaluation w γ t ground (ContextResources Γ reserved) := by
  intro supplies hsup
  obtain ⟨v, owned, he, hv, ho⟩ := ht.resource_semantic_used hΔ (hγ.restrict t.freeVars) ha supplies hsup
  exact ⟨v, owned, he, hv, ho.trans
    (Set.union_subset_union (ContextResources.restrict_subset Γ t.freeVars reserved) Set.Subset.rfl)⟩

/-- A closed typed program needs no assumed value interpretation or realized
result type: typing supplies the ground result and evaluation owns only fresh cells. -/
theorem Typing.resource_closed {Δ t a} (ht : Typing Δ [] t a)
    {ρ w supplies} (hΔ : GroundModels ρ Δ) (hs : w.Compatible supplies []) :
    ∃ ground v owned, a.realize ρ = some ground ∧ Eval supplies [] t v ∧
      ResourceInterpretation w ground Mode.identity v owned ∧
      owned ⊆ {l | supplies.FreshLocation l} := by
  obtain ⟨ground, ha⟩ := Option.isSome_iff_exists.mp (ht.realize_defined hΔ)
  obtain ⟨v, owned, he, hv, ho⟩ := ht.resource_semantic hΔ
    (ResourceEnvironmentInterpretation.nil (reserved := fun _ => ∅)) ha supplies hs
  exact ⟨ground, v, owned, ha, he, hv, by simpa using ho⟩

end ModalityInference
