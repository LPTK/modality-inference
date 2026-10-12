import ModalityInference.Proofs.ResourceClosure
import ModalityInference.Proofs.EvaluationReferences
import ModalityInference.Proofs.Evaluation

/-! Generalize a closed RHS using evaluation determinism across all ground instances,
then prove the closed-definition induction step with separated allocation supplies. -/
namespace ModalityInference

theorem Typing.resource_generalize_closed {Δ rhs a} (ht : Typing Δ [] rhs a)
    (hs : BoundsSatisfiable Δ)
    (ih : ∀ {ρ w ground}, GroundModels ρ Δ → a.realize ρ = some ground →
      ResourceSemanticEvaluation w [] rhs ground ∅)
    {w supplies} (hcom : w.Compatible supplies []) :
    ∃ v reserved, Eval supplies [] rhs v ∧
      (∀ ρ, ResourceSchemeInterpretation ρ w (Scheme.generalize Δ a) v reserved) ∧
      reserved ⊆ {l | supplies.FreshLocation l} := by
  obtain ⟨η, hη⟩ := hs.ground
  obtain ⟨ground, hg⟩ := Option.isSome_iff_exists.mp (ht.realize_defined hη)
  obtain ⟨v, _, he, _, _⟩ := ih hη hg supplies hcom
  refine ⟨v, {l | supplies.FreshLocation l ∧ References v l}, he, ?_, fun _ hl => hl.1⟩
  intro ρ
  refine ⟨fun _ hl => hl.2, ?_⟩
  intro ξ ground' hξ hg'
  obtain ⟨v', owned', he', hv', hr'⟩ := ih hξ.2.2 hg' supplies hcom
  cases he'.deterministic he
  exact ⟨owned', fun l hl => ⟨(hr' hl).resolve_left (fun h => h), hv'.references l hl⟩, hv'⟩

theorem Typing.resource_defn {rhsBounds rhs a} (hrhs : Typing rhsBounds [] rhs a)
    (hsat : BoundsSatisfiable rhsBounds)
    (ihr : ∀ {ρ w ground}, GroundModels ρ rhsBounds → a.realize ρ = some ground →
      ResourceSemanticEvaluation w [] rhs ground ∅)
    {Γ : Context} {body : AnnotatedTerm} {b : Ty} {ρ}
    (ihb : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w
        (Context.restrict (some (Scheme.generalize rhsBounds a) :: Γ) body.freeVars) γ reserved →
      b.realize ρ = some ground →
      ResourceSemanticEvaluation w γ body ground
        (ContextResources
          (Context.restrict (some (Scheme.generalize rhsBounds a) :: Γ) body.freeVars) reserved))
    {w γ reserved ground}
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ.restrict (Term.defn rhs body).freeVars) γ reserved)
    (ha : b.realize ρ = some ground) :
    ResourceSemanticEvaluation w γ (.defn rhs body) ground
      (ContextResources (Γ.restrict (Term.defn rhs body).freeVars) reserved) := by
  intro supplies hsup
  obtain ⟨v, r, he, hscheme, hreserve⟩ := hrhs.resource_generalize_closed hsat ihr
    (hsup.branch (by decide : 0 < 2) 0).empty
  simp only [Term.freeVars, hrhs.closed, Finset.empty_union] at hγ ⊢
  have hsep : Disjoint r (ContextResources (Context.restrict Γ (body.freeVars 1)) reserved) :=
    Set.disjoint_left.mpr fun l hl hc =>
      hsup.2.2.2 l (hγ.references l hc) (Supplies.fresh_branch (hreserve hl))
  obtain ⟨result, owned, hbe, hri, hbound⟩ := ihb
    (ResourceEnvironmentInterpretation.cons_used body (hscheme ρ) hγ hsep) ha
    (supplies.branch 2 1) ((hsup.branch (by decide) 1).cons
      (he.not_fresh_branch hsup.empty (by decide) (by decide) (by decide)))
  exact ⟨result, owned, .defn he hbe, hri, fun l hl => (hbound hl).elim
    (fun hc => (ContextResources.cons_used_subset body Γ
      (Scheme.generalize rhsBounds a) r reserved hc).elim
        (fun hr => Or.inr (Supplies.fresh_branch (hreserve hr))) Or.inl)
    (fun hf => Or.inr (Supplies.fresh_branch hf))⟩

end ModalityInference
