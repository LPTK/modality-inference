import ModalityInference.Proofs.ResourceSubtyping
import ModalityInference.Proofs.GroundAssignment

/-! Sharing and locking for ownership evidence indexed by ground instances. -/
namespace ModalityInference

theorem ResourceInterpretation.share {w a v owned}
    (ha : ResourceLe (a.modal Mode.aliased) a)
    (hv : ResourceInterpretation w (a.modal Mode.many) Mode.identity v owned) :
    ResourceInterpretation w a Mode.identity v ∅ := by
  obtain ⟨middle, hm, hx⟩ :=
    (ResourceLe.modal (.refl a) (m := Mode.many) (n := Mode.many.compose Mode.aliased)
      (by decide)) w Mode.identity v owned hv
  have hzero : middle = ∅ := (ResourceInterpretation.modal_iff.mp hx).shared_resources
    (by simp [Mode.compose, Mode.many, Mode.aliased])
    (by simp [Mode.compose, Mode.many, Mode.aliased])
  obtain ⟨target, ht, hr⟩ :=
    ((ResourceLe.modal (.refl a) (m := Mode.many.compose Mode.aliased)
      (n := Mode.aliased) (by decide)).trans ha) w Mode.identity v middle hx
  exact (Set.subset_empty_iff.mp (hzero ▸ ht)) ▸ hr

theorem ResourceSchemeInterpretation.shared {ρ w Δ s v reserved}
    (hΔ : GroundModels ρ Δ) (hf : s.FreshForBounds Δ)
    (hs : Subtype (Δ ++ s.bounds) (.modal s.body (.const Mode.aliased)) s.body)
    (hv : ResourceSchemeInterpretation ρ w (s.modal (.const Mode.many)) v reserved) :
    ResourceSchemeInterpretation ρ w s v ∅ := by
  refine ⟨fun _ h => h.elim, ?_⟩
  intro η t hη ht
  obtain ⟨owned, _, hv'⟩ := hv.2 η (t.modal Mode.many) hη
    (by simp [Scheme.modal, TypeExpr.realize, ht, ModExpr.eval])
  have hbounds : GroundModels η (Δ ++ s.bounds) := fun c hc =>
    (List.mem_append.mp hc).elim (hη.models_fresh hf hΔ c) (hη.2.2 c)
  exact ⟨∅, Set.Subset.rfl, ResourceInterpretation.share
    (hs.resourceLe hbounds (by simp [TypeExpr.realize, ht, ModExpr.eval]) ht) hv'⟩

theorem ResourceSchemeInterpretation.capture {ρ w Δ s m v reserved}
    (hΔ : GroundModels ρ Δ) (hf : s.FreshForBounds Δ)
    (hs : Subtype (Δ ++ s.bounds) s.body (.modal s.body (.future m)))
    (hv : ResourceSchemeInterpretation ρ w s v reserved) :
    ResourceSchemeInterpretation ρ w (s.modal (.capture m)) v reserved := by
  refine ⟨hv.1, ?_⟩
  intro η t hη ht
  cases ha : s.body.realize η <;> cases hm : m.eval (some ∘ η.modes) <;>
    simp [Scheme.modal, TypeExpr.realize, ModExpr.eval, ha, hm] at ht
  rename_i a n
  obtain ⟨owned, hsub, hv'⟩ := hv.2 η _ hη ha
  have hbounds : GroundModels η (Δ ++ s.bounds) := fun c hc =>
    (List.mem_append.mp hc).elim
      ((show GroundInstantiates ρ s η from hη).models_fresh hf hΔ c) (hη.2.2 c)
  obtain ⟨middle, hmiddle, hfuture⟩ := hs.resource_semantic (y := a.modal n.future) hbounds ha
    (by simp [TypeExpr.realize, ha, ModExpr.eval, hm]) hv'
  obtain ⟨target, htarget, hcapture⟩ :=
    ResourceLe.modal (.refl a) (m := n.future) (n := n.capture)
      (by simp [Mode.le, Mode.future, Mode.capture]) w Mode.identity v middle hfuture
  exact ⟨target, htarget.trans (hmiddle.trans hsub), ht ▸ hcapture⟩

theorem ContextJoin.left_present {Δ Γ Γ₁ Γ₂} (h : ContextJoin Δ Γ₁ Γ₂ Γ)
    {i : Nat} {s : Scheme} (hi : Γ₁[i]? = some (some s)) : ∃ t, Γ[i]? = some (some t) := by
  induction h generalizing i
  all_goals cases i <;> simp_all

theorem ContextJoin.right_present {Δ Γ Γ₁ Γ₂} (h : ContextJoin Δ Γ₁ Γ₂ Γ)
    {i : Nat} {s : Scheme} (hi : Γ₂[i]? = some (some s)) : ∃ t, Γ[i]? = some (some t) := by
  induction h generalizing i
  all_goals cases i <;> simp_all

private theorem ContextJoin.resources_at {ρ w Δ Γ Γ₁ Γ₂}
    (hΔ : GroundModels ρ Δ) (h : ContextJoin Δ Γ₁ Γ₂ Γ) (i : Nat)
    (value : Option Value) (reserved : Resources)
    (hv : ∀ s, Γ[i]? = some (some s) →
      ∃ v, value = some v ∧ ResourceSchemeInterpretation ρ w s v reserved) :
    ∃ left right : Resources, left ⊆ reserved ∧ right ⊆ reserved ∧ Disjoint left right ∧
      (∀ s, Γ₁[i]? = some (some s) →
        ∃ v, value = some v ∧ ResourceSchemeInterpretation ρ w s v left) ∧
      (∀ s, Γ₂[i]? = some (some s) →
        ∃ v, value = some v ∧ ResourceSchemeInterpretation ρ w s v right) := by
  induction h generalizing i
  all_goals cases i <;> simp_all
  case shared.zero _ hf hs _ =>
    obtain ⟨v, hvalue, hresource⟩ := hv
    exact ⟨∅, Set.empty_subset _, ∅, Set.empty_subset _, disjoint_bot_left,
      ⟨v, hvalue, hresource.shared hΔ hf hs⟩, ⟨v, hvalue, hresource.shared hΔ hf hs⟩⟩
  case left.zero => exact ⟨reserved, Set.Subset.rfl, ∅, Set.empty_subset _, disjoint_bot_right, hv⟩
  case right.zero => exact ⟨∅, Set.empty_subset _, reserved, Set.Subset.rfl, disjoint_bot_left, hv⟩
  all_goals exact ⟨∅, Set.empty_subset _, ∅, Set.empty_subset _, disjoint_bot_left⟩

theorem ContextJoin.resource_semantics {ρ w Γ Γ₁ Γ₂ γ Δ reserved}
    (hΔ : GroundModels ρ Δ) (h : ContextJoin Δ Γ₁ Γ₂ Γ)
    (hγ : ResourceEnvironmentInterpretation ρ w Γ γ reserved) :
    ∃ left right,
      ResourceEnvironmentInterpretation ρ w Γ₁ γ left ∧
      ResourceEnvironmentInterpretation ρ w Γ₂ γ right ∧
      ContextResources Γ₁ left ⊆ ContextResources Γ reserved ∧
      ContextResources Γ₂ right ⊆ ContextResources Γ reserved ∧
      Disjoint (ContextResources Γ₁ left) (ContextResources Γ₂ right) := by
  choose left right hl hr hd hleft hright using
    fun i => h.resources_at hΔ i γ[i]? (reserved i) (hγ.1 i)
  refine ⟨left, right,
    ⟨hleft, fun i j s t hij hi hj =>
      let ⟨s', hi'⟩ := h.left_present hi
      let ⟨t', hj'⟩ := h.left_present hj
      (hγ.2 i j s' t' hij hi' hj').mono (hl i) (hl j)⟩,
    ⟨hright, fun i j s t hij hi hj =>
      let ⟨s', hi'⟩ := h.right_present hi
      let ⟨t', hj'⟩ := h.right_present hj
      (hγ.2 i j s' t' hij hi' hj').mono (hr i) (hr j)⟩, ?_, ?_, ?_⟩
  case refine_3 =>
    apply Set.disjoint_left.mpr
    rintro l ⟨i, s, hi, hli⟩ ⟨j, t, hj, hlj⟩
    by_cases hij : i = j
    case neg =>
      exact let ⟨s', hi'⟩ := h.left_present hi
        let ⟨t', hj'⟩ := h.right_present hj
        Set.disjoint_left.mp (hγ.2 i j s' t' hij hi' hj') (hl i hli) (hr j hlj)
    case pos => exact Set.disjoint_left.mp (hd i) hli (hij.symm ▸ hlj)
  case refine_1 =>
    exact fun l ⟨i, s, hi, hli⟩ =>
      let ⟨t, ht⟩ := h.left_present hi
      ⟨i, t, ht, hl i hli⟩
  case refine_2 =>
    exact fun l ⟨i, s, hi, hli⟩ =>
      let ⟨t, ht⟩ := h.right_present hi
      ⟨i, t, ht, hr i hli⟩

theorem Lock.kept {Δ m Γ Γ'} (h : Lock Δ m Γ Γ')
    {i : Nat} {t : Scheme} (hi : Γ'[i]? = some (some t)) :
    ∃ s, Γ[i]? = some (some s) ∧ t = s.modal (.capture m) ∧
      s.FreshForBounds Δ ∧ s.FreshForMode m ∧
      Subtype (Δ ++ s.bounds) s.body (.modal s.body (.future m)) := by
  induction h generalizing i
  all_goals cases i <;> simp_all

theorem Lock.resource_semantics {ρ w Δ m Γ Γ' γ reserved}
    (hΔ : GroundModels ρ Δ) (h : Lock Δ m Γ Γ')
    (hγ : ResourceEnvironmentInterpretation ρ w Γ γ reserved) :
    ResourceEnvironmentInterpretation ρ w Γ' γ reserved ∧
      ContextResources Γ' reserved ⊆ ContextResources Γ reserved := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  case refine_1 =>
    exact fun i t hi =>
      let ⟨s, hs, ht, hf, _, hcross⟩ := h.kept hi
      let ⟨v, hvalue, hv⟩ := hγ.1 i s hs
      ⟨v, hvalue, ht ▸ hv.capture hΔ hf hcross⟩
  case refine_2 =>
    exact fun i j s t hij hi hj =>
      let ⟨s', hi', _⟩ := h.kept hi
      let ⟨t', hj', _⟩ := h.kept hj
      hγ.2 i j s' t' hij hi' hj'
  case refine_3 =>
    exact fun l ⟨i, t, hi, hl⟩ =>
      let ⟨s, hs, _⟩ := h.kept hi
      ⟨i, s, hs, hl⟩

end ModalityInference
