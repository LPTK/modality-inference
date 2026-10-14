import ModalityInference.Proofs.GenerationEventualSharing

/-! Deterministic free-variable routing preserves the instances needed by each
branch, including sharing below symbolic locks. -/
namespace ModalityInference

def Scheme.GroundRefines (s t : Scheme) : Prop :=
  ∀ ρ η, GroundInstantiates ρ t η →
    GroundInstantiates ρ s η ∧ s.body.realize η = t.body.realize η

theorem Scheme.GroundRefines.refl (s : Scheme) : s.GroundRefines s :=
  fun _ _ h => ⟨h, rfl⟩

theorem Scheme.GroundRefines.trans {s t u : Scheme}
    (h₁ : s.GroundRefines t) (h₂ : t.GroundRefines u) : s.GroundRefines u := by
  intro ρ η hη
  obtain ⟨ht, het⟩ := h₂ ρ η hη
  obtain ⟨hs, hes⟩ := h₁ ρ η ht
  exact ⟨hs, hes.trans het⟩

theorem Scheme.GroundRefines.covers {s t : Scheme} (h : s.GroundRefines t)
    (ρ : GroundAssignment) : SchemeCovers ρ ρ s t := by
  intro η b hη hb
  obtain ⟨hs, he⟩ := h ρ η hη
  exact ⟨η, b, hs, he.trans hb, .refl⟩

theorem Scheme.GroundRefines.lock {s t : Scheme} (h : s.GroundRefines t) (p : ModExpr) :
    (s.lock p).GroundRefines (t.lock p) := by
  intro ρ η hη
  have ht : GroundInstantiates ρ t η := ⟨hη.1, hη.2.1,
    fun c hc => hη.2.2 c (List.mem_append_left _ hc)⟩
  obtain ⟨hs, he⟩ := h ρ η ht
  refine ⟨⟨hs.1, hs.2.1, ?_⟩, ?_⟩
  · have hg := hη.2.2 (.sub t.body (.modal t.body (.future p)))
      (by simp [Scheme.lock])
    have hg' : GroundSatisfies η (.sub s.body (.modal s.body (.future p))) := by
      simpa only [GroundSatisfies, TypeExpr.realize, he] using hg
    simpa [Scheme.lock, GroundModels, or_imp, forall_and] using And.intro hs.2.2 hg'
  · simp only [Scheme.lock, TypeExpr.realize, he]

theorem Scheme.share_lock_refines (s : Scheme) (p : ModExpr) :
    (s.share.lock p).GroundRefines ((s.lock p).share) := by
  intro ρ η hη
  have hs : GroundInstantiates ρ s η := ⟨hη.1, hη.2.1,
    fun c hc => hη.2.2 c (by simp [Scheme.share, Scheme.lock, hc])⟩
  have hfuture := hη.2.2 (.sub s.body (.modal s.body (.future p)))
    (by simp [Scheme.share, Scheme.lock])
  obtain ⟨a, b, ha, hb, hab⟩ := hfuture
  cases hp : p.eval (some ∘ η.modes) <;>
    simp [TypeExpr.realize, ModExpr.eval, hp, ha] at hb
  rename_i m
  subst b
  have hshare := hη.2.2 (.sub (.modal s.body (.capture p))
    (.modal (.modal s.body (.capture p)) (.const Mode.many)))
      (by simp [Scheme.share, Scheme.lock])
  have hshare' : GroundOrder (a.modal m.capture) ((a.modal m.capture).modal Mode.many) := by
    apply GroundOrder.of_subtype
    simpa [GroundSatisfies, TypeExpr.realize, ModExpr.eval, ha, hp] using hshare
  have hacapture : GroundOrder a (a.modal m.capture) :=
    (GroundOrder.of_subtype hab).trans ((GroundOrder.refl a).modal
      (by simp [Mode.le, Mode.future, Mode.capture]))
  have hamany := hacapture.modal_guard_downward hshare' rfl
  have halias := hab.ground_modal (Mode.le_refl Mode.aliased)
  refine ⟨⟨hs.1, hs.2.1, ?_⟩, ?_⟩
  · simp only [Scheme.lock, Scheme.share, GroundModels, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]
    intro c hc
    rcases hc with (hc | rfl) | rfl
    · exact hs.2.2 c hc
    · simpa [GroundSatisfies, TypeExpr.realize, ha, ModExpr.eval] using hamany.to_subtype
    · simpa [GroundSatisfies, TypeExpr.realize, ha, ModExpr.eval, hp,
        GroundTy.modal_compose, Mode.compose_comm Mode.aliased m.future] using halias
  · simp [Scheme.lock, Scheme.share, TypeExpr.realize, ha, ModExpr.eval, hp,
      GroundTy.modal_compose, Mode.compose_comm Mode.aliased m.capture]

theorem mem_routed_tail (X : Finset Nat) (i : Nat) :
    i ∈ (X.filter (0 < ·)).image (· - 1) ↔ i + 1 ∈ X := by
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨n, ⟨hn, hpos⟩, he⟩
    have hn' : n = i + 1 := by omega
    simpa only [hn'] using hn
  · intro hi
    exact ⟨i + 1, ⟨hi, by omega⟩, by omega⟩

theorem Lookup.split_left {Γ i s} (h : Lookup Γ i s) (X Y : Finset Nat) (hx : i ∈ X) :
    ∃ r, Lookup (splitContext X Y Γ).1 i r ∧
      r.GroundRefines (if i ∈ Y then s.share else s) := by
  induction h generalizing X Y
  case here Γ s =>
    by_cases hy : 0 ∈ Y
    · refine ⟨s.share, ?_, ?_⟩
      · simpa [splitContext, hx, hy] using
          (Lookup.here (Γ := (splitContext ((X.filter (0 < ·)).image (· - 1))
            ((Y.filter (0 < ·)).image (· - 1)) Γ).1) (s := s.share))
      · simpa only [if_pos hy] using Scheme.GroundRefines.refl s.share
    · refine ⟨s, ?_, ?_⟩
      · simpa [splitContext, hx, hy] using
          (Lookup.here (Γ := (splitContext ((X.filter (0 < ·)).image (· - 1))
            ((Y.filter (0 < ·)).image (· - 1)) Γ).1) (s := s))
      · simpa only [if_neg hy] using Scheme.GroundRefines.refl s
  case there Γ i s t h ih =>
    obtain ⟨r, hr, hs⟩ := ih ((X.filter (0 < ·)).image (· - 1))
      ((Y.filter (0 < ·)).image (· - 1)) ((mem_routed_tail X i).mpr hx)
    refine ⟨r, ?_, ?_⟩
    · simpa only [splitContext] using (Lookup.there (t :=
        if 0 ∈ X then (if 0 ∈ X ∧ 0 ∈ Y then t.map Scheme.share else t) else none) hr)
    · simpa only [mem_routed_tail] using hs
  case locked Γ i s p h ih =>
    obtain ⟨r, hr, hs⟩ := ih X Y hx
    refine ⟨r.lock p, ?_, ?_⟩
    · simpa only [splitContext, Scheme.lock] using Lookup.locked (m := p) hr
    · by_cases hy : i ∈ Y
      · simpa only [if_pos hy, Scheme.lock] using
          ((show r.GroundRefines s.share from by simpa only [if_pos hy] using hs).lock p).trans
            (s.share_lock_refines p)
      · simpa only [if_neg hy, Scheme.lock] using
          (show r.GroundRefines s from by simpa only [if_neg hy] using hs).lock p

theorem splitContext_swap (Γ : AlgorithmicContext) (X Y : Finset Nat) :
    splitContext Y X Γ = ((splitContext X Y Γ).2, (splitContext X Y Γ).1) := by
  induction Γ generalizing X Y
  case nil => rfl
  case cons e Γ ih =>
    cases e
    case lock p =>
      simp only [splitContext]
      rw [ih X Y]
    case binding s =>
      simp only [splitContext]
      rw [ih ((X.filter (0 < ·)).image (· - 1)) ((Y.filter (0 < ·)).image (· - 1))]
      simp only [and_comm]

theorem Lookup.split_right {Γ i s} (h : Lookup Γ i s) (X Y : Finset Nat) (hy : i ∈ Y) :
    ∃ r, Lookup (splitContext X Y Γ).2 i r ∧
      r.GroundRefines (if i ∈ X then s.share else s) := by
  simpa only [splitContext_swap Γ X Y] using h.split_left Y X hy

theorem SchemeCovers.modal_many (ρ : GroundAssignment) (s : Scheme) :
    SchemeCovers ρ ρ (s.modal (.const Mode.many)) s := by
  intro η b hη hb
  refine ⟨η, b.modal Mode.many, hη, ?_, ?_⟩
  · simp [Scheme.modal, TypeExpr.realize, hb, ModExpr.eval]
  · simpa only [GroundTy.modal_identity] using
      (Subtype.refl (a := b.reify)).ground_modal
        (m := Mode.many) (n := Mode.identity) (by decide)

theorem ContextJoin.left_scheme {Δ Γ Γ₁ Γ₂} {i : Nat} {s t : Scheme}
    (h : ContextJoin Δ Γ₁ Γ₂ Γ) (hs : Γ[i]? = some (some s))
    (ht : Γ₁[i]? = some (some t)) :
    (s = t ∧ Γ₂[i]? = some none) ∨
      (s = t.modal (.const Mode.many) ∧ Γ₂[i]? = some (some t) ∧
        t.FreshForBounds Δ ∧
        Subtype (Δ ++ t.bounds) (.modal t.body (.const Mode.aliased)) t.body) := by
  induction h generalizing i
  all_goals cases i <;> simp_all

theorem ContextJoin.symm {Δ Γ Γ₁ Γ₂} (h : ContextJoin Δ Γ₁ Γ₂ Γ) :
    ContextJoin Δ Γ₂ Γ₁ Γ := by
  induction h
  all_goals solve_by_elim [ContextJoin.nil, ContextJoin.unused, ContextJoin.left,
    ContextJoin.right, ContextJoin.shared]

theorem AlgorithmicContextCovers.split_left {ρ τ Δ source Γ Γ₁ Γ₂ X Y}
    (h : AlgorithmicContextCovers ρ τ source Γ (X ∪ Y))
    (hj : ContextJoin Δ Γ₁ Γ₂ Γ) (hΔ : GroundModels τ Δ)
    (hY : ∀ i ∈ Y, ∃ t, Γ₂[i]? = some (some t)) :
    AlgorithmicContextCovers ρ τ (splitContext X Y source).1 Γ₁ X := by
  intro i hi t ht
  obtain ⟨s, hs⟩ := hj.left_present ht
  obtain ⟨u, hu, hus⟩ := h i (Finset.mem_union.mpr (.inl hi)) s hs
  obtain ⟨r, hr, hru⟩ := hu.split_left X Y hi
  refine ⟨r, hr, (hru.covers ρ).trans ?_⟩
  rcases hj.left_scheme hs ht with ⟨rfl, hnone⟩ | ⟨rfl, hright, hf, halias⟩
  · have hy : i ∉ Y := by
      intro hy
      obtain ⟨v, hv⟩ := hY i hy
      simp [hnone] at hv
    simpa only [if_neg hy] using hus
  · by_cases hy : i ∈ Y
    · simpa only [if_pos hy] using hus.share hΔ hf halias
    · simpa only [if_neg hy] using hus.trans (SchemeCovers.modal_many τ t)

theorem AlgorithmicContextCovers.split {ρ τ Δ source Γ Γ₁ Γ₂ X Y}
    (h : AlgorithmicContextCovers ρ τ source Γ (X ∪ Y))
    (hj : ContextJoin Δ Γ₁ Γ₂ Γ) (hΔ : GroundModels τ Δ)
    (hX : ∀ i ∈ X, ∃ t, Γ₁[i]? = some (some t))
    (hY : ∀ i ∈ Y, ∃ t, Γ₂[i]? = some (some t)) :
    AlgorithmicContextCovers ρ τ (splitContext X Y source).1 Γ₁ X ∧
      AlgorithmicContextCovers ρ τ (splitContext X Y source).2 Γ₂ Y := by
  refine ⟨h.split_left hj hΔ hY, ?_⟩
  have hh : AlgorithmicContextCovers ρ τ source Γ (Y ∪ X) :=
    Finset.union_comm X Y ▸ h
  simpa only [splitContext_swap source X Y] using hh.split_left hj.symm hΔ hX

end ModalityInference
