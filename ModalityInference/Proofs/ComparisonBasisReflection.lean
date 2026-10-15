import ModalityInference.Proofs.ComparisonAlgebraIntervals

/-! Every nonconstant Boolean observer of a common-shape basis satisfies one
of its four executable coordinate theories under one actual mode assignment. -/
namespace ModalityInference.ComparisonControls

open ComparisonAlgebra

theorem Basis.modalPairs_defined (b : Basis) (ms : ModVar → ModExpr)
    (hm : ∀ v ∈ b.modes, DefinedMode Δ (ms v)) :
    ∀ p ∈ b.modalPairs, DefinedMode Δ (p.2.subst ms) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact fun _ _ => rfl
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    obtain ⟨v, hv, hc⟩ := List.mem_flatMap.mp hc
    exact control_subst_defined c ms ((controls_name_mem hc).symm ▸ hm v hv)

theorem Basis.observer_model (b : Basis) (f : LatticeHom (Order Δ shape) Bool)
    (lower upper : Carrier Δ shape) (hlu : lower ≤ upper)
    (hlo : observer f (lower.atMode Mode.bottom) = false)
    (hhi : observer f (upper.atMode Mode.top) = true)
    (ms : ModVar → ModExpr) (actual : (ModVar → Mode) → ModVar → Mode)
    (hactual : ∀ η v, (ms v).eval (some ∘ η) = some (actual η v))
    (hm : ∀ v ∈ b.modes, DefinedMode Δ (ms v))
    (hpairs : ∀ p ∈ b.modalPairs,
      InInterval (lower.atMode Mode.bottom) (upper.atMode Mode.top)
        (p.1.subst CompareTy.var ms))
    (labels : List ModExpr) (hd : ∀ m ∈ labels, DefinedMode Δ (m.subst ms)) :
    ∃ c η, (c = Coordinate.unaffected ∨ ModeModels Δ η) ∧
      ∀ (σ : Nat → Bool) (basisAtom headAtom modeAtom : Nat → Nat),
        (∀ i (hi : i < b.heads.length),
          σ (headAtom i) = booleanValue f (b.heads[i].subst CompareTy.var ms)) →
        (∀ i (hi : i < b.types.length),
          σ (basisAtom i) = booleanValue f (b.types[i].subst CompareTy.var ms)) →
        (∀ i, σ (modeAtom i) = encodeModes (actual η) i) →
        (b.theoryAt basisAtom headAtom modeAtom c).eval σ = true ∧
        ∀ t (_ht : InInterval (lower.atMode Mode.bottom) (upper.atMode Mode.top)
            (t.subst CompareTy.var ms)),
          ∀ m ∈ labels,
            booleanValue f ((.modal t m : CompareTy).subst CompareTy.var ms) =
              (c.modalWith modeAtom (.const (booleanValue f (t.subst CompareTy.var ms))) m).eval σ := by
  have hdefined : ∀ m ∈ b.modalPairs.map Prod.snd ++ labels, DefinedMode Δ (m.subst ms) := by
    intro m hm'
    rcases List.mem_append.mp hm' with hm' | hm'
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm'
      exact b.modalPairs_defined ms hm p hp
    · exact hd m hm'
  obtain ⟨c, η, hη, hmodal⟩ := observer_substituted_realizable f lower upper hlu hlo hhi
    ms actual hactual _ hdefined
  refine ⟨c, η, hη, ?_⟩
  intro σ basisAtom headAtom modeAtom hh hb hs
  constructor
  · apply b.theoryAt_of_modal basisAtom headAtom modeAtom c σ
      (fun t => booleanValue f (t.subst CompareTy.var ms)) (fun _ _ => rfl) (fun _ _ => rfl) hh hb
    intro a m hpair
    obtain ⟨ht, hlo', hhi'⟩ := hpairs (a, m) hpair
    exact hmodal σ modeAtom hs a ht hlo' hhi' m
      (List.mem_append_left _ (List.mem_map.mpr ⟨(a, m), hpair, rfl⟩))
  · intro t ht m hm'
    obtain ⟨ht, hlo', hhi'⟩ := ht
    exact hmodal σ modeAtom hs t ht hlo' hhi' m (List.mem_append_right _ hm')

end ModalityInference.ComparisonControls
