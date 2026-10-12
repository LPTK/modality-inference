import ModalityInference.Proofs.Grounding

/-! Ground interpretation depends only on occurring identifiers. Fresh scheme
quantifiers therefore preserve the surrounding constraints and symbolic locks.
-/
namespace ModalityInference

theorem ModExpr.eval_congr (m : ModExpr) {σ τ : ModVar → Option Mode}
    (h : ∀ v ∈ m.vars, σ v = τ v) : m.eval σ = m.eval τ := by
  induction m <;> simp_all [ModExpr.vars, ModExpr.eval, Finset.mem_union, or_imp, forall_and]

theorem TypeExpr.realize_congr (t : Ty) {ρ η : GroundAssignment}
    (ht : ∀ v ∈ t.typeVars, ρ.types v = η.types v)
    (hm : ∀ v ∈ t.modVars, ρ.modes v = η.modes v) : t.realize ρ = t.realize η := by
  induction t <;> simp_all [TypeExpr.typeVars, TypeExpr.modVars,
    TypeExpr.realize, Finset.mem_union, or_imp, forall_and]
  rw [ModExpr.eval_congr _ (σ := some ∘ ρ.modes) (τ := some ∘ η.modes)
    (fun v hv => congrArg some (hm.2 v hv))]

theorem GroundSatisfies.congr (c : Constraint) {ρ η : GroundAssignment}
    (ht : ∀ v ∈ c.typeVars, ρ.types v = η.types v)
    (hm : ∀ v ∈ c.modVars, ρ.modes v = η.modes v) :
    GroundSatisfies ρ c ↔ GroundSatisfies η c := by
  cases c <;> simp only [Constraint.typeVars, Constraint.modVars, Finset.mem_union,
    Finset.mem_insert, or_imp, forall_and, forall_eq] at ht hm
  case sub a b | equiv a b =>
    simp only [GroundSatisfies, a.realize_congr ht.1 hm.1, b.realize_congr ht.2 hm.2]
  case equal v t => simp only [GroundSatisfies, t.realize_congr ht.2 hm, ht.1]
  case mode m n =>
    simp only [GroundSatisfies, ModExpr.Below,
      m.eval_congr (σ := some ∘ ρ.modes) (τ := some ∘ η.modes)
        (fun v hv => congrArg some (hm.1 v hv)),
      n.eval_congr (σ := some ∘ ρ.modes) (τ := some ∘ η.modes)
        (fun v hv => congrArg some (hm.2 v hv))]
  case defined m =>
    simp only [GroundSatisfies, ModExpr.WellFormed,
      m.eval_congr (σ := some ∘ ρ.modes) (τ := some ∘ η.modes)
        (fun v hv => congrArg some (hm v hv))]

@[simp] theorem Bounds.typeVars_cons (c : Constraint) (cs : Bounds) :
    Bounds.typeVars (c :: cs) = c.typeVars ∪ cs.typeVars := by
  simp [Bounds.typeVars, ← List.foldl_map, ← List.foldl_assoc, Finset.union_comm]

@[simp] theorem Bounds.modVars_cons (c : Constraint) (cs : Bounds) :
    Bounds.modVars (c :: cs) = c.modVars ∪ cs.modVars := by
  simp [Bounds.modVars, ← List.foldl_map, ← List.foldl_assoc, Finset.union_comm]

theorem GroundModels.congr (Δ : Bounds) {ρ η : GroundAssignment}
    (ht : ∀ v ∈ Δ.typeVars, ρ.types v = η.types v)
    (hm : ∀ v ∈ Δ.modVars, ρ.modes v = η.modes v) :
    GroundModels ρ Δ ↔ GroundModels η Δ := by
  induction Δ <;> simp_all [Bounds.typeVars_cons, Bounds.modVars_cons,
    Finset.mem_union, or_imp, forall_and, GroundModels]
  exact fun _ => GroundSatisfies.congr _ ht.1 hm.1

theorem GroundInstantiates.models_fresh {ρ η s Δ} (h : GroundInstantiates ρ s η)
    (hf : s.FreshForBounds Δ) (hΔ : GroundModels ρ Δ) : GroundModels η Δ := by
  exact (GroundModels.congr Δ
    (fun v hv => h.1 v (fun hp =>
      let ⟨n, hn, he⟩ := List.mem_map.mp hp
      hf.1 n hn (he.symm ▸ hv)))
    (fun v hv => h.2.1 v (fun hp =>
      let ⟨n, hn, he⟩ := List.mem_map.mp hp
      hf.2 n hn (he.symm ▸ hv)))).mpr hΔ

theorem GroundInstantiates.eval_fresh {ρ η s m} (h : GroundInstantiates ρ s η)
    (hf : s.FreshForMode m) : m.eval (some ∘ η.modes) = m.eval (some ∘ ρ.modes) := by
  exact m.eval_congr (fun v hv => congrArg some (h.2.1 v (fun hp =>
    let ⟨n, hn, he⟩ := List.mem_map.mp hp
    hf n hn (he.symm ▸ hv))))

end ModalityInference
