import ModalityInference.Proofs.InstanceDefinedness

/-! Defined generalized instances transport every solved consequence, including
through partial modality substitutions. -/
namespace ModalityInference

theorem Scheme.generalize_typeParams {cs : Bounds} {a : Ty} {n : Nat} :
    n ∈ (generalize cs a).typeParams ↔ .flex n ∈ a.typeVars ∪ cs.typeVars := by
  simp [generalize, List.mem_filterMap]
  exact ⟨fun ⟨v, hv, he⟩ => by cases v <;> simp_all, fun h => ⟨.flex n, h, rfl⟩⟩

theorem Scheme.generalize_modParams {cs : Bounds} {a : Ty} {n : Nat} :
    n ∈ (generalize cs a).modParams ↔ .flex n ∈ a.modVars ∪ cs.modVars := by
  simp [generalize, List.mem_filterMap]
  exact ⟨fun ⟨v, hv, he⟩ => by cases v <;> simp_all, fun h => ⟨.flex n, h, rfl⟩⟩

theorem Instantiates.generalize_type_defined {cs : Bounds} {a : Ty} {θ : Substitution} {Δ : Bounds}
    (hi : Instantiates (Scheme.generalize cs a) θ) (hb : EntailsAll Δ (θ.bounds cs))
    (hd : (θ.ty a).DefinedUnder Δ) (v : TypeVar) : (θ.type v).DefinedUnder Δ := by
  cases v with
  | rigid n => simp [Substitution.type, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]
  | flex n =>
    by_cases hn : n ∈ (Scheme.generalize cs a).typeParams
    · exact (Scheme.instance_support_defined (s := Scheme.generalize cs a) hb hd).1 _
        (Scheme.generalize_typeParams.mp hn)
    · rw [θ.type_fresh (fun h => hn (hi.1.mem_iff.mp h))]
      simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]

theorem Instantiates.generalize_mode_defined {cs : Bounds} {a : Ty} {θ : Substitution} {Δ : Bounds}
    (hi : Instantiates (Scheme.generalize cs a) θ) (hb : EntailsAll Δ (θ.bounds cs))
    (hd : (θ.ty a).DefinedUnder Δ) (v : ModVar) : Entails Δ (.defined (θ.mode v)) := by
  cases v with
  | rigid n => exact fun _ _ => rfl
  | flex n =>
    by_cases hn : n ∈ (Scheme.generalize cs a).modParams
    · exact (Scheme.instance_support_defined (s := Scheme.generalize cs a) hb hd).2 _
        (Scheme.generalize_modParams.mp hn)
    · rw [θ.mode_fresh (fun h => hn (hi.2.mem_iff.mp h))]
      exact fun _ _ => rfl

theorem JudgmentMap.of_entails {Ξ Δ : Bounds} {ts : TypeVar → Ty} {ms : ModVar → ModExpr}
    (ht : ∀ v, (ts v).DefinedUnder Δ)
    (hm : ∀ v, Entails Δ (.defined (ms v)))
    (hb : EntailsAll Δ (Ξ.map (Constraint.subst ts ms))) : JudgmentMap Ξ Δ ts ms := by
  refine ⟨?_, fun a b hc => (hb _ (List.mem_map.mpr ⟨.sub a b, hc, rfl⟩)).1, ht⟩
  intro η hη
  choose ξ hξ using fun v => Option.isSome_iff_exists.mp (hm v η hη)
  exact ⟨ξ, hξ, fun c hc => (ModeSatisfies.subst_functions c ts ms hξ).mp
    (hb.modeModels hη _ (List.mem_map.mpr ⟨c, hc, rfl⟩))⟩

theorem Substitution.WellFormedUnder.judgmentMap {Ξ Δ : Bounds} {θ : Substitution}
    (hθ : θ.WellFormedUnder Δ) (hb : EntailsAll Δ (θ.bounds Ξ)) :
    JudgmentMap Ξ Δ θ.type θ.mode := by
  apply JudgmentMap.of_entails hθ.types hθ.modes
  exact fun _ h => let ⟨c, hc, he⟩ := List.mem_map.mp h
    he ▸ (θ.constraint_subst_entails c Δ).mp (hb _ (List.mem_map.mpr ⟨c, hc, rfl⟩))

theorem Instantiates.generalize_judgmentMap {cs : Bounds} {a : Ty} {θ : Substitution} {Δ : Bounds}
    (hi : Instantiates (Scheme.generalize cs a) θ) (hb : EntailsAll Δ (θ.bounds cs))
    (hd : (θ.ty a).DefinedUnder Δ) : JudgmentMap cs Δ θ.type θ.mode := by
  apply JudgmentMap.of_entails (hi.generalize_type_defined hb hd) (hi.generalize_mode_defined hb hd)
  exact fun _ h => let ⟨c, hc, he⟩ := List.mem_map.mp h
    he ▸ (θ.constraint_subst_entails c Δ).mp (hb _ (List.mem_map.mpr ⟨c, hc, rfl⟩))

theorem JudgmentMap.entails_substituted_bounds {Ξ Δ cs : Bounds} {θ : Substitution}
    (h : JudgmentMap Ξ Δ θ.type θ.mode) (hb : EntailsAll Ξ cs) :
    EntailsAll Δ (θ.bounds cs) := by
  exact fun _ hc => let ⟨c, hc, he⟩ := List.mem_map.mp hc
    he ▸ (θ.constraint_subst_entails c Δ).mpr (h.entails (hb c hc))

theorem Solution.generalize_instance {cs residual Δ : Bounds} {a : Ty} {σ θ : Substitution}
    (hs : Solution cs residual σ) (hi : Instantiates (Scheme.generalize residual (σ.ty a)) θ)
    (hb : EntailsAll Δ (θ.bounds residual)) (hd : (θ.ty (σ.ty a)).DefinedUnder Δ) :
    Solution cs Δ (θ.compose σ) := by
  simpa only [Solution, Substitution.bounds_compose] using
    (hi.generalize_judgmentMap hb hd).entails_substituted_bounds hs

theorem Substitution.WellFormedUnder.compose_of_entails {Ξ Δ : Bounds} {σ θ : Substitution}
    (hσ : σ.WellFormedUnder Ξ) (hθ : θ.WellFormedUnder Δ)
    (hb : EntailsAll Δ (θ.bounds Ξ)) : (θ.compose σ).WellFormedUnder Δ := by
  exact ⟨fun v => by simpa only [Substitution.type_compose] using
    (hθ.judgmentMap hb).type_defined (hσ.types v),
    fun v => by simpa only [Substitution.mode_compose] using
      (hθ.judgmentMap hb).defined (hσ.modes v)⟩

end ModalityInference
