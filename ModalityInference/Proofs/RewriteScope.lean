import ModalityInference.Proofs.RewriteModels
import ModalityInference.Proofs.VariableOccurrences

namespace ModalityInference

private theorem mem_of_lookup {xs : List (Nat × α)} {n a} (h : xs.lookup n = some a) :
    (n,a) ∈ xs := by
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp h
  simp [he]

theorem RewriteConfig.type_image_scoped (s : RewriteConfig) {v} (hv : v ∈ s.typeVars) :
    (s.substitution.type v).Scoped ⟨s.typeVars, s.modVars⟩ := by
  cases v
  case rigid n => simpa [Substitution.type, TypeExpr.Scoped, TypeExpr.typeVars, TypeExpr.modVars] using hv
  case flex n =>
    cases hl : s.substitution.types.lookup n
    case none => simpa [Substitution.type, hl, TypeExpr.Scoped, TypeExpr.typeVars, TypeExpr.modVars] using hv
    case some a =>
      have ha := mem_of_lookup hl
      simp only [Substitution.type, hl, Option.getD_some, TypeExpr.Scoped]
      constructor
      · intro w hw
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_flatMap.mpr
          ⟨(n,a), ha, List.mem_cons_of_mem _ ((a.mem_typeVariables w).mpr hw)⟩))
      · intro w hw
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨(n,a), ha, (a.mem_modeVariables w).mpr hw⟩)))

theorem RewriteConfig.mode_image_scoped (s : RewriteConfig) {v} (hv : v ∈ s.modVars) :
    (s.substitution.mode v).vars ⊆ s.modVars := by
  cases v
  case rigid n => simpa [Substitution.mode, ModExpr.vars] using hv
  case flex n =>
    cases hl : s.substitution.modes.lookup n
    case none => simpa [Substitution.mode, hl, ModExpr.vars] using hv
    case some m =>
      have hm := mem_of_lookup hl
      simp only [Substitution.mode, hl, Option.getD_some]
      intro w hw
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨(n,m), hm, List.mem_cons_of_mem _ ((m.mem_freeVariables w).mpr hw)⟩)))

@[simp] theorem RewriteConfig.typeVars_pending_cons (s : RewriteConfig) (c : Constraint) :
    ({s with pending := c :: s.pending} : RewriteConfig).typeVars = c.typeVars ∪ s.typeVars := by
  change Bounds.typeVars (c :: s.constraints) ∪ _ = _
  rw [Bounds.typeVars_cons, Finset.union_assoc]
  rfl

@[simp] theorem RewriteConfig.modVars_pending_cons (s : RewriteConfig) (c : Constraint) :
    ({s with pending := c :: s.pending} : RewriteConfig).modVars = c.modVars ∪ s.modVars := by
  change Bounds.modVars (c :: s.constraints) ∪ _ = _
  rw [Bounds.modVars_cons, Finset.union_assoc]
  rfl

namespace Deferred

theorem ConfigModels.expand {scope ρ c shape v} {s : RewriteConfig}
    (hf : FreshFor c shape s) (hv : v ∈ c.typeVars)
    (ht : scope.types ⊆ c.typeVars ∪ s.typeVars) (hm : scope.modes ⊆ c.modVars ∪ s.modVars)
    (hex : ∀ η, GroundSatisfies η c → ∃ ζ, shape.realize ζ = some (η.types v) ∧
      (∀ w, w ∉ shape.typeVars → ζ.types w = η.types w) ∧
      (∀ w, w ∉ shape.modVars → ζ.modes w = η.modes w)) :
    ConfigModels scope {s with pending := c :: s.pending} ρ ↔
      ConfigModels scope {s with pending := .equal v shape :: c :: s.pending} ρ := by
  constructor
  · rintro ⟨η, hη, htypes, hmodes⟩
    let old : RewriteConfig := {s with pending := c :: s.pending}
    obtain ⟨ζ, hshape, houtsideT, houtsideM⟩ := hex η (hη c (by simp [RewriteConfig.constraints]))
    have hsameT : ∀ w ∈ old.typeVars, ζ.types w = η.types w := by
      simpa only [old, RewriteConfig.typeVars_pending_cons] using
        (fun w hw => houtsideT w (fun hshape => hf.1 w hshape hw))
    have hsameM : ∀ w ∈ old.modVars, ζ.modes w = η.modes w := by
      simpa only [old, RewriteConfig.modVars_pending_cons] using
        (fun w hw => houtsideM w (fun hshape => hf.2 w hshape hw))
    have hmodel : GroundModels ζ old.constraints :=
      (GroundModels.congr old.constraints
        (fun w hw => hsameT w (Finset.mem_union_left _ hw))
        (fun w hw => hsameM w (Finset.mem_union_left _ hw))).mpr hη
    refine ⟨ζ, ?_, ?_, ?_⟩
    · change GroundModels ζ (.equal v shape :: old.constraints)
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · refine ⟨η.types v, hshape, ?_⟩
        have he : ζ.types v = η.types v := houtsideT v (fun hs => hf.1 v hs (Finset.mem_union_left _ hv))
        simpa [he] using (Subtype.refl (Δ := []) (a := (η.types v).reify))
      · exact hmodel d hd
    · intro w hw
      have hscope := old.type_image_scoped (show w ∈ old.typeVars by simpa [old] using ht hw)
      have he := (s.substitution.type w).realize_congr
        (fun v hv => hsameT v (hscope.1 hv)) (fun v hv => hsameM v (hscope.2 hv))
      simpa only [he] using htypes w hw
    · intro w hw
      have hscope := old.mode_image_scoped (show w ∈ old.modVars by simpa [old] using hm hw)
      have he := (s.substitution.mode w).eval_congr (σ := some ∘ ζ.modes) (τ := some ∘ η.modes)
        (fun v hv => congrArg some (hsameM v (hscope hv)))
      simpa only [he] using hmodes w hw
  · rintro ⟨η, hη, htypes, hmodes⟩
    exact ⟨η, fun d hd => hη d (List.mem_cons_of_mem _ hd), htypes, hmodes⟩

end Deferred
end ModalityInference
