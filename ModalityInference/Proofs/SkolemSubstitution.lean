import ModalityInference.Proofs.SchemeFreshening
import ModalityInference.Proofs.ConstraintSubstitution

/-! Substitution by functions can replace fresh rigid variables in a proof.
Primitive bounds and modality models are transported separately, so an arbitrary
ambient bound list need not entail itself. -/
namespace ModalityInference

structure JudgmentMap (Δ Γ : Bounds) (ts : TypeVar → Ty) (ms : ModVar → ModExpr) : Prop where
  models : ∀ η, ModeModels Γ η → ∃ ξ,
    (∀ v, (ms v).eval (some ∘ η) = some (ξ v)) ∧ ModeModels Δ ξ
  bounds : ∀ a b, Constraint.sub a b ∈ Δ → Subtype Γ (a.subst ts ms) (b.subst ts ms)
  types : ∀ v, (ts v).DefinedUnder Γ

theorem JudgmentMap.submode {Δ Γ ts ms} (h : JudgmentMap Δ Γ ts ms)
    {m n} (hm : Submode Δ m n) : Submode Γ (m.subst ms) (n.subst ms) := by
  apply Submode.valid
  exact fun η hη =>
    let ⟨ξ, hv, hξ⟩ := h.models η hη
    let ⟨a, b, ha, hb, hab⟩ := hm.denote hξ
    ⟨a, b, by simpa only [ModExpr.eval_subst, funext hv] using ha,
      by simpa only [ModExpr.eval_subst, funext hv] using hb, hab⟩

theorem JudgmentMap.subtype {Δ Γ ts ms} (h : JudgmentMap Δ Γ ts ms)
    {a b} (ht : Subtype Δ a b) : Subtype Γ (a.subst ts ms) (b.subst ts ms) := by
  induction ht <;> dsimp only [TypeExpr.subst, ModExpr.subst]
  all_goals first
    | exact .refl
    | exact .trans ‹_› ‹_›
    | exact h.bounds _ _ ‹_›
    | exact .identity
    | exact .identityRev
    | exact .compose
    | exact .composeRev
    | exact .congr ‹_› (h.submode ‹_›)
    | exact .prod ‹_› ‹_›
    | exact .sum ‹_› ‹_›
    | exact .fn ‹_› ‹_› (h.submode ‹_›)

theorem JudgmentMap.defined {Δ Γ ts ms} (h : JudgmentMap Δ Γ ts ms)
    {m} (hm : Entails Δ (.defined m)) : Entails Γ (.defined (m.subst ms)) := by
  exact fun η hη =>
    let ⟨ξ, hv, hξ⟩ := h.models η hη
    by simpa only [ModExpr.WellFormed, ModExpr.eval_subst, funext hv] using hm ξ hξ

theorem JudgmentMap.type_defined {Δ Γ ts ms} (h : JudgmentMap Δ Γ ts ms)
    {a : Ty} (ha : a.DefinedUnder Δ) : (a.subst ts ms).DefinedUnder Γ := by
  induction a <;> simp_all only [TypeExpr.subst, TypeExpr.definedUnder_fn,
    TypeExpr.definedUnder_prod, TypeExpr.definedUnder_sum, TypeExpr.definedUnder_modal]
  all_goals first
    | exact h.types _
    | exact ⟨trivial, h.defined ha.2⟩
    | trivial
    | simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]

theorem JudgmentMap.entails {Δ Γ ts ms} (h : JudgmentMap Δ Γ ts ms)
    {c} (hc : Entails Δ c) : Entails Γ (c.subst ts ms) := by
  cases c
  case sub a b => exact ⟨h.subtype hc.1, h.type_defined hc.2.1, h.type_defined hc.2.2⟩
  case equal v a => exact ⟨h.subtype hc.1, h.subtype hc.2.1, h.types v, h.type_defined hc.2.2⟩
  case equiv a b =>
    exact ⟨h.subtype hc.1, h.subtype hc.2.1, h.type_defined hc.2.2.1, h.type_defined hc.2.2.2⟩
  case mode a b => exact h.submode hc
  case defined m => exact h.defined hc

theorem ModExpr.subst_subst (m : ModExpr) (σ τ : ModVar → ModExpr) :
    (m.subst σ).subst τ = m.subst (fun v => (σ v).subst τ) := by
  induction m <;> simp_all [ModExpr.subst]

theorem TypeExpr.subst_subst (a : Ty) (ts us : TypeVar → Ty) (ms ns : ModVar → ModExpr) :
    (a.subst ts ms).subst us ns =
      a.subst (fun v => (ts v).subst us ns) (fun v => (ms v).subst ns) := by
  induction a <;> simp_all [TypeExpr.subst, ModExpr.subst_subst]

theorem Constraint.subst_subst (c : Constraint) (ts us : TypeVar → Ty) (ms ns : ModVar → ModExpr) :
    (c.subst ts ms).subst us ns =
      c.subst (fun v => (ts v).subst us ns) (fun v => (ms v).subst ns) := by
  cases c <;> simp [Constraint.subst, TypeExpr.subst_subst, ModExpr.subst_subst]

theorem Substitution.constraint_subst (σ : Substitution) (c : Constraint)
    (ts : TypeVar → Ty) (ms : ModVar → ModExpr) :
    (σ.constraint c).subst ts ms = (c.subst σ.type σ.mode).subst ts ms := by
  cases c <;> try rfl
  case equal v a =>
    cases v
    case rigid n => rfl
    case flex n => cases he : σ.types.lookup n <;>
      simp [constraint, type, ty, he, Constraint.subst, TypeExpr.subst]

def Substitution.mapFunctions (σ : Substitution) (ts : TypeVar → Ty) (ms : ModVar → ModExpr) :
    Substitution :=
  {types := σ.types.map fun (n, a) => (n, a.subst ts ms)
   modes := σ.modes.map fun (n, m) => (n, m.subst ms)}

theorem Instantiates.mapFunctions {s : Scheme} {σ : Substitution} (h : Instantiates s σ)
    (ts : TypeVar → Ty) (ms : ModVar → ModExpr) : Instantiates s (σ.mapFunctions ts ms) := by
  simpa [Instantiates, Substitution.mapFunctions, List.map_map, Function.comp_def] using h

theorem Substitution.mapFunctions_type (σ : Substitution) (ts : TypeVar → Ty)
    (ms : ModVar → ModExpr) (v : TypeVar) (hv : ts v = .var v) :
    (σ.mapFunctions ts ms).type v = (σ.type v).subst ts ms := by
  cases v
  case rigid n => exact hv.symm
  case flex n =>
    simp only [mapFunctions, type, lookup_map_values]
    cases σ.types.lookup n <;> simp [TypeExpr.subst, hv]

theorem Substitution.mapFunctions_mode (σ : Substitution) (ts : TypeVar → Ty)
    (ms : ModVar → ModExpr) (v : ModVar) (hv : ms v = .var v) :
    (σ.mapFunctions ts ms).mode v = (σ.mode v).subst ms := by
  cases v with
  | rigid n => exact hv.symm
  | flex n =>
    simp only [mapFunctions, mode, lookup_map_values]
    cases σ.modes.lookup n <;> simp [ModExpr.subst, hv]

theorem Substitution.mapFunctions_ty (σ : Substitution) (ts : TypeVar → Ty)
    (ms : ModVar → ModExpr) (a : Ty)
    (ht : ∀ v ∈ a.typeVars, ts v = .var v) (hm : ∀ v ∈ a.modVars, ms v = .var v) :
    (σ.mapFunctions ts ms).ty a = (σ.ty a).subst ts ms := by
  simpa only [Substitution.ty, TypeExpr.subst_subst] using
    a.subst_congr (fun v hv => σ.mapFunctions_type ts ms v (ht v hv))
      (fun v hv => σ.mapFunctions_mode ts ms v (hm v hv))

theorem Substitution.mapFunctions_constraint_entails (σ : Substitution) (ts : TypeVar → Ty)
    (ms : ModVar → ModExpr) (c : Constraint) (Γ : Bounds)
    (ht : ∀ v ∈ c.typeVars, ts v = .var v) (hm : ∀ v ∈ c.modVars, ms v = .var v) :
    Entails Γ ((σ.mapFunctions ts ms).constraint c) ↔
      Entails Γ ((σ.constraint c).subst ts ms) := by
  rw [(σ.mapFunctions ts ms).constraint_subst_entails, σ.constraint_subst, Constraint.subst_subst]
  rw [c.subst_congr (fun v hv => σ.mapFunctions_type ts ms v (ht v hv))
    (fun v hv => σ.mapFunctions_mode ts ms v (hm v hv))]

theorem JudgmentMap.bounds_entails {Δ Γ ts ms} (h : JudgmentMap Δ Γ ts ms)
    (σ : Substitution) (cs : Bounds)
    (ht : ∀ v ∈ cs.typeVars, ts v = .var v) (hm : ∀ v ∈ cs.modVars, ms v = .var v)
    (hb : EntailsAll Δ (σ.bounds cs)) : EntailsAll Γ ((σ.mapFunctions ts ms).bounds cs) := by
  rintro _ hc
  obtain ⟨c, hmem, rfl⟩ := List.mem_map.mp hc
  exact (σ.mapFunctions_constraint_entails ts ms c Γ
    (fun v hv => ht v ((cs.mem_typeVars_iff v).mpr ⟨c, hmem, hv⟩))
    (fun v hv => hm v ((cs.mem_modVars_iff v).mpr ⟨c, hmem, hv⟩))).mpr
      (h.entails (hb _ (List.mem_map.mpr ⟨c, hmem, rfl⟩)))

theorem TypeExpr.wellFormedBounds_subst_subset (a : Ty) (ts : TypeVar → Ty) (ms : ModVar → ModExpr) :
    a.wellFormedBounds.map (Constraint.subst ts ms) ⊆ (a.subst ts ms).wellFormedBounds := by
  induction a <;> simp_all [TypeExpr.subst, TypeExpr.wellFormedBounds, Constraint.subst]

theorem TypeExpr.DefinedUnder.subst_function_guards {a : Ty} {ts : TypeVar → Ty}
    {ms : ModVar → ModExpr} {Δ} (h : (a.subst ts ms).DefinedUnder Δ) :
    EntailsAll Δ (a.wellFormedBounds.map (Constraint.subst ts ms)) :=
  fun c hc => ((a.subst ts ms).definedUnder_iff_entails_wellFormed Δ).mp h c
    (a.wellFormedBounds_subst_subset ts ms hc)

theorem Entails.subst_function_assumptions {c : Constraint} {ts : TypeVar → Ty}
    {ms : ModVar → ModExpr} {Δ} (h : Entails Δ (c.subst ts ms)) :
    EntailsAll Δ (c.assumptions.map (Constraint.subst ts ms)) := by
  cases c <;> simp only [Constraint.assumptions, List.map_cons, List.map_nil, List.map_append,
    EntailsAll, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
    forall_eq, or_imp, forall_and]
  case sub => exact ⟨⟨h, h.2.1.subst_function_guards⟩, h.2.2.subst_function_guards⟩
  case equiv => exact ⟨⟨⟨⟨h.1, h.2.2⟩, ⟨h.2.1, h.2.2.2, h.2.2.1⟩⟩,
    h.2.2.1.subst_function_guards⟩, h.2.2.2.subst_function_guards⟩
  case equal => exact ⟨⟨⟨h.1, h.2.2⟩, ⟨h.2.1, h.2.2.2, h.2.2.1⟩⟩,
    h.2.2.2.subst_function_guards⟩
  all_goals exact h

theorem EntailsAll.subst_function_assumptions {cs Δ : Bounds} {ts : TypeVar → Ty}
    {ms : ModVar → ModExpr} (h : EntailsAll Δ (cs.map (Constraint.subst ts ms))) :
    EntailsAll Δ (cs.assumptions.map (Constraint.subst ts ms)) := by
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  obtain ⟨c, hc, he⟩ := List.mem_flatMap.mp he
  exact (h _ (List.mem_map.mpr ⟨c, hc, rfl⟩)).subst_function_assumptions _
    (List.mem_map.mpr ⟨e, he, rfl⟩)

theorem ModeSatisfies.subst_functions (c : Constraint) (ts : TypeVar → Ty)
    (ms : ModVar → ModExpr) {η ξ : ModVar → Mode}
    (hv : ∀ v, (ms v).eval (some ∘ η) = some (ξ v)) :
    ModeSatisfies η (c.subst ts ms) ↔ ModeSatisfies ξ c := by
  cases c <;> simp only [Constraint.subst, ModeSatisfies, ModExpr.Below,
    ModExpr.WellFormed, ModExpr.eval_subst, funext hv] <;> rfl

theorem JudgmentMap.append_of_fixed {Δ cs : Bounds} {ts : TypeVar → Ty}
    {ms : ModVar → ModExpr} (ht : ∀ v ∈ Δ.typeVars, ts v = .var v)
    (hm : ∀ v ∈ Δ.modVars, ms v = .var v)
    (hdt : ∀ v, (ts v).DefinedUnder Δ)
    (hdm : ∀ v η, ModeModels Δ η → (ms v).WellFormed η)
    (hb : EntailsAll Δ (cs.map (Constraint.subst ts ms))) :
    JudgmentMap (Δ ++ cs) Δ ts ms := by
  refine ⟨?_, ?_, hdt⟩
  case refine_1 =>
    intro η hη
    let ξ := fun v => ((ms v).eval (some ∘ η)).getD Mode.identity
    have hv : ∀ v, (ms v).eval (some ∘ η) = some (ξ v) := fun v =>
      match Option.isSome_iff_exists.mp (hdm v η hη) with
      | ⟨m, he⟩ => by simp only [ξ, he, Option.getD_some]
    refine ⟨ξ, hv, ?_⟩
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (ModeModels.congr Δ (fun v hv =>
        show ξ v = η v by simp [ξ, hm v hv, ModExpr.eval])).mpr hη c hc
    · exact (ModeSatisfies.subst_functions c ts ms hv).mp
        (hb.modeModels hη _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
  case refine_2 =>
    intro a b hc
    rcases List.mem_append.mp hc with hc | hc
    · have he := (Constraint.sub a b).subst_congr
        (fun v hv => ht v ((Δ.mem_typeVars_iff v).mpr ⟨_, hc, hv⟩))
        (fun v hv => hm v ((Δ.mem_modVars_iff v).mpr ⟨_, hc, hv⟩))
      simp only [Constraint.subst, TypeExpr.subst_id, Constraint.sub.injEq] at he
      simpa only [he.1, he.2] using Subtype.bound hc
    · exact (hb _ (List.mem_map.mpr ⟨_, hc, rfl⟩)).1

end ModalityInference
