import ModalityInference.Proofs.Normalization
import ModalityInference.Proofs.ConstraintModels
import ModalityInference.Proofs.SubstitutionSupport

/-! Transport of declarative entailment through contexts and the solver's
type-only substitutions. Explicit assumptions preserve entailment under arbitrary
substitutions; transport of other consequences retains image-definedness premises. -/
namespace ModalityInference

theorem Submode.of_entails {Δ Γ a b} (h : Submode Δ a b) (hΔ : EntailsAll Γ Δ) :
    Submode Γ a b := .valid fun _ hη => h.denote (hΔ.modeModels hη)

theorem Subtype.of_entails {Δ Γ a b} (h : Subtype Δ a b) (hΔ : EntailsAll Γ Δ) :
    Subtype Γ a b := by
  induction h
  case bound a b hc => exact (hΔ _ hc).1
  all_goals first
    | exact .refl
    | exact .trans ‹_› ‹_›
    | exact .identity
    | exact .identityRev
    | exact .compose
    | exact .composeRev
    | exact .congr ‹_› (Submode.of_entails ‹_› hΔ)
    | exact .prod ‹_› ‹_›
    | exact .sum ‹_› ‹_›
    | exact .fn ‹_› ‹_› (Submode.of_entails ‹_› hΔ)
    | exact .credit (Submode.of_entails ‹_› hΔ)

theorem TypeExpr.DefinedUnder.of_entails {Δ Γ} {a : Ty} (h : a.DefinedUnder Δ)
    (hΔ : EntailsAll Γ Δ) : a.DefinedUnder Γ := fun _ hη => h _ (hΔ.modeModels hη)

theorem Entails.of_entails {Δ Γ c} (h : Entails Δ c) (hΔ : EntailsAll Γ Δ) :
    Entails Γ c := by
  cases c with
  | sub a b => exact ⟨h.1.of_entails hΔ, TypeExpr.DefinedUnder.of_entails h.2.1 hΔ,
      TypeExpr.DefinedUnder.of_entails h.2.2 hΔ⟩
  | mode a b => exact Submode.of_entails h hΔ
  | defined a => exact fun _ hη => h _ (hΔ.modeModels hη)
  | equal v a => exact ⟨h.1.of_entails hΔ, h.2.1.of_entails hΔ,
      TypeExpr.DefinedUnder.of_entails h.2.2 hΔ⟩
  | equiv a b => exact ⟨h.1.of_entails hΔ, h.2.1.of_entails hΔ,
      TypeExpr.DefinedUnder.of_entails h.2.2.1 hΔ, TypeExpr.DefinedUnder.of_entails h.2.2.2 hΔ⟩

theorem EntailsAll.trans {Δ Γ cs} (h : EntailsAll Δ cs) (hΔ : EntailsAll Γ Δ) :
    EntailsAll Γ cs := fun c hc => (h c hc).of_entails hΔ

theorem Substitution.mode_eq_var {σ : Substitution} (hm : σ.modes = []) :
    σ.mode = ModExpr.var := by
  funext v
  cases v <;> simp [Substitution.mode, hm]

theorem Substitution.modeSatisfies_types {σ : Substitution} (hm : σ.modes = [])
    (c : Constraint) (η : ModVar → Mode) :
    ModeSatisfies η (σ.constraint c) ↔ ModeSatisfies η c := by
  cases c <;> simp [Substitution.constraint, Constraint.subst, ModeSatisfies, σ.mode_eq_var hm]
  rename_i v a
  cases v with
  | rigid n => trivial
  | flex n => cases he : σ.types.lookup n <;> simp [he]

theorem Substitution.modeModels_types {σ : Substitution} (hm : σ.modes = [])
    (cs : Bounds) (η : ModVar → Mode) : ModeModels (σ.bounds cs) η ↔ ModeModels cs η := by
  simp only [ModeModels, Substitution.bounds, List.forall_mem_map, σ.modeSatisfies_types hm]

theorem TypeExpr.definedUnder_substitute_types {σ : Substitution} (hm : σ.modes = [])
    (a : Ty) (Δ : Bounds) :
    (σ.ty a).DefinedUnder Δ ↔
      a.DefinedUnder Δ ∧ ∀ v ∈ a.typeVars, (σ.type v).DefinedUnder Δ := by
  induction a <;> simp_all [Substitution.ty, TypeExpr.subst, σ.mode_eq_var hm,
    TypeExpr.typeVars, or_imp, forall_and, and_assoc, and_left_comm, and_comm]
  simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]

theorem Subtype.substitute_types {Δ Γ a b} {σ : Substitution} (h : Subtype Δ a b)
    (hm : σ.modes = []) (hΔ : EntailsAll Γ (σ.bounds Δ)) :
    Subtype Γ (σ.ty a) (σ.ty b) :=
  (h.substitute σ (fun η _ v => by simp [σ.mode_eq_var hm, ModExpr.WellFormed, ModExpr.eval])).of_entails hΔ

theorem TypeExpr.DefinedUnder.substitute_types {Δ Γ} {σ : Substitution} {a : Ty} (h : a.DefinedUnder Δ)
    (hm : σ.modes = []) (hΔ : EntailsAll Γ (σ.bounds Δ))
    (ht : ∀ v ∈ a.typeVars, (σ.type v).DefinedUnder Γ) : (σ.ty a).DefinedUnder Γ :=
  (a.definedUnder_substitute_types hm Γ).mpr
    ⟨fun η hη => h η ((σ.modeModels_types hm Δ η).mp (hΔ.modeModels hη)), ht⟩

theorem Entails.substitute_types {Δ Γ c} {σ : Substitution} (h : Entails Δ c)
    (hm : σ.modes = []) (hΔ : EntailsAll Γ (σ.bounds Δ))
    (ht : ∀ v ∈ c.typeVars, (σ.type v).DefinedUnder Γ) : Entails Γ (σ.constraint c) := by
  cases c with
  | sub a b =>
    exact ⟨h.1.substitute_types hm hΔ,
      TypeExpr.DefinedUnder.substitute_types h.2.1 hm hΔ (fun v hv => ht v (by simp [Constraint.typeVars, hv])),
      TypeExpr.DefinedUnder.substitute_types h.2.2 hm hΔ (fun v hv => ht v (by simp [Constraint.typeVars, hv]))⟩
  | equiv a b =>
    exact ⟨h.1.substitute_types hm hΔ, h.2.1.substitute_types hm hΔ,
      TypeExpr.DefinedUnder.substitute_types h.2.2.1 hm hΔ (fun v hv => ht v (by simp [Constraint.typeVars, hv])),
      TypeExpr.DefinedUnder.substitute_types h.2.2.2 hm hΔ (fun v hv => ht v (by simp [Constraint.typeVars, hv]))⟩
  | mode a b =>
    change Submode Γ (a.subst σ.mode) (b.subst σ.mode)
    rw [σ.mode_eq_var hm, ModExpr.subst_id, ModExpr.subst_id]
    exact .valid fun η hη => h.denote ((σ.modeModels_types hm Δ η).mp (hΔ.modeModels hη))
  | defined a =>
    simp only [Substitution.constraint, Constraint.subst, σ.mode_eq_var hm, ModExpr.subst_id]
    exact fun η hη => h η ((σ.modeModels_types hm Δ η).mp (hΔ.modeModels hη))
  | equal v a =>
    have hleft : Subtype Γ (σ.type v) (σ.ty a) := h.1.substitute_types hm hΔ
    have hright : Subtype Γ (σ.ty a) (σ.type v) := h.2.1.substitute_types hm hΔ
    have ha := TypeExpr.DefinedUnder.substitute_types h.2.2 hm hΔ
      (fun w hw => ht w (by simp [Constraint.typeVars, hw]))
    have hv := ht v (by simp [Constraint.typeVars])
    cases v with
    | rigid n => exact ⟨hleft, hright, ha⟩
    | flex n =>
      cases he : σ.types.lookup n <;>
        simp only [Substitution.constraint, he, Substitution.type,
          Option.getD_none, Option.getD_some] at hleft hright hv ⊢
      · exact ⟨hleft, hright, ha⟩
      · exact ⟨hleft, hright, hv, ha⟩

theorem EntailsAll.substitute_types {Δ Γ cs} {σ : Substitution} (h : EntailsAll Δ cs)
    (hm : σ.modes = []) (hΔ : EntailsAll Γ (σ.bounds Δ))
    (ht : ∀ v ∈ cs.typeVars, (σ.type v).DefinedUnder Γ) : EntailsAll Γ (σ.bounds cs) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact (h d hd).substitute_types hm hΔ fun v hv => ht v ((cs.mem_typeVars_iff v).mpr ⟨d, hd, hv⟩)

theorem TypeExpr.wellFormedBounds_is_defined (a : Ty) :
    ∀ c ∈ a.wellFormedBounds, ∃ m, c = .defined m := by
  induction a <;> simp_all [TypeExpr.wellFormedBounds, or_imp]

theorem TypeExpr.definedUnder_iff_entails_wellFormed (a : Ty) (Δ : Bounds) :
    a.DefinedUnder Δ ↔ EntailsAll Δ a.wellFormedBounds := by
  constructor
  · intro h c hc
    obtain ⟨m, rfl⟩ := a.wellFormedBounds_is_defined c hc
    exact fun η hη => h η hη (.defined m) hc
  · exact fun h _ hη => h.modeModels hη

/-- The existing per-constraint assumption contexts, combined over a worklist. -/
def Bounds.assumptions (cs : Bounds) : Bounds := cs.flatMap Constraint.assumptions

theorem Bounds.assumptions_entails (cs : Bounds) : EntailsAll cs.assumptions cs := by
  intro c hc
  exact c.assumptions_entail fun _ hd => List.mem_flatMap.mpr ⟨c, hc, hd⟩

theorem Substitution.wellFormedBounds_fixed {σ : Substitution} (hm : σ.modes = []) (a : Ty) :
    σ.bounds a.wellFormedBounds = a.wellFormedBounds := by
  refine (List.map_congr_left (g := id) ?_).trans (List.map_id _)
  intro c hc
  obtain ⟨m, rfl⟩ := a.wellFormedBounds_is_defined c hc
  simp [Substitution.constraint, Constraint.subst, σ.mode_eq_var hm]

theorem Substitution.wellFormedBounds_subset (σ : Substitution) (a : Ty) :
    σ.bounds a.wellFormedBounds ⊆ (σ.ty a).wellFormedBounds := by
  induction a <;> simp_all [Substitution.bounds, Substitution.ty, TypeExpr.subst,
    TypeExpr.wellFormedBounds, Substitution.constraint, Constraint.subst]

theorem TypeExpr.DefinedUnder.subst_guards {σ : Substitution} {a : Ty} {Δ}
    (h : (σ.ty a).DefinedUnder Δ) : EntailsAll Δ (σ.bounds a.wellFormedBounds) :=
  fun c hc => ((σ.ty a).definedUnder_iff_entails_wellFormed Δ).mp h c
    (σ.wellFormedBounds_subset a hc)

theorem TypeExpr.DefinedUnder.substituted_guards {σ : Substitution} {a : Ty} {Δ}
    (h : (σ.ty a).DefinedUnder Δ) (_hm : σ.modes = []) :
    EntailsAll Δ (σ.bounds a.wellFormedBounds) := h.subst_guards

theorem Substitution.equal_entails (σ : Substitution) (Δ : Bounds) (v : TypeVar) (a : Ty) :
    Entails Δ (σ.constraint (.equal v a)) ↔
      Entails Δ (.sub (σ.type v) (σ.ty a)) ∧ Entails Δ (.sub (σ.ty a) (σ.type v)) := by
  cases v with
  | rigid n =>
    simp [Substitution.constraint, Substitution.type, Entails, TypeExpr.DefinedUnder,
      TypeExpr.wellFormedBounds, ModeModels, and_left_comm, and_comm]
  | flex n =>
    cases he : σ.types.lookup n <;>
      simp [Substitution.constraint, Substitution.type, he, Entails, TypeExpr.DefinedUnder,
        TypeExpr.wellFormedBounds, ModeModels, and_left_comm, and_comm]

theorem Entails.subst_assumptions {Δ c} {σ : Substitution}
    (h : Entails Δ (σ.constraint c)) :
    EntailsAll Δ (σ.bounds c.assumptions) := by
  cases c
  case sub a b =>
    have ha := TypeExpr.DefinedUnder.subst_guards h.2.1
    have hb := TypeExpr.DefinedUnder.subst_guards h.2.2
    simpa only [Constraint.assumptions, Substitution.bounds, List.map_cons, List.map_nil,
      List.map_append, EntailsAll, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, or_imp, forall_and] using And.intro (And.intro h ha) hb
  case equiv a b =>
    have ha := TypeExpr.DefinedUnder.subst_guards h.2.2.1
    have hb := TypeExpr.DefinedUnder.subst_guards h.2.2.2
    have hab : Entails Δ (.sub (σ.ty a) (σ.ty b)) := ⟨h.1, h.2.2⟩
    have hba : Entails Δ (.sub (σ.ty b) (σ.ty a)) := ⟨h.2.1, h.2.2.2, h.2.2.1⟩
    simpa only [Constraint.assumptions, Substitution.bounds, List.map_cons, List.map_nil,
      List.map_append, Substitution.constraint, Constraint.subst,
      EntailsAll, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, or_imp, forall_and] using And.intro (And.intro ⟨hab, hba⟩ ha) hb
  case equal v a =>
    have hab := (σ.equal_entails Δ v a).mp h
    have ha := TypeExpr.DefinedUnder.subst_guards hab.1.2.2
    simpa only [Constraint.assumptions, Substitution.bounds, List.map_cons, List.map_nil,
      List.map_append, Substitution.constraint, Constraint.subst, Substitution.ty, TypeExpr.subst,
      EntailsAll, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, or_imp, forall_and] using And.intro hab ha
  all_goals simpa only [Constraint.assumptions, Substitution.bounds, List.map_cons,
    List.map_nil, EntailsAll, List.mem_singleton, forall_eq] using h

theorem Entails.substituted_assumptions {Δ c} {σ : Substitution}
    (h : Entails Δ (σ.constraint c)) (_hm : σ.modes = []) :
    EntailsAll Δ (σ.bounds c.assumptions) := h.subst_assumptions

theorem Entails.of_subst_assumptions {Δ c} {σ : Substitution}
    (h : EntailsAll Δ (σ.bounds c.assumptions)) : Entails Δ (σ.constraint c) := by
  cases c <;> simp only [Constraint.assumptions, Substitution.bounds, List.map_cons,
    List.map_nil, List.map_append, EntailsAll, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false, forall_eq, or_imp, forall_and] at h
  case equal v a =>
    exact (σ.equal_entails Δ v a).mpr h.1
  case equiv a b => exact ⟨h.1.1.1.1, h.1.1.2.1, h.1.1.1.2⟩
  case sub a b => exact h.1.1
  all_goals exact h

theorem EntailsAll.subst_assumptions {Δ cs} {σ : Substitution}
    (h : EntailsAll Δ (σ.bounds cs)) :
    EntailsAll Δ (σ.bounds cs.assumptions) := by
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  obtain ⟨c, hc, he⟩ := List.mem_flatMap.mp he
  exact (h _ (List.mem_map.mpr ⟨c, hc, rfl⟩)).subst_assumptions _
    (List.mem_map.mpr ⟨e, he, rfl⟩)

theorem EntailsAll.substituted_assumptions {Δ cs} {σ : Substitution}
    (h : EntailsAll Δ (σ.bounds cs)) (_hm : σ.modes = []) :
    EntailsAll Δ (σ.bounds cs.assumptions) := h.subst_assumptions

theorem EntailsAll.of_subst_assumptions {Δ cs} {σ : Substitution}
    (h : EntailsAll Δ (σ.bounds cs.assumptions)) : EntailsAll Δ (σ.bounds cs) := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  exact Entails.of_subst_assumptions fun d hd => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact h _ (List.mem_map.mpr ⟨e, List.mem_flatMap.mpr ⟨c, hc, he⟩, rfl⟩)

theorem Substitution.bounds_assumptions_entails (σ : Substitution) (cs Δ : Bounds) :
    EntailsAll Δ (σ.bounds cs.assumptions) ↔ EntailsAll Δ (σ.bounds cs) :=
  ⟨EntailsAll.of_subst_assumptions, EntailsAll.subst_assumptions⟩

/-- A consequence valid in every ambient context survives a type-only
substitution when the type images appearing in its conclusion are defined. -/
theorem Entails.consequence_substitute_types {cs c Δ} {σ : Substitution}
    (hc : ∀ Γ, EntailsAll Γ cs → Entails Γ c) (hm : σ.modes = [])
    (hs : EntailsAll Δ (σ.bounds cs))
    (ht : ∀ v ∈ c.typeVars, (σ.type v).DefinedUnder Δ) : Entails Δ (σ.constraint c) :=
  (hc cs.assumptions cs.assumptions_entails).substitute_types hm
    (hs.substituted_assumptions hm) ht

theorem Entails.substituted_images_defined {Δ c} {σ : Substitution}
    (h : Entails Δ (σ.constraint c)) (hm : σ.modes = []) :
    ∀ v ∈ c.typeVars, (σ.type v).DefinedUnder Δ := by
  cases c
  case sub a b =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ((a.definedUnder_substitute_types hm Δ).mp h.2.1).2 v hv
    · exact ((b.definedUnder_substitute_types hm Δ).mp h.2.2).2 v hv
  case equiv a b =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ((a.definedUnder_substitute_types hm Δ).mp h.2.2.1).2 v hv
    · exact ((b.definedUnder_substitute_types hm Δ).mp h.2.2.2).2 v hv
  case equal v a =>
    have hab := (σ.equal_entails Δ v a).mp h
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hab.1.2.1
    · exact ((a.definedUnder_substitute_types hm Δ).mp hab.1.2.2).2 w hw
  all_goals simp [Constraint.typeVars]

theorem Entails.equivalent_substitute_types {c d Δ} {σ : Substitution}
    (he : ∀ Γ, Entails Γ c ↔ Entails Γ d) (hv : c.typeVars = d.typeVars)
    (hm : σ.modes = []) : Entails Δ (σ.constraint c) ↔ Entails Δ (σ.constraint d) := by
  constructor
  · intro h
    apply Entails.consequence_substitute_types (cs := [c])
      (fun Γ hΓ => (he Γ).mp (hΓ c (by simp))) hm
      (by simpa [EntailsAll, Substitution.bounds] using h)
    exact fun v hh => h.substituted_images_defined hm v (hv ▸ hh)
  · intro h
    apply Entails.consequence_substitute_types (cs := [d])
      (fun Γ hΓ => (he Γ).mpr (hΓ d (by simp))) hm
      (by simpa [EntailsAll, Substitution.bounds] using h)
    exact fun v hh => h.substituted_images_defined hm v (hv ▸ hh)

end ModalityInference
