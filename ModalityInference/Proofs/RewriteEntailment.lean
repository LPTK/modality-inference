import ModalityInference.Proofs.SolverExtension
import ModalityInference.Proofs.ReductionEntailment

/-! Symbolic soundness of abstract constraint rewriting, including the
definedness obligations retained by recording and hypothesis discharge. -/
namespace ModalityInference

theorem Substitution.extendType_constraint_entails {σ : Substitution} {n a}
    (hn : n ∉ σ.types.map Prod.fst) (c : Constraint) (Δ : Bounds) :
    Entails Δ ((σ.extendType n a).constraint c) ↔
      Entails Δ (({types := [(n, a)]} : Substitution).constraint (σ.constraint c)) := by
  rw [Substitution.constraint_compose]
  apply Substitution.constraint_entails_congr
  · exact funext fun v => (Substitution.extendType_type hn v).trans
      (Substitution.type_compose v σ _).symm
  · funext v
    rw [Substitution.mode_compose]
    change σ.mode v = (σ.mode v).subst _
    rw [Substitution.mode_eq_var (σ := {types := [(n, a)]}) rfl, ModExpr.subst_id]

/-- Each configuration entails the original constraints through its accumulated
substitution, in every context satisfying the remaining obligations. -/
def RewriteConfig.EntailsInput (s : RewriteConfig) (cs : Bounds) : Prop :=
  ∀ Δ, EntailsAll Δ s.constraints → EntailsAll Δ (s.substitution.bounds cs)

theorem RewriteConfig.EntailsInput.substitute {s : RewriteConfig} {cs n a}
    (hs : ({s with pending := .equal (.flex n) a :: s.pending}).EntailsInput cs)
    (hn : TypeVar.flex n ∉ a.typeVars) (hk : n ∉ s.substitution.types.map Prod.fst) :
    (⟨({types := [(n, a)]} : Substitution).bounds (s.constraints ++ a.wellFormedBounds),
      [], s.substitution.extendType n a⟩ : RewriteConfig).EntailsInput cs := by
  intro Δ hΔ
  have hparts : EntailsAll Δ (({types := [(n, a)]} : Substitution).bounds s.constraints) ∧
      EntailsAll Δ (({types := [(n, a)]} : Substitution).bounds a.wellFormedBounds) := by
    simpa only [RewriteConfig.constraints, List.append_nil, Substitution.bounds,
      List.map_append, EntailsAll, List.mem_append, or_imp, forall_and] using hΔ
  have ha : a.DefinedUnder Δ := (a.definedUnder_iff_entails_wellFormed Δ).mpr
    (by simpa only [Substitution.wellFormedBounds_fixed (σ := {types := [(n, a)]}) rfl]
      using hparts.2)
  have hin : EntailsAll Δ (({types := [(n, a)]} : Substitution).bounds
      (.equal (.flex n) a :: s.constraints)) :=
    fun d hd => (List.mem_cons.mp hd).elim
      (fun he => he ▸ Substitution.singleType_equal_entails hn ha) (hparts.1 d)
  exact fun d hd => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    exact (Substitution.extendType_constraint_entails hk c Δ).mpr
      (Entails.consequence_substitute_types
        (fun Γ hΓ => hs Γ hΓ _ (List.mem_map.mpr ⟨c, hc, rfl⟩)) rfl hin
        (fun v _ => Substitution.singleType_images_defined ha v))

theorem Rewrites.entailsInput {s t : RewriteConfig} {cs}
    (h : Rewrites s t) (hs : s.EntailsInput cs) : t.EntailsInput cs := by
  cases h
  case substitute n a s hn hk => exact hs.substitute hn hk
  all_goals intro Δ hΔ; apply hs Δ
  all_goals simp only [RewriteConfig.constraints, EntailsAll, List.mem_append, List.mem_cons,
    or_imp, forall_and, forall_eq] at hΔ ⊢
  case equivalence xs ys s he => exact ⟨⟨(he Δ).mpr hΔ.1.1, hΔ.1.2⟩, hΔ.2⟩
  case discharge c hc => exact ⟨⟨hc.of_entails hΔ.2, hΔ.1⟩, hΔ.2⟩
  case reduce xs ys s he => exact ⟨⟨he.entails_backward hΔ.1.1, hΔ.1.2⟩, hΔ.2⟩
  case record => exact ⟨⟨hΔ.2.1, hΔ.1.2⟩, hΔ.2.2⟩
  case hyp c s hr hc => exact ⟨⟨hΔ.2 c hc, hΔ.1.2⟩, hΔ.2⟩
  case expandLeft | expandRight | propagate => exact ⟨hΔ.1.2, hΔ.2⟩
  case permute xs ys s he => exact ⟨fun c hc => hΔ.1 c (he.mem_iff.mp hc), hΔ.2⟩

theorem Entails.assumptions_modeModels {Δ c η} (h : Entails Δ c)
    (hη : ModeModels Δ η) : ModeModels c.assumptions η := by
  cases c <;> simp only [Constraint.assumptions, ModeModels, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, ModeSatisfies]
  case sub => exact ⟨⟨trivial, h.2.1 η hη⟩, h.2.2 η hη⟩
  case mode => exact h.denote hη
  case defined => exact h η hη
  case equal => exact ⟨⟨trivial, trivial⟩, h.2.2 η hη⟩
  case equiv => exact ⟨⟨⟨trivial, trivial⟩, h.2.2.1 η hη⟩, h.2.2.2 η hη⟩

theorem EntailsAll.assumptions_modeModels {Δ cs η} (h : EntailsAll Δ cs)
    (hη : ModeModels Δ η) : ModeModels cs.assumptions η := by
  intro d hd
  obtain ⟨c, hc, hd⟩ := List.mem_flatMap.mp hd
  exact (h c hc).assumptions_modeModels hη d hd

theorem ModeModels.consequence_assumptions {cs ds η}
    (h : ∀ Δ, EntailsAll Δ cs → EntailsAll Δ ds)
    (hm : ModeModels cs.assumptions η) : ModeModels ds.assumptions η :=
  (h cs.assumptions cs.assumptions_entails).assumptions_modeModels hm

theorem Constraint.residual_assumptions {c η} (hc : Residual [c]) :
    ModeModels c.assumptions η ↔ ModeSatisfies η c ∧ ModeModels c.typeGuards η := by
  cases c <;> simp_all [Residual, Constraint.assumptions, Constraint.typeGuards,
    ModeModels, ModeSatisfies]

/-- Written guards on retained type bounds follow from the remaining guard
obligations and scalar bounds. This prevents hypothesis discharge from losing
definedness even when obligations are rearranged or replaced by equivalents. -/
def RewriteConfig.GuardsValid (s : RewriteConfig) : Prop :=
  ∀ η, ModeModels s.pending.assumptions η → ModeModels s.bounds η →
    ModeModels s.bounds.assumptions η

theorem Rewrites.guardsValid {s t : RewriteConfig} (h : Rewrites s t)
    (hs : s.GuardsValid) : t.GuardsValid := by
  cases h
  case substitute => simp [RewriteConfig.GuardsValid, Bounds.assumptions, ModeModels]
  all_goals intro η hp hb
  all_goals simp only [RewriteConfig.GuardsValid, Bounds.assumptions, List.flatMap_cons,
    List.flatMap_append, ModeModels, List.mem_append, List.mem_cons, or_imp,
    forall_and, forall_eq] at hp hb hs ⊢
  case equivalence xs ys s he =>
    exact hs η ⟨ModeModels.consequence_assumptions (fun Δ => (he Δ).mpr) hp.1, hp.2⟩ hb
  case reduce xs ys s he =>
    exact hs η ⟨ModeModels.consequence_assumptions (fun _ => he.entails_backward) hp.1, hp.2⟩ hb
  case discharge c hc => exact hs η ⟨hc.assumptions_modeModels hb, hp⟩ hb
  case record c s hr hc =>
    have hg := (Constraint.residual_assumptions hr).mpr
      ⟨hb.1, c.typeGuards.assumptions_entails.modeModels hp.1⟩
    exact ⟨hg, hs η ⟨hg, hp.2⟩ hb.2⟩
  case hyp c s hr hc =>
    exact hs η ⟨(Constraint.residual_assumptions hr).mpr
      ⟨hb c hc, c.typeGuards.assumptions_entails.modeModels hp.1⟩, hp.2⟩ hb
  case expandLeft | expandRight | propagate => exact hs η hp.2 hb
  case permute xs ys s he =>
    exact hs η (fun c hc => hp c ((he.flatMap (fun _ _ => List.Perm.refl _)).mem_iff.mp hc)) hb

theorem Rewrites.residual {s t : RewriteConfig} (h : Rewrites s t)
    (hs : Residual s.bounds) : Residual t.bounds := by
  cases h <;> first | exact hs | skip
  case substitute => trivial
  case record c s hr hc =>
    exact List.forall_iff_forall_mem.mpr fun d hd => (List.mem_cons.mp hd).elim
      (fun he => he ▸ List.forall_iff_forall_mem.mp hr c (by simp))
      (List.forall_iff_forall_mem.mp hs d)

theorem RewriteConfig.GuardsValid.finished {s : RewriteConfig}
    (hs : s.GuardsValid) (hr : Residual s.bounds) (hp : s.pending = []) :
    EntailsAll s.bounds s.bounds := by
  intro c hc
  have hrc := List.forall_iff_forall_mem.mp hr c hc
  have hg : ∀ η, ModeModels s.bounds η → ModeModels c.assumptions η :=
    fun η hη d hd => hs η (by simp [hp, Bounds.assumptions, ModeModels]) hη d
      (List.mem_flatMap.mpr ⟨c, hc, hd⟩)
  cases c with
  | sub a b =>
    exact ⟨.bound hc,
      fun η hη d hd => hg η hη d (by simp [Constraint.assumptions, hd]),
      fun η hη d hd => hg η hη d (by simp [Constraint.assumptions, hd])⟩
  | mode a b => exact .valid fun _ hη => hη _ hc
  | defined a => exact fun _ hη => hη _ hc
  | equal v a => exact False.elim hrc
  | equiv a b => exact False.elim hrc

theorem RewriteStar.entailsInput {s t : RewriteConfig} {cs} (h : RewriteStar s t) :
    s.EntailsInput cs → t.EntailsInput cs := by
  induction h with
  | refl => exact id
  | step h _ ih => exact fun hs => ih (h.entailsInput hs)

theorem RewriteStar.guardsValid {s t : RewriteConfig} (h : RewriteStar s t) :
    s.GuardsValid → t.GuardsValid := by
  induction h with
  | refl => exact id
  | step h _ ih => exact fun hs => ih (h.guardsValid hs)

theorem RewriteStar.residual {s t : RewriteConfig} (h : RewriteStar s t) :
    Residual s.bounds → Residual t.bounds := by
  induction h with
  | refl => exact id
  | step h _ ih => exact fun hs => ih (h.residual hs)

theorem RewriteStar.finished_entails {cs bounds σ}
    (h : RewriteStar ⟨cs, [], {}⟩ ⟨[], bounds, σ⟩) : EntailsAll bounds bounds :=
  (h.guardsValid (by simp [RewriteConfig.GuardsValid, Bounds.assumptions, ModeModels])).finished
    (h.residual (by trivial)) rfl

/-- Every completed abstract rewrite derives the substituted input from the
returned bounds. No consistency, closedness, or ground-model premise is needed. -/
theorem RewriteStar.sound {cs bounds σ}
    (h : RewriteStar ⟨cs, [], {}⟩ ⟨[], bounds, σ⟩) : EntailsAll bounds (σ.bounds cs) := by
  exact h.entailsInput (by simp [RewriteConfig.EntailsInput, RewriteConfig.constraints])
    bounds (by simpa [RewriteConfig.constraints] using h.finished_entails)

theorem RewriteStar.images_defined {cs bounds σ}
    (h : RewriteStar ⟨cs, [], {}⟩ ⟨[], bounds, σ⟩) (v : TypeVar) :
    (σ.type v).DefinedUnder bounds := by
  have hi : (⟨cs, [], {}⟩ : RewriteConfig).EntailsInput [.sub (.var v) (.var v)] := by
    intro Δ _
    simpa [Substitution.empty_bounds, EntailsAll, Entails, TypeExpr.DefinedUnder,
      TypeExpr.wellFormedBounds, ModeModels] using (Subtype.refl (Δ := Δ) (a := .var v))
  have he := h.entailsInput hi bounds
    (by simpa [RewriteConfig.constraints] using h.finished_entails)
  exact (he _ (List.mem_singleton_self _)).2.1

theorem Rewrites.substitution_modes {s t : RewriteConfig} (h : Rewrites s t) :
    t.substitution.modes = s.substitution.modes := by cases h <;> rfl

theorem RewriteStar.substitution_modes {s t : RewriteConfig} (h : RewriteStar s t) :
    t.substitution.modes = s.substitution.modes := by
  induction h with
  | refl => rfl
  | step h _ ih => exact ih.trans h.substitution_modes

theorem RewriteStar.substitution_wellFormed {cs bounds σ}
    (h : RewriteStar ⟨cs, [], {}⟩ ⟨[], bounds, σ⟩) : σ.WellFormedUnder bounds :=
  ⟨h.images_defined, fun v η _ => by
    simp [Substitution.mode_eq_var h.substitution_modes, ModExpr.WellFormed, ModExpr.eval]⟩

end ModalityInference
