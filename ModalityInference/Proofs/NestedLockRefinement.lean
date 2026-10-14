import ModalityInference.Proofs.ModalRefinement

/-! Transport modal refinement and sharing through arbitrary lists of symbolic locks. -/
namespace ModalityInference

theorem Scheme.lockAll_params (s : Scheme) (ms : List ModExpr) :
    (s.lockAll ms).typeParams = s.typeParams ∧ (s.lockAll ms).modParams = s.modParams := by
  induction ms <;> simp_all [lockAll, lock]

theorem Scheme.lockAll_instantiates (s : Scheme) (ms : List ModExpr) (σ : Substitution) :
    Instantiates (s.lockAll ms) σ ↔ Instantiates s σ := by
  simp only [Instantiates, (s.lockAll_params ms).1, (s.lockAll_params ms).2]

theorem Scheme.lock_instance_body (s : Scheme) (σ : Substitution) (m : ModExpr) :
    σ.ty (s.lock m).body = .modal (σ.ty s.body) (.capture (m.subst σ.mode)) := rfl

theorem Scheme.lockAll_body_congr {s t : Scheme} {σ τ : Substitution}
    (he : σ.ty s.body = τ.ty t.body) (ms : List ModExpr)
    (hm : ∀ m ∈ ms, m.subst σ.mode = m.subst τ.mode) :
    σ.ty (s.lockAll ms).body = τ.ty (t.lockAll ms).body := by
  induction ms with
  | nil => exact he
  | cons m ms ih =>
    simp only [lockAll, lock_instance_body, hm m List.mem_cons_self,
      ih (fun k hk => hm k (List.mem_cons_of_mem _ hk))]

theorem Scheme.lockAll_base_bounds {s : Scheme} {ms : List ModExpr} {σ : Substitution} {Δ : Bounds}
    (h : EntailsAll Δ (σ.bounds (s.lockAll ms).bounds)) : EntailsAll Δ (σ.bounds s.bounds) := by
  induction ms with
  | nil => exact h
  | cons m ms ih => exact ih (((s.lockAll ms).lock_instance_bounds σ m Δ).mp h).1

theorem Scheme.lockAll_base_defined {s : Scheme} {ms : List ModExpr} {σ : Substitution} {Δ : Bounds}
    (h : (σ.ty (s.lockAll ms).body).DefinedUnder Δ) : (σ.ty s.body).DefinedUnder Δ := by
  induction ms with
  | nil => exact h
  | cons m ms ih => exact ih (TypeExpr.definedUnder_modal.mp h).1

theorem Scheme.lockAll_transport {s t : Scheme} {σ τ : Substitution} {Δ : Bounds}
    (hb : EntailsAll Δ (σ.bounds s.bounds)) (hd : (σ.ty s.body).DefinedUnder Δ)
    (hst : Subtype Δ (σ.ty s.body) (τ.ty t.body))
    (hts : Subtype Δ (τ.ty t.body) (σ.ty s.body)) (ms : List ModExpr)
    (hm : ∀ m ∈ ms, m.subst σ.mode = m.subst τ.mode)
    (ht : EntailsAll Δ (τ.bounds (t.lockAll ms).bounds)) :
    EntailsAll Δ (σ.bounds (s.lockAll ms).bounds) ∧
      (σ.ty (s.lockAll ms).body).DefinedUnder Δ ∧
      Subtype Δ (σ.ty (s.lockAll ms).body) (τ.ty (t.lockAll ms).body) ∧
      Subtype Δ (τ.ty (t.lockAll ms).body) (σ.ty (s.lockAll ms).body) := by
  induction ms with
  | nil => exact ⟨hb, hd, hst, hts⟩
  | cons m ms ih =>
    have hl := ((t.lockAll ms).lock_instance_bounds τ m Δ).mp ht
    obtain ⟨hb', hd', hst', hts'⟩ := ih (fun k hk => hm k (List.mem_cons_of_mem _ hk)) hl.1
    have hf := (TypeExpr.definedUnder_modal.mp hl.2.2.2).2
    simp only [Scheme.lockAll, Scheme.lock_instance_bounds, Scheme.lock_instance_body,
      hm m List.mem_cons_self]
    exact ⟨⟨hb', hst'.trans (hl.2.1.trans (.congr hts' (.refl hf))), hd',
        TypeExpr.definedUnder_modal.mpr ⟨hd', hf⟩⟩,
      TypeExpr.definedUnder_modal.mpr ⟨hd', Entails.defined_capture_of_future hf⟩,
      .congr hst' (.refl (Entails.defined_capture_of_future hf)),
      .congr hts' (.refl (Entails.defined_capture_of_future hf))⟩

theorem Instantiates.refineMode_lockAll_shared {s : Scheme} {σ : Substitution} {p : Nat}
    {ms : List ModExpr} {Δ : Bounds} (hi : Instantiates s σ) (hp : s.freshModeIndex ≤ p)
    (hm : ∀ m ∈ ms, .flex p ∉ m.vars)
    (hb : EntailsAll Δ (σ.bounds (s.share.lockAll ms).bounds)) :
    Instantiates ((s.refineMode p).lockAll ms) (σ.extendMode p (.const Mode.aliased)) ∧
      EntailsAll Δ ((σ.extendMode p (.const Mode.aliased)).bounds ((s.refineMode p).lockAll ms).bounds) ∧
      (σ.extendMode p (.const Mode.aliased)).ty ((s.refineMode p).lockAll ms).body =
        σ.ty (s.share.lockAll ms).body := by
  have hs := (s.share_instance_bounds σ Δ).mp (Scheme.lockAll_base_bounds hb)
  have hw : Entails Δ (.sub (σ.ty s.body) (.modal (σ.ty s.body) (.const Mode.aliased))) :=
    ⟨Subtype.identityRev.trans (.congr .refl (.valid fun _ _ =>
      ⟨_, _, rfl, rfl, by decide⟩)), hs.2.2.1,
      TypeExpr.definedUnder_modal.mpr ⟨hs.2.2.1, fun _ _ => rfl⟩⟩
  have he : (σ.extendMode p (.const Mode.aliased)).ty (s.refineMode p).body = σ.ty s.share.body :=
    hi.refineMode_body hp (.const Mode.aliased)
  have hm' : ∀ m ∈ ms, m.subst (σ.extendMode p (.const Mode.aliased)).mode = m.subst σ.mode :=
    fun m hmem => σ.extendMode_modExpr p (.const Mode.aliased) m (hm m hmem)
  have hl := Scheme.lockAll_transport
    ((hi.refineMode_bounds hp (.const Mode.aliased) Δ).mpr ⟨hs.1, hw⟩) (he.symm ▸ hw.2.2)
    (by simpa only [he] using (Subtype.refl (Δ := Δ) (a := σ.ty s.share.body)))
    (by simpa only [he] using (Subtype.refl (Δ := Δ) (a := σ.ty s.share.body))) ms hm' hb
  exact ⟨((s.refineMode p).lockAll_instantiates ms _).mpr (hi.refineMode p (.const Mode.aliased)),
    hl.1, Scheme.lockAll_body_congr he ms hm'⟩

theorem Instantiates.refineMode_lockAll {s : Scheme} {σ : Substitution} {p : Nat}
    {ms : List ModExpr} {Δ : Bounds} (hi : Instantiates s σ) (hp : s.freshModeIndex ≤ p)
    (hm : ∀ m ∈ ms, .flex p ∉ m.vars)
    (hb : EntailsAll Δ (σ.bounds (s.lockAll ms).bounds)) (hd : (σ.ty s.body).DefinedUnder Δ) :
    Instantiates ((s.refineMode p).lockAll ms) (σ.extendMode p .epsilon) ∧
      EntailsAll Δ ((σ.extendMode p .epsilon).bounds ((s.refineMode p).lockAll ms).bounds) ∧
      ((σ.extendMode p .epsilon).ty ((s.refineMode p).lockAll ms).body).DefinedUnder Δ ∧
      Subtype Δ ((σ.extendMode p .epsilon).ty ((s.refineMode p).lockAll ms).body)
        (σ.ty (s.lockAll ms).body) ∧
      Subtype Δ (σ.ty (s.lockAll ms).body)
        ((σ.extendMode p .epsilon).ty ((s.refineMode p).lockAll ms).body) := by
  have he := hi.refineMode_body hp .epsilon
  have hd' : (TypeExpr.modal (σ.ty s.body) .epsilon).DefinedUnder Δ :=
    TypeExpr.definedUnder_modal.mpr ⟨hd, fun _ _ => rfl⟩
  exact ⟨((s.refineMode p).lockAll_instantiates ms _).mpr (hi.refineMode p .epsilon),
    Scheme.lockAll_transport
      ((hi.refineMode_bounds hp .epsilon Δ).mpr
        ⟨Scheme.lockAll_base_bounds hb, .identityRev, hd, hd'⟩)
      (he.symm ▸ hd') (he.symm ▸ Subtype.identity) (he.symm ▸ Subtype.identityRev)
      ms (fun m hmem => σ.extendMode_modExpr p .epsilon m (hm m hmem)) hb⟩

theorem Scheme.lockAll_instance_many {s : Scheme} {σ : Substitution} {ms : List ModExpr} {Δ : Bounds}
    (hm : Subtype Δ (σ.ty s.body) (.modal (σ.ty s.body) (.const Mode.many)))
    (hb : EntailsAll Δ (σ.bounds (s.lockAll ms).bounds)) :
    Subtype Δ (σ.ty (s.lockAll ms).body)
      (.modal (σ.ty (s.lockAll ms).body) (.const Mode.many)) := by
  induction ms with
  | nil => exact hm
  | cons m ms ih =>
    have hl := ((s.lockAll ms).lock_instance_bounds σ m Δ).mp hb
    exact (ih hl.1).modal_many
      (Entails.defined_capture_of_future (TypeExpr.definedUnder_modal.mp hl.2.2.2).2)

theorem Scheme.refineMode_lockAll_subsumes_shared {s : Scheme} {p : Nat} {ms : List ModExpr}
    (hp : s.freshModeIndex ≤ p) (hm : ∀ m ∈ ms, .flex p ∉ m.vars) (Δ : Bounds) :
    Subsumes Δ ((s.refineMode p).lockAll ms).withAssumptions
      ((s.share.lockAll ms).withAssumptions.modal (.const Mode.many)) := by
  refine Subsumes.of_instances (fun Ξ σ hi hb => ?_)
  have hi₀ : Instantiates s σ := (s.share.lockAll_instantiates ms σ).mp hi
  obtain ⟨hθ, hbounds, hbody⟩ := hi₀.refineMode_lockAll_shared hp hm hb.of_subst_assumptions
  exact ⟨σ.extendMode p (.const Mode.aliased), hθ, hbounds.subst_assumptions,
    hbody.symm ▸ Scheme.lockAll_instance_many
      (((s.share_instance_bounds σ Ξ).mp
        (Scheme.lockAll_base_bounds hb.of_subst_assumptions)).2.1.modal_many
          (m := .const Mode.aliased) (fun _ _ => rfl)) hb.of_subst_assumptions⟩

theorem Scheme.lockAll_bounds_base_defined {s : Scheme} {ms : List ModExpr}
    {σ : Substitution} {Δ : Bounds} (hn : ms ≠ [])
    (h : EntailsAll Δ (σ.bounds (s.lockAll ms).bounds)) : (σ.ty s.body).DefinedUnder Δ := by
  cases ms with
  | nil => exact False.elim (hn rfl)
  | cons m ms =>
    exact Scheme.lockAll_base_defined (((s.lockAll ms).lock_instance_bounds σ m Δ).mp h).2.2.1

theorem Scheme.refineMode_lockAll_subsumes {s : Scheme} {p : Nat} {ms : List ModExpr}
    (hp : s.freshModeIndex ≤ p) (hm : ∀ m ∈ ms, .flex p ∉ m.vars) (hn : ms ≠ []) (Δ : Bounds) :
    Subsumes Δ ((s.refineMode p).lockAll ms).withAssumptions (s.lockAll ms).withAssumptions := by
  refine Subsumes.of_instances (fun Ξ σ hi hb => ?_)
  obtain ⟨hθ, hbounds, _, hsub, _⟩ := ((s.lockAll_instantiates ms σ).mp hi).refineMode_lockAll hp hm
    hb.of_subst_assumptions (Scheme.lockAll_bounds_base_defined hn hb.of_subst_assumptions)
  exact ⟨σ.extendMode p .epsilon, hθ, hbounds.subst_assumptions, hsub⟩

theorem Scheme.lockAll_aliased {s : Scheme} {ms : List ModExpr} {Δ : Bounds}
    (ha : Subtype Δ (.modal s.body (.const Mode.aliased)) s.body)
    (hb : EntailsAll Δ (s.lockAll ms).bounds) :
    Subtype Δ (.modal (s.lockAll ms).body (.const Mode.aliased)) (s.lockAll ms).body := by
  induction ms with
  | nil => exact ha
  | cons m ms ih =>
    have hl : EntailsAll Δ (s.lockAll ms).bounds ∧
        Entails Δ (.sub (s.lockAll ms).body (.modal (s.lockAll ms).body (.future m))) := by
      simpa [lockAll, lock, EntailsAll, or_imp, forall_and] using hb
    have hc := Entails.defined_capture_of_future (TypeExpr.definedUnder_modal.mp hl.2.2.2).2
    exact (Subtype.modal_comm (n := .const Mode.aliased) hc (fun _ _ => rfl)).trans
      (.congr (ih hl.1) (.refl hc))

theorem Scheme.shared_lockAll_join {s : Scheme} {ms : List ModExpr} {Δ : Bounds}
    (hf : s.FreshForBounds Δ) :
    ContextJoin Δ [some (s.share.lockAll ms).withAssumptions]
      [some (s.share.lockAll ms).withAssumptions]
      [some ((s.share.lockAll ms).withAssumptions.modal (.const Mode.many))] := by
  refine .shared .nil ?_ (Scheme.lockAll_aliased (Subtype.aliased_idempotent _ _)
    (Bounds.assumptions_entails_append _ _))
  simpa only [FreshForBounds, withAssumptions, (s.share.lockAll_params ms).1,
    (s.share.lockAll_params ms).2] using (show s.share.FreshForBounds Δ from hf)

end ModalityInference
