import ModalityInference.Proofs.ComparisonReductionAlgebra

namespace ModalityInference.ComparisonReduction

def PairHolds (Δ : Bounds) (σ : CompareSubstitution) (p : Ty × Ty) : Prop :=
  AlgebraSubtype Δ (σ.ty p.1) (σ.ty p.2)

def BareHolds (Δ : Bounds) (σ : CompareSubstitution) (b : ComparisonPartial.BareBound) : Prop :=
  if b.isLower then AlgebraSubtype Δ (σ.ty b.endpoint) (σ.type (.flex b.name))
  else AlgebraSubtype Δ (σ.type (.flex b.name)) (σ.ty b.endpoint)

/-- A final comparison action satisfies each residual obligation with the same
bare-body versus guarded-bound distinction as the input judgment. -/
structure Holds (Δ : Bounds) (σ : CompareSubstitution) (s : State) : Prop where
  pending : ∀ p ∈ s.pending, PairHolds Δ σ p
  inequalities : ∀ p ∈ s.inequalities, PairHolds Δ σ p
  modes : AlgebraEntailsAll Δ (σ.bounds s.modes)
  bareBounds : ∀ b ∈ s.bareBounds, BareHolds Δ σ b

theorem holds_iff {Δ σ s} : Holds Δ σ s ↔
    (∀ p ∈ s.pending, PairHolds Δ σ p) ∧
    (∀ p ∈ s.inequalities, PairHolds Δ σ p) ∧
    AlgebraEntailsAll Δ (σ.bounds s.modes) ∧
    ∀ b ∈ s.bareBounds, BareHolds Δ σ b :=
  ⟨fun h => ⟨h.pending, h.inequalities, h.modes, h.bareBounds⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

private theorem algebraEntailsAll_cons {Δ c cs} :
    AlgebraEntailsAll Δ (c :: cs) ↔ AlgebraEntails Δ c ∧ AlgebraEntailsAll Δ cs := by
  simp only [AlgebraEntailsAll, List.forall_mem_cons]

theorem bareVariable_algebra {Δ : Bounds} {σ : CompareSubstitution}
    (hσ : σ.WellShaped Δ) (names : List Nat) {t : Ty} {n : Nat}
    (h : bareVariable names t = some n) :
    AlgebraSubtype Δ (σ.ty t) (σ.type (.flex n)) ∧
      AlgebraSubtype Δ (σ.type (.flex n)) (σ.ty t) := by
  induction t with
  | var v =>
    cases v <;> simp only [bareVariable] at h <;> try contradiction
    split at h
    · cases Option.some.inj h
      exact ⟨.refl (σ.type_wellShaped hσ (.flex n)),
        .refl (σ.type_wellShaped hσ (.flex n))⟩
    · contradiction
  | modal a m ih =>
    unfold bareVariable at h
    split at h <;> try contradiction
    all_goals cases ‹a.modal m = _›
    exact ⟨(AlgebraSubtype.identity (σ.ty_wellShaped hσ _)).trans (ih h).1,
      (ih h).2.trans (.identityRev (σ.ty_wellShaped hσ _))⟩
  | unit | credit | prod | sum | fn => contradiction

private theorem outer_reconstruct {Δ : Bounds} {σ : CompareSubstitution}
    (hσ : σ.WellShaped Δ) {left right a b : Ty}
    (hl : left.outer.1 = a) (hr : right.outer.1 = b)
    (hml : Entails Δ (.defined (left.outer.2.subst σ.mode)))
    (hmr : Entails Δ (.defined (right.outer.2.subst σ.mode)))
    (h : AlgebraSubtype Δ (.modal (σ.ty a) (left.outer.2.subst σ.mode))
      (.modal (σ.ty b) (right.outer.2.subst σ.mode))) : PairHolds Δ σ (left, right) :=
  (outer_algebra hσ left (.refl hml)).1.trans
    (AlgebraSubtype.trans (by simpa only [hl, hr] using h)
      (outer_algebra hσ right (.refl hmr)).2)

/-- Reconstruction for one worklist transition. The action may contain internal
joins and meets and need not define the bare body images. -/
theorem step_sound {Δ : Bounds} {σ : CompareSubstitution} {s next : State}
    (hσ : σ.WellShaped Δ)
    (hassumptions : ∀ a b, Constraint.sub a b ∈ s.assumptions →
      AlgebraSubtype Δ (σ.ty a) (σ.ty b))
    (htotal : ∀ m, ComparisonBody.isTotal s.totalModes m = true →
      Submode Δ (m.subst σ.mode) (m.subst σ.mode))
    (hstep : step s = .success next) (hnext : Holds Δ σ next) : Holds Δ σ s := by
  unfold step at hstep
  split at hstep
  · cases hstep
    exact hnext
  · next left right rest hpending =>
    simp only [holds_iff, hpending, List.forall_mem_cons] at hnext ⊢
    simp only at hstep
    split at hstep
    · next he =>
      cases hstep
      refine ⟨⟨?_, hnext.1⟩, hnext.2⟩
      simp only [Bool.or_eq_true] at he
      rcases he with he | he
      · cases beq_iff_eq.mp he
        exact .refl (σ.ty_wellShaped hσ _)
      · exact hassumptions _ _ (List.contains_iff_mem.mp he)
    · split at hstep
      ·
        cases hstep
        simp only [List.forall_mem_cons] at hnext
        refine ⟨⟨?_, hnext.1⟩, hnext.2.1, hnext.2.2.1, hnext.2.2.2.2⟩
        exact (bareVariable_algebra hσ _ ‹bareVariable s.bareVariables left = some _›).1.trans
          hnext.2.2.2.1
      ·
        cases hstep
        simp only [List.forall_mem_cons] at hnext
        refine ⟨⟨?_, hnext.1⟩, hnext.2.1, hnext.2.2.1, hnext.2.2.2.2⟩
        exact AlgebraSubtype.trans hnext.2.2.2.1
          (bareVariable_algebra hσ _ ‹bareVariable s.bareVariables right = some _›).2
      · split at hstep
        · next step hshared =>
          cases hstep
          simp only [List.forall_mem_cons, CompareSubstitution.bounds,
            List.map_cons, algebraEntailsAll_cons] at hnext
          refine ⟨⟨?_, hnext.1.2⟩, hnext.2.1, hnext.2.2.1.2, hnext.2.2.2⟩
          split at hshared
          · exact stripTotal_algebra hσ _ htotal hshared hnext.1.1 hnext.2.2.1.1
          · contradiction
        · split at hstep
          · next he =>
            cases hstep
            refine ⟨⟨?_, hnext.1⟩, hnext.2⟩
            exact (normalizeOuter_algebra hσ left).1.trans
              (by simpa only [beq_iff_eq.mp he] using (normalizeOuter_algebra hσ right).2)
          · split at hstep
            · next m n hsuffix =>
              cases hstep
              simp only [CompareSubstitution.bounds, List.map_cons,
                algebraEntailsAll_cons] at hnext
              refine ⟨⟨?_, hnext.1⟩, hnext.2.1, hnext.2.2.1.2, hnext.2.2.2⟩
              split at hsuffix
              · exact suffixGoal_algebra hσ _ htotal hsuffix hnext.2.2.1.1
              · contradiction
            · split at hstep
              all_goals try contradiction
              all_goals cases hstep
              all_goals simp only [List.forall_mem_cons, CompareSubstitution.bounds,
                List.map_cons, algebraEntailsAll_cons] at hnext
              · exact ⟨⟨hnext.2.1.1, hnext.1⟩, hnext.2.1.2,
                  hnext.2.2.1.2.2, hnext.2.2.2⟩
              · refine ⟨⟨?_, hnext.1⟩, hnext.2.1, hnext.2.2.1.2, hnext.2.2.2⟩
                have hm : Submode Δ (left.outer.2.subst σ.mode) (right.outer.2.subst σ.mode) :=
                  hnext.2.2.1.1
                exact outer_reconstruct hσ ‹left.outer.1 = .unit› ‹right.outer.1 = .unit›
                  hm.defined.1 hm.defined.2 (.congr (.refl trivial) hm)
              · refine ⟨⟨?_, hnext.1⟩, hnext.2.1, hnext.2.2.1.2, hnext.2.2.2⟩
                have hm : Submode Δ (.compose (left.outer.2.subst σ.mode) (.const Mode.many))
                    (right.outer.2.subst σ.mode) := hnext.2.2.1.1
                exact outer_reconstruct hσ ‹left.outer.1 = .credit› ‹right.outer.1 = .credit›
                  (Entails.defined_compose_iff.mp hm.defined.1).1 hm.defined.2 (.shaped (.credit hm))
              · refine ⟨⟨?_, hnext.1.2.2⟩, hnext.2.1, hnext.2.2.1.2, hnext.2.2.2⟩
                have hm : Submode Δ (left.outer.2.subst σ.mode) (right.outer.2.subst σ.mode) :=
                  hnext.2.2.1.1
                exact outer_reconstruct hσ ‹left.outer.1 = .prod _ _› ‹right.outer.1 = .prod _ _›
                  hm.defined.1 hm.defined.2 (.prod_cross hnext.1.1 hnext.1.2.1 hm)
              · refine ⟨⟨?_, hnext.1.2.2⟩, hnext.2.1, hnext.2.2.1.2, hnext.2.2.2⟩
                have hm : Submode Δ (left.outer.2.subst σ.mode) (right.outer.2.subst σ.mode) :=
                  hnext.2.2.1.1
                exact outer_reconstruct hσ ‹left.outer.1 = .sum _ _› ‹right.outer.1 = .sum _ _›
                  hm.defined.1 hm.defined.2 (.sum_cross hnext.1.1 hnext.1.2.1 hm)
              · refine ⟨⟨?_, hnext.1.2.2⟩, hnext.2.1, hnext.2.2.1.2, hnext.2.2.2⟩
                have hm : Submode Δ (left.outer.2.subst σ.mode)
                    (.compose (right.outer.2.subst σ.mode) .top) := hnext.2.2.1.1
                exact outer_reconstruct hσ ‹left.outer.1 = .fn _ _› ‹right.outer.1 = .fn _ _›
                  hm.defined.1 (Entails.defined_compose_iff.mp hm.defined.2).1
                  (.fn hnext.1.1 hnext.1.2.1 hm)

theorem step_metadata {s next : State} (h : step s = .success next) :
    next.assumptions = s.assumptions ∧ next.totalModes = s.totalModes ∧
      next.bareVariables = s.bareVariables ∧ next.shared = s.shared := by
  unfold step at h
  repeat' first
    | contradiction
    | (cases h; exact ⟨rfl, rfl, rfl, rfl⟩)
    | (split at h <;> try simp only at h)

theorem run_sound {Δ : Bounds} {σ : CompareSubstitution} {s next : State} {fuel : Nat}
    (hσ : σ.WellShaped Δ)
    (hassumptions : ∀ a b, Constraint.sub a b ∈ s.assumptions →
      AlgebraSubtype Δ (σ.ty a) (σ.ty b))
    (htotal : ∀ m, ComparisonBody.isTotal s.totalModes m = true →
      Submode Δ (m.subst σ.mode) (m.subst σ.mode))
    (h : run fuel s = .success next) (hnext : Holds Δ σ next) : Holds Δ σ s := by
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at h
    split at h
    · cases h
      exact hnext
    · cases hs : step s <;> simp only [hs] at h <;> try contradiction
      next middle =>
        have hm := step_metadata hs
        exact step_sound hσ hassumptions htotal hs
          (ih (by simpa only [hm.1] using hassumptions)
            (by simpa only [hm.2.1] using htotal) h)

theorem run_metadata {s next : State} {fuel : Nat} (h : run fuel s = .success next) :
    next.assumptions = s.assumptions ∧ next.totalModes = s.totalModes ∧
      next.bareVariables = s.bareVariables ∧ next.shared = s.shared := by
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at h
    split at h
    · cases h
      exact ⟨rfl, rfl, rfl, rfl⟩
    · cases hs : step s <;> simp only [hs] at h <;> try contradiction
      next middle =>
        have hm := step_metadata hs
        have hn := ih h
        exact ⟨hn.1.trans hm.1, hn.2.1.trans hm.2.1,
          hn.2.2.1.trans hm.2.2.1, hn.2.2.2.trans hm.2.2.2⟩

theorem run_pending_empty {s next : State} {fuel : Nat} (h : run fuel s = .success next) :
    next.pending = [] := by
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at h
    split at h
    · next hempty => cases h; exact List.isEmpty_iff.mp hempty
    · cases hs : step s <;> simp only [hs] at h <;> try contradiction
      exact ih h

theorem bareVariable_mem {names : List Nat} {t : Ty} {n : Nat}
    (h : bareVariable names t = some n) : n ∈ names := by
  induction t with
  | var v =>
    cases v <;> simp only [bareVariable] at h <;> try contradiction
    split at h
    · next hn => cases Option.some.inj h; exact List.contains_iff_mem.mp hn
    · contradiction
  | modal a m ih =>
    unfold bareVariable at h
    split at h <;> try contradiction
    all_goals cases ‹a.modal m = _›
    exact ih h
  | unit | credit | prod | sum | fn => contradiction

theorem step_partialTypes {s next : State} (h : step s = .success next) :
    next.partialTypes = s.partialTypes := by
  unfold step at h
  repeat' first
    | contradiction
    | (cases h; rfl)
    | (split at h <;> try simp only at h)

theorem run_partialTypes {s next : State} {fuel : Nat} (h : run fuel s = .success next) :
    next.partialTypes = s.partialTypes := by
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at h
    split at h
    · cases h; rfl
    · cases hs : step s <;> simp only [hs] at h <;> try contradiction
      exact (ih h).trans (step_partialTypes hs)

theorem step_bare_scope {s next : State} (h : step s = .success next)
    (hs : ∀ b ∈ s.bareBounds, b.name ∈ s.bareVariables) :
    ∀ b ∈ next.bareBounds, b.name ∈ next.bareVariables := by
  unfold step at h
  repeat' first
    | contradiction
    | (cases h; exact hs)
    | (split at h <;> try simp only at h)
  all_goals cases h
  all_goals simp only [List.forall_mem_cons]
  all_goals refine ⟨?_, hs⟩
  all_goals exact bareVariable_mem ‹bareVariable s.bareVariables _ = some _›

theorem run_bare_scope {s next : State} {fuel : Nat} (h : run fuel s = .success next)
    (hs : ∀ b ∈ s.bareBounds, b.name ∈ s.bareVariables) :
    ∀ b ∈ next.bareBounds, b.name ∈ next.bareVariables := by
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at h
    split at h
    · cases h; exact hs
    · cases hstep : step s <;> simp only [hstep] at h <;> try contradiction
      exact ih h (step_bare_scope hstep hs)

theorem bare_image_action (σ : CompareSubstitution) (name : Nat)
    (bounds : List ComparisonPartial.BareBound) :
    (ComparisonPartial.image name bounds).subst σ.type σ.mode =
      ComparisonInterpolation.witness ((ComparisonPartial.lower name bounds).map σ.ty)
        ((ComparisonPartial.upper name bounds).map σ.ty) := by
  simp only [ComparisonPartial.image, ComparisonInterpolation.witness_subst, List.map_map,
    Function.comp_def]
  rfl

/-- Shape-compatible finite interval reconstruction after any final action.
The source interval images and their endpoints may remain undefined. -/
theorem reduceBare_algebra {Δ : Bounds} {σ : CompareSubstitution}
    {names : List Nat} {bounds : List ComparisonPartial.BareBound}
    (hσ : σ.WellShaped Δ) (hscope : ∀ b ∈ bounds, b.name ∈ names)
    (himages : ∀ name ∈ names, σ.type (.flex name) =
      (ComparisonPartial.image name bounds).subst σ.type σ.mode)
    (hgoals : ∀ p ∈ (ComparisonPartial.reduceBare names bounds).goals, PairHolds Δ σ p) :
    ∀ b ∈ bounds, BareHolds Δ σ b := by
  intro b hb
  have hn := hscope b hb
  have he := himages b.name hn
  rw [bare_image_action] at he
  have hi := ComparisonInterpolation.witness_algebra_interval
    (Δ := Δ) (he ▸ σ.type_wellShaped hσ (.flex b.name))
  simp only [List.forall_mem_map] at hi
  have hc : ∀ a ∈ ComparisonPartial.lower b.name bounds,
      ∀ c ∈ ComparisonPartial.upper b.name bounds, AlgebraSubtype Δ (σ.ty a) (σ.ty c) := by
    intro a ha c hc
    apply hgoals (a, c)
    exact List.mem_flatMap.mpr ⟨b.name, hn,
      List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨c, hc, rfl⟩⟩⟩
  have hw := hi hc
  cases hs : b.isLower with
  | false =>
    simp only [BareHolds, hs, Bool.false_eq_true, ↓reduceIte]
    rw [he]
    exact hw.2 _ (ComparisonPartial.mem_upper.mpr ⟨b, hb, rfl, hs, rfl⟩)
  | true =>
    simp only [BareHolds, hs, ↓reduceIte]
    rw [he]
    exact hw.1 _ (ComparisonPartial.mem_lower.mpr ⟨b, hb, rfl, hs, rfl⟩)

/-- The two reduction passes reconstruct all substituted source bounds and the
bare body goal. The image equation identifies the finite interval witnesses
retained in the successful output with their final interpretations. -/
theorem prepare_sound {Δ : Bounds} {σ : CompareSubstitution} {fuel : Nat}
    {p : SchemePreparation.Prepared} {templates : ComparisonSkeleton.Templates}
    {bare : List Nat} {known : List ModExpr} {shared : Bool} {result : State}
    (hσ : σ.WellShaped Δ)
    (hassumptions : ∀ a b, Constraint.sub a b ∈ p.assumptions →
      AlgebraSubtype Δ (σ.ty a) (σ.ty b))
    (htotal : ∀ m, ComparisonBody.isTotal known m = true →
      Submode Δ (m.subst σ.mode) (m.subst σ.mode))
    (himages : ∀ entry ∈ result.partialTypes, σ.type (.flex entry.1) =
      entry.2.subst σ.type σ.mode)
    (h : prepare fuel p templates bare known shared = .success result)
    (hresult : Holds Δ σ result) :
    Holds Δ σ { initial (templates.substitution.bounds p.sourceBounds)
        (templates.substitution.ty p.sourceType) p.targetType with
      assumptions := p.assumptions, bareVariables := bare, totalModes := known, shared := shared } := by
  simp only [prepare, bind, RunResult.bind] at h
  split at h
  · next reduced hfirst =>
    have hm := run_metadata hfirst
    have hsecond := run_sound hσ
      (by simpa only [hm.1] using hassumptions)
      (by simpa only [hm.2.1] using htotal) h hresult
    apply run_sound hσ hassumptions htotal hfirst
    refine ⟨?_, hsecond.inequalities, hsecond.modes, ?_⟩
    · simp only [run_pending_empty hfirst, List.not_mem_nil, false_implies, implies_true]
    · apply reduceBare_algebra hσ
      · intro b hb
        simpa only [hm.2.2.1] using
          (run_bare_scope hfirst (by simp [initial])) b hb
      · intro name hn
        apply himages (name, ComparisonPartial.image name reduced.bareBounds)
        rw [run_partialTypes h]
        exact List.mem_map.mpr ⟨name, hn, rfl⟩
      · exact hsecond.pending
  · contradiction
  · contradiction

theorem ty_defined_of_guards {Δ : Bounds} {σ : CompareSubstitution} (t : Ty)
    (hvars : ∀ v ∈ t.typeVars, (σ.type v).DefinedUnder Δ)
    (hguards : ∀ m, Constraint.defined m ∈ t.wellFormedBounds →
      Entails Δ (.defined (m.subst σ.mode))) : (σ.ty t).DefinedUnder Δ := by
  induction t with
  | var v => exact hvars v (by simp [TypeExpr.typeVars])
  | unit | credit => intro η hη c hc; contradiction
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    have ha := iha
      (fun v hv => hvars v (by simp [TypeExpr.typeVars, hv]))
      (fun m hm => hguards m (List.mem_append_left _ hm))
    have hb := ihb
      (fun v hv => hvars v (by simp [TypeExpr.typeVars, hv]))
      (fun m hm => hguards m (List.mem_append_right _ hm))
    intro η hη c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ha η hη c hc
    · exact hb η hη c hc
  | modal a m ih =>
    have ha := ih hvars (fun n hn => hguards n (List.mem_append_left _ hn))
    intro η hη c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ha η hη c hc
    · obtain rfl := List.mem_singleton.mp hc
      exact hguards m (List.mem_append_right _ (List.mem_singleton_self _)) η hη

theorem initial_body {Δ : Bounds} {σ : CompareSubstitution} {bounds : Bounds} {source target : Ty}
    (h : Holds Δ σ (initial bounds source target)) : AlgebraSubtype Δ (σ.ty source) (σ.ty target) :=
  h.pending (source, target) (List.mem_append_right _ (List.mem_singleton_self _))

theorem initial_sub {Δ : Bounds} {σ : CompareSubstitution} {bounds : Bounds} {source target a b : Ty}
    (h : Holds Δ σ (initial bounds source target)) (hc : Constraint.sub a b ∈ bounds.assumptions) :
    AlgebraSubtype Δ (σ.ty a) (σ.ty b) :=
  h.pending (a, b) (List.mem_append_left _ (List.mem_filterMap.mpr ⟨.sub a b, hc, rfl⟩))

theorem initial_mode {Δ : Bounds} {σ : CompareSubstitution} {bounds : Bounds} {source target : Ty}
    {a b : ModExpr} (h : Holds Δ σ (initial bounds source target))
    (hc : Constraint.mode a b ∈ bounds.assumptions) :
    Submode Δ (a.subst σ.mode) (b.subst σ.mode) :=
  h.modes (σ.constraint (.mode a b))
    (List.mem_map.mpr ⟨.mode a b, List.mem_filter.mpr ⟨hc, rfl⟩, rfl⟩)

theorem initial_defined {Δ : Bounds} {σ : CompareSubstitution} {bounds : Bounds} {source target : Ty}
    {a : ModExpr} (h : Holds Δ σ (initial bounds source target))
    (hc : Constraint.defined a ∈ bounds.assumptions) : Entails Δ (.defined (a.subst σ.mode)) :=
  h.modes (σ.constraint (.defined a))
    (List.mem_map.mpr ⟨.defined a, List.mem_filter.mpr ⟨hc, rfl⟩, rfl⟩)

/-- Original written guards suffice once the images of variables occurring in
source bounds are defined. No condition is imposed on body-only images. -/
theorem initial_entails {Δ : Bounds} {σ : CompareSubstitution} {bounds : Bounds} {source target : Ty}
    (h : Holds Δ σ (initial bounds source target))
    (hvars : ∀ c ∈ bounds, ∀ v ∈ c.typeVars, (σ.type v).DefinedUnder Δ) :
    AlgebraEntailsAll Δ (σ.bounds bounds) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hmem : ∀ e ∈ d.assumptions, e ∈ bounds.assumptions :=
    fun e he => List.mem_flatMap.mpr ⟨d, hd, he⟩
  cases d with
  | sub a b =>
    refine ⟨initial_sub h (hmem _ (by simp [Constraint.assumptions])), ?_, ?_⟩
    · apply ty_defined_of_guards a
      · exact fun v hv => hvars _ hd v (by simp [Constraint.typeVars, hv])
      · exact fun m hm => initial_defined h (hmem _ (by simp [Constraint.assumptions, hm]))
    · apply ty_defined_of_guards b
      · exact fun v hv => hvars _ hd v (by simp [Constraint.typeVars, hv])
      · exact fun m hm => initial_defined h (hmem _ (by simp [Constraint.assumptions, hm]))
  | equiv a b =>
    refine ⟨initial_sub h (hmem _ (by simp [Constraint.assumptions])),
      initial_sub h (hmem _ (by simp [Constraint.assumptions])), ?_, ?_⟩
    · apply ty_defined_of_guards a
      · exact fun v hv => hvars _ hd v (by simp [Constraint.typeVars, hv])
      · exact fun m hm => initial_defined h (hmem _ (by simp [Constraint.assumptions, hm]))
    · apply ty_defined_of_guards b
      · exact fun v hv => hvars _ hd v (by simp [Constraint.typeVars, hv])
      · exact fun m hm => initial_defined h (hmem _ (by simp [Constraint.assumptions, hm]))
  | mode a b => exact initial_mode h (hmem _ (by simp [Constraint.assumptions]))
  | defined a => exact initial_defined h (hmem _ (by simp [Constraint.assumptions]))
  | equal v a =>
    have ha : AlgebraSubtype Δ (σ.type v) (σ.ty a) :=
      initial_sub (a := .var v) (b := a) h (hmem _ (by simp [Constraint.assumptions]))
    have hb : AlgebraSubtype Δ (σ.ty a) (σ.type v) :=
      initial_sub (a := a) (b := .var v) h (hmem _ (by simp [Constraint.assumptions]))
    have hva : (σ.ty a).DefinedUnder Δ := ty_defined_of_guards a
      (fun w hw => hvars _ hd w (by simp [Constraint.typeVars, hw]))
      (fun m hm => initial_defined h (hmem _ (by simp [Constraint.assumptions, hm])))
    have hv : (σ.type v).DefinedUnder Δ := hvars _ hd v (by simp [Constraint.typeVars])
    cases v with
    | rigid n => exact ⟨ha, hb, hva⟩
    | flex n =>
      cases he : σ.types.lookup n with
      | none =>
        simpa only [CompareSubstitution.constraint, he, AlgebraEntails,
          CompareSubstitution.type, Option.getD_none] using And.intro ha (And.intro hb hva)
      | some t =>
        simpa only [CompareSubstitution.constraint, he, AlgebraEntails,
          CompareSubstitution.type, Option.getD_some] using And.intro ha (And.intro hb (And.intro hv hva))

end ModalityInference.ComparisonReduction
