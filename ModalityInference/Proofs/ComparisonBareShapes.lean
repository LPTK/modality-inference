import ModalityInference.Proofs.ComparisonWitnessShapes
import ModalityInference.Proofs.ComparisonExactContext
import ModalityInference.Proofs.ComparisonAnnotations
import ModalityInference.ComparisonChecker

namespace ModalityInference.ComparisonReduction

/-- Shape matching observes precisely the paths containing a selected bare
variable. Other source subtrees may be specialized independently. -/
def Fits (names : List Nat) (ρ : TypeVar → ComparisonShape) : Ty → ComparisonShape → Prop
  | .var (.flex n), shape => if n ∈ names then ρ (.flex n) = shape else True
  | .var (.rigid _), _ | .unit, _ | .credit, _ => True
  | .prod a b, .prod c d | .sum a b, .sum c d | .fn a b, .fn c d =>
    Fits names ρ a c ∧ Fits names ρ b d
  | .prod a b, _ | .sum a b, _ | .fn a b, _ => TypeFree names a ∧ TypeFree names b
  | .modal a _, shape => Fits names ρ a shape

theorem Fits.of_free {names : List Nat} {ρ : TypeVar → ComparisonShape} {t : Ty}
    (h : TypeFree names t) (shape : ComparisonShape) : Fits names ρ t shape := by
  induction t generalizing shape with
  | var v =>
    cases v with
    | rigid => trivial
    | flex n =>
      have hn : n ∉ names := fun hn => h n hn (Finset.mem_singleton_self _)
      simp [Fits, hn]
  | unit | credit => trivial
  | modal a m ih => exact ih h shape
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    have ha : TypeFree names a := fun n hn hv => h n hn (Finset.mem_union_left _ hv)
    have hb : TypeFree names b := fun n hn hv => h n hn (Finset.mem_union_right _ hv)
    cases shape <;> first | exact ⟨iha ha _, ihb hb _⟩ | exact ⟨ha, hb⟩

theorem Fits.self (names : List Nat) (ρ : TypeVar → ComparisonShape) (t : Ty) :
    Fits names ρ t ((ComparisonShape.ofTy t).subst ρ) := by
  induction t with
  | var v => cases v <;> simp [Fits, ComparisonShape.ofTy, ComparisonShape.subst]
  | unit | credit => trivial
  | prod | sum | fn => exact ⟨by assumption, by assumption⟩
  | modal _ _ ih => exact ih

theorem Fits.of_shape {names : List Nat} {ρ : TypeVar → ComparisonShape} {t : Ty}
    {shape : ComparisonShape} (h : (ComparisonShape.ofTy t).subst ρ = shape) :
    Fits names ρ t shape := h ▸ Fits.self names ρ t

theorem typeFree_subst {names : List Nat} {σ : Substitution} {t : Ty}
    (h : TypeFree names t)
    (hi : ∀ v, (∀ n ∈ names, v ≠ .flex n) → TypeFree names (σ.type v)) :
    TypeFree names (σ.ty t) := by
  intro n hn hv
  obtain ⟨v, hv, hi'⟩ := (TypeExpr.mem_typeVars_subst _ _ _ _).mp hv
  exact hi v (fun k hk he => h k hk (he ▸ hv)) n hn hi'

theorem Fits.subst {names : List Nat} {ρ : TypeVar → ComparisonShape} {σ : Substitution}
    {t : Ty} {shape : ComparisonShape} (h : Fits names ρ t shape)
    (hf : ∀ n ∈ names, σ.type (.flex n) = .var (.flex n))
    (hi : ∀ v, (∀ n ∈ names, v ≠ .flex n) → TypeFree names (σ.type v)) :
    Fits names ρ (σ.ty t) shape := by
  induction t generalizing shape with
  | var v =>
    cases v with
    | rigid => trivial
    | flex n =>
      by_cases hn : n ∈ names
      · simpa only [Substitution.ty, TypeExpr.subst, hf n hn] using h
      · apply Fits.of_free
        apply hi (.flex n)
        intro k hk he
        exact hn (TypeVar.flex.inj he ▸ hk)
  | unit | credit => exact h
  | modal a m ih => exact ih h
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    cases shape <;> first
    | exact ⟨iha h.1, ihb h.2⟩
    | exact ⟨typeFree_subst h.1 hi, typeFree_subst h.2 hi⟩

theorem fits_outer (names : List Nat) (ρ : TypeVar → ComparisonShape) (t : Ty)
    (shape : ComparisonShape) : Fits names ρ t.outer.1 shape ↔ Fits names ρ t shape := by
  induction t <;> simp_all only [TypeExpr.outer, Fits]

theorem normalizeOuterFuel_fits (names : List Nat) (ρ : TypeVar → ComparisonShape)
    (fuel : Nat) (t : Ty) (shape : ComparisonShape) :
    Fits names ρ (ComparisonPartialModes.normalizeOuterFuel fuel t) shape ↔ Fits names ρ t shape := by
  induction fuel generalizing t with
  | zero => rfl
  | succ fuel ih =>
    cases t <;> try rfl
    next a m =>
      cases m <;> simp only [ComparisonPartialModes.normalizeOuterFuel]
      case compose m n => exact ih (.modal (.modal a m) n)
      all_goals split
      all_goals first | exact ih a | rfl

theorem peelFuel_fits (names : List Nat) (ρ : TypeVar → ComparisonShape)
    (total : ModExpr → Bool) (fuel : Nat) (t : Ty) (shape : ComparisonShape) :
    Fits names ρ (ComparisonBody.peelFuel total fuel t).base shape ↔ Fits names ρ t shape := by
  induction fuel generalizing t with
  | zero => rfl
  | succ fuel ih =>
    have hn := normalizeOuterFuel_fits names ρ (ComparisonPartialModes.modalitySize t) t shape
    change Fits names ρ (ComparisonPartialModes.normalizeOuter t) shape ↔ _ at hn
    cases he : ComparisonPartialModes.normalizeOuter t <;> simp only [ComparisonBody.peelFuel, he]
    all_goals try exact he ▸ hn
    split
    · exact (ih _).trans (by simpa only [he, Fits] using hn)
    · exact he ▸ hn

theorem bareVariable_fits {indices names : List Nat} {ρ : TypeVar → ComparisonShape}
    {t : Ty} {n : Nat} {shape : ComparisonShape}
    (h : bareVariable indices t = some n) (hn : n ∈ names) (hf : Fits names ρ t shape) :
    ρ (.flex n) = shape := by
  induction t with
  | var v =>
    cases v <;> simp only [bareVariable] at h <;> try contradiction
    split at h
    · cases Option.some.inj h; simpa only [Fits, hn, ↓reduceIte] using hf
    · contradiction
  | modal a m ih =>
    unfold bareVariable at h
    split at h <;> try contradiction
    all_goals cases ‹a.modal m = _›
    exact ih h hf
  | unit | credit | prod | sum | fn => contradiction

def FitsHolds (names : List Nat) (ρ : TypeVar → ComparisonShape) (s : State) : Prop :=
  (∀ p ∈ s.pending, Fits names ρ p.1 ((ComparisonShape.ofTy p.2).subst ρ) ∧
    Fits names ρ p.2 ((ComparisonShape.ofTy p.1).subst ρ)) ∧
  ∀ b ∈ s.bareBounds, (ComparisonShape.ofTy b.endpoint).subst ρ = ρ (.flex b.name)

theorem step_fitsHolds {s next : State} {ρ : TypeVar → ComparisonShape} {names : List Nat}
    (h : step s = .success next) (hnames : ∀ n ∈ s.bareVariables, n ∈ names)
    (hs : FitsHolds names ρ s) : FitsHolds names ρ next := by
  unfold step at h
  split at h
  · cases h; exact hs
  · next left right rest hpending =>
    simp only [FitsHolds, hpending, List.forall_mem_cons] at hs
    simp only at h
    split at h
    · cases h; exact ⟨hs.1.2, hs.2⟩
    · split at h
      · cases h
        refine ⟨hs.1.2, ?_⟩
        simp only [List.forall_mem_cons]
        exact ⟨(bareVariable_fits ‹bareVariable s.bareVariables left = some _›
          (hnames _ (bareVariable_mem ‹bareVariable s.bareVariables left = some _›)) hs.1.1.1).symm,
          hs.2⟩
      · cases h
        refine ⟨hs.1.2, ?_⟩
        simp only [List.forall_mem_cons]
        exact ⟨(bareVariable_fits ‹bareVariable s.bareVariables right = some _›
          (hnames _ (bareVariable_mem ‹bareVariable s.bareVariables right = some _›)) hs.1.1.2).symm,
          hs.2⟩
      · split at h
        · next result hshared =>
          cases h
          refine ⟨?_, hs.2⟩
          simp only [List.forall_mem_cons]
          refine ⟨?_, hs.1.2⟩
          split at hshared
          · obtain ⟨hl, hr⟩ := ComparisonBody.stripTotal_shape hshared
            obtain ⟨hb, _⟩ := ComparisonBody.stripTotal_spec hshared
            rw [hl, hr, hb]
            exact ⟨(peelFuel_fits names ρ _ 1 left _).mpr hs.1.1.1,
              (peelFuel_fits names ρ _ 1 right _).mpr hs.1.1.2⟩
          · contradiction
        · split at h
          · cases h; exact ⟨hs.1.2, hs.2⟩
          · split at h
            · cases h; exact ⟨hs.1.2, hs.2⟩
            · split at h
              all_goals try contradiction
              all_goals cases h
              all_goals try exact ⟨hs.1.2, hs.2⟩
              all_goals refine ⟨?_, hs.2⟩
              all_goals simp only [List.forall_mem_cons, ComparisonShape.ofTy, Fits]
              all_goals have hl := (fits_outer names ρ left _).mpr hs.1.1.1
              all_goals have hr := (fits_outer names ρ right _).mpr hs.1.1.2
              all_goals rw [← TypeExpr.outer_comparisonShape right] at hl
              all_goals rw [← TypeExpr.outer_comparisonShape left] at hr
              all_goals simp only [*, ComparisonShape.ofTy, ComparisonShape.subst, Fits] at hl hr
              · exact ⟨⟨hl.1, hr.1⟩, ⟨hl.2, hr.2⟩, hs.1.2⟩
              · exact ⟨⟨hl.1, hr.1⟩, ⟨hl.2, hr.2⟩, hs.1.2⟩
              · exact ⟨⟨hr.1, hl.1⟩, ⟨hl.2, hr.2⟩, hs.1.2⟩

theorem run_fitsHolds {s next : State} {names : List Nat} {ρ : TypeVar → ComparisonShape} {fuel : Nat}
    (h : run fuel s = .success next) (hnames : ∀ n ∈ s.bareVariables, n ∈ names)
    (hs : FitsHolds names ρ s) : FitsHolds names ρ next := by
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at h
    split at h
    · cases h; exact hs
    · cases he : step s <;> simp only [he] at h <;> try contradiction
      next middle =>
        exact ih h (by simpa only [(step_metadata he).2.2.1] using hnames)
          (step_fitsHolds he hnames hs)

def Supported (P : TypeVar → Prop) (t : Ty) : Prop := ∀ v ∈ t.typeVars, P v

def PairPinned (names : List Nat) (P : TypeVar → Prop) (p : Ty × Ty) : Prop :=
  (TypeFree names p.1 ∧ TypeFree names p.2) ∨
    (TypeFree names p.1 ∧ Supported P p.1) ∨ (TypeFree names p.2 ∧ Supported P p.2)

def PinnedHolds (names : List Nat) (P : TypeVar → Prop) (s : State) : Prop :=
  (∀ p ∈ s.pending, PairPinned names P p) ∧
    ∀ b ∈ s.bareBounds, TypeFree names b.endpoint ∧ Supported P b.endpoint

theorem step_pinnedHolds {s next : State} {P : TypeVar → Prop} {names : List Nat}
    (h : step s = .success next) (hnames : ∀ n ∈ s.bareVariables, n ∈ names)
    (hs : PinnedHolds names P s) : PinnedHolds names P next := by
  unfold step at h
  split at h
  · cases h; exact hs
  · next left right rest hpending =>
    simp only [PinnedHolds, hpending, List.forall_mem_cons] at hs
    simp only at h
    split at h
    · cases h; exact ⟨hs.1.2, hs.2⟩
    · split at h
      · cases h
        refine ⟨hs.1.2, ?_⟩
        simp only [List.forall_mem_cons]
        refine ⟨?_, hs.2⟩
        have hn : ¬TypeFree names left := fun hf => hf _
          (hnames _ (bareVariable_mem ‹bareVariable s.bareVariables left = some _›))
          (bareVariable_type_mem ‹bareVariable s.bareVariables left = some _›)
        rcases hs.1.1 with hf | hl | hr
        · exact (hn hf.1).elim
        · exact (hn hl.1).elim
        · exact hr
      · cases h
        refine ⟨hs.1.2, ?_⟩
        simp only [List.forall_mem_cons]
        refine ⟨?_, hs.2⟩
        have hn : ¬TypeFree names right := fun hf => hf _
          (hnames _ (bareVariable_mem ‹bareVariable s.bareVariables right = some _›))
          (bareVariable_type_mem ‹bareVariable s.bareVariables right = some _›)
        rcases hs.1.1 with hf | hl | hr
        · exact (hn hf.2).elim
        · exact hl
        · exact (hn hr.1).elim
      · split at h
        · next result hshared =>
          cases h
          refine ⟨?_, hs.2⟩
          simp only [List.forall_mem_cons]
          refine ⟨?_, hs.1.2⟩
          split at hshared
          · obtain ⟨hl, hr⟩ := ComparisonBody.stripTotal_typeVars hshared
            simpa only [PairPinned, TypeFree, Supported, hl, hr] using hs.1.1
          · contradiction
        · split at h
          · cases h; exact ⟨hs.1.2, hs.2⟩
          · split at h
            · cases h; exact ⟨hs.1.2, hs.2⟩
            · split at h
              all_goals try contradiction
              all_goals cases h
              all_goals try exact ⟨hs.1.2, hs.2⟩
              all_goals refine ⟨?_, hs.2⟩
              all_goals simp only [List.forall_mem_cons]
              all_goals
                have hf : PairPinned names P (left.outer.1, right.outer.1) := by
                  simpa only [PairPinned, TypeFree, Supported, TypeExpr.outer_typeVars] using hs.1.1
              all_goals simp only [*, PairPinned, TypeFree, Supported, TypeExpr.typeVars,
                Finset.mem_union, not_or, or_imp, forall_and] at hf
              · rcases hf with hf | hl | hr
                · exact ⟨Or.inl ⟨hf.1.1, hf.2.1⟩, Or.inl ⟨hf.1.2, hf.2.2⟩, hs.1.2⟩
                · exact ⟨Or.inr (Or.inl ⟨hl.1.1, hl.2.1⟩),
                    Or.inr (Or.inl ⟨hl.1.2, hl.2.2⟩), hs.1.2⟩
                · exact ⟨Or.inr (Or.inr ⟨hr.1.1, hr.2.1⟩),
                    Or.inr (Or.inr ⟨hr.1.2, hr.2.2⟩), hs.1.2⟩
              · rcases hf with hf | hl | hr
                · exact ⟨Or.inl ⟨hf.1.1, hf.2.1⟩, Or.inl ⟨hf.1.2, hf.2.2⟩, hs.1.2⟩
                · exact ⟨Or.inr (Or.inl ⟨hl.1.1, hl.2.1⟩),
                    Or.inr (Or.inl ⟨hl.1.2, hl.2.2⟩), hs.1.2⟩
                · exact ⟨Or.inr (Or.inr ⟨hr.1.1, hr.2.1⟩),
                    Or.inr (Or.inr ⟨hr.1.2, hr.2.2⟩), hs.1.2⟩
              · rcases hf with hf | hl | hr
                · exact ⟨Or.inl ⟨hf.2.1, hf.1.1⟩, Or.inl ⟨hf.1.2, hf.2.2⟩, hs.1.2⟩
                · exact ⟨Or.inr (Or.inr ⟨hl.1.1, hl.2.1⟩),
                    Or.inr (Or.inl ⟨hl.1.2, hl.2.2⟩), hs.1.2⟩
                · exact ⟨Or.inr (Or.inl ⟨hr.1.1, hr.2.1⟩),
                    Or.inr (Or.inr ⟨hr.1.2, hr.2.2⟩), hs.1.2⟩

theorem run_pinnedHolds {s next : State} {names : List Nat} {P : TypeVar → Prop} {fuel : Nat}
    (h : run fuel s = .success next) (hnames : ∀ n ∈ s.bareVariables, n ∈ names)
    (hs : PinnedHolds names P s) : PinnedHolds names P next := by
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at h
    split at h
    · cases h; exact hs
    · cases he : step s <;> simp only [he] at h <;> try contradiction
      next middle =>
        exact ih h (by simpa only [(step_metadata he).2.2.1] using hnames)
          (step_pinnedHolds he hnames hs)

theorem initial_fitsHolds {bounds : Bounds} {source target : Ty} {names : List Nat}
    {ρ : TypeVar → ComparisonShape}
    (hb : ∀ n ∈ names, ∀ c ∈ bounds, TypeVar.flex n ∉ c.typeVars)
    (ht : TypeFree names target)
    (hf : Fits names ρ source ((ComparisonShape.ofTy target).subst ρ)) :
    FitsHolds names ρ (initial bounds source target) := by
  refine ⟨?_, by simp [initial]⟩
  intro pair hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨c, hc, hp⟩ := List.mem_filterMap.mp hp
    cases c <;> simp only at hp <;> try contradiction
    next a b =>
      cases hp
      obtain ⟨c, hc, hab⟩ := List.mem_flatMap.mp hc
      exact ⟨Fits.of_free (fun n hn hv => hb n hn c hc
          (Constraint.sub_assumptions_typeVars hab (Finset.mem_union_left _ hv))) _,
        Fits.of_free (fun n hn hv => hb n hn c hc
          (Constraint.sub_assumptions_typeVars hab (Finset.mem_union_right _ hv))) _⟩
  · obtain rfl := List.mem_singleton.mp hp
    exact ⟨hf, Fits.of_free ht _⟩

theorem initial_pinnedHolds {bounds : Bounds} {source target : Ty} {names : List Nat}
    {P : TypeVar → Prop}
    (hb : ∀ n ∈ names, ∀ c ∈ bounds, TypeVar.flex n ∉ c.typeVars)
    (ht : TypeFree names target) (hp : Supported P target) :
    PinnedHolds names P (initial bounds source target) := by
  refine ⟨?_, by simp [initial]⟩
  intro pair hpair
  rcases List.mem_append.mp hpair with hpair | hpair
  · obtain ⟨c, hc, hpair⟩ := List.mem_filterMap.mp hpair
    cases c <;> simp only at hpair <;> try contradiction
    next a b =>
      cases hpair
      obtain ⟨c, hc, hab⟩ := List.mem_flatMap.mp hc
      exact Or.inl ⟨fun n hn hv => hb n hn c hc
          (Constraint.sub_assumptions_typeVars hab (Finset.mem_union_left _ hv)),
        fun n hn hv => hb n hn c hc
          (Constraint.sub_assumptions_typeVars hab (Finset.mem_union_right _ hv))⟩
  · obtain rfl := List.mem_singleton.mp hpair
    exact Or.inr (Or.inr ⟨ht, hp⟩)

/-- Bare interval images require matching only along selected-variable paths.
Their fixed endpoints may be interpreted independently of other source images. -/
theorem prepare_partialTypes_wellShaped_of_fits {Δ : Bounds} {σ : CompareSubstitution}
    {fuel : Nat} {p : SchemePreparation.Prepared} {templates : ComparisonSkeleton.Templates}
    {bare : List Nat} {known : List ModExpr} {shared : Bool} {result : State}
    (ρ : (TypeVar → ComparisonShape) → TypeVar → ComparisonShape) (P : TypeVar → Prop)
    (h : prepare fuel p templates bare known shared = .success result)
    (hpinned : PinnedHolds bare P (initial (templates.substitution.bounds p.sourceBounds)
      (templates.substitution.ty p.sourceType) p.targetType))
    (hshape : ∀ η, ComparisonShape.Models Δ η → FitsHolds bare (ρ η)
      (initial (templates.substitution.bounds p.sourceBounds)
        (templates.substitution.ty p.sourceType) p.targetType))
    (htypes : ∀ v, P v → (σ.type v).WellShaped Δ)
    (hagrees : ∀ η, ComparisonShape.Models Δ η →
      ∀ v, P v → (σ.type v).shape.subst η = ρ η v) :
    ∀ entry ∈ result.partialTypes, (entry.2.subst σ.type σ.mode).WellShaped Δ := by
  simp only [prepare, bind, RunResult.bind] at h
  split at h
  · next reduced hfirst =>
    have hp := run_pinnedHolds hfirst (fun _ hn => hn) hpinned
    have hs := fun η hη => run_fitsHolds hfirst (fun _ hn => hn) (hshape η hη)
    intro entry he
    rw [run_partialTypes h] at he
    obtain ⟨name, hn, rfl⟩ := List.mem_map.mp he
    apply ComparisonPartial.image_subst_wellShaped
    · intro b hb _
      exact σ.ty_wellShaped_of_vars _ (fun v hv => htypes v ((hp.2 b hb).2 v hv))
    · intro a ha han b hb hbn η hη
      have hta : (σ.ty a.endpoint).shape.subst η =
          (ComparisonShape.ofTy a.endpoint).subst (ρ η) :=
        σ.ty_shape_eval _ _ _ (fun v hv => hagrees η hη v ((hp.2 a ha).2 v hv))
      have htb : (σ.ty b.endpoint).shape.subst η =
          (ComparisonShape.ofTy b.endpoint).subst (ρ η) :=
        σ.ty_shape_eval _ _ _ (fun v hv => hagrees η hη v ((hp.2 b hb).2 v hv))
      calc
        (σ.ty a.endpoint).shape.subst η =
            (ComparisonShape.ofTy a.endpoint).subst (ρ η) := hta
        _ = ρ η (.flex name) := by simpa only [han] using (hs η hη).2 a ha
        _ = (ComparisonShape.ofTy b.endpoint).subst (ρ η) :=
          by simpa only [hbn] using ((hs η hη).2 b hb).symm
        _ = (σ.ty b.endpoint).shape.subst η := htb.symm
  · contradiction
  · contradiction

private def ShapeFree (names : List Nat) (shape : ComparisonShape) : Prop :=
  ∀ n ∈ names, TypeVar.flex n ∉ shape.vars

private def ShapeFits (names : List Nat) (ρ : TypeVar → ComparisonShape) :
    ComparisonShape → ComparisonShape → Prop
  | .var (.flex n), shape => if n ∈ names then ρ (.flex n) = shape else True
  | .var (.rigid _), _ | .unit, _ | .credit, _ => True
  | .prod a b, .prod c d | .sum a b, .sum c d | .fn a b, .fn c d =>
    ShapeFits names ρ a c ∧ ShapeFits names ρ b d
  | .prod a b, _ | .sum a b, _ | .fn a b, _ => ShapeFree names a ∧ ShapeFree names b

private theorem shapeFree_ofTy (names : List Nat) (t : Ty) :
    ShapeFree names (ComparisonShape.ofTy t) ↔ TypeFree names t := by
  simp only [ShapeFree, TypeFree, ComparisonShapeSolver.mem_vars_ofTy]

private theorem shapeFits_ofTy (names : List Nat) (ρ : TypeVar → ComparisonShape)
    (t : Ty) (shape : ComparisonShape) :
    ShapeFits names ρ (ComparisonShape.ofTy t) shape ↔ Fits names ρ t shape := by
  induction t generalizing shape with
  | var v => cases v <;> rfl
  | unit | credit => rfl
  | modal _ _ ih => exact ih _
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    cases shape <;> simp only [ComparisonShape.ofTy, ShapeFits, Fits, shapeFree_ofTy, iha, ihb]

theorem fits_congr_shape {names : List Nat} {ρ : TypeVar → ComparisonShape}
    {t u : Ty} {shape : ComparisonShape} (h : ComparisonShape.ofTy t = ComparisonShape.ofTy u) :
    Fits names ρ t shape ↔ Fits names ρ u shape := by
  rw [← shapeFits_ofTy, ← shapeFits_ofTy, h]

end ModalityInference.ComparisonReduction

namespace ModalityInference.ComparisonAbsorption

theorem rewrite_shape {total : ModExpr → Bool} {owners : Owners} {t u : Ty}
    (h : rewrite total owners t = some u) : ComparisonShape.ofTy u = ComparisonShape.ofTy t := by
  induction t generalizing u with
  | var | unit | credit =>
    rw [rewrite.eq_def] at h
    split at h
    · cases Option.some.inj h; rfl
    · contradiction
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    rw [rewrite.eq_def] at h
    split at h
    · cases Option.some.inj h; rfl
    · cases ha : rewrite total owners a <;> simp only [ha, Option.bind_eq_bind, Option.bind] at h
      · contradiction
      · cases hb : rewrite total owners b <;> simp only [hb] at h
        · contradiction
        · cases Option.some.inj h
          simp only [ComparisonShape.ofTy, iha ha, ihb hb]
  | modal a m ih =>
    rw [rewrite.eq_def] at h
    split at h
    · cases Option.some.inj h; rfl
    · split at h
      · next x n he =>
        cases he
        split at h
        · cases Option.some.inj h; rfl
        · contradiction
      · next _ _ he => cases he
      · next _ _ he => cases he
      · next _ _ he => cases he
      · next a' m' _ he =>
        cases he
        split at h
        · cases ha : rewrite total owners a <;> simp only [ha, Option.map] at h
          · contradiction
          · cases Option.some.inj h
            simpa only [ComparisonShape.ofTy] using ih ha
        · contradiction
      · contradiction

theorem plan_shape (p : SchemePreparation.Prepared) (total : ModExpr → Bool) :
    ComparisonShape.ofTy (plan p total).body = ComparisonShape.ofTy p.sourceType :=
  rewrite_shape (plan_spec p total).2

end ModalityInference.ComparisonAbsorption

namespace ModalityInference

theorem Constraint.mem_typeVars_substitution (c : Constraint) (σ : Substitution) (v : TypeVar) :
    v ∈ (σ.constraint c).typeVars ↔ ∃ w ∈ c.typeVars, v ∈ (σ.type w).typeVars := by
  cases c <;> simp [Substitution.constraint, Constraint.subst, Constraint.typeVars,
    Substitution.ty, TypeExpr.mem_typeVars_subst, or_and_right, exists_or]
  rename_i w a
  cases w with
  | rigid n => simp [Substitution.type, TypeExpr.typeVars, TypeExpr.mem_typeVars_subst]
  | flex n =>
    cases he : σ.types.lookup n <;>
      simp [he, Substitution.type, TypeExpr.typeVars, TypeExpr.mem_typeVars_subst]

namespace ComparisonReduction

theorem typeFree_type_of_images {names : List Nat} {σ : Substitution}
    (hi : ∀ entry ∈ σ.types, TypeFree names entry.2)
    (v : TypeVar) (hv : ∀ n ∈ names, v ≠ .flex n) : TypeFree names (σ.type v) := by
  cases v with
  | rigid n => simp [Substitution.type, TypeFree, TypeExpr.typeVars]
  | flex n =>
    cases he : σ.types.lookup n with
    | none =>
      simp only [Substitution.type, he, Option.getD_none, TypeFree, TypeExpr.typeVars,
        Finset.mem_singleton, TypeVar.flex.injEq]
      intro k hk heq
      exact hv k hk (congrArg TypeVar.flex heq.symm)
    | some image =>
      obtain ⟨before, after, hs, _⟩ := List.lookup_eq_some_iff.mp he
      simpa only [Substitution.type, he, Option.getD_some] using
        hi (n, image) (by simp [hs])

theorem bounds_typeFree_subst {names : List Nat} {σ : Substitution} {bounds : Bounds}
    (hb : ∀ n ∈ names, ∀ c ∈ bounds, TypeVar.flex n ∉ c.typeVars)
    (hi : ∀ v, (∀ n ∈ names, v ≠ .flex n) → TypeFree names (σ.type v)) :
    ∀ n ∈ names, ∀ c ∈ σ.bounds bounds, TypeVar.flex n ∉ c.typeVars := by
  intro n hn c hc hv
  change c ∈ bounds.map σ.constraint at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨v, hv, hsub⟩ := (Constraint.mem_typeVars_substitution d σ (.flex n)).mp hv
  exact hi v (fun k hk he => hb k hk d hd (he ▸ hv)) n hn hsub

end ComparisonReduction

namespace ComparisonExactContext

theorem Scoped.typeImages_free {p : Prepared} {action : Substitution} {names : List Nat}
    (h : Scoped p action)
    (hn : ∀ n ∈ names, ComparisonInstance.typeAllowed p (.flex n) = true) :
    ∀ entry ∈ action.types, ComparisonReduction.TypeFree names entry.2 := by
  intro entry he n hn' hv
  exact Bool.noConfusion ((hn n hn').symm.trans ((h.1 entry.1 entry.2 he).2.1 _ hv))

end ComparisonExactContext

namespace ComparisonSkeleton

theorem allocate_images_typeVars (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (names : List Nat) (nt nm : Nat) :
    ∀ entry ∈ (allocate p shapes names nt nm).substitution.types,
      ∀ v ∈ entry.2.typeVars, ∃ leaf ∈ (allocate p shapes names nt nm).leaves,
        v = .flex leaf.name := by
  induction names generalizing nt nm with
  | nil => simp [allocate]
  | cons name names ih =>
    intro entry he v hv
    simp only [allocate, List.mem_cons] at he
    rcases he with rfl | he
    · obtain ⟨leaf, hl, he⟩ := build_typeVars p (shapes.resolveAll (.flex name)) nt nm v hv
      exact ⟨leaf, List.mem_append_left _ hl, he⟩
    · obtain ⟨leaf, hl, he⟩ := ih _ _ entry he v hv
      exact ⟨leaf, List.mem_append_right _ hl, he⟩

theorem allocate_images_free (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (names bare : List Nat) (nt nm : Nat)
    (hb : ∀ n ∈ bare, n < nt) :
    ∀ entry ∈ (allocate p shapes names nt nm).substitution.types,
      ComparisonReduction.TypeFree bare entry.2 := by
  intro entry he n hn hv
  obtain ⟨leaf, hl, he⟩ := allocate_images_typeVars p shapes names nt nm entry he (.flex n) hv
  have he := TypeVar.flex.inj he
  have hlo := (allocate_leaf_range p shapes names nt nm leaf hl).1
  have hhi := hb n hn
  omega

end ComparisonSkeleton

namespace ComparisonShapeSolver

theorem prepared_target_fixed (ambient : Bounds) (source target : Scheme) :
    ∀ v ∈ (SchemePreparation.prepare ambient source target).targetType.typeVars,
      sourceAllowed (SchemePreparation.prepare ambient source target) v = false := by
  let p := SchemePreparation.prepare ambient source target
  intro v hv
  obtain ⟨w, hw, hv⟩ := (TypeExpr.mem_typeVars_subst target.body
    p.targetRenaming.type p.targetRenaming.mode v).mp hv
  have ho : w ∈ SchemePreparation.originalTypeIds ambient source target := by
    simp only [SchemePreparation.originalTypeIds, List.mem_append]
    have hm := (TypeExpr.mem_typeVariables target.body w).mpr hw
    tauto
  cases w with
  | rigid n =>
    simp only [Substitution.type, TypeExpr.typeVars, Finset.mem_singleton] at hv
    exact hv ▸ rfl
  | flex n =>
    by_cases hn : n ∈ target.typeParams
    · obtain ⟨k, he, _, _⟩ := SchemePreparation.prepare_target_type_param ambient source target hn
      change p.targetRenaming.type (.flex n) = .var (.rigid k) at he
      simp only [he, TypeExpr.typeVars, Finset.mem_singleton] at hv
      exact hv ▸ rfl
    · have hf : p.targetRenaming.type (.flex n) = .var (.flex n) := by
        apply Substitution.type_fresh
        have hi := (target.freshSubstitution_instantiates
          (source.subsumptionIndices ambient target).1
          (source.subsumptionIndices ambient target).2 true).1
        exact fun hmem => hn (hi.mem_iff.mp hmem)
      simp only [hf, TypeExpr.typeVars, Finset.mem_singleton] at hv
      subst v
      exact prepared_original_fixed ambient source target _ ho

end ComparisonShapeSolver

end ModalityInference

namespace ModalityInference

@[simp] theorem CompareSubstitution.empty_type (v : TypeVar) :
    ({} : CompareSubstitution).type v = .var v := by cases v <;> rfl

@[simp] theorem CompareSubstitution.empty_mode (v : ModVar) :
    ({} : CompareSubstitution).mode v = .var v := by cases v <;> rfl

@[simp] theorem CompareTy.subst_id (t : CompareTy) : t.subst .var .var = t := by
  induction t <;> simp_all [CompareTy.subst, ModExpr.subst_id]

end ModalityInference

namespace ModalityInference.ComparisonChecker

open ComparisonReduction

/-- The actual interval witnesses are shape compatible even when the context
prepass independently specializes subtrees containing no interval variables. -/
theorem partial_images_wellShaped {ambient : Bounds} {source target : Scheme}
    {fuel : Nat} {shapes : ComparisonShapeSolver.Solved} {before : Substitution}
    {known : List ModExpr} {shared : Bool} {reduced : ComparisonReduction.State}
    (hshapes : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved shapes))
    (hbefore : ComparisonExactContext.Scoped (SchemePreparation.prepare ambient source target) before) :
    let p := SchemePreparation.prepare ambient source target
    let input := ComparisonExactContext.rewrite p before
    let total := ComparisonBody.isTotal known
    let absorption := ComparisonAbsorption.plan input total
    let absorbed := { input with sourceType := absorption.body }
    let annotations := ComparisonAnnotations.prepare absorbed total
    let work := { absorbed with sourceType := annotations.substitution.ty absorbed.sourceType }
    let selected := before.types.map Prod.fst
    let bare := (if shared then ComparisonBody.eligible work total
      else ComparisonPartial.eligible work).filter (fun n => !selected.contains n)
    let names := (List.range' p.firstType (p.nextType - p.firstType)).filter
      (fun n => !selected.contains n && !bare.contains n)
    let templates := ComparisonSkeleton.allocate work shapes names p.nextType annotations.nextMode
    ComparisonReduction.prepare fuel work templates bare known shared = .success reduced →
      ∀ entry ∈ reduced.partialTypes, entry.2.WellShaped p.assumptions := by
  let p := SchemePreparation.prepare ambient source target
  let input := ComparisonExactContext.rewrite p before
  let total := ComparisonBody.isTotal known
  let absorption := ComparisonAbsorption.plan input total
  let absorbed := { input with sourceType := absorption.body }
  let annotations := ComparisonAnnotations.prepare absorbed total
  let work := { absorbed with sourceType := annotations.substitution.ty absorbed.sourceType }
  let selected := before.types.map Prod.fst
  let bare := (if shared then ComparisonBody.eligible work total
    else ComparisonPartial.eligible work).filter (fun n => !selected.contains n)
  let names := (List.range' p.firstType (p.nextType - p.firstType)).filter
    (fun n => !selected.contains n && !bare.contains n)
  let templates := ComparisonSkeleton.allocate work shapes names p.nextType annotations.nextMode
  change ComparisonReduction.prepare fuel work templates bare known shared = .success reduced → _
  intro h
  have hb_range : ∀ n ∈ bare, p.firstType ≤ n ∧ n < p.nextType := by
    intro n hn
    have hn := (List.mem_filter.mp hn).1
    split at hn
    all_goals have hr := (List.mem_filter.mp hn).1
    all_goals simp only [List.mem_range'] at hr
    all_goals change ∃ i < p.nextType - p.firstType, n = p.firstType + 1 * i at hr
    all_goals obtain ⟨i, hi, he⟩ := hr
    all_goals constructor <;> omega
  have hb_allowed : ∀ n ∈ bare, ComparisonInstance.typeAllowed p (.flex n) = true := by
    intro n hn
    simpa only [ComparisonInstance.typeAllowed, Bool.and_eq_true, decide_eq_true_eq] using hb_range n hn
  have hb_bounds : ∀ n ∈ bare, ∀ c ∈ work.sourceBounds, TypeVar.flex n ∉ c.typeVars := by
    intro n hn
    have hn := (List.mem_filter.mp hn).1
    split at hn
    all_goals
      have hb := (List.mem_filter.mp hn).2
      simp only [Bool.and_eq_true] at hb
      exact (ComparisonPartial.absentFromBounds_correct n work.sourceBounds).mp hb.1
  have hb_before : ∀ n ∈ bare, before.type (.flex n) = .var (.flex n) := by
    intro n hn
    apply Substitution.type_fresh
    simpa [selected] using (List.mem_filter.mp hn).2
  have before_free := typeFree_type_of_images (hbefore.typeImages_free hb_allowed)
  have hb_names : ∀ n ∈ bare, n ∉ names := by
    intro n hn hm
    have hm := (List.mem_filter.mp hm).2
    simp only [Bool.and_eq_true] at hm
    have hm' : n ∉ bare := by simpa using hm.2
    exact hm' hn
  have templates_fix : ∀ n ∈ bare, templates.substitution.type (.flex n) = .var (.flex n) :=
    fun n hn => ComparisonSkeleton.allocate_fixes work shapes names p.nextType annotations.nextMode n
      (hb_names n hn)
  have templates_free := typeFree_type_of_images
    (ComparisonSkeleton.allocate_images_free work shapes names bare p.nextType annotations.nextMode
      (fun n hn => (hb_range n hn).2))
  have htarget : ∀ v ∈ p.targetType.typeVars, ComparisonShapeSolver.sourceAllowed p v = false :=
    ComparisonShapeSolver.prepared_target_fixed ambient source target
  have htfree : TypeFree bare p.targetType := by
    intro n hn hv
    exact Bool.noConfusion ((hb_allowed n hn).symm.trans (htarget _ hv))
  have hbounds := bounds_typeFree_subst hb_bounds templates_free
  let ρ : (TypeVar → ComparisonShape) → TypeVar → ComparisonShape :=
    fun η v => (shapes.resolveAll v).subst η
  have hfits : ∀ η, ComparisonShape.Models p.assumptions η →
      FitsHolds bare (ρ η) (initial (templates.substitution.bounds work.sourceBounds)
        (templates.substitution.ty work.sourceType) work.targetType) := by
    intro η _
    apply initial_fitsHolds hbounds htfree
    have ho := (ComparisonShapeSolver.prepare_sound hshapes).2
      (ComparisonShape.ofTy p.sourceType, ComparisonShape.ofTy p.targetType)
      (List.mem_append_right _ (List.mem_singleton_self _))
    have hs : (ComparisonShape.ofTy p.sourceType).subst (ρ η) =
        (ComparisonShape.ofTy p.targetType).subst (ρ η) := by
      simpa only [ComparisonShapeSolver.subst_comp] using congrArg (ComparisonShape.subst η) ho
    have hinput := (Fits.of_shape (names := bare) hs).subst hb_before before_free
    have habsorbed : Fits bare (ρ η) absorbed.sourceType
        ((ComparisonShape.ofTy p.targetType).subst (ρ η)) :=
      (fits_congr_shape (ComparisonAbsorption.plan_shape input total)).mpr hinput
    have hann_free : ∀ v, (∀ n ∈ bare, v ≠ .flex n) →
        TypeFree bare (annotations.substitution.type v) := by
      intro v hv n hn hm
      rw [ComparisonAnnotations.prepare_type] at hm
      exact hv n hn ((Finset.mem_singleton.mp hm).symm)
    have hwork := habsorbed.subst
      (fun n _ => ComparisonAnnotations.prepare_type absorbed total (.flex n)) hann_free
    exact hwork.subst templates_fix templates_free
  have hpinned := initial_pinnedHolds (source := templates.substitution.ty work.sourceType) hbounds htfree
    (show Supported (fun v => v ∈ p.targetType.typeVars) p.targetType from fun _ hv => hv)
  have hi := prepare_partialTypes_wellShaped_of_fits
    (σ := ({} : CompareSubstitution)) ρ (fun v => v ∈ p.targetType.typeVars)
    h hpinned hfits (by intro v _; simp only [CompareSubstitution.empty_type]; trivial) (by
      intro η hη v hv
      simp only [CompareSubstitution.empty_type, CompareTy.shape, ComparisonShape.subst]
      change η v = (shapes.resolveAll v).subst η
      rw [ComparisonShapeSolver.prepared_resolve_fixed hshapes (htarget v hv)]
      exact (ComparisonShapeSolver.unify_factor
        (ComparisonShapeSolver.prepare_solved_iff.mp hshapes).1 hη v).symm)
  have ht : ({} : CompareSubstitution).type = CompareTy.var := funext CompareSubstitution.empty_type
  have hm : ({} : CompareSubstitution).mode = ModExpr.var := funext CompareSubstitution.empty_mode
  simpa only [ht, hm, CompareTy.subst_id] using hi

end ModalityInference.ComparisonChecker
