import ModalityInference.Proofs.ComparisonElimination

namespace ModalityInference

theorem CompareTy.shape_subst_modes (a : CompareTy) (ms : ModVar → ModExpr) :
    (a.subst CompareTy.var ms).shape = a.shape := by
  induction a <;> simp_all [CompareTy.subst, CompareTy.shape]

theorem CompareTy.wellShaped_subst_modes_iff {Δ : Bounds} (a : CompareTy) (ms : ModVar → ModExpr) :
    (a.subst CompareTy.var ms).WellShaped Δ ↔ a.WellShaped Δ := by
  induction a <;> simp_all [CompareTy.subst, CompareTy.WellShaped, CompareTy.shape_subst_modes]

theorem CompareSubstitution.ty_wellShaped_of_vars {Δ : Bounds} (σ : CompareSubstitution) (t : Ty)
    (ht : ∀ v ∈ t.typeVars, (σ.type v).WellShaped Δ) : (σ.ty t).WellShaped Δ := by
  induction t <;> simp_all [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst,
    CompareTy.WellShaped, TypeExpr.typeVars, or_imp, forall_and]

theorem CompareSubstitution.ty_shape (σ : CompareSubstitution) (t : Ty) :
    (σ.ty t).shape = (ComparisonShape.ofTy t).subst (fun v => (σ.type v).shape) := by
  induction t <;> simp_all [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst,
    CompareTy.shape, ComparisonShape.ofTy, ComparisonShape.subst]

theorem CompareSubstitution.ty_shape_eval (σ : CompareSubstitution) (t : Ty)
    (ρ η : TypeVar → ComparisonShape)
    (ht : ∀ v ∈ t.typeVars, (σ.type v).shape.subst ρ = η v) :
    (σ.ty t).shape.subst ρ = (ComparisonShape.ofTy t).subst η := by
  rw [σ.ty_shape, ComparisonShapeSolver.subst_comp]
  exact ComparisonShapeSolver.subst_congr _
    (fun v hv => ht v ((ComparisonShapeSolver.mem_vars_ofTy t v).mp hv))

@[simp] theorem TypeExpr.outer_comparisonShape (t : Ty) :
    ComparisonShape.ofTy t.outer.1 = ComparisonShape.ofTy t := by
  induction t <;> simp_all [TypeExpr.outer, ComparisonShape.ofTy]

theorem ComparisonPartialModes.normalizeOuterFuel_shape (fuel : Nat) (t : Ty) :
    ComparisonShape.ofTy (normalizeOuterFuel fuel t) = ComparisonShape.ofTy t := by
  induction fuel generalizing t with
  | zero => rfl
  | succ fuel ih =>
    cases t <;> try rfl
    next a m =>
      cases m <;> simp only [normalizeOuterFuel]
      case compose m n => exact ih (.modal (.modal a m) n)
      all_goals split
      all_goals first | exact ih a | rfl

theorem ComparisonBody.peelFuel_shape (total : ModExpr → Bool) (fuel : Nat) (t : Ty) :
    ComparisonShape.ofTy (peelFuel total fuel t).base = ComparisonShape.ofTy t := by
  induction fuel generalizing t with
  | zero => rfl
  | succ fuel ih =>
    have hn := ComparisonPartialModes.normalizeOuterFuel_shape
      (ComparisonPartialModes.modalitySize t) t
    change ComparisonShape.ofTy (ComparisonPartialModes.normalizeOuter t) = _ at hn
    cases he : ComparisonPartialModes.normalizeOuter t <;> simp only [peelFuel, he]
    all_goals try exact he ▸ hn
    split
    · exact (ih _).trans (by simpa only [he, ComparisonShape.ofTy] using hn)
    · exact he ▸ hn

theorem ComparisonBody.stripTotal_shape {total : ModExpr → Bool} {left right : Ty}
    {result : TotalStep} (h : stripTotal total left right = some result) :
    ComparisonShape.ofTy result.bases.1 = ComparisonShape.ofTy left ∧
      ComparisonShape.ofTy result.bases.2 = ComparisonShape.ofTy right := by
  obtain ⟨hb, _⟩ := stripTotal_spec h
  rw [hb]
  exact ⟨peelFuel_shape total 1 left, peelFuel_shape total 1 right⟩

private theorem sub_not_wellFormedBounds (a b t : Ty) :
    Constraint.sub a b ∉ t.wellFormedBounds := by
  intro h
  obtain ⟨m, hm⟩ := t.wellFormedBounds_is_defined _ h
  contradiction

theorem ComparisonShape.Models.sub_assumptions {bounds : Bounds} {ρ : TypeVar → ComparisonShape}
    (h : ComparisonShape.Models bounds ρ) {a b : Ty}
    (hc : Constraint.sub a b ∈ bounds.assumptions) :
    (ComparisonShape.ofTy a).subst ρ = (ComparisonShape.ofTy b).subst ρ := by
  obtain ⟨c, hc, hd⟩ := List.mem_flatMap.mp hc
  have hm : ∀ pair ∈ ComparisonShape.pairs [c],
      pair.1.subst ρ = pair.2.subst ρ := by
    intro pair hp
    have hp' : pair ∈ ComparisonShape.pairs bounds := by
      apply List.mem_flatMap.mpr
      refine ⟨c, hc, ?_⟩
      simpa only [ComparisonShape.pairs, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] using hp
    exact h pair hp'
  cases c <;> simp only [Constraint.assumptions, List.mem_append, List.mem_cons,
    List.not_mem_nil, sub_not_wellFormedBounds, or_false] at hd
  all_goals simp only [ComparisonShape.pairs, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_singleton, forall_eq] at hm
  case sub x y => cases hd; exact hm
  case equiv x y | equal v t =>
    rcases hd with hd | hd
    · cases hd; exact hm
    · cases hd; exact hm.symm
  all_goals contradiction

theorem Constraint.sub_assumptions_typeVars {c : Constraint} {a b : Ty}
    (h : Constraint.sub a b ∈ c.assumptions) : a.typeVars ∪ b.typeVars ⊆ c.typeVars := by
  cases c <;> simp only [Constraint.assumptions, List.mem_append, List.mem_cons,
    List.not_mem_nil, sub_not_wellFormedBounds, or_false] at h
  case sub x y => cases h; exact Finset.Subset.refl _
  case equiv x y | equal v t =>
    rcases h with h | h <;> cases h <;>
      simp [Constraint.typeVars, TypeExpr.typeVars, Finset.union_comm]
  all_goals contradiction

theorem ComparisonPartialModes.normalizeOuterFuel_typeVars (fuel : Nat) (t : Ty) :
    (normalizeOuterFuel fuel t).typeVars = t.typeVars := by
  induction fuel generalizing t with
  | zero => rfl
  | succ fuel ih =>
    cases t <;> try rfl
    next a m =>
      cases m <;> simp only [normalizeOuterFuel]
      case compose m n => exact ih (.modal (.modal a m) n)
      all_goals split
      all_goals first | exact ih a | rfl

theorem ComparisonBody.peelFuel_typeVars (total : ModExpr → Bool) (fuel : Nat) (t : Ty) :
    (peelFuel total fuel t).base.typeVars = t.typeVars := by
  induction fuel generalizing t with
  | zero => rfl
  | succ fuel ih =>
    have hn := ComparisonPartialModes.normalizeOuterFuel_typeVars
      (ComparisonPartialModes.modalitySize t) t
    change (ComparisonPartialModes.normalizeOuter t).typeVars = _ at hn
    cases he : ComparisonPartialModes.normalizeOuter t <;> simp only [peelFuel, he]
    all_goals try exact he ▸ hn
    split
    · exact (ih _).trans (by simpa only [he, TypeExpr.typeVars] using hn)
    · exact he ▸ hn

theorem ComparisonBody.stripTotal_typeVars {total : ModExpr → Bool} {left right : Ty}
    {result : TotalStep} (h : stripTotal total left right = some result) :
    result.bases.1.typeVars = left.typeVars ∧ result.bases.2.typeVars = right.typeVars := by
  obtain ⟨hb, _⟩ := stripTotal_spec h
  rw [hb]
  exact ⟨peelFuel_typeVars total 1 left, peelFuel_typeVars total 1 right⟩

namespace ComparisonReduction

def ShapeHolds (ρ : TypeVar → ComparisonShape) (s : State) : Prop :=
  (∀ p ∈ s.pending, (ComparisonShape.ofTy p.1).subst ρ = (ComparisonShape.ofTy p.2).subst ρ) ∧
    ∀ b ∈ s.bareBounds, (ComparisonShape.ofTy b.endpoint).subst ρ = ρ (.flex b.name)

theorem bareVariable_shape {names : List Nat} {t : Ty} {n : Nat}
    (h : bareVariable names t = some n) : ComparisonShape.ofTy t = .var (.flex n) := by
  induction t with
  | var v =>
    cases v <;> simp only [bareVariable] at h <;> try contradiction
    split at h
    · cases Option.some.inj h; rfl
    · contradiction
  | modal a m ih =>
    unfold bareVariable at h
    split at h <;> try contradiction
    all_goals cases ‹a.modal m = _›
    exact ih h
  | unit | credit | prod | sum | fn => contradiction

theorem bareVariable_type_mem {names : List Nat} {t : Ty} {n : Nat}
    (h : bareVariable names t = some n) : TypeVar.flex n ∈ t.typeVars := by
  apply (ComparisonShapeSolver.mem_vars_ofTy t (.flex n)).mp
  rw [bareVariable_shape h]
  exact List.mem_singleton_self _

def TypeFree (names : List Nat) (t : Ty) : Prop :=
  ∀ n ∈ names, TypeVar.flex n ∉ t.typeVars

def FreeHolds (names : List Nat) (s : State) : Prop :=
  (∀ p ∈ s.pending, TypeFree names p.1 ∨ TypeFree names p.2) ∧
    ∀ b ∈ s.bareBounds, TypeFree names b.endpoint

private theorem typeFree_prod {names a b} :
    TypeFree names (.prod a b) ↔ TypeFree names a ∧ TypeFree names b := by
  simp [TypeFree, TypeExpr.typeVars, not_or, forall_and]

private theorem typeFree_sum {names a b} :
    TypeFree names (.sum a b) ↔ TypeFree names a ∧ TypeFree names b := by
  simp [TypeFree, TypeExpr.typeVars, not_or, forall_and]

private theorem typeFree_fn {names a b} :
    TypeFree names (.fn a b) ↔ TypeFree names a ∧ TypeFree names b := by
  simp [TypeFree, TypeExpr.typeVars, not_or, forall_and]

theorem initial_freeHolds {bounds : Bounds} {source target : Ty} {names : List Nat}
    (hb : ∀ n ∈ names, ∀ c ∈ bounds, TypeVar.flex n ∉ c.typeVars)
    (ht : TypeFree names target) : FreeHolds names (initial bounds source target) := by
  refine ⟨?_, by simp [initial]⟩
  intro pair hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨c, hc, hp⟩ := List.mem_filterMap.mp hp
    cases c <;> simp only at hp <;> try contradiction
    next a b =>
      cases hp
      obtain ⟨c, hc, hab⟩ := List.mem_flatMap.mp hc
      exact Or.inl (fun n hn hv => hb n hn c hc
        (Constraint.sub_assumptions_typeVars hab (Finset.mem_union_left _ hv)))
  · obtain rfl := List.mem_singleton.mp hp
    exact Or.inr ht

theorem step_freeHolds {s next : State} {names : List Nat}
    (h : step s = .success next) (hnames : ∀ n ∈ s.bareVariables, n ∈ names)
    (hs : FreeHolds names s) : FreeHolds names next := by
  unfold step at h
  split at h
  · cases h; exact hs
  · next left right rest hpending =>
    simp only [FreeHolds, hpending, List.forall_mem_cons] at hs
    simp only at h
    split at h
    · cases h; exact ⟨hs.1.2, hs.2⟩
    · split at h
      · cases h
        refine ⟨hs.1.2, ?_⟩
        simp only [List.forall_mem_cons]
        refine ⟨?_, hs.2⟩
        rcases hs.1.1 with hl | hr
        · exact False.elim (hl _
            (hnames _ (bareVariable_mem ‹bareVariable s.bareVariables left = some _›))
            (bareVariable_type_mem ‹bareVariable s.bareVariables left = some _›))
        · exact hr
      · cases h
        refine ⟨hs.1.2, ?_⟩
        simp only [List.forall_mem_cons]
        refine ⟨?_, hs.2⟩
        rcases hs.1.1 with hl | hr
        · exact hl
        · exact False.elim (hr _
            (hnames _ (bareVariable_mem ‹bareVariable s.bareVariables right = some _›))
            (bareVariable_type_mem ‹bareVariable s.bareVariables right = some _›))
      · split at h
        · next result hshared =>
          cases h
          refine ⟨?_, hs.2⟩
          simp only [List.forall_mem_cons]
          refine ⟨?_, hs.1.2⟩
          split at hshared
          · obtain ⟨hl, hr⟩ := ComparisonBody.stripTotal_typeVars hshared
            simpa only [TypeFree, hl, hr] using hs.1.1
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
                have hf : TypeFree names left.outer.1 ∨ TypeFree names right.outer.1 := by
                  simpa only [TypeFree, TypeExpr.outer_typeVars] using hs.1.1
              all_goals simp only [*, typeFree_prod, typeFree_sum, typeFree_fn] at hf
              · rcases hf with hl | hr
                · exact ⟨Or.inl hl.1, Or.inl hl.2, hs.1.2⟩
                · exact ⟨Or.inr hr.1, Or.inr hr.2, hs.1.2⟩
              · rcases hf with hl | hr
                · exact ⟨Or.inl hl.1, Or.inl hl.2, hs.1.2⟩
                · exact ⟨Or.inr hr.1, Or.inr hr.2, hs.1.2⟩
              · rcases hf with hl | hr
                · exact ⟨Or.inr hl.1, Or.inl hl.2, hs.1.2⟩
                · exact ⟨Or.inl hr.1, Or.inr hr.2, hs.1.2⟩

theorem run_freeHolds {s next : State} {names : List Nat} {fuel : Nat}
    (h : run fuel s = .success next) (hnames : ∀ n ∈ s.bareVariables, n ∈ names)
    (hs : FreeHolds names s) : FreeHolds names next := by
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at h
    split at h
    · cases h; exact hs
    · cases he : step s <;> simp only [he] at h <;> try contradiction
      next middle =>
        exact ih h (by simpa only [(step_metadata he).2.2.1] using hnames)
          (step_freeHolds he hnames hs)

theorem step_shapeHolds {s next : State} {ρ : TypeVar → ComparisonShape}
    (h : step s = .success next) (hs : ShapeHolds ρ s) : ShapeHolds ρ next := by
  unfold step at h
  split at h
  · cases h; exact hs
  · next left right rest hpending =>
    simp only [ShapeHolds, hpending, List.forall_mem_cons] at hs
    simp only at h
    split at h
    · cases h; exact ⟨hs.1.2, hs.2⟩
    · split at h
      · cases h
        refine ⟨hs.1.2, ?_⟩
        simp only [List.forall_mem_cons]
        exact ⟨hs.1.1.symm.trans (congrArg (ComparisonShape.subst ρ)
          (bareVariable_shape ‹bareVariable s.bareVariables left = some _›)), hs.2⟩
      · cases h
        refine ⟨hs.1.2, ?_⟩
        simp only [List.forall_mem_cons]
        exact ⟨hs.1.1.trans (congrArg (ComparisonShape.subst ρ)
          (bareVariable_shape ‹bareVariable s.bareVariables right = some _›)), hs.2⟩
      · split at h
        · next result hshared =>
          cases h
          refine ⟨?_, hs.2⟩
          simp only [List.forall_mem_cons]
          refine ⟨?_, hs.1.2⟩
          split at hshared
          · obtain ⟨hl, hr⟩ := ComparisonBody.stripTotal_shape hshared
            exact (congrArg (ComparisonShape.subst ρ) hl).trans
              (hs.1.1.trans (congrArg (ComparisonShape.subst ρ) hr).symm)
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
              all_goals simp only [List.forall_mem_cons, ComparisonShape.ofTy]
              all_goals have he := hs.1.1
              all_goals rw [← TypeExpr.outer_comparisonShape left,
                ← TypeExpr.outer_comparisonShape right] at he
              all_goals simp only [*, ComparisonShape.ofTy, ComparisonShape.subst,
                ComparisonShape.prod.injEq, ComparisonShape.sum.injEq,
                ComparisonShape.fn.injEq] at he
              · exact ⟨he.1, he.2, hs.1.2⟩
              · exact ⟨he.1, he.2, hs.1.2⟩
              · exact ⟨he.1.symm, he.2, hs.1.2⟩

theorem initial_shapeHolds {ρ : TypeVar → ComparisonShape} {bounds : Bounds} {source target : Ty}
    (hb : ComparisonShape.Models bounds ρ)
    (ht : (ComparisonShape.ofTy source).subst ρ = (ComparisonShape.ofTy target).subst ρ) :
    ShapeHolds ρ (initial bounds source target) := by
  refine ⟨?_, by simp [initial]⟩
  intro pair hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨c, hc, hp⟩ := List.mem_filterMap.mp hp
    cases c <;> simp only at hp <;> try contradiction
    next a b => cases hp; exact hb.sub_assumptions hc
  · obtain rfl := List.mem_singleton.mp hp
    exact ht

theorem run_shapeHolds {s next : State} {ρ : TypeVar → ComparisonShape} {fuel : Nat}
    (h : run fuel s = .success next) (hs : ShapeHolds ρ s) : ShapeHolds ρ next := by
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at h
    split at h
    · cases h; exact hs
    · cases he : step s <;> simp only [he] at h <;> try contradiction
      next middle => exact ih h (step_shapeHolds he hs)

end ComparisonReduction
namespace ComparisonInterpolation

theorem witness_wellShaped {Δ : Bounds} {lower upper : List CompareTy}
    (hh : ∀ a ∈ lower ++ upper, a.WellShaped Δ)
    (hc : ∀ a ∈ lower ++ upper, ∀ b ∈ lower ++ upper,
      ComparisonShape.Equivalent Δ a.shape b.shape) : (witness lower upper).WellShaped Δ := by
  cases lower with
  | nil =>
    cases upper with
    | nil => trivial
    | cons a upper =>
      exact (meet_commonShape (fun b hb => ⟨hh b hb, hc b hb a List.mem_cons_self⟩)).1
  | cons a lower =>
    exact (join_commonShape (fun b hb =>
      ⟨hh b (List.mem_append_left _ hb),
        hc b (List.mem_append_left _ hb) a (List.mem_append_left _ List.mem_cons_self)⟩)).1

end ComparisonInterpolation

namespace ComparisonPartial

theorem image_subst_wellShaped {Δ : Bounds} {σ : CompareSubstitution} {name : Nat}
    {bounds : List BareBound}
    (hh : ∀ b ∈ bounds, b.name = name → (σ.ty b.endpoint).WellShaped Δ)
    (hc : ∀ a ∈ bounds, a.name = name → ∀ b ∈ bounds, b.name = name →
      ComparisonShape.Equivalent Δ (σ.ty a.endpoint).shape (σ.ty b.endpoint).shape) :
    ((image name bounds).subst σ.type σ.mode).WellShaped Δ := by
  rw [ComparisonReduction.bare_image_action]
  have horigin : ∀ a ∈ (lower name bounds).map σ.ty ++ (upper name bounds).map σ.ty,
      ∃ b ∈ bounds, b.name = name ∧ σ.ty b.endpoint = a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b, hb, hn, _, rfl⟩ := mem_lower.mp ht
      exact ⟨b, hb, hn, rfl⟩
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b, hb, hn, _, rfl⟩ := mem_upper.mp ht
      exact ⟨b, hb, hn, rfl⟩
  apply ComparisonInterpolation.witness_wellShaped
  · intro a ha
    obtain ⟨b, hb, hn, rfl⟩ := horigin a ha
    exact hh b hb hn
  · intro a ha b hb
    obtain ⟨x, hx, hxn, rfl⟩ := horigin a ha
    obtain ⟨y, hy, hyn, rfl⟩ := horigin b hb
    exact hc x hx hxn y hy hyn

end ComparisonPartial

namespace ComparisonSkeleton

theorem leaves_name_injective (p : SchemePreparation.Prepared) (shape : ComparisonShape) (nt : Nat)
    {a b : Leaf} (ha : a ∈ leaves p shape nt) (hb : b ∈ leaves p shape nt)
    (he : a.name = b.name) : a = b := by
  induction shape generalizing nt with
  | var v =>
    by_cases h : ComparisonShapeSolver.sourceAllowed p v = true
    · simp [leaves, h] at ha
    · simp [leaves, h] at ha hb
      exact ha.trans hb.symm
  | unit | credit => simp [leaves] at ha
  | prod x y ihx ihy | sum x y ihx ihy | fn x y ihx ihy =>
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    · exact ihx _ ha hb
    · have hx := leaves_range p x nt a ha
      have hy := leaves_range p y (nt + typeCount p x) b hb
      omega
    · have hx := leaves_range p x nt b hb
      have hy := leaves_range p y (nt + typeCount p x) a ha
      omega
    · exact ihy _ ha hb

theorem allocate_leaf_name_injective (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (names : List Nat) (nt nm : Nat)
    {a b : Leaf} (ha : a ∈ (allocate p shapes names nt nm).leaves)
    (hb : b ∈ (allocate p shapes names nt nm).leaves) (he : a.name = b.name) : a = b := by
  induction names generalizing nt nm with
  | nil => simp [allocate] at ha
  | cons n names ih =>
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    · exact leaves_name_injective p _ _ ha hb he
    · have hx := leaves_range p (shapes.resolveAll (.flex n)) nt a ha
      have hy := allocate_leaf_range p shapes names _ _ b hb
      omega
    · have hx := leaves_range p (shapes.resolveAll (.flex n)) nt b hb
      have hy := allocate_leaf_range p shapes names _ _ a ha
      omega
    · exact ih _ _ ha hb

theorem build_shape (p : SchemePreparation.Prepared) (shape : ComparisonShape) (nt nm : Nat)
    (σ : CompareSubstitution) (η : TypeVar → ComparisonShape)
    (hh : ∀ leaf ∈ leaves p shape nt, (σ.type (.flex leaf.name)).shape.subst η = η leaf.shapeClass) :
    (σ.ty (build p shape nt nm)).shape.subst η =
      shape.subst (fun v => if ComparisonShapeSolver.sourceAllowed p v then .unit else η v) := by
  induction shape generalizing nt nm with
  | var v =>
    by_cases h : ComparisonShapeSolver.sourceAllowed p v = true
    · simp [build, h, CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst,
        CompareTy.shape, ComparisonShape.subst]
    · have hv := hh ⟨nt, v⟩ (by simp [leaves, h])
      simpa only [build, h, ↓reduceIte, CompareSubstitution.ty, CompareTy.ofTy,
        CompareTy.subst, CompareTy.shape, ComparisonShape.subst] using hv
  | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    have ha := iha nt (nm + 1) (fun leaf hl => hh leaf (List.mem_append_left _ hl))
    have hb := ihb (nt + typeCount p a) (nm + 1 + modeCount p a)
      (fun leaf hl => hh leaf (List.mem_append_right _ hl))
    first
    | exact congrArg₂ ComparisonShape.prod ha hb
    | exact congrArg₂ ComparisonShape.sum ha hb
    | exact congrArg₂ ComparisonShape.fn ha hb

theorem allocate_images_shape (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (names : List Nat) (nt nm : Nat)
    (σ : CompareSubstitution) (η : TypeVar → ComparisonShape)
    (hh : ∀ leaf ∈ (allocate p shapes names nt nm).leaves,
      (σ.type (.flex leaf.name)).shape.subst η = η leaf.shapeClass) :
    ∀ entry ∈ (allocate p shapes names nt nm).substitution.types,
      (σ.ty entry.2).shape.subst η = (shapes.resolveAll (.flex entry.1)).subst
        (fun v => if ComparisonShapeSolver.sourceAllowed p v then .unit else η v) := by
  induction names generalizing nt nm with
  | nil => simp [allocate]
  | cons n names ih =>
    intro entry he
    rcases List.mem_cons.mp he with rfl | he
    · exact build_shape p _ _ _ σ η (fun leaf hl => hh leaf (List.mem_append_left _ hl))
    · exact ih _ _ (fun leaf hl => hh leaf (List.mem_append_right _ hl)) entry he

end ComparisonSkeleton

namespace ComparisonGroups

theorem collect_leaf_coverage {p : SchemePreparation.Prepared} {shapes : ComparisonShapeSolver.Solved}
    {templates : ComparisonSkeleton.Templates} {reduced : ComparisonReduction.State}
    {groups : List Group} (h : collect p shapes templates reduced = .success groups) :
    ∀ leaf ∈ templates.leaves, ∃ g ∈ groups, leaf.name ∈ g.leaves := by
  unfold collect at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (split at h <;> try simp only at h)
  · cases h
    intro leaf hl
    refine ⟨_, List.mem_map.mpr ⟨leaf.shapeClass, ?_, rfl⟩, ?_⟩
    · exact List.mem_dedup.mpr (List.mem_append_left _
        (List.mem_append_left _ (List.mem_map.mpr ⟨leaf, hl, rfl⟩)))
    · exact List.mem_filterMap.mpr ⟨leaf, hl, by simp⟩
  · have hnone := RunResult.forIn_preserves
      (fun r : MProd (Option (List Group)) PUnit => r.fst = none) (by assumption) rfl (by
        intro pair hp before after hb hs
        repeat' first
          | contradiction
          | (cases hs; rfl)
          | (split at hs <;> try simp only at hs))
    simp_all

end ComparisonGroups

namespace ComparisonElimination

private theorem forall₂_output {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => simp at hx
  | cons hr h ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, hr⟩ := ih hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

theorem run_leaf_coverage {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {result : Result}
    (h : run fuel p shapes templates reduced = .success result) :
    ∀ leaf ∈ templates.leaves, ∃ t, result.types.lookup leaf.name = some t := by
  obtain ⟨groups, results, hc, hr, ht, _⟩ := run_spec h
  intro leaf hl
  obtain ⟨g, hg, hlg⟩ := ComparisonGroups.collect_leaf_coverage hc leaf hl
  obtain ⟨output, ho, hgo⟩ := forall₂_output hr hg
  rw [← group_domain hgo] at hlg
  obtain ⟨entry, he, hname⟩ := List.mem_map.mp hlg
  have hm : entry ∈ result.types := ht ▸ List.mem_flatMap.mpr ⟨output, ho, he⟩
  cases hlk : result.types.lookup leaf.name with
  | none =>
    have hn := List.lookup_eq_none_iff.mp hlk entry hm
    simp [hname] at hn
  | some t => exact ⟨t, rfl⟩

theorem run_leaf_commonShape {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {result : Result}
    (hfixed : ∀ η, ComparisonShape.Models p.assumptions η →
      ∀ v, (shapes.fixedShapes v).subst η = η v)
    (h : run fuel p shapes templates reduced = .success result)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    (hunique : ∀ a ∈ templates.leaves, ∀ b ∈ templates.leaves, a.name = b.name → a = b) :
    ∀ entry ∈ result.types, ∀ leaf ∈ templates.leaves, leaf.name = entry.1 →
      entry.2.WellShaped p.assumptions ∧
      ComparisonShape.Equivalent p.assumptions entry.2.shape (.var leaf.shapeClass) := by
  obtain ⟨groups, hc, hg⟩ := run_group_source h
  intro entry he leaf hl hln
  obtain ⟨g, hgm, output, hgo, heo⟩ := hg entry he
  have hn : entry.1 ∈ g.leaves := by
    rw [← group_domain hgo]
    exact List.mem_map.mpr ⟨entry, heo, rfl⟩
  obtain ⟨other, ho, hon, hoc⟩ := ComparisonGroups.collect_leaf_origin hc g hgm entry.1 hn
  have heq := hunique leaf hl other ho (hln.trans hon.symm)
  subst other
  have hi := group_commonShape (shape := .var g.shapeClass) hgo (by
    intro v hv η hη
    obtain ⟨hv', _, hvc⟩ := ComparisonGroups.collect_head_origin hc g hgm v hv
    have hc' := ComparisonGroups.shapeClass_fixed (fun leaf hl => hfresh leaf hl v hv') hvc
    simpa only [hc', ComparisonShape.subst] using (hfixed η hη v).symm) entry heo
  simpa only [hoc] using hi

theorem run_leaf_interpretation {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {result : Result}
    (hfixed : ∀ η, ComparisonShape.Models p.assumptions η →
      ∀ v, (shapes.fixedShapes v).subst η = η v)
    (h : run fuel p shapes templates reduced = .success result)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    (hunique : ∀ a ∈ templates.leaves, ∀ b ∈ templates.leaves, a.name = b.name → a = b) :
    ∀ leaf ∈ templates.leaves,
      let a := ({ types := result.types } : CompareSubstitution).type (.flex leaf.name)
      a.WellShaped p.assumptions ∧
        ComparisonShape.Equivalent p.assumptions a.shape (.var leaf.shapeClass) := by
  intro leaf hl
  obtain ⟨t, ht⟩ := run_leaf_coverage h leaf hl
  have hm : (leaf.name, t) ∈ result.types := by
    obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp ht
    simp [he]
  simpa only [CompareSubstitution.type, ht, Option.getD_some] using
    run_leaf_commonShape hfixed h hfresh hunique (leaf.name, t) hm leaf hl rfl

end ComparisonElimination

namespace ComparisonReduction

/-- Bare interval reconstruction uses only the pre-interval action on endpoint
variables. The final images are not assumed to be well-shaped. -/
theorem prepare_partialTypes_wellShaped {Δ : Bounds} {σ : CompareSubstitution} {fuel : Nat}
    {p : SchemePreparation.Prepared} {templates : ComparisonSkeleton.Templates}
    {bare : List Nat} {known : List ModExpr} {shared : Bool} {result : State}
    (ρ : (TypeVar → ComparisonShape) → TypeVar → ComparisonShape)
    (h : prepare fuel p templates bare known shared = .success result)
    (hfree : FreeHolds bare (initial (templates.substitution.bounds p.sourceBounds)
      (templates.substitution.ty p.sourceType) p.targetType))
    (hshape : ∀ η, ComparisonShape.Models Δ η → ShapeHolds (ρ η)
      (initial (templates.substitution.bounds p.sourceBounds)
        (templates.substitution.ty p.sourceType) p.targetType))
    (htypes : ∀ v, (∀ n ∈ bare, v ≠ .flex n) → (σ.type v).WellShaped Δ)
    (hagrees : ∀ η, ComparisonShape.Models Δ η →
      ∀ v, (∀ n ∈ bare, v ≠ .flex n) → (σ.type v).shape.subst η = ρ η v) :
    ∀ entry ∈ result.partialTypes, (entry.2.subst σ.type σ.mode).WellShaped Δ := by
  simp only [prepare, bind, RunResult.bind] at h
  split at h
  · next reduced hfirst =>
    have hf := run_freeHolds hfirst (fun _ hn => hn) hfree
    have hs := fun η hη => run_shapeHolds hfirst (hshape η hη)
    intro entry he
    rw [run_partialTypes h] at he
    obtain ⟨name, hn, rfl⟩ := List.mem_map.mp he
    apply ComparisonPartial.image_subst_wellShaped
    · intro b hb _
      apply σ.ty_wellShaped_of_vars
      intro v hv
      apply htypes v
      intro n hn he
      exact hf.2 b hb n hn (he ▸ hv)
    · intro a ha han b hb hbn η hη
      have hta : (σ.ty a.endpoint).shape.subst η =
          (ComparisonShape.ofTy a.endpoint).subst (ρ η) := by
        apply σ.ty_shape_eval
        intro v hv
        exact hagrees η hη v (fun n hn he => hf.2 a ha n hn (he ▸ hv))
      have htb : (σ.ty b.endpoint).shape.subst η =
          (ComparisonShape.ofTy b.endpoint).subst (ρ η) := by
        apply σ.ty_shape_eval
        intro v hv
        exact hagrees η hη v (fun n hn he => hf.2 b hb n hn (he ▸ hv))
      calc
        (σ.ty a.endpoint).shape.subst η =
            (ComparisonShape.ofTy a.endpoint).subst (ρ η) := hta
        _ = ρ η (.flex name) := by simpa only [han] using (hs η hη).2 a ha
        _ = (ComparisonShape.ofTy b.endpoint).subst (ρ η) :=
          by simpa only [hbn] using ((hs η hη).2 b hb).symm
        _ = (σ.ty b.endpoint).shape.subst η := htb.symm
  · contradiction
  · contradiction

end ComparisonReduction

end ModalityInference
