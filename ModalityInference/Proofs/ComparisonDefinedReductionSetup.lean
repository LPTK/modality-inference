import ModalityInference.Proofs.ComparisonReductionForward

/-! Defined template witnesses satisfy the invariants of ordinary structural
reduction, including opaque coordinate roots and certified written annotations. -/

namespace ModalityInference.ComparisonSkeleton

open ComparisonSkeletonCoordinates ComparisonStructuralProjection

theorem coordinateTypes_opaque {Δ : Bounds} (hR : Residual Δ)
    (p : SchemePreparation.Prepared) {s : ComparisonShape} (tree : Tree Δ s) (nt : Nat) :
    ∀ entry ∈ coordinateTypes p tree nt, rootTag entry.2.shape = 0 := by
  induction tree generalizing nt with
  | atom a =>
    intro entry he
    simp only [coordinateTypes, List.mem_singleton] at he
    subst entry
    exact rootTag_equivalent hR a.shape_eq
  | unit | credit => simp [coordinateTypes]
  | prod a b m iha ihb | sum a b m iha ihb | fn a b m iha ihb =>
    intro entry he
    exact (List.mem_append.mp he).elim (iha nt entry) (ihb _ entry)

theorem forestTypes_opaque {Δ : Bounds} (hR : Residual Δ)
    (p : SchemePreparation.Prepared) (solved : ComparisonShapeSolver.Solved)
    (trees : CoordinateTrees Δ p solved) (names : List Nat) (nt : Nat) :
    ∀ entry ∈ forestTypes p solved trees names nt, rootTag entry.2.shape = 0 := by
  induction names generalizing nt with
  | nil => simp [forestTypes]
  | cons v rest ih =>
    intro entry he
    exact (List.mem_append.mp he).elim (coordinateTypes_opaque hR p (trees v) nt entry) (ih _ entry)

theorem forestExtension_opaque {Δ : Bounds} (hR : Residual Δ)
    (p : SchemePreparation.Prepared) (solved : ComparisonShapeSolver.Solved)
    (trees : CoordinateTrees Δ p solved) (names : List Nat) (nt nm : Nat)
    (σ : CompareSubstitution) :
    ComparisonReduction.OpaqueAction (forestExtension p solved trees names nt nm σ) := by
  intro v
  cases v with
  | rigid n => rfl
  | flex n =>
    cases hl : (forestTypes p solved trees names nt).lookup n with
    | none => simp only [forestExtension, CompareSubstitution.type, hl, Option.getD_none]; rfl
    | some a =>
      obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp hl
      have ha : (n, a) ∈ forestTypes p solved trees names nt := by simp [he]
      simpa only [forestExtension, CompareSubstitution.type, hl, Option.getD_some] using
        forestTypes_opaque hR p solved trees names nt (n, a) ha

theorem preparedForest_opaque {Δ : Bounds} (hR : Residual Δ)
    (p : SchemePreparation.Prepared) (solved : ComparisonShapeSolver.Solved)
    (trees : CoordinateTrees Δ p solved) (σ : CompareSubstitution) :
    ComparisonReduction.OpaqueAction (preparedForest p solved trees σ) :=
  forestExtension_opaque hR p solved trees _ _ _ σ

end ModalityInference.ComparisonSkeleton

namespace ModalityInference.ComparisonReduction

theorem AnnotationsTotal.substitution {known : List ModExpr} (ρ : Substitution)
    (hm : ∀ v, ρ.mode v = .var v) (ht : ∀ v, AnnotationsTotal known (ρ.type v))
    {t : Ty} (h : AnnotationsTotal known t) : AnnotationsTotal known (ρ.ty t) := by
  change AnnotationsTotal known (t.subst ρ.type ρ.mode)
  rw [show ρ.mode = ModExpr.var from funext hm]
  induction t <;> simp_all [TypeExpr.subst, AnnotationsTotal,
    ComparisonAnnotations.expressions, or_imp, forall_and]
  exact ht _

end ModalityInference.ComparisonReduction

namespace ModalityInference.ComparisonSkeleton

open ComparisonReduction

theorem build_annotations_total (known : List ModExpr) (p : SchemePreparation.Prepared)
    (shape : ComparisonShape) (nt nm : Nat) : AnnotationsTotal known (build p shape nt nm) := by
  induction shape generalizing nt nm with
  | var v =>
    simp only [build]
    split <;> simp [AnnotationsTotal, ComparisonAnnotations.expressions, ComparisonBody.isTotal]
  | unit | credit => simp [build, AnnotationsTotal, ComparisonAnnotations.expressions, ComparisonBody.isTotal]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [build, AnnotationsTotal, ComparisonAnnotations.expressions,
      List.forall_mem_cons, ComparisonBody.isTotal, List.mem_append, or_imp, forall_and, true_and]
    exact ⟨iha _ _, ihb _ _⟩

theorem allocate_annotations_total (known : List ModExpr) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (names : List Nat) (nt nm : Nat) :
    ∀ entry ∈ (allocate p solved names nt nm).substitution.types,
      AnnotationsTotal known entry.2 := by
  induction names generalizing nt nm with
  | nil => simp [allocate]
  | cons v rest ih =>
    intro entry he
    rcases List.mem_cons.mp he with rfl | he
    · exact build_annotations_total known p _ nt nm
    · exact ih _ _ entry he

theorem prepare_type_annotations_total (known : List ModExpr) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (v : TypeVar) :
    AnnotationsTotal known ((prepare p solved).substitution.type v) := by
  cases v with
  | rigid n => simp [Substitution.type, AnnotationsTotal, ComparisonAnnotations.expressions]
  | flex n =>
    cases hl : (prepare p solved).substitution.types.lookup n with
    | none => simp [Substitution.type, hl, AnnotationsTotal, ComparisonAnnotations.expressions]
    | some a =>
      obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp hl
      have ha : (n, a) ∈ (prepare p solved).substitution.types := by simp [he]
      simpa only [Substitution.type, hl, Option.getD_some] using
        allocate_annotations_total known p solved _ _ _ (n, a) ha

theorem prepare_annotations_total (known : List ModExpr) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) {t : Ty} (h : AnnotationsTotal known t) :
    AnnotationsTotal known ((prepare p solved).substitution.ty t) :=
  h.substitution (prepare p solved).substitution (prepare_mode p solved)
    (prepare_type_annotations_total known p solved)

end ModalityInference.ComparisonSkeleton

namespace ModalityInference

theorem CompareSubstitution.algebra_assumptions {Δ : Bounds} {σ : CompareSubstitution}
    (hw : σ.WellFormedUnder Δ) {c : Constraint} (h : AlgebraEntails Δ (σ.constraint c)) :
    AlgebraEntailsAll Δ (σ.bounds c.assumptions) := by
  simp only [CompareSubstitution.bounds, AlgebraEntailsAll, List.forall_mem_map]
  intro d hd
  cases c with
  | sub a b =>
    rcases h with ⟨hab, ha, hb⟩
    simp only [Constraint.assumptions, List.mem_append, List.mem_singleton] at hd
    rcases hd with (rfl | hd) | hd
    · exact ⟨hab, ha, hb⟩
    · exact (σ.body_guards_iff hw.types a).mp ha _ (List.mem_map.mpr ⟨_, hd, rfl⟩)
    · exact (σ.body_guards_iff hw.types b).mp hb _ (List.mem_map.mpr ⟨_, hd, rfl⟩)
  | equiv a b =>
    rcases h with ⟨hab, hba, ha, hb⟩
    simp only [Constraint.assumptions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with ((rfl | rfl) | hd) | hd
    · exact ⟨hab, ha, hb⟩
    · exact ⟨hba, hb, ha⟩
    · exact (σ.body_guards_iff hw.types a).mp ha _ (List.mem_map.mpr ⟨_, hd, rfl⟩)
    · exact (σ.body_guards_iff hw.types b).mp hb _ (List.mem_map.mpr ⟨_, hd, rfl⟩)
  | equal v a =>
    have hh : AlgebraSubtype Δ (σ.type v) (σ.ty a) ∧
        AlgebraSubtype Δ (σ.ty a) (σ.type v) ∧ (σ.ty a).DefinedUnder Δ := by
      cases v with
      | rigid n => exact h
      | flex n =>
        cases he : σ.types.lookup n with
        | none => simpa only [CompareSubstitution.constraint, CompareSubstitution.type, he] using h
        | some b =>
          simp only [CompareSubstitution.constraint, he, AlgebraEntails] at h
          simpa only [CompareSubstitution.type, he, Option.getD_some] using
            And.intro h.1 (And.intro h.2.1 h.2.2.2)
    simp only [Constraint.assumptions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with (rfl | rfl) | hd
    · exact ⟨hh.1, hw.types v, hh.2.2⟩
    · exact ⟨hh.2.1, hh.2.2, hw.types v⟩
    · exact (σ.body_guards_iff hw.types a).mp hh.2.2 _ (List.mem_map.mpr ⟨_, hd, rfl⟩)
  | mode a b | defined a =>
    simp only [Constraint.assumptions, List.mem_singleton] at hd
    subst d
    exact h

theorem CompareSubstitution.algebra_bounds_assumptions {Δ : Bounds} {σ : CompareSubstitution}
    (hw : σ.WellFormedUnder Δ) {bounds : Bounds} (h : AlgebraEntailsAll Δ (σ.bounds bounds)) :
    AlgebraEntailsAll Δ (σ.bounds bounds.assumptions) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨e, he, hd⟩ := List.mem_flatMap.mp hd
  exact algebra_assumptions hw (h _ (List.mem_map.mpr ⟨e, he, rfl⟩)) _
    (List.mem_map.mpr ⟨d, hd, rfl⟩)

end ModalityInference

namespace ModalityInference.ComparisonReduction

theorem constraint_annotations_substitution {known : List ModExpr} (ρ : Substitution)
    (hm : ∀ v, ρ.mode v = .var v) (ht : ∀ v, AnnotationsTotal known (ρ.type v))
    {c : Constraint}
    (h : ∀ m ∈ ComparisonAnnotations.constraintExpressions c, ComparisonBody.isTotal known m = true) :
    ∀ m ∈ ComparisonAnnotations.constraintExpressions (ρ.constraint c),
      ComparisonBody.isTotal known m = true := by
  have hmode (m : ModExpr) : m.subst ρ.mode = m := by
    rw [show ρ.mode = ModExpr.var from funext hm]
    exact m.subst_id
  cases c with
  | sub a b | equiv a b =>
    have hab : AnnotationsTotal known a ∧ AnnotationsTotal known b := by
      simpa only [ComparisonAnnotations.constraintExpressions, AnnotationsTotal,
        List.mem_append, or_imp, forall_and] using h
    simpa only [Substitution.constraint, Constraint.subst, ComparisonAnnotations.constraintExpressions,
      Substitution.ty, List.mem_append, or_imp, forall_and, AnnotationsTotal] using
      And.intro (hab.1.substitution ρ hm ht) (hab.2.substitution ρ hm ht)
  | mode a b | defined a =>
    simpa only [Substitution.constraint, Constraint.subst, ComparisonAnnotations.constraintExpressions,
      hmode] using h
  | equal v a =>
    have ha : AnnotationsTotal known (ρ.ty a) := (show AnnotationsTotal known a from h).substitution ρ hm ht
    cases v with
    | rigid n => exact ha
    | flex n =>
      cases he : ρ.types.lookup n with
      | none => simpa only [Substitution.constraint, he, ComparisonAnnotations.constraintExpressions] using ha
      | some b =>
        have hb := ht (.flex n)
        simp only [Substitution.type, he, Option.getD_some] at hb
        simpa only [Substitution.constraint, he, ComparisonAnnotations.constraintExpressions,
          List.mem_append, or_imp, forall_and, AnnotationsTotal] using And.intro hb ha

private theorem sub_not_wellFormedBounds (a b t : Ty) :
    Constraint.sub a b ∉ t.wellFormedBounds := by
  intro h
  obtain ⟨m, hm⟩ := t.wellFormedBounds_is_defined _ h
  contradiction

theorem assumptions_sub_annotations {known : List ModExpr} {c : Constraint} {a b : Ty}
    (hc : ∀ m ∈ ComparisonAnnotations.constraintExpressions c, ComparisonBody.isTotal known m = true)
    (h : Constraint.sub a b ∈ c.assumptions) :
    AnnotationsTotal known a ∧ AnnotationsTotal known b := by
  cases c <;> simp only [Constraint.assumptions, List.mem_append, List.mem_cons,
    List.not_mem_nil, sub_not_wellFormedBounds, or_false] at h
  case sub x y =>
    cases h
    simpa only [ComparisonAnnotations.constraintExpressions, AnnotationsTotal,
      List.mem_append, or_imp, forall_and] using hc
  case equiv x y =>
    have hh : AnnotationsTotal known x ∧ AnnotationsTotal known y := by
      simpa only [ComparisonAnnotations.constraintExpressions, AnnotationsTotal,
        List.mem_append, or_imp, forall_and] using hc
    rcases h with h | h <;> cases h
    · exact hh
    · exact hh.symm
  case equal v t =>
    rcases h with h | h <;> cases h
    · exact ⟨by simp [AnnotationsTotal, ComparisonAnnotations.expressions], hc⟩
    · exact ⟨hc, by simp [AnnotationsTotal, ComparisonAnnotations.expressions]⟩
  all_goals contradiction

theorem initial_ordinary_holds {Δ : Bounds} {σ : CompareSubstitution}
    {bounds : Bounds} {source target : Ty} {known : List ModExpr}
    (hw : σ.WellFormedUnder Δ) (hb : AlgebraEntailsAll Δ (σ.bounds bounds))
    (ht : DefinedPair Δ σ known (source, target))
    (hknown : ∀ c ∈ bounds, ∀ m ∈ ComparisonAnnotations.constraintExpressions c,
      ComparisonBody.isTotal known m = true) :
    OrdinaryHolds Δ σ { initial bounds source target with totalModes := known } := by
  have hex := σ.algebra_bounds_assumptions hw hb
  refine ⟨?_, by simp [initial], ?_, rfl, rfl⟩
  · intro pair hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨c, hc, he⟩ := List.mem_filterMap.mp hp
      cases c <;> simp only at he <;> try contradiction
      next a b =>
        cases Option.some.inj he
        have ha := hex _ (List.mem_map.mpr ⟨_, hc, rfl⟩)
        obtain ⟨original, horiginal, hc⟩ := List.mem_flatMap.mp hc
        exact ⟨ha.1, ha.2.1, ha.2.2,
          assumptions_sub_annotations (hknown original horiginal) hc⟩
    · exact List.mem_singleton.mp hp ▸ ht
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact hex _ (List.mem_map.mpr ⟨d, (List.mem_filter.mp hd).1, rfl⟩)

end ModalityInference.ComparisonReduction
