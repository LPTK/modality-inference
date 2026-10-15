import ModalityInference.Proofs.ComparisonReductionCollectable

/-! The actual template and reduction stages retain only fixed input heads and
their allocated opaque coordinates. -/

namespace ModalityInference.ComparisonGroups

def HeadOrigin (p : SchemePreparation.Prepared) (templates : ComparisonSkeleton.Templates)
    (v : TypeVar) : Prop :=
  (v ∈ inputHeads p ∧ ComparisonShapeSolver.sourceAllowed p v = false) ∨
    ∃leaf∈templates.leaves, v = .flex leaf.name

theorem template_type_origin (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) {v : TypeVar} (hv : v ∈ inputHeads p) :
    ComparisonReduction.Supported (HeadOrigin p (ComparisonSkeleton.prepare p shapes))
      ((ComparisonSkeleton.prepare p shapes).substitution.type v) := by
  let templates := ComparisonSkeleton.prepare p shapes
  cases v with
  | rigid n =>
    intro w hw
    have he : w = .rigid n := by simpa [Substitution.type, TypeExpr.typeVars] using hw
    exact he ▸ .inl ⟨hv, rfl⟩
  | flex n =>
    cases he : templates.substitution.types.lookup n with
    | some a =>
      dsimp only [templates] at he
      obtain ⟨before, after, ha, _⟩ := List.lookup_eq_some_iff.mp he
      have ha : (n, a) ∈ (ComparisonSkeleton.prepare p shapes).substitution.types := by simp [ha]
      intro w hw
      simp only [Substitution.type, he, Option.getD_some] at hw
      exact .inr (ComparisonSkeleton.allocate_images_typeVars p shapes _ _ _ (n, a) ha w hw)
    | none =>
      dsimp only [templates] at he
      have hn : n ∉ templates.substitution.types.map Prod.fst := by
        intro hn
        obtain ⟨entry, hm, hn⟩ := List.mem_map.mp hn
        have hne := (List.lookup_eq_none_iff.mp he) entry hm
        simp only [hn, bne_self_eq_false, Bool.false_eq_true] at hne
      dsimp only [templates, ComparisonSkeleton.prepare] at hn
      rw [ComparisonSkeleton.allocate_domain] at hn
      have hf : ComparisonShapeSolver.sourceAllowed p (.flex n) = false := by
        simp only [ComparisonShapeSolver.sourceAllowed, Bool.and_eq_false_iff,
          decide_eq_false_iff_not, not_le, not_lt]
        simp only [List.mem_range'_1] at hn
        omega
      intro w hw
      have hew : w = .flex n := by simpa [Substitution.type, he, TypeExpr.typeVars] using hw
      exact hew ▸ .inl ⟨hv, hf⟩

theorem template_ty_origin (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) {t : Ty}
    (ht : ∀v∈t.typeVars, v ∈ inputHeads p) :
    ComparisonReduction.Supported (HeadOrigin p (ComparisonSkeleton.prepare p shapes))
      ((ComparisonSkeleton.prepare p shapes).substitution.ty t) := by
  intro v hv
  obtain ⟨w, hw, hv⟩ := (TypeExpr.mem_typeVars_subst _ _ _ _).mp hv
  exact template_type_origin p shapes (ht w hw) v hv

theorem template_bounds_origin (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) :
    ∀c∈(ComparisonSkeleton.prepare p shapes).substitution.bounds p.sourceBounds,
      ∀v∈c.typeVars, HeadOrigin p (ComparisonSkeleton.prepare p shapes) v := by
  intro c hc v hv
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨w, hw, hv⟩ := (Constraint.mem_typeVars_substitution _ _ _).mp hv
  apply template_type_origin p shapes ?_ v hv
  have hw := (Bounds.mem_typeVariables p.sourceBounds w).mpr
    ((Bounds.mem_typeVars_iff _ _).mpr ⟨d, hd, hw⟩)
  exact List.mem_append_right _ hw

theorem prepared_reduction_origins {ambient : Bounds} {source target : Scheme}
    {fuel : Nat} {shapes : ComparisonShapeSolver.Solved} {known : List ModExpr}
    {shared : Bool} {reduced : ComparisonReduction.State}
    (h : ComparisonReduction.prepare fuel (SchemePreparation.prepare ambient source target)
      (ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes)
      [] known shared = .success reduced) :
    ComparisonReduction.Collectable
      (HeadOrigin (SchemePreparation.prepare ambient source target)
        (ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes)) reduced := by
  apply ComparisonReduction.prepare_collectable h (template_bounds_origin _ _)
  · apply template_ty_origin
    intro v hv
    exact List.mem_append_left _ (List.mem_append_right _
      ((TypeExpr.mem_typeVariables _ _).mpr hv))
  · intro v hv
    refine .inl ⟨?_, ComparisonShapeSolver.prepared_target_fixed ambient source target v hv⟩
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      ((TypeExpr.mem_typeVariables _ _).mpr hv)))

theorem prepared_inputHeads_bounded (ambient : Bounds) (source target : Scheme) :
    ∀v∈inputHeads (SchemePreparation.prepare ambient source target),
      v.index < (SchemePreparation.prepare ambient source target).nextType := by
  intro v hv
  simp only [inputHeads, List.mem_append, Bounds.mem_typeVariables, TypeExpr.mem_typeVariables] at hv
  rcases hv with ((hv | hv) | hv) | hv
  · exact ((Bounds.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_assumptions_bounded ambient source target)).1 v hv
  · exact ((TypeExpr.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_targetType_bounded ambient source target)).1 v hv
  · exact ((TypeExpr.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_sourceType_bounded ambient source target)).1 v hv
  · exact ((Bounds.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_sourceBounds_bounded ambient source target)).1 v hv

theorem prepared_leaves_fresh (ambient : Bounds) (source target : Scheme)
    (shapes : ComparisonShapeSolver.Solved) :
    ∀leaf∈(ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes).leaves,
      ∀v∈inputHeads (SchemePreparation.prepare ambient source target), v ≠ .flex leaf.name := by
  intro leaf hl v hv he
  have hv := prepared_inputHeads_bounded ambient source target v hv
  have hl := (ComparisonSkeleton.allocate_leaf_range _ _ _ _ _ leaf hl).1
  subst v
  change leaf.name < _ at hv
  omega

theorem shapeClass_leaf {shapes : ComparisonShapeSolver.Solved}
    {templates : ComparisonSkeleton.Templates}
    (hinj : ∀a∈templates.leaves, ∀b∈templates.leaves, a.name = b.name → a = b)
    {leaf : ComparisonSkeleton.Leaf} (hl : leaf ∈ templates.leaves) :
    shapeClass shapes templates (.flex leaf.name) = some leaf.shapeClass := by
  unfold shapeClass
  cases hf : templates.leaves.find? (fun item => item.name == leaf.name) with
  | none =>
    have hn := List.find?_eq_none.mp hf leaf hl
    simp at hn
  | some item =>
    have hi := List.mem_of_find?_eq_some hf
    have hn : item.name = leaf.name := by
      have hh := List.find?_some (p := fun item : ComparisonSkeleton.Leaf => item.name == leaf.name) hf
      exact beq_iff_eq.mp hh
    have he := hinj item hi leaf hl hn
    simp only [hf, he]

theorem fixedShapes_var {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel p = .success (.solved shapes))
    (hR : Residual p.assumptions) (v : TypeVar) :
    ∃c, shapes.fixedShapes v = .var c := by
  have he := ComparisonStructuralProjection.rootTag_equivalent hR
    (ComparisonSkeleton.fixedShapes_equivalent h (.var v))
  change 0 = ComparisonStructuralProjection.rootTag (shapes.fixedShapes v) at he
  cases hh : shapes.fixedShapes v <;> simp [hh, ComparisonStructuralProjection.rootTag] at he
  case var c => exact ⟨c, rfl⟩

theorem prepared_origin_class {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {shapes : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved shapes))
    (hR : Residual (SchemePreparation.prepare ambient source target).assumptions)
    {v : TypeVar}
    (hv : HeadOrigin (SchemePreparation.prepare ambient source target)
      (ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes) v) :
    ∃c, shapeClass shapes
        (ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes) v = some c ∧
      shapes.fixedShapes c = .var c := by
  rcases hv with ⟨hv, _⟩ | ⟨leaf, hl, rfl⟩
  · obtain ⟨c, hc⟩ := fixedShapes_var h hR v
    have hi := ComparisonShapeSolver.unify_factor (ComparisonShapeSolver.prepare_solved_iff.mp h).1
      (ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp h).1) v
    change (shapes.fixedShapes v).subst shapes.fixedShapes = shapes.fixedShapes v at hi
    rw [hc] at hi
    exact ⟨c, shapeClass_fixed_of (fun leaf hl => prepared_leaves_fresh ambient source target shapes
      leaf hl v hv) hc, hi⟩
  · have hc := ComparisonSkeleton.prepare_class_origin h
      (ComparisonShapeSolver.prepared_assumptions_fixed ambient source target) hl
    exact ⟨leaf.shapeClass, shapeClass_leaf
      (fun a ha b hb => ComparisonSkeleton.allocate_leaf_name_injective _ _ _ _ _ ha hb) hl, hc.2.2⟩

theorem atom_shape {t : Ty} {atom : Atom} (h : ComparisonGroups.atom t = some atom)
    (σ : CompareSubstitution) (ρ : TypeVar → ComparisonShape) :
    (σ.ty t).shape.subst ρ = (σ.type atom.head).shape.subst ρ := by
  rw [σ.ty_shape, ← TypeExpr.outer_comparisonShape t, atom_spec h]
  rfl

theorem prepared_origin_shape {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {shapes : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (h : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved shapes))
    (hfixed : ∀v, v.index < (SchemePreparation.prepare ambient source target).nextType →
      σ.type v = .var v)
    (hleaf : ∀leaf∈(ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes).leaves,
      ComparisonShape.Equivalent (SchemePreparation.prepare ambient source target).assumptions
        (σ.type (.flex leaf.name)).shape (.var leaf.shapeClass))
    {v c : TypeVar}
    (hv : HeadOrigin (SchemePreparation.prepare ambient source target)
      (ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes) v)
    (hc : shapeClass shapes
      (ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes) v = some c) :
    (σ.type v).shape.subst shapes.fixedShapes = .var c := by
  rcases hv with ⟨hv, _⟩ | ⟨leaf, hl, rfl⟩
  · rw [hfixed v (prepared_inputHeads_bounded ambient source target v hv)]
    exact shapeClass_fixed (fun leaf hl => prepared_leaves_fresh ambient source target shapes
      leaf hl v hv) hc
  · have he := shapeClass_leaf (shapes := shapes)
      (fun a ha b hb => ComparisonSkeleton.allocate_leaf_name_injective _ _ _ _ _ ha hb) hl
    have he := Option.some.inj (he.symm.trans hc)
    have hh := hleaf leaf hl shapes.fixedShapes
      (ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp h).1)
    have horigin := ComparisonSkeleton.prepare_class_origin h
      (ComparisonShapeSolver.prepared_assumptions_fixed ambient source target) hl
    exact hh.trans (he ▸ horigin.2.2)

theorem prepared_collect_complete {fuel budget : Nat} {ambient : Bounds} {source target : Scheme}
    {shapes : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    {known : List ModExpr} {shared : Bool} {reduced : ComparisonReduction.State}
    (hshape : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved shapes))
    (hR : Residual (SchemePreparation.prepare ambient source target).assumptions)
    (hred : ComparisonReduction.prepare budget (SchemePreparation.prepare ambient source target)
      (ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes)
      [] known shared = .success reduced)
    (hfixed : ∀v, v.index < (SchemePreparation.prepare ambient source target).nextType → σ.type v = .var v)
    (hleaf : ∀leaf∈(ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes).leaves,
      ComparisonShape.Equivalent (SchemePreparation.prepare ambient source target).assumptions
        (σ.type (.flex leaf.name)).shape (.var leaf.shapeClass))
    (hgoals : ∀goal∈reduced.inequalities,
      ComparisonReduction.PairHolds (SchemePreparation.prepare ambient source target).assumptions σ goal) :
    ∃groups, collect (SchemePreparation.prepare ambient source target) shapes
      (ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes) reduced =
      .success groups := by
  have ho := prepared_reduction_origins hred
  apply collect_complete
  intro goal hg
  obtain ⟨pair, hi, hl, hr⟩ := ho.2 goal hg
  obtain ⟨c, hc, _⟩ := prepared_origin_class hshape hR hl
  obtain ⟨d, hd, _⟩ := prepared_origin_class hshape hR hr
  have he := (hgoals goal hg).shape_equivalent shapes.fixedShapes
    (ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp hshape).1)
  obtain ⟨hal, har⟩ := inequality_spec hi
  rw [atom_shape hal σ, atom_shape har σ,
    prepared_origin_shape hshape hfixed hleaf hl hc,
    prepared_origin_shape hshape hfixed hleaf hr hd] at he
  have he := ComparisonShape.var.inj he
  exact ⟨pair, hi, c, hc, he ▸ hd⟩

theorem atom_head_mem {t : Ty} {atom : Atom} (h : ComparisonGroups.atom t = some atom) :
    atom.head ∈ t.typeVars := by
  rw [← TypeExpr.outer_typeVars t, atom_spec h]
  exact Finset.mem_singleton_self _

theorem atom_public_shape {t : Ty} {atom : Atom} (h : ComparisonGroups.atom t = some atom)
    (ρ : TypeVar → ComparisonShape) : (ComparisonShape.ofTy t).subst ρ = ρ atom.head := by
  rw [← TypeExpr.outer_comparisonShape t, atom_spec h]
  rfl

theorem origin_head_covered {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {reduced : ComparisonReduction.State}
    {groups : List Group} (h : collect p shapes (ComparisonSkeleton.prepare p shapes) reduced = .success groups)
    {g : Group} (hg : g ∈ groups) {v : TypeVar}
    (hv : HeadOrigin p (ComparisonSkeleton.prepare p shapes) v)
    (hc : shapeClass shapes (ComparisonSkeleton.prepare p shapes) v = some g.shapeClass) :
    ComparisonJointGroup.HeadCovered g.heads g.leaves v := by
  rcases hv with ⟨hv, hs⟩ | ⟨leaf, hl, rfl⟩
  · exact .inl ((collect_head_iff h hg v).mpr ⟨hv, hs, hc⟩)
  · have he := shapeClass_leaf (shapes := shapes)
      (fun a ha b hb => ComparisonSkeleton.allocate_leaf_name_injective _ _ _ _ _ ha hb) hl
    have he := Option.some.inj (he.symm.trans hc)
    exact .inr ⟨leaf.name, collect_leaf_mem h hg hl he, rfl⟩

theorem prepared_collect_covered {fuel budget : Nat} {ambient : Bounds} {source target : Scheme}
    {shapes : ComparisonShapeSolver.Solved} {known : List ModExpr} {shared : Bool}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (hshape : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved shapes))
    (hred : ComparisonReduction.prepare budget (SchemePreparation.prepare ambient source target)
      (ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes)
      [] known shared = .success reduced)
    (hcollect : collect (SchemePreparation.prepare ambient source target) shapes
      (ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes) reduced =
      .success groups) {g : Group} (hg : g ∈ groups) : ComparisonJointGroup.Covered g := by
  let p := SchemePreparation.prepare ambient source target
  let templates := ComparisonSkeleton.prepare p shapes
  constructor
  · intro pair hp
    obtain ⟨left, right, hc, hi⟩ := collect_assumption_origin hcollect g hg pair hp
    obtain ⟨hal, har⟩ := inequality_spec hi
    have hl : pair.1.head ∈ p.assumptions.typeVars :=
      (Bounds.mem_typeVars_iff _ _).mpr ⟨.sub left right, hc,
        Finset.mem_union_left _ (atom_head_mem hal)⟩
    have hr : pair.2.head ∈ p.assumptions.typeVars :=
      (Bounds.mem_typeVars_iff _ _).mpr ⟨.sub left right, hc,
        Finset.mem_union_right _ (atom_head_mem har)⟩
    have input (v : TypeVar) (hv : v ∈ p.assumptions.typeVars) : v ∈ inputHeads p :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        ((Bounds.mem_typeVariables _ _).mpr hv)))
    have fixed (v : TypeVar) (hv : v ∈ p.assumptions.typeVars) :
        ComparisonShapeSolver.sourceAllowed p v = false := by
      apply ComparisonShapeSolver.prepared_assumptions_fixed ambient source target
      rwa [ComparisonShapeSolver.vars_pairs]
    have hcl := collect_assumption_class hcollect hg hp
    have hlshape := shapeClass_fixed (fun leaf hh =>
      prepared_leaves_fresh ambient source target shapes leaf hh pair.1.head (input _ hl)) hcl
    have he := ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp hshape).1
      (ComparisonShape.ofTy left, ComparisonShape.ofTy right)
      (List.mem_flatMap.mpr ⟨.sub left right, hc, by simp⟩)
    rw [atom_public_shape hal, atom_public_shape har] at he
    have hcr := shapeClass_fixed_of (fun leaf hh =>
      prepared_leaves_fresh ambient source target shapes leaf hh pair.2.head (input _ hr))
      (he.symm.trans hlshape)
    exact ⟨(collect_head_iff hcollect hg _).mpr ⟨input _ hl, fixed _ hl, hcl⟩,
      (collect_head_iff hcollect hg _).mpr ⟨input _ hr, fixed _ hr, hcr⟩⟩
  · intro pair hp
    obtain ⟨goal, hgoal, hi, hl, hr⟩ := collect_goal_origin hcollect g hg pair hp
    obtain ⟨pair', hi', hleft, hright⟩ := (prepared_reduction_origins hred).2 goal hgoal
    have he := Option.some.inj (hi'.symm.trans hi)
    cases he
    exact ⟨origin_head_covered hcollect hg hleft hl, origin_head_covered hcollect hg hright hr⟩

theorem prepared_collect_heads_nonempty {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {shapes : ComparisonShapeSolver.Solved} {reduced : ComparisonReduction.State}
    {groups : List Group}
    (hshape : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved shapes))
    (hcollect : collect (SchemePreparation.prepare ambient source target) shapes
      (ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes) reduced =
      .success groups) {g : Group} (hg : g ∈ groups) (hc : ComparisonJointGroup.Covered g) :
    g.heads ≠ [] := by
  have leaf_head (n : Nat) (hn : n ∈ g.leaves) : g.heads ≠ [] := by
    obtain ⟨leaf, hl, _, he⟩ := collect_leaf_origin hcollect g hg n hn
    obtain ⟨hi, hs, hf⟩ := ComparisonSkeleton.prepare_class_origin hshape
      (ComparisonShapeSolver.prepared_assumptions_fixed ambient source target) hl
    have hclass := shapeClass_fixed_of (shapes := shapes)
      (fun item hm => prepared_leaves_fresh ambient source target shapes item hm leaf.shapeClass hi) hf
    have hmem := (collect_head_iff hcollect hg leaf.shapeClass).mpr
      ⟨hi, hs, he ▸ hclass⟩
    exact List.ne_nil_of_mem hmem
  rcases collect_group_nonempty hcollect hg with hh | hl | hp
  · exact hh
  · cases he : g.leaves with
    | nil => exact False.elim (hl he)
    | cons n ns => exact leaf_head n (he ▸ List.mem_cons_self)
  · cases he : g.goals with
    | nil => exact False.elim (hp he)
    | cons pair pairs =>
      rcases (hc.2 pair (he ▸ List.mem_cons_self)).1 with hh | ⟨n, hn, _⟩
      · exact List.ne_nil_of_mem hh
      · exact leaf_head n hn

theorem prepared_collect_nonempty {fuel budget : Nat} {ambient : Bounds} {source target : Scheme}
    {shapes : ComparisonShapeSolver.Solved} {known : List ModExpr} {shared : Bool}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (hshape : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved shapes))
    (hred : ComparisonReduction.prepare budget (SchemePreparation.prepare ambient source target)
      (ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes)
      [] known shared = .success reduced)
    (hcollect : collect (SchemePreparation.prepare ambient source target) shapes
      (ComparisonSkeleton.prepare (SchemePreparation.prepare ambient source target) shapes) reduced =
      .success groups) {g : Group} (hg : g ∈ groups) : g.heads ≠ [] :=
  prepared_collect_heads_nonempty hshape hcollect hg (prepared_collect_covered hshape hred hcollect hg)

end ModalityInference.ComparisonGroups
