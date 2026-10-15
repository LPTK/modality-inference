import ModalityInference.Proofs.ComparisonGroupExtraction

/-! Group reconstruction uses only the scalar identifiers present in its
declared assumptions and residual obligations. -/
namespace ModalityInference

theorem TypeExpr.outer_modeVars_subset (t : Ty) : t.outer.2.vars ⊆ t.modVars := by
  induction t with
  | var | unit | credit | prod | sum | fn => simp [TypeExpr.outer, ModExpr.vars, ModExpr.epsilon]
  | modal a m ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (ih hv)
    · exact Finset.mem_union_right _ hv

theorem ComparisonGroups.atom_modeVars_subset {t : Ty} {a : Atom}
    (h : atom t = some a) : a.mode.vars ⊆ t.modVars := by
  have ho := TypeExpr.outer_modeVars_subset t
  simpa only [atom_spec h] using ho

theorem ComparisonInterpolation.Supports.subst_congr {P : TypeVar → Prop} {Q : ModVar → Prop}
    {a : CompareTy} (h : Supports P Q a)
    {types₁ types₂ : TypeVar → CompareTy} {modes₁ modes₂ : ModVar → ModExpr}
    (ht : ∀ v, P v → types₁ v = types₂ v) (hm : ∀ v, Q v → modes₁ v = modes₂ v) :
    a.subst types₁ modes₁ = a.subst types₂ modes₂ := by
  induction a <;> simp only [Supports] at h <;> simp only [CompareTy.subst]
  case var v => exact ht v h
  case modal a m ih =>
    rw [ih h.1]
    exact congrArg (CompareTy.modal _) (m.subst_congr (fun v hv => hm v (h.2 v hv)))
  case prod a b iha ihb | sum a b iha ihb | fn a b iha ihb |
      join a b iha ihb | meet a b iha ihb => rw [iha h.1, ihb h.2]

namespace ComparisonElimination

theorem groupModes_support {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {Q : ModVar → Prop}
    (ha : ∀ v ∈ assumptions.modVars, Q v)
    (hr : ∀ v ∈ required.modVars, Q v)
    (hl : ∀ pair ∈ g.assumptions ++ g.goals,
      ∀ v ∈ pair.1.mode.vars ∪ pair.2.mode.vars, Q v) :
    ∀ v ∈ groupModes assumptions required g, Q v := by
  intro v hv
  simp only [groupModes, List.mem_dedup, List.mem_append] at hv
  rcases hv with (hv | hv) | hv
  · obtain ⟨m, hm, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨pair, hp, hm⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hm)
    have hv := (ModExpr.mem_freeVariables m v).mp hv
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hl pair hp v (Finset.mem_union_left _ hv)
    · obtain rfl := List.mem_singleton.mp hm
      exact hl pair hp v (Finset.mem_union_right _ hv)
  · exact ha v ((Bounds.mem_modeVariables assumptions v).mp hv)
  · exact hr v ((Bounds.mem_modeVariables required v).mp hv)

theorem collected_groupModes_support {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    {Q : ModVar → Prop}
    (h : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (ha : ∀ v ∈ p.assumptions.modVars, Q v)
    (hr : ∀ v ∈ reduced.modes.modVars, Q v)
    (hi : ∀ pair ∈ reduced.inequalities, ∀ v ∈ pair.1.modVars ∪ pair.2.modVars, Q v) :
    ∀ g ∈ groups, ∀ v ∈ groupModes p.assumptions reduced.modes g, Q v := by
  intro g hg
  apply groupModes_support ha hr
  intro pair hp v hv
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨left, right, hc, he⟩ := ComparisonGroups.collect_assumption_origin h g hg pair hp
    obtain ⟨hl, hr⟩ := ComparisonGroups.inequality_spec he
    apply ha v
    apply (p.assumptions.mem_modVars_iff v).mpr
    refine ⟨.sub left right, hc, ?_⟩
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (ComparisonGroups.atom_modeVars_subset hl hv)
    · exact Finset.mem_union_right _ (ComparisonGroups.atom_modeVars_subset hr hv)
  · obtain ⟨goal, hgoal, he, _⟩ := ComparisonGroups.collect_goal_origin h g hg pair hp
    obtain ⟨hl, hr⟩ := ComparisonGroups.inequality_spec he
    apply hi goal hgoal v
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (ComparisonGroups.atom_modeVars_subset hl hv)
    · exact Finset.mem_union_right _ (ComparisonGroups.atom_modeVars_subset hr hv)

theorem run_mode_support {fuel p shapes templates reduced result} {Q : ModVar → Prop}
    (h : run fuel p shapes templates reduced = .success result)
    (ha : ∀ v ∈ p.assumptions.modVars, Q v)
    (hr : ∀ v ∈ reduced.modes.modVars, Q v)
    (hi : ∀ pair ∈ reduced.inequalities, ∀ v ∈ pair.1.modVars ∪ pair.2.modVars, Q v) :
    ∀ entry ∈ result.types, ComparisonInterpolation.Supports (fun _ => True) Q entry.2 := by
  obtain ⟨groups, hc, hgroups⟩ := run_group_source h
  intro entry he
  obtain ⟨g, hg, output, ho, he⟩ := hgroups entry he
  exact (group_supports ho entry he).mono (fun _ _ => trivial)
    (collected_groupModes_support hc ha hr hi g hg)

theorem run_mode_subst_eq {fuel p shapes templates reduced result} {Q : ModVar → Prop}
    (h : run fuel p shapes templates reduced = .success result)
    (ha : ∀ v ∈ p.assumptions.modVars, Q v)
    (hr : ∀ v ∈ reduced.modes.modVars, Q v)
    (hi : ∀ pair ∈ reduced.inequalities, ∀ v ∈ pair.1.modVars ∪ pair.2.modVars, Q v)
    (types : TypeVar → CompareTy) (left right : ModVar → ModExpr)
    (hm : ∀ v, Q v → left v = right v) :
    ∀ entry ∈ result.types, entry.2.subst types left = entry.2.subst types right := by
  intro entry he
  exact (run_mode_support h ha hr hi entry he).subst_congr (fun _ _ => rfl) hm

end ComparisonElimination
end ModalityInference
