import ModalityInference.ComparisonElimination
import ModalityInference.Proofs.ComparisonReduction
import ModalityInference.Proofs.ComparisonSkeleton
import ModalityInference.Proofs.ComparisonControls
import ModalityInference.Proofs.SchemeModeSynthesis

namespace ModalityInference

theorem RunResult.forIn_preserves {α β : Type} {xs : List α} {initial final : β}
    {f : α → β → RunResult (ForInStep β)} (P : β → Prop)
    (h : forIn xs initial f = .success final) (hinit : P initial)
    (hstep : ∀ a ∈ xs, ∀ before after, P before → f a before = .success after →
      match after with | .done result | .yield result => P result) : P final := by
  induction xs generalizing initial with
  | nil => cases h; exact hinit
  | cons a xs ih =>
    simp only [List.forIn_cons, pure] at h
    cases hf : f a initial <;> simp only [hf] at h <;> try contradiction
    next result =>
      have hp := hstep a (List.mem_cons_self) initial result hinit hf
      cases result with
      | done result => cases h; exact hp
      | yield result =>
        exact ih h hp (fun a ha => hstep a (List.mem_cons_of_mem _ ha))

theorem CompareTy.definedUnder_modal_iff {Δ : Bounds} {a : CompareTy} {m : ModExpr} :
    (.modal a m : CompareTy).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ Entails Δ (.defined m) := by
  simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels, ModeSatisfies, Entails,
    List.mem_append, or_imp, forall_and]

theorem CompareTy.definedUnder_join_iff {Δ : Bounds} {a b : CompareTy} :
    (.join a b : CompareTy).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels,
    List.mem_append, or_imp, forall_and]

theorem CompareTy.definedUnder_meet_iff {Δ : Bounds} {a b : CompareTy} :
    (.meet a b : CompareTy).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels,
    List.mem_append, or_imp, forall_and]

theorem ModExpr.subst_defined_of_total {Δ : Bounds} {m : ModExpr} {ms : ModVar → ModExpr}
    (htotal : ∀ η, m.WellFormed η)
    (hvars : ∀ v ∈ m.vars, Entails Δ (.defined (ms v))) :
    Entails Δ (.defined (m.subst ms)) := by
  intro η hη
  let τ := fun v => ((ms v).eval (some ∘ η)).getD Mode.identity
  have he : m.eval (fun v => (ms v).eval (some ∘ η)) = m.eval (some ∘ τ) := by
    apply m.eval_congr
    intro v hv
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hvars v hv η hη)
    simp [τ, hn]
  simpa only [ModExpr.WellFormed, ModExpr.eval_subst, he] using htotal τ

namespace ComparisonInterpolation

theorem Supports.mono {P P' : TypeVar → Prop} {Q Q' : ModVar → Prop}
    {a : CompareTy} (h : Supports P Q a)
    (ht : ∀ v, P v → P' v) (hm : ∀ v, Q v → Q' v) : Supports P' Q' a := by
  induction a <;> simp only [Supports] at h ⊢
  case var v => exact ht v h
  case modal a m ih => exact ⟨ih h.1, fun v hv => hm v (h.2 v hv)⟩
  all_goals exact ⟨‹_ → _› h.1, ‹_ → _› h.2⟩

theorem join_commonShape {Δ : Bounds} {shape : ComparisonShape} {head : CompareTy}
    {rest : List CompareTy}
    (hh : ∀ a ∈ head :: rest, a.WellShaped Δ ∧ ComparisonShape.Equivalent Δ a.shape shape) :
    (join head rest).WellShaped Δ ∧ ComparisonShape.Equivalent Δ (join head rest).shape shape := by
  induction rest generalizing head with
  | nil => exact hh head List.mem_cons_self
  | cons a rest ih =>
    have hhead := hh head List.mem_cons_self
    have hrest := ih (head := a) (fun b hb => hh b (List.mem_cons_of_mem _ hb))
    exact ⟨⟨hhead.1, hrest.1, hhead.2.trans hrest.2.symm⟩, hhead.2⟩

theorem meet_commonShape {Δ : Bounds} {shape : ComparisonShape} {head : CompareTy}
    {rest : List CompareTy}
    (hh : ∀ a ∈ head :: rest, a.WellShaped Δ ∧ ComparisonShape.Equivalent Δ a.shape shape) :
    (meet head rest).WellShaped Δ ∧ ComparisonShape.Equivalent Δ (meet head rest).shape shape := by
  induction rest generalizing head with
  | nil => exact hh head List.mem_cons_self
  | cons a rest ih =>
    have hhead := hh head List.mem_cons_self
    have hrest := ih (head := a) (fun b hb => hh b (List.mem_cons_of_mem _ hb))
    exact ⟨⟨hhead.1, hrest.1, hhead.2.trans hrest.2.symm⟩, hhead.2⟩

end ComparisonInterpolation

namespace ComparisonControls

theorem controls_name_mem {v : ModVar} {c : Control} (h : c ∈ controls v) : c.name = v := by
  simp only [controls, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem control_subst_defined {Δ : Bounds} (c : Control) (ms : ModVar → ModExpr)
    (h : Entails Δ (.defined (ms c.name))) :
    Entails Δ (.defined (c.expression.subst ms)) :=
  ModExpr.subst_defined_of_total (control_total c)
    (by simpa only [control_vars, Finset.mem_singleton, forall_eq] using h)

theorem Basis.defined_subst {Δ : Bounds} {b : Basis}
    (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (hh : ∀ a ∈ b.heads, (a.subst ts ms).DefinedUnder Δ)
    (hm : ∀ v ∈ b.modes, Entails Δ (.defined (ms v))) :
    ∀ a ∈ b.types, (a.subst ts ms).DefinedUnder Δ := by
  have hlo : (b.bottom.subst ts ms).DefinedUnder Δ := by
    rw [Basis.bottom, CompareTy.subst, CompareTy.definedUnder_modal_iff,
      ComparisonInterpolation.meet_subst]
    refine ⟨(ComparisonInterpolation.meet_defined_iff _ _ _).mpr ?_, fun _ _ => rfl⟩
    simpa only [ComparisonInterpolation.EndpointsDefined, Basis.heads,
      List.forall_mem_cons, List.forall_mem_map] using hh
  have hhi : (b.top.subst ts ms).DefinedUnder Δ := by
    rw [Basis.top, CompareTy.subst, CompareTy.definedUnder_modal_iff,
      ComparisonInterpolation.join_subst]
    refine ⟨(ComparisonInterpolation.join_defined_iff _ _ _).mpr ?_, fun _ _ => rfl⟩
    simpa only [ComparisonInterpolation.EndpointsDefined, Basis.heads,
      List.forall_mem_cons, List.forall_mem_map] using hh
  intro a ha
  obtain ⟨key, hk, rfl⟩ := List.mem_map.mp ha
  cases key with
  | head t =>
    exact hh t (by simpa [Basis.keys] using hk)
  | bottom => exact hlo
  | top => exact hhi
  | raised => exact CompareTy.definedUnder_modal_iff.mpr ⟨hlo, fun _ _ => rfl⟩
  | localFloor | affineFloor => exact CompareTy.definedUnder_modal_iff.mpr ⟨hhi, fun _ _ => rfl⟩
  | control c =>
    have hc : c ∈ b.modes.flatMap controls := by simpa [Basis.keys] using hk
    obtain ⟨v, hv, hc⟩ := List.mem_flatMap.mp hc
    apply CompareTy.definedUnder_modal_iff.mpr
    refine ⟨?_, control_subst_defined c ms ((controls_name_mem hc).symm ▸ hm v hv)⟩
    change ((if c.channel == .lower then b.bottom else b.top).subst ts ms).DefinedUnder Δ
    split <;> assumption

theorem Basis.commonShape {Δ : Bounds} {shape : ComparisonShape} {b : Basis}
    (hh : ∀ a ∈ b.heads, a.WellShaped Δ ∧ ComparisonShape.Equivalent Δ a.shape shape) :
    ∀ a ∈ b.types, a.WellShaped Δ ∧ ComparisonShape.Equivalent Δ a.shape shape := by
  have hlo : b.bottom.WellShaped Δ ∧ ComparisonShape.Equivalent Δ b.bottom.shape shape :=
    ComparisonInterpolation.meet_commonShape hh
  have hhi : b.top.WellShaped Δ ∧ ComparisonShape.Equivalent Δ b.top.shape shape :=
    ComparisonInterpolation.join_commonShape hh
  intro a ha
  obtain ⟨key, hk, rfl⟩ := List.mem_map.mp ha
  cases key with
  | head t => exact hh t (by simpa [Basis.keys] using hk)
  | bottom | raised => exact hlo
  | top | localFloor | affineFloor => exact hhi
  | control c =>
    change (if c.channel == .lower then b.bottom else b.top).WellShaped Δ ∧
      ComparisonShape.Equivalent Δ (if c.channel == .lower then b.bottom else b.top).shape shape
    split <;> assumption

end ComparisonControls

namespace ComparisonGroups

theorem collect_head_origin {p : SchemePreparation.Prepared} {shapes : ComparisonShapeSolver.Solved}
    {templates : ComparisonSkeleton.Templates} {reduced : ComparisonReduction.State}
    {groups : List Group} (h : collect p shapes templates reduced = .success groups) :
    ∀ g ∈ groups, ∀ v ∈ g.heads,
      v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables ∧
      ComparisonShapeSolver.sourceAllowed p v = false ∧
      shapeClass shapes templates v = some g.shapeClass := by
  unfold collect at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (split at h <;> try simp only at h)
  · cases h
    intro g hg v hv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hv, hc⟩ := List.mem_filter.mp hv
    obtain ⟨hv, hs⟩ := List.mem_filter.mp hv
    exact ⟨List.mem_dedup.mp hv, by simpa using hs, beq_iff_eq.mp hc⟩
  · have hnone := RunResult.forIn_preserves (fun r : MProd (Option (List Group)) PUnit => r.fst = none)
      (by assumption) rfl (by
        intro pair hp before after hb hs
        repeat' first
          | contradiction
          | (cases hs; rfl)
          | (split at hs <;> try simp only at hs))
    simp_all

theorem collect_leaf_origin {p : SchemePreparation.Prepared} {shapes : ComparisonShapeSolver.Solved}
    {templates : ComparisonSkeleton.Templates} {reduced : ComparisonReduction.State}
    {groups : List Group} (h : collect p shapes templates reduced = .success groups) :
    ∀ g ∈ groups, ∀ n ∈ g.leaves, ∃ leaf ∈ templates.leaves,
      leaf.name = n ∧ leaf.shapeClass = g.shapeClass := by
  unfold collect at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (split at h <;> try simp only at h)
  · cases h
    intro g hg n hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
    obtain ⟨leaf, hl, he⟩ := List.mem_filterMap.mp hn
    split at he
    · exact ⟨leaf, hl, Option.some.inj he, beq_iff_eq.mp ‹(leaf.shapeClass == c) = true›⟩
    · contradiction
  · have hnone := RunResult.forIn_preserves (fun r : MProd (Option (List Group)) PUnit => r.fst = none)
      (by assumption) rfl (by
        intro pair hp before after hb hs
        repeat' first
          | contradiction
          | (cases hs; rfl)
          | (split at hs <;> try simp only at hs))
    simp_all

theorem shapeClass_fixed {shapes : ComparisonShapeSolver.Solved}
    {templates : ComparisonSkeleton.Templates} {v c : TypeVar}
    (hfresh : ∀ leaf ∈ templates.leaves, v ≠ .flex leaf.name)
    (h : shapeClass shapes templates v = some c) : shapes.fixedShapes v = .var c := by
  cases v with
  | rigid n =>
    simp only [shapeClass] at h
    split at h <;> try contradiction
    next d hd => cases Option.some.inj h; exact hd
  | flex n =>
    have hn : templates.leaves.find? (fun leaf => leaf.name == n) = none := by
      apply List.find?_eq_none.mpr
      intro leaf hl
      have hne : leaf.name ≠ n := fun he => hfresh leaf hl (he ▸ rfl)
      simpa only [beq_iff_eq] using hne
    simp only [shapeClass, hn] at h
    split at h <;> try contradiction
    next d hd => cases Option.some.inj h; exact hd

theorem collect_heads_compatible {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (hshape : ∀ a b, ComparisonShape.Equivalent p.assumptions a b ↔
      a.subst shapes.fixedShapes = b.subst shapes.fixedShapes)
    (h : collect p shapes templates reduced = .success groups)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name) :
    ∀ g ∈ groups, ∀ a ∈ g.heads, ∀ b ∈ g.heads,
      ComparisonShape.Equivalent p.assumptions (.var a) (.var b) := by
  intro g hg a ha b hb
  obtain ⟨has, _, hac⟩ := collect_head_origin h g hg a ha
  obtain ⟨hbs, _, hbc⟩ := collect_head_origin h g hg b hb
  apply (hshape (.var a) (.var b)).mpr
  exact (shapeClass_fixed (fun leaf hl => hfresh leaf hl a has) hac).trans
    (shapeClass_fixed (fun leaf hl => hfresh leaf hl b hbs) hbc).symm

end ComparisonGroups

namespace ComparisonElimination

def groupModes (assumptions required : Bounds) (g : ComparisonGroups.Group) : List ModVar :=
  let labels := ((g.assumptions ++ g.goals).flatMap fun (a, b) => [a.mode, b.mode]).dedup
  (labels.flatMap ModExpr.freeVariables ++ assumptions.modeVariables ++
    required.modeVariables).dedup

def groupBasis (assumptions required : Bounds) (g : ComparisonGroups.Group)
    (first : TypeVar) (rest : List TypeVar) : ComparisonControls.Basis :=
  ⟨.var first, rest.map CompareTy.var, groupModes assumptions required g⟩

theorem group_reifies {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {result : Result} (h : group fuel assumptions required g = .success result) :
    ∃ first rest, g.heads = first :: rest ∧
      ∀ entry ∈ result.types, ∃ clauses,
        ComparisonPropagation.reify (groupBasis assumptions required g first rest).types clauses =
          some entry.2 := by
  unfold group at h
  simp only [bind, pure, RunResult.bind] at h
  split at h
  · next first rest hheads =>
    repeat' first
      | contradiction
      | (split at h <;> try simp only at h)
    cases h
    have hreduce := ComparisonPropagation.reduce_correct ‹ComparisonPropagation.reduce _ _ = .success _›
    refine ⟨first, rest, hheads, ?_⟩
    rintro ⟨name, t⟩ ht
    obtain ⟨i, hi, he⟩ := Vector.mem_iff_getElem.mp
      (Vector.mem_toList_iff.mp (List.of_mem_zip ht).2)
    have hr := hreduce.2.1 ⟨i, hi⟩
    simp only [Fin.getElem_fin] at hr
    exact ⟨_, by simpa only [he, groupBasis, groupModes] using hr⟩
  · contradiction

theorem group_domain {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {result : Result} (h : group fuel assumptions required g = .success result) :
    result.types.map Prod.fst = g.leaves := by
  unfold group at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (split at h <;> try simp only at h)
  cases h
  apply List.map_fst_zip
  simp

theorem group_property {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {result : Result} (h : group fuel assumptions required g = .success result)
    (P : CompareTy → Prop)
    (hb : ∀ first rest, g.heads = first :: rest →
      ∀ a ∈ (groupBasis assumptions required g first rest).types, P a)
    (hj : ∀ a b, P a → P b → P (.join a b))
    (hm : ∀ a b, P a → P b → P (.meet a b)) :
    ∀ entry ∈ result.types, P entry.2 := by
  obtain ⟨first, rest, hheads, hreify⟩ := group_reifies h
  intro entry he
  obtain ⟨clauses, hc⟩ := hreify entry he
  exact ComparisonPropagation.reify_property hc P (hb first rest hheads) hj hm

theorem group_commonShape {Δ : Bounds} {shape : ComparisonShape} {fuel : Nat}
    {assumptions required : Bounds} {g : ComparisonGroups.Group} {result : Result}
    (h : group fuel assumptions required g = .success result)
    (hh : ∀ v ∈ g.heads, ComparisonShape.Equivalent Δ (.var v) shape) :
    ∀ entry ∈ result.types, entry.2.WellShaped Δ ∧
      ComparisonShape.Equivalent Δ entry.2.shape shape := by
  apply group_property h (fun a => a.WellShaped Δ ∧ ComparisonShape.Equivalent Δ a.shape shape)
  · intro first rest hheads
    apply ComparisonControls.Basis.commonShape
    intro a ha
    change a ∈ CompareTy.var first :: rest.map CompareTy.var at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨trivial, hh first (hheads ▸ List.mem_cons_self)⟩
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
      exact ⟨trivial, hh v (hheads ▸ List.mem_cons_of_mem _ hv)⟩
  · exact fun _ _ ha hb => ⟨⟨ha.1, hb.1, ha.2.trans hb.2.symm⟩, ha.2⟩
  · exact fun _ _ ha hb => ⟨⟨ha.1, hb.1, ha.2.trans hb.2.symm⟩, ha.2⟩

theorem group_supports {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {result : Result} (h : group fuel assumptions required g = .success result) :
    ∀ entry ∈ result.types,
      ComparisonInterpolation.Supports (· ∈ g.heads) (· ∈ groupModes assumptions required g) entry.2 := by
  apply group_property h
  · intro first rest hheads
    apply ComparisonControls.Basis.supports
    · intro a ha
      change a ∈ CompareTy.var first :: rest.map CompareTy.var at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hheads ▸ List.mem_cons_self
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
        exact hheads ▸ List.mem_cons_of_mem _ hv
    · exact fun _ hv => hv
  · exact fun _ _ ha hb => ⟨ha, hb⟩
  · exact fun _ _ ha hb => ⟨ha, hb⟩

theorem group_defined_subst {Δ : Bounds} {fuel : Nat} {assumptions required : Bounds}
    {g : ComparisonGroups.Group} {result : Result}
    (h : group fuel assumptions required g = .success result)
    (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (hh : ∀ v ∈ g.heads, (ts v).DefinedUnder Δ)
    (hm : ∀ v ∈ groupModes assumptions required g, Entails Δ (.defined (ms v))) :
    ∀ entry ∈ result.types, (entry.2.subst ts ms).DefinedUnder Δ := by
  apply group_property h (fun a => (a.subst ts ms).DefinedUnder Δ)
  · intro first rest hheads
    apply ComparisonControls.Basis.defined_subst ts ms
    · intro a ha
      change a ∈ CompareTy.var first :: rest.map CompareTy.var at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hh first (hheads ▸ List.mem_cons_self)
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
        exact hh v (hheads ▸ List.mem_cons_of_mem _ hv)
    · exact hm
  · exact fun _ _ ha hb => CompareTy.definedUnder_join_iff.mpr ⟨ha, hb⟩
  · exact fun _ _ ha hb => CompareTy.definedUnder_meet_iff.mpr ⟨ha, hb⟩

theorem run_group_source {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {result : Result}
    (h : run fuel p shapes templates reduced = .success result) :
    ∃ groups, ComparisonGroups.collect p shapes templates reduced = .success groups ∧
      ∀ entry ∈ result.types, ∃ g ∈ groups, ∃ output,
        group fuel p.assumptions reduced.modes g = .success output ∧ entry ∈ output.types := by
  simp only [run, bind, pure, RunResult.bind] at h
  split at h
  · next groups hgroups =>
    split at h
    · next final hloop =>
      cases h
      refine ⟨groups, hgroups, ?_⟩
      apply RunResult.forIn_preserves
        (fun r => ∀ entry ∈ r.snd, ∃ g ∈ groups, ∃ output,
          group fuel p.assumptions reduced.modes g = .success output ∧ entry ∈ output.types) hloop
      · simp
      · intro g hg before after hbefore hstep
        cases he : group fuel p.assumptions reduced.modes g <;>
          simp only [he] at hstep <;> try contradiction
        next output =>
          cases hstep
          intro entry hentry
          rcases List.mem_append.mp hentry with hentry | hentry
          · exact hbefore entry hentry
          · exact ⟨g, hg, output, he, hentry⟩
    · contradiction
    · contradiction
  · contradiction
  · contradiction

theorem run_defined_subst {Δ : Bounds} {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {result : Result}
    (h : run fuel p shapes templates reduced = .success result)
    (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (hh : ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
      p.sourceType.typeVariables ++ p.sourceBounds.typeVariables,
      ComparisonShapeSolver.sourceAllowed p v = false → (ts v).DefinedUnder Δ)
    (hm : ∀ v, Entails Δ (.defined (ms v))) :
    ∀ entry ∈ result.types, (entry.2.subst ts ms).DefinedUnder Δ := by
  obtain ⟨groups, hc, hg⟩ := run_group_source h
  intro entry he
  obtain ⟨g, hgm, output, hgo, heo⟩ := hg entry he
  apply group_defined_subst hgo ts ms _ (fun v _ => hm v) entry heo
  intro v hv
  obtain ⟨hv, hf, _⟩ := ComparisonGroups.collect_head_origin hc g hgm v hv
  exact hh v hv hf

theorem run_type_domain {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {result : Result}
    (h : run fuel p shapes templates reduced = .success result) :
    ∀ entry ∈ result.types, ∃ leaf ∈ templates.leaves, leaf.name = entry.1 := by
  obtain ⟨groups, hc, hg⟩ := run_group_source h
  intro entry he
  obtain ⟨g, hgm, output, hgo, heo⟩ := hg entry he
  have hn : entry.1 ∈ g.leaves := by
    rw [← group_domain hgo]
    exact List.mem_map.mpr ⟨entry, heo, rfl⟩
  obtain ⟨leaf, hl, hn, _⟩ := ComparisonGroups.collect_leaf_origin hc g hgm entry.1 hn
  exact ⟨leaf, hl, hn⟩

theorem run_wellShaped {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {result : Result}
    (hshape : ∀ a b, ComparisonShape.Equivalent p.assumptions a b ↔
      a.subst shapes.fixedShapes = b.subst shapes.fixedShapes)
    (h : run fuel p shapes templates reduced = .success result)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name) :
    ∀ entry ∈ result.types, entry.2.WellShaped p.assumptions := by
  obtain ⟨groups, hc, hg⟩ := run_group_source h
  intro entry he
  obtain ⟨g, hgm, output, hgo, heo⟩ := hg entry he
  obtain ⟨first, rest, hheads, _⟩ := group_reifies hgo
  have hh := ComparisonGroups.collect_heads_compatible hshape hc hfresh g hgm
  exact (group_commonShape hgo
    (fun v hv => hh v hv first (hheads ▸ List.mem_cons_self)) entry heo).1

end ComparisonElimination

namespace ComparisonSkeleton

theorem leaves_range (p : SchemePreparation.Prepared) (shape : ComparisonShape) (nt : Nat) :
    ∀ leaf ∈ leaves p shape nt, nt ≤ leaf.name ∧ leaf.name < nt + typeCount p shape := by
  induction shape generalizing nt with
  | var v =>
    by_cases h : ComparisonShapeSolver.sourceAllowed p v = true
    · simp [leaves, h]
    · simp [leaves, typeCount, h]
  | unit | credit => simp [leaves]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    intro leaf hl
    rcases List.mem_append.mp hl with hl | hl
    · have hr := iha nt leaf hl
      change nt ≤ leaf.name ∧ leaf.name < nt + (typeCount p a + typeCount p b)
      omega
    · have hr := ihb (nt + typeCount p a) leaf hl
      change nt ≤ leaf.name ∧ leaf.name < nt + (typeCount p a + typeCount p b)
      omega

theorem allocate_type_mono (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved)
    (names : List Nat) (nt nm : Nat) : nt ≤ (allocate p shapes names nt nm).nextType := by
  induction names generalizing nt nm with
  | nil => exact Nat.le_refl _
  | cons n names ih =>
    have ht := ih (nt + typeCount p (shapes.resolveAll (.flex n)))
      (nm + modeCount p (shapes.resolveAll (.flex n)))
    exact (Nat.le_add_right _ _).trans ht

theorem allocate_leaf_range (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved)
    (names : List Nat) (nt nm : Nat) :
    ∀ leaf ∈ (allocate p shapes names nt nm).leaves,
      nt ≤ leaf.name ∧ leaf.name < (allocate p shapes names nt nm).nextType := by
  induction names generalizing nt nm with
  | nil => simp [allocate]
  | cons n names ih =>
    intro leaf hl
    rcases List.mem_append.mp hl with hl | hl
    · have hr := leaves_range p (shapes.resolveAll (.flex n)) nt leaf hl
      have ht := allocate_type_mono p shapes names (nt + typeCount p (shapes.resolveAll (.flex n)))
        (nm + modeCount p (shapes.resolveAll (.flex n)))
      exact ⟨hr.1, hr.2.trans_le ht⟩
    · have hr := ih _ _ leaf hl
      exact ⟨(Nat.le_add_right _ _).trans hr.1, hr.2⟩

theorem build_typeVars (p : SchemePreparation.Prepared) (shape : ComparisonShape) (nt nm : Nat) :
    ∀ v ∈ (build p shape nt nm).typeVars,
      ∃ leaf ∈ leaves p shape nt, v = .flex leaf.name := by
  induction shape generalizing nt nm with
  | var v =>
    by_cases h : ComparisonShapeSolver.sourceAllowed p v = true
    · simp [build, leaves, h, TypeExpr.typeVars]
    · simp [build, leaves, h, TypeExpr.typeVars]
  | unit | credit => simp [build, TypeExpr.typeVars]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    intro v hv
    simp only [build, TypeExpr.typeVars, Finset.mem_union] at hv
    rcases hv with hv | hv
    · obtain ⟨leaf, hl, he⟩ := iha _ _ v hv
      exact ⟨leaf, List.mem_append_left _ hl, he⟩
    · obtain ⟨leaf, hl, he⟩ := ihb _ _ v hv
      exact ⟨leaf, List.mem_append_right _ hl, he⟩

theorem build_guards (p : SchemePreparation.Prepared) (shape : ComparisonShape) (nt nm : Nat) :
    ∀ m, Constraint.defined m ∈ (build p shape nt nm).wellFormedBounds →
      ∃ n, m = .var (.flex n) := by
  induction shape generalizing nt nm with
  | var v =>
    by_cases h : ComparisonShapeSolver.sourceAllowed p v = true
    · simp [build, h, TypeExpr.wellFormedBounds]
    · simp [build, h, TypeExpr.wellFormedBounds]
  | unit | credit => simp [build, TypeExpr.wellFormedBounds]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    intro m hm
    simp only [build, TypeExpr.wellFormedBounds, List.mem_append, List.mem_singleton,
      Constraint.defined.injEq] at hm
    rcases hm with (hm | hm) | rfl
    · exact iha _ _ m hm
    · exact ihb _ _ m hm
    · exact ⟨nm, rfl⟩

theorem build_defined {Δ : Bounds} {σ : CompareSubstitution}
    (p : SchemePreparation.Prepared) (shape : ComparisonShape) (nt nm : Nat)
    (ht : ∀ leaf ∈ leaves p shape nt, (σ.type (.flex leaf.name)).DefinedUnder Δ)
    (hm : ∀ v, Entails Δ (.defined (σ.mode v))) : (σ.ty (build p shape nt nm)).DefinedUnder Δ := by
  apply ComparisonReduction.ty_defined_of_guards
  · intro v hv
    obtain ⟨leaf, hl, rfl⟩ := build_typeVars p shape nt nm v hv
    exact ht leaf hl
  · intro m hm'
    obtain ⟨n, rfl⟩ := build_guards p shape nt nm m hm'
    exact hm (.flex n)

theorem allocate_images_defined {Δ : Bounds} {σ : CompareSubstitution}
    (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved)
    (names : List Nat) (nt nm : Nat)
    (ht : ∀ leaf ∈ (allocate p shapes names nt nm).leaves,
      (σ.type (.flex leaf.name)).DefinedUnder Δ)
    (hm : ∀ v, Entails Δ (.defined (σ.mode v))) :
    ∀ entry ∈ (allocate p shapes names nt nm).substitution.types, (σ.ty entry.2).DefinedUnder Δ := by
  induction names generalizing nt nm with
  | nil => simp [allocate]
  | cons name names ih =>
    intro entry he
    simp only [allocate, List.mem_cons] at he
    rcases he with rfl | he
    · apply build_defined p
      · exact fun leaf hl => ht leaf (List.mem_append_left _ hl)
      · exact hm
    · exact ih _ _ (fun leaf hl => ht leaf (List.mem_append_right _ hl)) entry he

end ComparisonSkeleton

theorem CompareSubstitution.ty_fixed {σ : CompareSubstitution} (t : Ty)
    (ht : ∀ v ∈ t.typeVars, σ.type v = .var v)
    (hm : ∀ v ∈ t.modVars, σ.mode v = .var v) : σ.ty t = .ofTy t := by
  induction t <;> simp_all [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst,
    TypeExpr.typeVars, TypeExpr.modVars, or_imp, forall_and]
  case modal a m ih =>
    exact (m.subst_congr hm.2).trans (ModExpr.subst_id m)

theorem CompareSubstitution.declared_subtype {Δ : Bounds} {σ : CompareSubstitution}
    (ht : ∀ v ∈ Δ.typeVars, σ.type v = .var v)
    (hm : ∀ v ∈ Δ.modVars, σ.mode v = .var v) {a b : Ty} (hc : Constraint.sub a b ∈ Δ) :
    AlgebraSubtype Δ (σ.ty a) (σ.ty b) := by
  have hta : ∀ v ∈ a.typeVars, σ.type v = .var v :=
    fun v hv => ht v ((Δ.mem_typeVars_iff v).mpr ⟨.sub a b, hc, by simp [Constraint.typeVars, hv]⟩)
  have htb : ∀ v ∈ b.typeVars, σ.type v = .var v :=
    fun v hv => ht v ((Δ.mem_typeVars_iff v).mpr ⟨.sub a b, hc, by simp [Constraint.typeVars, hv]⟩)
  have hma : ∀ v ∈ a.modVars, σ.mode v = .var v :=
    fun v hv => hm v ((Δ.mem_modVars_iff v).mpr ⟨.sub a b, hc, by simp [Constraint.modVars, hv]⟩)
  have hmb : ∀ v ∈ b.modVars, σ.mode v = .var v :=
    fun v hv => hm v ((Δ.mem_modVars_iff v).mpr ⟨.sub a b, hc, by simp [Constraint.modVars, hv]⟩)
  rw [σ.ty_fixed a hta hma, σ.ty_fixed b htb hmb]
  exact .shaped (.bound hc)

end ModalityInference
