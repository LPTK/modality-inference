import ModalityInference.Proofs.ComparisonPropagationComposition
import ModalityInference.Proofs.ComparisonEliminationSupport
import ModalityInference.Proofs.ComparisonPreparedBounds
import ModalityInference.Proofs.ComparisonReductionSupport
import ModalityInference.Proofs.ComparisonPropagationSetup
import ModalityInference.Proofs.ComparisonGuardedTotal

/-! The reconstructed type images avoid the modality domains restored by
the absorption and annotation adapters. -/
namespace ModalityInference

theorem Substitution.mode_map_append (before after : Substitution) (v : ModVar) :
    ({ modes := before.modes.map (fun (n, m) => (n, m.subst after.mode)) ++ after.modes } :
      Substitution).mode v = (before.mode v).subst after.mode := by
  cases v with
  | rigid n => rfl
  | flex n =>
    simp only [Substitution.mode, List.lookup_append, lookup_map_values]
    cases before.modes.lookup n <;> rfl

def AvoidsModes (names : List Nat) (v : ModVar) : Prop := ∀ n ∈ names, v ≠ .flex n

theorem Substitution.mode_append_of_avoids (left right : List (Nat × ModExpr)) (v : ModVar)
    (h : AvoidsModes (left.map Prod.fst) v) :
    ({modes := left ++ right} : Substitution).mode v = ({modes := right} : Substitution).mode v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    have hl : left.lookup n = none := List.lookup_eq_none_iff.mpr fun entry he =>
      bne_iff_ne.mpr (fun hn => h entry.1 (List.mem_map.mpr ⟨entry, he, rfl⟩) (congrArg ModVar.flex hn))
    simp only [Substitution.mode, List.lookup_append, hl, Option.or]

theorem Substitution.type_modeSupport {σ : Substitution} {Q : ModVar → Prop}
    (hi : ∀ entry ∈ σ.types, ∀ w ∈ entry.2.modVars, Q w) (v : TypeVar) :
    ∀ w ∈ (σ.type v).modVars, Q w := by
  cases v with
  | rigid n => simp [Substitution.type, TypeExpr.modVars]
  | flex n =>
    cases he : σ.types.lookup n with
    | none => simp [Substitution.type, he, TypeExpr.modVars]
    | some t =>
      obtain ⟨before, after, heq, _⟩ := List.lookup_eq_some_iff.mp he
      simpa only [Substitution.type, he, Option.getD_some] using hi (n, t) (by simp [heq])

theorem Constraint.mode_support_subst {Q : ModVar → Prop} (c : Constraint) (σ : Substitution)
    (ht : ∀ v, ∀ w ∈ (σ.type v).modVars, Q w)
    (hm : ∀ v, Q v → ∀ w ∈ (σ.mode v).vars, Q w)
    (hc : ∀ v ∈ c.modVars, Q v) : ∀ w ∈ (σ.constraint c).modVars, Q w := by
  have hty (t : Ty) (h : ∀ v ∈ t.modVars, Q v) :=
    TypeExpr.mode_support_subst t σ (fun v _ => ht v) (fun v hv => hm v (h v hv))
  have hmode (m : ModExpr) (h : ∀ v ∈ m.vars, Q v) :=
    ModExpr.support_subst m σ.mode (fun v hv => hm v (h v hv))
  cases c with
  | sub a b | equiv a b =>
    simp only [Constraint.modVars, Finset.mem_union, or_imp, forall_and] at hc
    simpa only [Substitution.constraint, Constraint.subst, Constraint.modVars,
      Finset.mem_union, or_imp, forall_and] using And.intro (hty a hc.1) (hty b hc.2)
  | mode a b =>
    simp only [Constraint.modVars, Finset.mem_union, or_imp, forall_and] at hc
    simpa only [Substitution.constraint, Constraint.subst, Constraint.modVars,
      Finset.mem_union, or_imp, forall_and] using And.intro (hmode a hc.1) (hmode b hc.2)
  | defined m => exact hmode m hc
  | equal v t =>
    cases v with
    | rigid n => exact hty t hc
    | flex n =>
      cases he : σ.types.lookup n with
      | none => simpa only [Substitution.constraint, he, Constraint.modVars] using hty t hc
      | some a =>
        have ha := ht (.flex n)
        simp only [Substitution.type, he, Option.getD_some] at ha
        simpa only [Substitution.constraint, he, Constraint.modVars,
          Finset.mem_union, or_imp, forall_and] using And.intro ha (hty t hc)

theorem ComparisonInterpolation.Supports.subst {P P' : TypeVar → Prop}
    {Q Q' : ModVar → Prop} {a : CompareTy} (h : Supports P Q a)
    {types : TypeVar → CompareTy} {modes : ModVar → ModExpr}
    (ht : ∀ v, P v → Supports P' Q' (types v))
    (hm : ∀ v, Q v → ∀ w ∈ (modes v).vars, Q' w) :
    Supports P' Q' (a.subst types modes) := by
  induction a <;> simp only [Supports] at h <;> simp only [CompareTy.subst, Supports]
  case var v => exact ht v h
  case modal a m ih =>
    exact ⟨ih h.1, ModExpr.support_subst m modes (fun v hv => hm v (h.2 v hv))⟩
  case prod a b iha ihb | sum a b iha ihb | fn a b iha ihb |
      join a b iha ihb | meet a b iha ihb => exact ⟨iha h.1, ihb h.2⟩

theorem CompareSubstitution.type_modeSupport {σ : CompareSubstitution} {Q : ModVar → Prop}
    (hi : ∀ entry ∈ σ.types, ComparisonInterpolation.Supports (fun _ => True) Q entry.2)
    (v : TypeVar) : ComparisonInterpolation.Supports (fun _ => True) Q (σ.type v) := by
  cases v with
  | rigid n => trivial
  | flex n =>
    cases he : σ.types.lookup n with
    | none => simp [CompareSubstitution.type, he, ComparisonInterpolation.Supports]
    | some t =>
      obtain ⟨before, after, heq, _⟩ := List.lookup_eq_some_iff.mp he
      simpa only [CompareSubstitution.type, he, Option.getD_some] using hi (n, t) (by simp [heq])

namespace ComparisonChecker

def restoredModes (absorption : ComparisonAbsorption.Result)
    (annotations : ComparisonPartialModes.Result) (synth : Substitution) : Substitution :=
  { modes := absorption.action.modes ++
      annotations.images.map (fun (n, m) => (n, m.subst synth.mode)) ++ synth.modes }

theorem restoredModes_finish (absorption : ComparisonAbsorption.Result)
    (annotations : ComparisonPartialModes.Result) (after : CompareSubstitution) (v : ModVar) :
    (restoredModes absorption annotations {modes := after.modes}).mode v =
      (ComparisonExactContext.finish absorption.action
        (ComparisonExactContext.finish annotations.substitution after)).mode v := by
  let middle : Substitution :=
    {modes := annotations.images.map (fun (n, m) => (n, m.subst after.mode)) ++ after.modes}
  have hm : middle.mode = (ComparisonExactContext.finish annotations.substitution after).mode := by
    funext w
    exact (Substitution.mode_map_append annotations.substitution {modes := after.modes} w).trans
      (ComparisonExactContext.finish_mode annotations.substitution after w).symm
  rw [ComparisonExactContext.finish_mode, ← hm]
  simpa only [ComparisonAbsorption.Result.action, List.map_map, Function.comp_def,
    ModExpr.epsilon, ModExpr.subst, restoredModes, middle, List.append_assoc] using
      Substitution.mode_map_append absorption.action middle v

theorem restoredModes_agrees (absorption : ComparisonAbsorption.Result)
    (annotations : ComparisonPartialModes.Result) (synth : Substitution) (v : ModVar)
    (h : AvoidsModes (absorption.modes ++ annotations.images.map Prod.fst) v) :
    (restoredModes absorption annotations synth).mode v = synth.mode v := by
  have ha := Substitution.mode_append_of_avoids absorption.action.modes
    (annotations.images.map (fun (n, m) => (n, m.subst synth.mode)) ++ synth.modes) v (by
      intro n hn
      apply h n
      apply List.mem_append_left
      simpa [ComparisonAbsorption.Result.action, List.map_map, Function.comp_def] using hn)
  have hb := Substitution.mode_append_of_avoids
    (annotations.images.map (fun (n, m) => (n, m.subst synth.mode))) synth.modes v (by
      intro n hn
      apply h n
      apply List.mem_append_right
      simpa [List.map_map, Function.comp_def] using hn)
  simpa only [restoredModes, List.append_assoc] using ha.trans hb

end ComparisonChecker

namespace ComparisonSkeleton

theorem build_modeSupport {Q : ModVar → Prop} (p : SchemePreparation.Prepared)
    (shape : ComparisonShape) (nt nm : Nat) (hf : ∀ n, nm ≤ n → Q (.flex n)) :
    ∀ v ∈ (build p shape nt nm).modVars, Q v := by
  induction shape generalizing nt nm with
  | var v =>
    simp only [build]
    split
    · simpa only [TypeExpr.modVars, Finset.empty_union, ModExpr.vars,
        Finset.mem_singleton, forall_eq] using hf nm le_rfl
    · simp only [TypeExpr.modVars, Finset.notMem_empty, false_implies, implies_true]
  | unit | credit =>
    simpa only [build, TypeExpr.modVars, Finset.empty_union, ModExpr.vars,
      Finset.mem_singleton, forall_eq] using hf nm le_rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [build, TypeExpr.modVars, ModExpr.vars, Finset.mem_union,
      Finset.mem_singleton, or_imp, forall_and, forall_eq]
    exact ⟨⟨iha nt (nm + 1) (fun n hn => hf n (by omega)),
      ihb (nt + typeCount p a) (nm + 1 + modeCount p a) (fun n hn => hf n (by omega))⟩,
      hf nm le_rfl⟩

theorem allocate_modeSupport {Q : ModVar → Prop} (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (names : List Nat) (nt nm : Nat)
    (hf : ∀ n, nm ≤ n → Q (.flex n)) :
    ∀ entry ∈ (allocate p shapes names nt nm).substitution.types,
      ∀ v ∈ entry.2.modVars, Q v := by
  induction names generalizing nt nm with
  | nil => simp [allocate]
  | cons name names ih =>
    simp only [allocate, List.forall_mem_cons]
    exact ⟨build_modeSupport p _ nt nm hf,
      ih _ _ (fun n hn => hf n (by omega))⟩

end ComparisonSkeleton

namespace ComparisonPartialModes

theorem Request.bound_support {Q : ModVar → Prop} (total : ModExpr → Bool) (r : Request)
    (fresh : Nat) (hf : Q (.flex fresh)) (hr : ∀ v ∈ r.target.vars, Q v) :
    ∀ v ∈ (r.bound total fresh).modVars, Q v := by
  have hs := recompose_support (split total [r.target]).suffix
    (split_support total [r.target] (by simpa [SpineSupports] using hr)).2
  unfold Request.bound
  split <;> intro v hv <;>
    simp only [Constraint.modVars, ModExpr.vars, Finset.mem_union, Finset.mem_singleton] at hv
  · exact hv.elim (hs v) (fun he => he ▸ hf)
  · exact hv.elim (fun he => he ▸ hf) (hs v)

theorem adapt_bounds_support {Q : ModVar → Prop} {total : ModExpr → Bool} {indices : List Nat}
    {requests : List Request} {firstFresh : Nat}
    (hf : ∀ n, firstFresh ≤ n → n < (adapt total indices requests firstFresh).nextMode → Q (.flex n))
    (hr : ∀ r ∈ requests, ∀ v ∈ r.target.vars, Q v) :
    ∀ c ∈ (adapt total indices requests firstFresh).bounds, ∀ v ∈ c.modVars, Q v := by
  intro c hc
  obtain ⟨b, hb, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨r, hrb, rfl⟩ := List.mem_map.mp hc
  obtain ⟨name, offset, _, hp⟩ := mem_adapt_bindings.mp hb
  have hr' : r ∈ requests := (List.mem_filter.mp ((plan_spec hp).2.2.1 ▸ hrb)).1
  exact Request.bound_support total r b.fresh
    (hf _ (adapt_fresh_range hb).1 (adapt_fresh_range hb).2) (hr r hr')

end ComparisonPartialModes

namespace ComparisonAnnotations

theorem prepare_bounds_support {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    {Q : ModVar → Prop}
    (hf : ∀ n, p.nextMode ≤ n → n < (prepare p total).nextMode → Q (.flex n))
    (ht : ∀ v ∈ p.targetType.modVars, Q v) :
    ∀ c ∈ (prepare p total).bounds, ∀ v ∈ c.modVars, Q v := by
  apply ComparisonPartialModes.adapt_bounds_support hf
  intro r hr v hv
  exact ht v (requests_support _ hr hv)

theorem prepare_nextMode (p : SchemePreparation.Prepared) (total : ModExpr → Bool) :
    p.nextMode ≤ (prepare p total).nextMode := by
  simp [prepare, ComparisonPartialModes.adapt]

end ComparisonAnnotations

namespace ComparisonChecker

def adaptedNames (p : SchemePreparation.Prepared) (total : ModExpr → Bool) : List Nat :=
  let absorption := ComparisonAbsorption.plan p total
  let absorbed := {p with sourceType := absorption.body}
  absorption.modes ++ (ComparisonAnnotations.prepare absorbed total).images.map Prod.fst

theorem adaptedNames_range {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    {n : Nat} (hn : n ∈ adaptedNames p total) : p.firstMode ≤ n ∧ n < p.nextMode := by
  rcases List.mem_append.mp hn with hn | hn
  · simp only [ComparisonAbsorption.Result.modes, ComparisonAbsorption.modes,
      List.mem_dedup, List.mem_map] at hn
    obtain ⟨pair, hp, rfl⟩ := hn
    exact ((ComparisonAbsorption.scopeCheck_spec _ _).mp
      (ComparisonAbsorption.plan_spec p total).1 pair hp).2.1
  · have hr := (ComparisonPartialModes.mem_eligible.mp (ComparisonAnnotations.prepare_domain hn)).1
    simp only [List.mem_range'] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    omega

theorem avoids_adaptedNames_of_fixed {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    {v : ModVar} (hv : ComparisonInstance.modeAllowed p v = false) :
    AvoidsModes (adaptedNames p total) v := by
  intro n hn he
  have hr := adaptedNames_range hn
  subst v
  simp only [ComparisonInstance.modeAllowed, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hv
  omega

theorem avoids_adaptedNames_of_fresh {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    {n : Nat} (hn : p.nextMode ≤ n) : AvoidsModes (adaptedNames p total) (.flex n) := by
  apply avoids_adaptedNames_of_fixed
  simp [ComparisonInstance.modeAllowed]
  omega

theorem absorbed_modes_avoid {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    {v : ModVar} (hv : v ∈ (ComparisonAbsorption.plan p total).body.modVars) :
    AvoidsModes (ComparisonAbsorption.plan p total).modes v := by
  have hf := ComparisonAbsorption.plan_modes_free p total v hv
  intro n hn he
  subst v
  have hn' : n ∉ (ComparisonAbsorption.plan p total).modes := by
    simpa [ComparisonAbsorption.modeFree, ComparisonAbsorption.Result.modes] using hf
  exact hn' hn

theorem work_body_avoids {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    (ht : ∀ v ∈ p.targetType.modVars, ComparisonInstance.modeAllowed p v = false) :
    let absorption := ComparisonAbsorption.plan p total
    let absorbed := {p with sourceType := absorption.body}
    let annotations := ComparisonAnnotations.prepare absorbed total
    ∀ v ∈ (annotations.substitution.ty absorption.body).modVars,
      AvoidsModes (adaptedNames p total) v := by
  let absorption := ComparisonAbsorption.plan p total
  let absorbed := {p with sourceType := absorption.body}
  let annotations := ComparisonAnnotations.prepare absorbed total
  have hscoped := ComparisonAnnotations.prepare_scoped (p := absorbed) (total := total) ht
  have hi : ∀ entry ∈ annotations.images, ∀ v ∈ entry.2.vars,
      AvoidsModes absorption.modes v := by
    intro entry he
    apply ComparisonAnnotations.prepare_support (p := absorbed) (total := total)
      (P := AvoidsModes absorption.modes) _ _ he
    · intro n hn _ m hm
      exact avoids_adaptedNames_of_fresh (p := p) (total := total) hn m
        (List.mem_append_left _ hm)
    · intro v hv m hm
      exact avoids_adaptedNames_of_fixed (total := total) (ht v hv) m
        (List.mem_append_left _ hm)
  apply TypeExpr.mode_support_subst
  · intro v _ w hw
    simp only [ComparisonAnnotations.prepare_type, TypeExpr.modVars, Finset.notMem_empty] at hw
  · intro v hv w hw n hn
    rcases List.mem_append.mp hn with hn | hn
    · exact Substitution.mode_support hi v (absorbed_modes_avoid hv) w hw n hn
    · exact hscoped.mode_avoids_domain v w hw n hn

theorem sourceBounds_avoid {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    {c : Constraint} (hc : c ∈ p.sourceBounds) {v : ModVar} (hv : v ∈ c.modVars) :
    AvoidsModes (adaptedNames p total) v := by
  intro n hn he
  subst v
  rcases List.mem_append.mp hn with hn | hn
  · exact ComparisonAbsorption.plan_mode_avoids_bounds hn hc hv
  · exact ComparisonPartialModes.eligible_avoids_bounds
      (ComparisonAnnotations.prepare_domain hn) hc hv

theorem annotation_bounds_avoid {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    (ht : ∀ v ∈ p.targetType.modVars, ComparisonInstance.modeAllowed p v = false) :
    let absorption := ComparisonAbsorption.plan p total
    let absorbed := {p with sourceType := absorption.body}
    ∀ c ∈ (ComparisonAnnotations.prepare absorbed total).bounds, ∀ v ∈ c.modVars,
      AvoidsModes (adaptedNames p total) v := by
  apply ComparisonAnnotations.prepare_bounds_support
  · intro n hn _
    exact avoids_adaptedNames_of_fresh hn
  · intro v hv
    exact avoids_adaptedNames_of_fixed (ht v hv)

def Setup.rawImages (s : Setup) (reduced : ComparisonReduction.State)
    (types : ComparisonElimination.Result) : List (Nat × CompareTy) :=
  reduced.partialTypes ++ s.templates.substitution.types.map
    (fun (n, t) => (n, ({types := types.types} : CompareSubstitution).ty t))

theorem Setup.rawImages_avoid (s : Setup) {fuel : Nat}
    {reduced : ComparisonReduction.State} {types : ComparisonElimination.Result}
    (hreduce : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared =
      .success reduced)
    (helim : ComparisonElimination.run fuel s.work s.shapes s.templates
      (s.reduced reduced) = .success types)
    (htarget : ∀ v ∈ s.original.targetType.modVars,
      ComparisonInstance.modeAllowed s.original v = false)
    (hassumptions : ∀ v ∈ s.original.assumptions.modVars,
      ComparisonInstance.modeAllowed s.original v = false) :
    ∀ entry ∈ s.rawImages reduced types,
      ComparisonInterpolation.Supports (fun _ => True)
        (AvoidsModes (adaptedNames s.input s.total)) entry.2 := by
  let Q := AvoidsModes (adaptedNames s.input s.total)
  have htarget' : ∀ v ∈ s.work.targetType.modVars, Q v :=
    fun v hv => avoids_adaptedNames_of_fixed (htarget v hv)
  have htemplates : ∀ entry ∈ s.templates.substitution.types,
      ∀ v ∈ entry.2.modVars, Q v := by
    apply ComparisonSkeleton.allocate_modeSupport
    intro n hn
    apply avoids_adaptedNames_of_fresh
    have hf := ComparisonAnnotations.prepare_nextMode s.absorbed s.total
    exact le_trans hf hn
  have htypes : ∀ v, ∀ w ∈ (s.templates.substitution.type v).modVars, Q w :=
    Substitution.type_modeSupport htemplates
  have hmodes : ∀ v, Q v → ∀ w ∈ (s.templates.substitution.mode v).vars, Q w := by
    intro v hv
    cases v <;> simpa only [Substitution.mode, s.templates_modes, List.lookup_nil,
      Option.getD_none, ModExpr.vars, Finset.mem_singleton, forall_eq] using hv
  have hbounds : ∀ c ∈ s.templates.substitution.bounds s.work.sourceBounds,
      ∀ v ∈ c.modVars, Q v := by
    intro c hc
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hc
    exact Constraint.mode_support_subst original s.templates.substitution htypes hmodes
      (fun v hv => sourceBounds_avoid (p := s.input) ho hv)
  have hbody : ∀ v ∈ (s.templates.substitution.ty s.work.sourceType).modVars, Q v := by
    apply TypeExpr.mode_support_subst
    · exact fun v _ => htypes v
    · intro v hv
      exact hmodes v (work_body_avoids (p := s.input) (total := s.total) htarget v hv)
  have hsupport := ComparisonReduction.prepare_modeSupport hreduce hbounds hbody htarget'
  have hann : ∀ c ∈ s.annotations.bounds, ∀ v ∈ c.modVars, Q v :=
    annotation_bounds_avoid (p := s.input) (total := s.total) htarget
  have hguards : ∀ c ∈ ComparisonGuardedTotal.scalarBounds s.input.sourceBounds,
      ∀ v ∈ c.modVars, Q v :=
    ComparisonGuardedTotal.scalarBounds_modeSupport
      (fun _ hc _ hv => sourceBounds_avoid (p := s.input) hc hv)
  have hleaf : ∀ entry ∈ types.types,
      ComparisonInterpolation.Supports (fun _ => True) Q entry.2 := by
    apply ComparisonElimination.run_mode_support helim
    · intro v hv
      exact avoids_adaptedNames_of_fixed (hassumptions v hv)
    · intro v hv
      obtain ⟨c, hc, hv⟩ := (Bounds.mem_modVars_iff _ _).mp hv
      rcases List.mem_append.mp hc with hc | hc
      · exact (List.mem_append.mp hc).elim (fun hc => hann c hc v hv)
          (fun hc => hguards c hc v hv)
      · exact hsupport.modes c hc v hv
    · intro pair hp v hv
      exact (Finset.mem_union.mp hv).elim ((hsupport.inequalities pair hp).1 v)
        ((hsupport.inequalities pair hp).2 v)
  intro entry he
  rcases List.mem_append.mp he with he | he
  · exact hsupport.partialTypes entry he
  · obtain ⟨original, ho, rfl⟩ := List.mem_map.mp he
    apply ((ComparisonInterpolation.supports_ofTy_modes Q original.2).mpr
      (htemplates original ho)).subst
    · exact fun v _ => CompareSubstitution.type_modeSupport hleaf v
    · intro v hv
      cases v <;> simpa only [CompareSubstitution.mode, List.lookup_nil, Option.getD_none,
        ModExpr.vars, Finset.mem_singleton, forall_eq] using hv

theorem Setup.rawImages_mode_eq (s : Setup) {fuel : Nat}
    {reduced : ComparisonReduction.State} {types : ComparisonElimination.Result}
    (hreduce : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared =
      .success reduced)
    (helim : ComparisonElimination.run fuel s.work s.shapes s.templates
      (s.reduced reduced) = .success types)
    (htarget : ∀ v ∈ s.original.targetType.modVars,
      ComparisonInstance.modeAllowed s.original v = false)
    (hassumptions : ∀ v ∈ s.original.assumptions.modVars,
      ComparisonInstance.modeAllowed s.original v = false)
    (synth : Substitution) :
    ∀ entry ∈ s.rawImages reduced types,
      entry.2.subst CompareTy.var (restoredModes s.absorption s.annotations synth).mode =
        entry.2.subst CompareTy.var synth.mode := by
  intro entry he
  exact (s.rawImages_avoid hreduce helim htarget hassumptions entry he).subst_congr
    (fun _ _ => rfl) (fun v hv => restoredModes_agrees s.absorption s.annotations synth v hv)

end ComparisonChecker

end ModalityInference
