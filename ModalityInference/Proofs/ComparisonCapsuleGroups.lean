import ModalityInference.Proofs.ComparisonCapsuleJoint

namespace ModalityInference.ComparisonCapsuleIntervals

open ComparisonBody ComparisonPartialCapsule ComparisonInterpolation

/-- Source modalities are instantiated uniformly across the group; the actual
planner still uses the original input requests and their shared fresh suffix. -/
theorem plan_complete_mapped_known_supported {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {fuel : Nat} {expressions known : List ModExpr}
    (hknown : knownTotal fuel Δ expressions = .success known)
    (name fresh : Nat) (rs : List Request) (W : CompareTy)
    (images : ModVar → ModExpr)
    {P : TypeVar → Prop} {Q : ModVar → Prop} (hs : Supports P Q W)
    (hatomic : ∀ r ∈ rs.filter (fun r => r.name == name),
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (hpartial : ∀ r ∈ rs.filter (fun r => r.name == name),
      ¬(CompareTy.ofTy r.endpoint).DefinedUnder Δ)
    (hcovered : ∀ r ∈ rs.filter (fun r => r.name == name),
      typeResiduals r.endpoint ⊆ expressions.flatMap residuals)
    (haction : ∀ r ∈ rs.filter (fun r => r.name == name),
      Entails Δ (.defined (r.action.subst images)))
    (hholds : ∀ r ∈ rs.filter (fun r => r.name == name),
      (r.mapAction images).AlgebraHolds Δ W)
    (hlower : ∃ r ∈ rs.filter (fun r => r.name == name), r.isLower = true)
    (hupper : ∃ r ∈ rs.filter (fun r => r.name == name), r.isLower = false) :
    ∃ b q, plan (isTotal known) name fresh rs = some b ∧ Entails Δ (.defined q) ∧
      (∀ v ∈ q.vars, Q v) ∧
      ∀ r ∈ b.requests, Entails Δ ((r.mapAction images).bound (isTotal known) q) := by
  have hmem : ∀ r ∈ (rs.map (Request.mapAction images)).filter (fun r => r.name == name),
      ∃ s ∈ rs.filter (fun r => r.name == name), r = s.mapAction images := by
    intro r hr
    rw [filter_mapAction] at hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact ⟨s, hs, rfl⟩
  have hlo : ∃ r ∈ (rs.map (Request.mapAction images)).filter (fun r => r.name == name),
      r.isLower = true := by
    obtain ⟨r, hr, hp⟩ := hlower
    refine ⟨r.mapAction images, ?_, hp⟩
    rw [filter_mapAction]
    exact List.mem_map.mpr ⟨r, hr, rfl⟩
  have hhi : ∃ r ∈ (rs.map (Request.mapAction images)).filter (fun r => r.name == name),
      r.isLower = false := by
    obtain ⟨r, hr, hp⟩ := hupper
    refine ⟨r.mapAction images, ?_, hp⟩
    rw [filter_mapAction]
    exact List.mem_map.mpr ⟨r, hr, rfl⟩
  obtain ⟨b', q, hb', hq, hqs, hbounds⟩ := plan_complete_known_supported hΔ hρ hknown
    name fresh (rs.map (Request.mapAction images)) W hs
    (fun r hr => by obtain ⟨s, hs, rfl⟩ := hmem r hr; exact hatomic s hs)
    (fun r hr => by obtain ⟨s, hs, rfl⟩ := hmem r hr; exact hpartial s hs)
    (fun r hr => by obtain ⟨s, hs, rfl⟩ := hmem r hr; exact hcovered s hs)
    (fun r hr => by obtain ⟨s, hs, rfl⟩ := hmem r hr; exact haction s hs)
    (fun r hr => by obtain ⟨s, hs, rfl⟩ := hmem r hr; exact hholds s hs) hlo hhi
  rw [plan_mapAction] at hb'
  cases hb : plan (isTotal known) name fresh rs with
  | none => simp only [hb, Option.map_none] at hb'; contradiction
  | some b =>
    simp only [hb, Option.map_some, Option.some.injEq] at hb'
    subst b'
    refine ⟨b, q, rfl, hq, hqs, ?_⟩
    intro r hr
    exact hbounds (r.mapAction images) (List.mem_map.mpr ⟨r, hr, rfl⟩)

end ModalityInference.ComparisonCapsuleIntervals

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonBody ComparisonPartialCapsule ComparisonInterpolation ComparisonCapsuleIntervals

private theorem nodup_map_filterMap_of {α β γ : Type} {xs : List α}
    (f : α → Option β) (key : β → γ) (oldKey : α → γ)
    (hkey : ∀ a b, f a = some b → key b = oldKey a)
    (hn : (xs.map oldKey).Nodup) : ((xs.filterMap f).map key).Nodup := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.filterMap f _ (List.pairwise_map.mp hn)
  intro a a' hneq b hb b' hb' he
  exact hneq ((hkey a b hb).symm.trans (he.trans (hkey a' b' hb')))

theorem bindings_fresh_nodup (p : Prepared) (total : ModExpr → Bool) :
    ((bindings p total).map Binding.fresh).Nodup := by
  apply nodup_map_filterMap_of _ _ (fun pair : Nat × Nat => p.nextMode + pair.2)
    (fun _ _ hp => (plan_spec hp).2.1)
  have hn : (((collect p total).map Request.name).dedup.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' _
  have ha := hn.map (fun a b h => Nat.add_left_cancel h :
    Function.Injective (fun n => p.nextMode + n))
  simpa only [List.map_map, Function.comp_def] using ha

theorem bindings_name_nodup (p : Prepared) (total : ModExpr → Bool) :
    ((bindings p total).map Binding.name).Nodup := by
  apply nodup_map_filterMap_of _ _ Prod.fst (fun _ _ hp => (plan_spec hp).1)
  rw [List.zipIdx_map_fst]
  exact List.nodup_dedup _

theorem mixedBindings_fresh_nodup (p : Prepared) (total : ModExpr → Bool) :
    ((mixedBindings p total).map Binding.fresh).Nodup := by
  exact List.pairwise_map.mpr ((List.pairwise_map.mp (bindings_fresh_nodup p total)).filter _)

theorem mixedBindings_name_nodup (p : Prepared) (total : ModExpr → Bool) :
    ((mixedBindings p total).map Binding.name).Nodup := by
  exact List.pairwise_map.mpr ((List.pairwise_map.mp (bindings_name_nodup p total)).filter _)


theorem binding_plan {p : Prepared} {total : ModExpr → Bool} {b : Binding}
    (hb : b ∈ bindings p total) :
    plan total b.name b.fresh (collect p total) = some b := by
  obtain ⟨⟨name, offset⟩, _, hp⟩ := List.mem_filterMap.mp hb
  have hs := plan_spec hp
  simpa only [hs.1, hs.2.1] using hp

theorem mixed_binding_plan {p : Prepared} {total : ModExpr → Bool} {b : Binding}
    (hb : b ∈ mixedBindings p total) :
    plan total b.name b.fresh (collect p total) = some b :=
  binding_plan (List.mem_filter.mp hb).1

theorem mixed_binding_flags {p : Prepared} {total : ModExpr → Bool} {b : Binding}
    (hb : b ∈ mixedBindings p total) :
    (∃ r ∈ b.requests, r.isLower = true) ∧
      (∃ r ∈ b.requests, r.isLower = false) ∧
      ∀ r ∈ b.requests, ComparisonAnnotations.hasPartial total r.endpoint = true := by
  have h := (List.mem_filter.mp hb).2
  simpa only [Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true', List.all_eq_true,
    and_assoc] using h

/-- An actual selected mixed atomic group has an input-supported suffix witness
under the same source modality substitution used by every other group. -/
theorem mixed_binding_suffix_complete {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hρ : ComparisonShape.Models p.assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    (images : ModVar → ModExpr) (hi : ComparisonModeRestriction.Fixed p.assumptions images)
    {b : Binding} (hb : b ∈ mixedBindings p (isTotal known))
    (W : CompareTy) {P : TypeVar → Prop} {Q : ModVar → Prop} (hs : Supports P Q W)
    (hatomic : ∀ r ∈ b.requests,
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (hholds : ∀ r ∈ b.requests, (r.mapAction images).AlgebraHolds p.assumptions W) :
    ∃ q, Entails p.assumptions (.defined q) ∧ (∀ v ∈ q.vars, Q v) ∧
      ∀ r ∈ b.requests, Entails p.assumptions ((r.mapAction images).bound (isTotal known) q) := by
  have hp := mixed_binding_plan hb
  have he := (plan_spec hp).2.2.1
  have hf := mixed_binding_flags hb
  obtain ⟨c, q, hplan, hq, hqs, hbounds⟩ := plan_complete_mapped_known_supported hΔ hρ hknown
    b.name b.fresh (collect p (isTotal known)) W images hs
    (fun r hr => hatomic r (he.symm ▸ hr))
    (fun r hr => (ComparisonAnnotations.hasPartial_known_true_iff hknown r.endpoint
      (collect_residuals_covered p _ (List.mem_filter.mp hr).1)).mp
        (hf.2.2 r (he.symm ▸ hr)))
    (fun r hr => collect_residuals_covered p _ (List.mem_filter.mp hr).1)
    (fun r hr => hi.defined (collect_action_total p (isTotal known)
      (fun _ hm => isTotal_defined (knownTotal_sound hknown) hm) (List.mem_filter.mp hr).1))
    (fun r hr => hholds r (he.symm ▸ hr)) (he ▸ hf.1) (he ▸ hf.2.1)
  have hcb : c = b := Option.some.inj (hplan.symm.trans hp)
  subst c
  exact ⟨q, hq, hqs, hbounds⟩

theorem binding_request_mem_collect {p : Prepared} {total : ModExpr → Bool} {b : Binding}
    (hb : b ∈ bindings p total) {r : Request} (hr : r ∈ b.requests) :
    r ∈ collect p total := by
  rw [(plan_spec (binding_plan hb)).2.2.1] at hr
  exact (List.mem_filter.mp hr).1

/-- All selected mixed atomic groups admit one joint scalar synthesis. The
same source action is retained across groups, and every local suffix is an
input-supported projection of its original internal image. -/
theorem mixed_bindings_run_complete {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hρ : ComparisonShape.Models p.assumptions ρ)
    {totalFuel : Nat} {known : List ModExpr}
    (hknown : knownTotal totalFuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    (images : ModVar → ModExpr) (hi : ComparisonModeRestriction.Fixed p.assumptions images)
    (W : Nat → CompareTy) {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hs : ∀ b ∈ mixedBindings p (isTotal known), Supports P Q (W b.name))
    (hatomic : ∀ b ∈ mixedBindings p (isTotal known), ∀ r ∈ b.requests,
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (hholds : ∀ b ∈ mixedBindings p (isTotal known), ∀ r ∈ b.requests,
      (r.mapAction images).AlgebraHolds p.assumptions (W b.name))
    (hn : ((mixedBindings p (isTotal known)).map Binding.fresh).Nodup)
    (hfixed : ∀ v, (∀ n ∈ List.range' p.firstMode (p.nextMode - p.firstMode), v ≠ .flex n) →
      images v = .var v)
    (hscope : ∀ v ∈ p.assumptions.modVars,
      ∀ n ∈ modeIds p (mixedBindings p (isTotal known)), v ≠ .flex n)
    (htarget : ∀ v ∈ p.targetType.modVars, images v = .var v)
    (hsourceBound : ∀ v ∈ p.sourceType.modVars, v.index < p.nextMode)
    (htargetBound : ∀ v ∈ p.targetType.modVars, v.index < p.nextMode)
    (hfresh : ∀ b ∈ mixedBindings p (isTotal known), p.nextMode ≤ b.fresh) :
    ∃ n, ∀ fuel ≥ n, ∃ result, SchemeModeSynthesis.run fuel
      (modeIds p (mixedBindings p (isTotal known)))
      (.imp (boundsModeFormula p.assumptions)
        (boundsModeFormula (goals (isTotal known) (mixedBindings p (isTotal known))))) =
      .success result := by
  have hmem : ∀ b ∈ mixedBindings p (isTotal known), ∀ r ∈ b.requests,
      r ∈ collect p (isTotal known) := by
    intro b hb r hr
    exact binding_request_mem_collect (List.mem_filter.mp hb).1 hr
  have hfreshAvoid : ∀ (v : ModVar), v.index < p.nextMode →
      ∀ k ∈ (mixedBindings p (isTotal known)).map Binding.fresh, v ≠ .flex k := by
    intro v hv k hk he
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
    have hl := hfresh b hb
    rw [he] at hv
    simp only [ModVar.index] at hv
    omega
  apply run_complete_suffix_family (isTotal known)
    (List.range' p.firstMode (p.nextMode - p.firstMode)) (mixedBindings p (isTotal known))
    images hn hfixed hscope (fun v η hη => hi.total η hη v)
  · intro b hb r hr v hv
    exact htarget v ((collect_support p _ (hmem b hb r hr)).2.2.1 hv)
  · intro b hb r hr v hv
    exact hfreshAvoid v (htargetBound v ((collect_support p _ (hmem b hb r hr)).2.2.1 hv))
  · intro b hb r hr v hv
    exact hfreshAvoid v (hsourceBound v ((collect_support p _ (hmem b hb r hr)).2.1 hv))
  · intro b hb
    obtain ⟨q, hq, _, hg⟩ := mixed_binding_suffix_complete hΔ hρ hknown images hi hb
      (W b.name) (hs b hb) (hatomic b hb) (hholds b hb)
    exact ⟨q, hq, hg⟩

end ModalityInference.ComparisonCapsuleContext
