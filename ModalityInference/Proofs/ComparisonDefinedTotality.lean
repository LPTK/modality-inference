import ModalityInference.Proofs.ComparisonDefinedTemplateWitness
import ModalityInference.Proofs.ComparisonGuardedTotalCompleteness
import ModalityInference.Proofs.ComparisonCapsuleDichotomy

/-! The original source obligations certify every annotation inspected by
structural comparison. The instantiated target body inherits definedness from
an admissible comparison witness; no model or extra target guard is required. -/

namespace ModalityInference.ComparisonAnnotations

theorem expression_guard {a : Ty} {m : ModExpr} (h : m ∈ expressions a) :
    Constraint.defined m ∈ a.wellFormedBounds := by
  induction a with
  | var | unit | credit => contradiction
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left _ (iha h)
    · exact List.mem_append_right _ (ihb h)
  | modal a n ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_left _ (ih h)

theorem constraintExpressions_defined {Δ : Bounds} {c : Constraint}
    (hc : c.assumptions ⊆ Δ) :
    ∀ m ∈ constraintExpressions c, Entails Δ (.defined m) := by
  intro m hm η hη
  cases c with
  | sub a b | equiv a b =>
    rcases List.mem_append.mp hm with hm | hm
    · exact hη _ (hc (List.mem_append_left _ (List.mem_append_right _ (expression_guard hm))))
    · exact hη _ (hc (List.mem_append_right _ (expression_guard hm)))
  | equal v a => exact hη _ (hc (List.mem_append_right _ (expression_guard hm)))
  | mode a b =>
    have hh := hη (.mode a b) (hc List.mem_cons_self)
    obtain ⟨x,y,hx,hy,_⟩ := hh
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Option.isSome_iff_exists.mpr ⟨x,hx⟩
    · cases List.mem_singleton.mp hm
      exact Option.isSome_iff_exists.mpr ⟨y,hy⟩
  | defined a =>
    cases List.mem_singleton.mp hm
    exact hη _ (hc List.mem_cons_self)

theorem boundsExpressions_defined (Δ bounds : Bounds) :
    ∀ m ∈ boundsExpressions bounds, Entails (Δ ++ bounds.assumptions) (.defined m) := by
  intro m hm
  obtain ⟨c,hc,hm⟩ := List.mem_flatMap.mp hm
  exact constraintExpressions_defined (fun d hd =>
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨c,hc,hd⟩)) m hm

theorem obligationExpressions_defined {p : SchemePreparation.Prepared}
    (hs : p.sourceType.wellFormedBounds ⊆ p.sourceBounds)
    (ht : p.targetType.DefinedUnder p.assumptions) :
    ∀ m ∈ obligationExpressions p,
      Entails (p.assumptions ++ p.sourceBounds.assumptions) (.defined m) := by
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · intro η hη
      have hg := hs (expression_guard hm)
      exact hη (.defined m) (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨.defined m,hg,List.mem_cons_self⟩))
    · intro η hη
      exact ht η (fun c hc => hη c (List.mem_append_left _ hc)) _ (expression_guard hm)
  · exact boundsExpressions_defined _ _ m hm

/-- A successful finite certificate pass classifies every original body and
source-bound annotation as total when the source includes its body guards. -/
theorem known_obligationExpressions_total {p : SchemePreparation.Prepared} {fuel known}
    (hk : ComparisonBody.knownTotal fuel (p.assumptions ++ p.sourceBounds.assumptions)
      (obligationExpressions p) = .success known)
    (hs : p.sourceType.wellFormedBounds ⊆ p.sourceBounds)
    (ht : p.targetType.DefinedUnder p.assumptions) :
    ∀ m ∈ obligationExpressions p, ComparisonBody.isTotal known m = true := by
  intro m hm
  exact ComparisonBody.knownTotal_isTotal_complete hk m
    (fun r hr => List.mem_flatMap.mpr ⟨m,hm,hr⟩)
    (obligationExpressions_defined hs ht m hm)

end ModalityInference.ComparisonAnnotations

namespace ModalityInference.SchemePreparation

theorem prepare_body_guards {ambient : Bounds} {source target : Scheme}
    (hs : source.body.wellFormedBounds ⊆ source.bounds) :
    (prepare ambient source target).sourceType.wellFormedBounds ⊆
      (prepare ambient source target).sourceBounds := by
  let p := prepare ambient source target
  have hr : ∀ v, ∃ w, p.sourceRenaming.type v = .var w :=
    source.freshSubstitution_type_variable _ _ false
  change (p.sourceRenaming.ty source.body).wellFormedBounds ⊆ p.sourceRenaming.bounds source.bounds
  rw [← p.sourceRenaming.wellFormedBounds_renaming source.body hr]
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  exact List.mem_map.mpr ⟨d,hs hd,rfl⟩

theorem prepare_defined_body_guards (ambient : Bounds) (source target : Scheme) :
    (prepare ambient source.requireDefinedInstances target).sourceType.wellFormedBounds ⊆
      (prepare ambient source.requireDefinedInstances target).sourceBounds := by
  apply prepare_body_guards
  intro c hc
  exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hc))

end ModalityInference.SchemePreparation

namespace ModalityInference.ComparisonPreparation

theorem PreparedWitnessUnder.target_defined {source target : Scheme}
    {action : CompareSubstitution}
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) action) :
    (SchemePreparation.prepare [] source target).targetType.DefinedUnder
      (SchemePreparation.prepare [] source target).assumptions :=
  ComparisonPartialBoundary.prepared_public_defined_of_above source target hw.2.2 hw.1.2.2.2

/-- Every annotation used by the guarded prepared comparison is certified by
its original assumptions and source obligations. -/
theorem PreparedWitnessUnder.known_annotations {source target : Scheme}
    {action : CompareSubstitution} {fuel known}
    (hw : PreparedWitnessUnder
      (SchemePreparation.prepare [] source.requireDefinedInstances target) action)
    (hk : ComparisonBody.knownTotal fuel
      ((SchemePreparation.prepare [] source.requireDefinedInstances target).assumptions ++
        (SchemePreparation.prepare [] source.requireDefinedInstances target).sourceBounds.assumptions)
      (ComparisonAnnotations.obligationExpressions
        (SchemePreparation.prepare [] source.requireDefinedInstances target)) = .success known) :
    ∀ m ∈ ComparisonAnnotations.obligationExpressions
      (SchemePreparation.prepare [] source.requireDefinedInstances target),
      ComparisonBody.isTotal known m = true :=
  ComparisonAnnotations.known_obligationExpressions_total hk
    (SchemePreparation.prepare_defined_body_guards [] source target) hw.target_defined

end ModalityInference.ComparisonPreparation
