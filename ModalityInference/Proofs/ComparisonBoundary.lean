import ModalityInference.Proofs.ComparisonTypes
import ModalityInference.Proofs.GroundOrder
import ModalityInference.Proofs.SchemeReconstructionClosed
import ModalityInference.RuntimeSemantics

/-! Internal comparison witnesses and ordinary scheme instances are distinct
domains. Extending the former alone does not establish semantic subsumption. -/
namespace ModalityInference.ComparisonBoundary

private theorem fn_congr {Δ a b c d} (ha : CompareSubtype Δ c a)
    (hb : CompareSubtype Δ b d) : CompareSubtype Δ (.fn a b) (.fn c d) :=
  CompareSubtype.identityRev.trans ((CompareSubtype.fn ha hb (.valid fun _ _ =>
    ⟨Mode.identity, Mode.identity.compose Mode.top, rfl, rfl, by decide⟩)).trans .identity)

private theorem prod_congr {Δ a b c d} (ha : CompareSubtype Δ a c)
    (hb : CompareSubtype Δ b d) : CompareSubtype Δ (.prod a b) (.prod c d) :=
  CompareSubtype.identityRev.trans
    ((CompareSubtype.prod (CompareSubtype.identity.trans (ha.trans .identityRev))
      (CompareSubtype.identity.trans (hb.trans .identityRev))).trans .identity)

private theorem rigid_bound {Δ i j}
    (h : Constraint.sub (.var (.rigid i)) (.var (.rigid j)) ∈ Δ) :
    CompareSubtype Δ (.var (.rigid i)) (.var (.rigid j)) := .bound h

/-- One internal join supplies all four uses of the quantified source type in
these closed schemes, across contravariant inputs and covariant outputs. -/
theorem closed_join_comparison : CompareSubsumes []
    SchemeReconstructionClosed.source SchemeReconstructionClosed.target := by
  refine ⟨{ types := [(0, .join (.var (.rigid 4)) (.var (.rigid 5)))] }, ?_, ?_, ?_⟩
  case refine_3 =>
    change CompareSubtype SchemeReconstructionClosed.bounds
      (.fn (.join (.var (.rigid 4)) (.var (.rigid 5)))
        (.fn (.join (.var (.rigid 4)) (.var (.rigid 5)))
          (.prod (.join (.var (.rigid 4)) (.var (.rigid 5)))
            (.join (.var (.rigid 4)) (.var (.rigid 5))))))
      (.fn (.var (.rigid 4)) (.fn (.var (.rigid 5))
        (.prod (.var (.rigid 6)) (.var (.rigid 7)))))
    refine fn_congr .joinLeft (fn_congr .joinRight ?_)
    refine prod_congr (.joinLeast ?_ ?_) (.joinLeast ?_ ?_)
    all_goals exact rigid_bound (by simp [SchemeReconstructionClosed.bounds])
  case refine_1 => exact ⟨List.Perm.refl _, List.Perm.refl _⟩
  case refine_2 =>
    simp [CompareEntailsAll, CompareSubstitution.bounds, SchemeReconstructionClosed.source]

def source : Scheme :=
  { typeParams := [0]
    bounds := [.sub .unit (.var (.flex 0)), .sub .credit (.var (.flex 0))]
    body := .unit }

def target : Scheme := .mono .unit

theorem compares : CompareSubsumes [] source target := by
  refine ⟨{ types := [(0, .join .unit .credit)] }, ?_, ?_, ?_⟩
  case refine_2 =>
    simp [source, target, Scheme.mono, CompareEntailsAll, CompareEntails,
      CompareSubstitution.bounds, CompareSubstitution.constraint, CompareSubstitution.ty,
      CompareSubstitution.type, CompareTy.ofTy, CompareTy.subst, Substitution.bounds,
      Bounds.assumptions, CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
    exact ⟨.joinLeft, .joinRight⟩
  case refine_1 => exact ⟨List.Perm.refl _, List.Perm.refl _⟩
  case refine_3 => exact .refl

theorem no_ground_models (ρ : GroundAssignment) : ¬GroundModels ρ source.bounds := by
  intro h
  have hunit := h (.sub .unit (.var (.flex 0))) (by simp [source])
  have hcredit := h (.sub .credit (.var (.flex 0))) (by simp [source])
  simp only [GroundSatisfies, TypeExpr.realize, Option.some.injEq] at hunit hcredit
  obtain ⟨_, _, rfl, rfl, hunit⟩ := hunit
  obtain ⟨_, _, rfl, rfl, hcredit⟩ := hcredit
  have hc := GroundOrder.of_subtype hcredit
  generalize hx : ρ.types (.flex 0) = t at hunit hc
  cases GroundOrder.of_subtype hunit
  cases hc

theorem no_ground_instances (ambient ρ : GroundAssignment) :
    ¬GroundInstantiates ambient source ρ := fun h => no_ground_models ρ h.2.2

theorem source_interpretation (ρ : GroundAssignment) (w : World) (v : Value) :
    SchemeInterpretation ρ w source v := fun η _ hη _ =>
  False.elim (no_ground_instances ρ η hη)

theorem target_not_credit (ρ : GroundAssignment) (w : World) (l : Location) :
    ¬SchemeInterpretation ρ w target (.credit l) := by
  intro h
  have hi : GroundInstantiates ρ target ρ :=
    ⟨fun _ _ => rfl, fun _ _ => rfl, by simp [target, Scheme.mono, GroundModels]⟩
  exact (h ρ (.unit Mode.identity) hi rfl).2

theorem source_resource_interpretation (ρ : GroundAssignment) (w : World) (v : Runtime.Value) :
    Runtime.ResourceSchemeInterpretation ρ w source v ∅ :=
  ⟨by simp, fun η _ hη _ => False.elim (no_ground_instances ρ η hη)⟩

theorem target_not_resource_credit (ρ : GroundAssignment) (w : World) (l : Location)
    (reserved : Resources) :
    ¬Runtime.ResourceSchemeInterpretation ρ w target (.credit l) reserved := by
  intro h
  have hi : GroundInstantiates ρ target ρ :=
    ⟨fun _ _ => rfl, fun _ _ => rfl, by simp [target, Scheme.mono, GroundModels]⟩
  obtain ⟨_, _, hv⟩ := h.2 ρ (.unit Mode.identity) hi rfl
  simp [ResourceInterpretation, Runtime.Value.annotate] at hv

/-- A complete comparison checker cannot use this relation alone as a theorem
of preservation for the existing resource interpretation of public schemes. -/
theorem resource_semantic_preservation_fails (ρ : GroundAssignment) (w : World) (l : Location) :
    CompareSubsumes [] source target ∧
      Runtime.ResourceSchemeInterpretation ρ w source (.credit l) ∅ ∧
      ¬Runtime.ResourceSchemeInterpretation ρ w target (.credit l) ∅ :=
  ⟨compares, source_resource_interpretation ρ w _, target_not_resource_credit ρ w l ∅⟩

end ModalityInference.ComparisonBoundary
