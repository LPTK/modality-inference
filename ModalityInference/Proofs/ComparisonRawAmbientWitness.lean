import ModalityInference.Proofs.ComparisonNormalizedAmbientDriver
import ModalityInference.Proofs.ComparisonDefinedInstances

namespace ModalityInference.ComparisonRawAmbientWitness

def partialMode : ModExpr := .leftResidual .epsilon .bottom
def partialType : Ty := .modal .unit partialMode
def ambient : Bounds := [.sub partialType partialType]
def source : Scheme := {body:=.unit}
def target : Scheme := {body:=.unit}

theorem ordinary : SubsumesUnder ambient source target := by
  refine ⟨{},?_,?_,Subtype.refl⟩
  · constructor
    · exact ⟨List.Perm.refl _,List.Perm.refl _⟩
    · constructor
      · intro v
        cases v <;> exact fun _ _ _ hc => False.elim (List.not_mem_nil hc)
      · intro v η hη
        cases v <;> rfl
    · exact fun _ _ _ hc => False.elim (List.not_mem_nil hc)
  · intro c hc
    cases hc

theorem algebra_admissible : AlgebraSubsumesUnder ambient source target := ordinary.to_algebra

theorem finite_model : ∃φ,ComparisonShape.Models
    (SchemePreparation.prepare ambient source.requireDefinedInstances target).assumptions φ := by
  refine ⟨fun _=>.unit,?_⟩
  change ComparisonShape.Models ambient _
  simp [ComparisonShape.Models,ambient,partialType,ComparisonShape.pairs,
    ComparisonShape.ofTy,ComparisonShape.subst]

theorem partial_guard_not_entailed : ¬Entails ambient (.defined partialMode) := by
  intro h
  apply (show ¬partialMode.WellFormed (fun _=>Mode.identity) from by change false≠true;decide)
  apply h
  intro c hc
  have he : c=.sub partialType partialType := by simpa [ambient] using hc
  subst c
  trivial

theorem normalized_empty : ComparisonAmbientNormalization.normalize ambient=[] := rfl

/-- The actual driver eventually accepts while the ambient partial label remains
undefined. Its source instance and returned images satisfy the usual guards. -/
theorem eventually_accepts : ∃threshold result,∀fuel≥threshold,
    ComparisonNormalizedAmbientDriver.run fuel ambient source target=.success result :=
  ComparisonNormalizedAmbientDriver.run_complete_normalizes_empty normalized_empty
    (by simp [source]) (by simp [source]) algebra_admissible finite_model

#guard match ComparisonNormalizedAmbientDriver.run 10000 ambient source target with
  | .success result => result.types.isEmpty && result.modes.isEmpty
  | _ => false

#guard match ComparisonNormalizedAmbientDriver.run 10000 ambient source {target with body:=.credit} with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonRawAmbientWitness
