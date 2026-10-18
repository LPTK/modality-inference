import ModalityInference.Proofs.ComparisonDefinedInstances
import ModalityInference.Proofs.ComparisonInfeasibleShapes
import ModalityInference.SchemeSubsumption

/-! A declared whole-type edge can certify a defined instance even when its
shape equation has no finite model. -/
namespace ModalityInference.ComparisonCyclicDeclaredWitness

def A : Ty := .var (.rigid 0)

def source : Scheme := { body := A }

def target : Scheme := { bounds := [.sub A (.prod A A)], body := .prod A A }

theorem instance_defined : InstantiatesUnder target.bounds.assumptions source {} := by
  constructor
  · constructor <;> exact List.Perm.refl _
  · constructor
    · intro v
      cases v <;> simp [Substitution.type, TypeExpr.DefinedUnder,
        TypeExpr.wellFormedBounds, ModeModels]
    · intro v
      cases v <;> simp [Substitution.mode, Entails, ModExpr.WellFormed,
        ModExpr.eval, Function.comp_def]
  · simp [source, A, Substitution.ty, TypeExpr.subst, Substitution.type,
      TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]

theorem subsumes : SubsumesUnder [] source target := by
  refine ⟨{}, instance_defined, ?_, ?_⟩
  · simp [EntailsAll, source, Substitution.bounds]
  · change Subtype target.bounds.assumptions A (.prod A A)
    exact .bound (by simp [target, Bounds.assumptions, Constraint.assumptions])

theorem algebra_subsumes : AlgebraSubsumesUnder [] source target :=
  subsumes.to_algebra

theorem no_finite_shape_model :
    ¬ ∃ ρ, ComparisonShape.Models target.bounds.assumptions ρ := by
  rintro ⟨ρ, hρ⟩
  have h := hρ (.var (.rigid 0), .prod (.var (.rigid 0)) (.var (.rigid 0)))
    (by simp [target, A, Bounds.assumptions, Constraint.assumptions,
      ComparisonShape.pairs, ComparisonShape.ofTy, TypeExpr.wellFormedBounds])
  have hs := congrArg ComparisonShapeSolver.size h
  simp only [ComparisonShape.subst, ComparisonShapeSolver.size] at hs
  omega

#guard match checkSubsumption 20000 source target with
  | .success result => result.substitution.types.isEmpty && result.substitution.modes.isEmpty
  | _ => false

-- Shape incompatibility does not manufacture a subtype certificate.
#guard match checkSubsumption 20000 { body := .unit } { target with body := .credit } with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonCyclicDeclaredWitness
