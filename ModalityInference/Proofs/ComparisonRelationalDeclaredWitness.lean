import ModalityInference.Proofs.ComparisonDefinedInstances
import ModalityInference.Proofs.ComparisonInfeasibleShapes
import ModalityInference.SchemeSubsumption
/-! A relational declared-bound comparison with a fully defined shared image.
The checked rejection records the remaining arbitrary-context completeness
obligation: both sides of the source bound contain the same quantified name. -/
namespace ModalityInference.ComparisonRelationalDeclaredWitness

def B : Ty := .var (.rigid 0)
def X : Ty := .var (.flex 0)
def F (t : Ty) : Ty := .fn t .unit

def source : Scheme :=
  { typeParams := [0], bounds := [.sub X (F X)], body := .unit }
def target : Scheme :=
  { bounds := [.sub B (F B)], body := .unit }

def action : Substitution := { types := [(0,B)] }

theorem instance_defined : InstantiatesUnder target.bounds.assumptions source action := by
  constructor
  · constructor <;> exact List.Perm.refl _
  · constructor
    · intro v
      cases v with
      | rigid n => simp [Substitution.type,TypeExpr.DefinedUnder,TypeExpr.wellFormedBounds,ModeModels]
      | flex n =>
        by_cases hn : n = 0
        · subst n
          simp [action,Substitution.type,B,TypeExpr.DefinedUnder,TypeExpr.wellFormedBounds,ModeModels]
        · have he : (n == 0) = false := by simp [hn]
          simp [action,Substitution.type,List.lookup_cons,he,B,
            TypeExpr.DefinedUnder,TypeExpr.wellFormedBounds,ModeModels]
    · intro v
      cases v <;> simp [action,Substitution.mode,Entails,ModExpr.WellFormed,ModExpr.eval,Function.comp_def]
  · simp [source,action,Substitution.ty,TypeExpr.subst,TypeExpr.DefinedUnder,
      TypeExpr.wellFormedBounds,ModeModels]

theorem subsumes : SubsumesUnder [] source target := by
  refine ⟨action,instance_defined,?_,?_⟩
  · change EntailsAll target.bounds.assumptions [.sub B (F B)]
    intro c hc
    simp only [List.mem_singleton] at hc
    subst c
    refine ⟨.bound ?_,?_,?_⟩
    · simp [target,Bounds.assumptions,Constraint.assumptions]
    · simp [B,TypeExpr.DefinedUnder,TypeExpr.wellFormedBounds,ModeModels]
    · simp [B,F,TypeExpr.DefinedUnder,TypeExpr.wellFormedBounds,ModeModels]
  · exact .refl

theorem algebra_subsumes : AlgebraSubsumesUnder [] source target := subsumes.to_algebra

theorem guarded_subsumes : AlgebraSubsumes [] source.requireDefinedInstances target :=
  (algebraSubsumes_requireDefinedInstances_iff [] source target).mpr algebra_subsumes

#guard source.instanceGuards == [.sub X X]

theorem no_finite_shape_model :
    ¬∃ρ,ComparisonShape.Models target.bounds.assumptions ρ := by
  rintro ⟨ρ,hρ⟩
  have h := hρ (.var (.rigid 0),.fn (.var (.rigid 0)) .unit)
    (by simp [target,B,F,Bounds.assumptions,Constraint.assumptions,
      ComparisonShape.pairs,ComparisonShape.ofTy,TypeExpr.wellFormedBounds])
  have hs := congrArg ComparisonShapeSolver.size h
  simp only [ComparisonShape.subst,ComparisonShapeSolver.size] at hs
  omega

#guard match checkSubsumption 100 source target with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonRelationalDeclaredWitness
