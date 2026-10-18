import ModalityInference.Proofs.ComparisonDefinedInstances
import ModalityInference.Proofs.ComparisonInfeasibleShapes
import ModalityInference.SchemeSubsumption
/-! A defined shared source image is recovered beneath a declared product
context even when the declared shape equations have no finite model. -/
namespace ModalityInference.ComparisonNestedDeclaredWitness

def A : Ty := .var (.rigid 0)
def B : Ty := .var (.rigid 1)
def C : Ty := .var (.rigid 2)
def X : Ty := .var (.flex 0)
def F (t : Ty) : Ty := .prod t .unit

def source : Scheme :=
  { typeParams := [0], bounds := [.sub A (F X), .sub (F X) C], body := .unit }
def target : Scheme :=
  { bounds := [.sub A (F B), .sub (F B) C, .sub B (.prod B B)], body := .unit }

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
  · change EntailsAll target.bounds.assumptions [.sub A (F B),.sub (F B) C]
    intro c hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    all_goals
      refine ⟨.bound ?_,?_,?_⟩
      · simp [target,Bounds.assumptions,Constraint.assumptions]
      · simp [A,B,F,TypeExpr.DefinedUnder,TypeExpr.wellFormedBounds,ModeModels]
      · simp [B,C,F,TypeExpr.DefinedUnder,TypeExpr.wellFormedBounds,ModeModels]
  · exact .refl

theorem algebra_subsumes : AlgebraSubsumesUnder [] source target := subsumes.to_algebra

theorem no_finite_shape_model :
    ¬∃ρ,ComparisonShape.Models target.bounds.assumptions ρ := by
  rintro ⟨ρ,hρ⟩
  have h := hρ (.var (.rigid 1),.prod (.var (.rigid 1)) (.var (.rigid 1)))
    (by simp [target,A,B,C,F,Bounds.assumptions,Constraint.assumptions,
      ComparisonShape.pairs,ComparisonShape.ofTy,TypeExpr.wellFormedBounds])
  have hs := congrArg ComparisonShapeSolver.size h
  simp only [ComparisonShape.subst,ComparisonShapeSolver.size] at hs
  omega

#guard match checkSubsumption 1000 source target with
  | .success evidence =>
      evidence.substitution.types == [(0, CompareTy.ofTy B)] &&
        evidence.substitution.modes.isEmpty
  | _ => false

end ModalityInference.ComparisonNestedDeclaredWitness
