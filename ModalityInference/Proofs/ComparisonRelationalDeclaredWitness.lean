import ModalityInference.Proofs.ComparisonDefinedInstances
import ModalityInference.Proofs.ComparisonInfeasibleShapes
import ModalityInference.SchemeSubsumption
import ModalityInference.Proofs.ComparisonRankedEndpointReflection
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

/-- The shared image `B` is a rank-zero polynomial and needs no modality
assignment. The ranked solver accepts its original prepared endpoint family. -/
theorem ranked_run_eventual :
    let p := SchemePreparation.prepare [] source target
    let b := ComparisonRankedBasis.basis (ComparisonSelectedBases.inputNames p)
      (ComparisonSelectedBases.inputModes p) 0
    let generators := (ComparisonRankedBasis.basis (ComparisonSelectedBases.inputNames p)
      (ComparisonSelectedBases.inputModes p)
      (ComparisonRankedDecision.endpointRank (ComparisonSignedObservation.endpoints p))).types
    ∃ threshold result, ∀ fuel ≥ threshold,
      ComparisonRankedDecision.run fuel p.assumptions
        ⟨ComparisonSelectedBases.inputTypeKeys p, fun _ => b.types⟩
        (ComparisonObserverBoundary.retainedTypes p.assumptions generators)
        (ComparisonObserverBoundary.retainedModes p.assumptions generators)
        (ComparisonObserverBoundary.sizeBound p.assumptions generators)
        ModExpr.var (ComparisonSignedObservation.endpoints p) = .success result := by
  intro p b generators
  have hΔ : p.assumptions.TypeBoundsDefined := by
    intro a c h
    change Constraint.sub a c ∈ [.sub B (F B)] at h
    simp only [List.mem_singleton, Constraint.sub.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [B, F, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]
  have hi (k : Nat) (_ : k ∈ ComparisonSelectedBases.inputTypeKeys p) :
      ComparisonControls.LatticeForm b.types (.ofTy B) := by
    apply ComparisonControls.LatticeForm.atom
    apply ComparisonRankedBasis.head_mem_types
    change CompareTy.var (.rigid 0) ∈
      (ComparisonRankedBasis.basis (ComparisonSelectedBases.inputNames p)
        (ComparisonSelectedBases.inputModes p) 0).heads
    decide
  have he : ∀ pair ∈ ComparisonSignedObservation.endpoints p,
      AlgebraSubtype p.assumptions
        (ComparisonRankedDecision.instantiate (ComparisonSelectedBases.inputTypeKeys p)
          (fun _ => .ofTy B) ModExpr.var pair.1)
        (ComparisonRankedDecision.instantiate (ComparisonSelectedBases.inputTypeKeys p)
          (fun _ => .ofTy B) ModExpr.var pair.2) ∧
      (ComparisonRankedDecision.instantiate (ComparisonSelectedBases.inputTypeKeys p)
        (fun _ => .ofTy B) ModExpr.var pair.1).DefinedUnder p.assumptions ∧
      (ComparisonRankedDecision.instantiate (ComparisonSelectedBases.inputTypeKeys p)
        (fun _ => .ofTy B) ModExpr.var pair.2).DefinedUnder p.assumptions := by
    intro pair hp
    have hk : ComparisonSelectedBases.inputTypeKeys p = [1] := by decide
    change pair ∈ [(B,F B),(.var (.flex 1),F (.var (.flex 1))),(.unit,.unit)] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    all_goals
      change AlgebraSubtype p.assumptions _ _ ∧ _
      simp [ComparisonRankedDecision.instantiate, B, F, CompareTy.ofTy, CompareTy.subst,
        ComparisonRankedDecision.imageTypes, hk, CompareTy.DefinedUnder,
        CompareTy.wellFormedBounds, ModeModels]
    all_goals first
      | exact .shaped (.bound (a := B) (b := F B) (by decide))
      | exact .shaped (.refl (CompareTy.wellShaped_ofTy .unit _))
  exact ComparisonRankedDecision.run_complete p.assumptions
    (ComparisonSelectedBases.inputTypeKeys p) (fun _ => b)
    (ComparisonObserverBoundary.retainedTypes p.assumptions generators)
    (ComparisonObserverBoundary.retainedModes p.assumptions generators)
    (ComparisonObserverBoundary.sizeBound p.assumptions generators)
    ModExpr.var (ComparisonSignedObservation.endpoints p) (fun _ => .ofTy B) hi
    (ComparisonRankedDecision.machineValid_of_endpoints hΔ _ _ _ _ _ _ _ he)

#guard match checkSubsumption 100 source target with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonRelationalDeclaredWitness
