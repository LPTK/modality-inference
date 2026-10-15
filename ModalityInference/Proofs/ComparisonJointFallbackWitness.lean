import ModalityInference.Proofs.ComparisonDefinedInstances
import ModalityInference.SchemeSubsumption

/-! A defined comparison whose shared modality choice must satisfy the
opaque type coordinates together. The explicit witness uses only public types. -/
namespace ModalityInference.ComparisonJointFallbackWitness

def A : Ty := .var (.rigid 0)
def B : Ty := .var (.rigid 1)
def X : Ty := .var (.flex 0)
def mu : ModExpr := .var (.flex 0)
def k : ModExpr := .const ⟨false,true,true⟩
def negLocal : ModExpr := .rightResidual (.join (.future mu) k) k
def source : Scheme :=
  { typeParams := [0]
    modParams := [0]
    bounds := [.sub (.modal X k) B, .sub (.modal A negLocal) (.modal X .top)]
    body := .unit }
def target : Scheme :=
  { bounds := [.sub (.modal A k) (.modal B .top)]
    body := .unit }
def witness : Substitution := {types := [(0,B)], modes := [(0,.epsilon)]}

theorem negLocal_defined (Δ : Bounds) : Entails Δ (.defined negLocal) := by
  simp [Entails, negLocal, mu, k, ModExpr.WellFormed, ModExpr.eval,
    Function.comp_def, Mode.future, Mode.join, Mode.rightResidual]

theorem target_residual : Residual target.bounds := by
  simp only [Residual, target, List.forall_cons]
  exact ⟨⟨_, _, _, _, rfl, rfl⟩, trivial⟩

theorem bound_witness :
    EntailsAll target.bounds.assumptions (witness.bounds source.bounds) := by
  have first : Subtype target.bounds.assumptions (.modal B k) B :=
    .trans (.congr .refl (.valid (by intro η hη; exact ⟨_, _, rfl, rfl, rfl⟩))) .identity
  have second : Subtype target.bounds.assumptions
      (.modal A (negLocal.subst witness.mode)) (.modal B .top) := by
    apply ModalityInference.Subtype.trans (b := .modal A k)
    · exact .congr .refl (.valid (by intro η hη; exact ⟨_, _, rfl, rfl, rfl⟩))
    · exact .bound (by simp [target, Bounds.assumptions, Constraint.assumptions])
  change EntailsAll target.bounds.assumptions
    [.sub (.modal B k) B, .sub (.modal A (negLocal.subst witness.mode)) (.modal B .top)]
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · refine ⟨first, ?_, ?_⟩ <;>
      simp [TypeExpr.DefinedUnder, B, TypeExpr.wellFormedBounds, ModeModels,
        ModeSatisfies, ModExpr.WellFormed, ModExpr.eval, k]
  · refine ⟨second, ?_, ?_⟩ <;>
      simp [TypeExpr.DefinedUnder, A, B, TypeExpr.wellFormedBounds, ModeModels,
        ModeSatisfies, ModExpr.WellFormed, ModExpr.eval, negLocal,
        ModExpr.subst, mu, witness, Substitution.mode, k, ModExpr.epsilon,
        ModExpr.top, Mode.future, Mode.identity, Mode.join, Mode.rightResidual]

theorem witness_instance : InstantiatesUnder target.bounds.assumptions source witness := by
  constructor
  · constructor <;> exact List.Perm.refl _
  · constructor
    · intro v
      cases v with
      | flex n => cases n <;>
          simp [witness, Substitution.type, List.lookup_cons, B, TypeExpr.DefinedUnder,
            TypeExpr.wellFormedBounds, ModeModels]
      | rigid n =>
          simp [Substitution.type, TypeExpr.DefinedUnder,
            TypeExpr.wellFormedBounds, ModeModels]
    · intro v
      cases v with
      | flex n => cases n <;>
          simp [witness, Substitution.mode, List.lookup_cons, Entails, ModExpr.WellFormed,
            ModExpr.eval, ModExpr.epsilon, Function.comp_def]
      | rigid n =>
          simp [Substitution.mode, Entails, ModExpr.WellFormed,
            ModExpr.eval, Function.comp_def]
  · simp [source, Substitution.ty, TypeExpr.subst, TypeExpr.DefinedUnder,
      TypeExpr.wellFormedBounds, ModeModels]

theorem subsumes : SubsumesUnder [] source target := by
  exact ⟨witness, witness_instance, bound_witness, .refl⟩

theorem algebra_subsumes : AlgebraSubsumesUnder [] source target := subsumes.to_algebra

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
#guard match ComparisonChecker.run 20000 source.requireDefinedInstances target with
  | .rejected _ => true
  | _ => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
#guard match checkSubsumption 20000 source target with
  | .success result => result.substitution.types.map Prod.fst == [0] &&
      result.substitution.modes.map Prod.fst == [0]
  | _ => false

end ModalityInference.ComparisonJointFallbackWitness
