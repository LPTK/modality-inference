import ModalityInference.Proofs.ComparisonContextWitnesses

namespace ModalityInference.ComparisonFrozenContextWitness

def bad : ModExpr := .leftResidual .epsilon .bottom
def base : Ty := .var (.rigid 0)
def typeSource : Scheme := { typeParams := [0], body := .modal (.var (.flex 0)) bad }
def typeTarget : Scheme := .mono (.modal (.modal base bad) .top)
def typeWitness : Substitution := { types := [(0, base)] }

theorem raise (a : Ty) : Subtype [] a (.modal a .top) :=
  Subtype.identityRev.trans (.congr .refl
    (.valid fun _ _ => ⟨Mode.identity, Mode.top, rfl, rfl, by decide⟩))

theorem type_ordinary_witness : Subsumes [] typeSource typeTarget := by
  refine ⟨typeWitness, ?_, ?_, ?_⟩
  · simp [Instantiates, typeSource, typeWitness]
  · simp [typeSource, typeWitness, EntailsAll, Substitution.bounds]
  · exact raise (.modal base bad)

def sharedSource : Scheme :=
  { modParams := [0]
    body := .prod (.modal base (.close (.var (.flex 0)))) (.modal base (.var (.flex 0))) }
def sharedTarget : Scheme := .mono
  (.prod (.modal (.modal base (.close bad)) .top) (.modal (.modal base bad) .top))
def sharedWitness : Substitution := { modes := [(0, bad)] }

theorem shared_ordinary_witness : Subsumes [] sharedSource sharedTarget := by
  refine ⟨sharedWitness, ?_, ?_, ?_⟩
  · simp [Instantiates, sharedSource, sharedWitness]
  · simp [sharedSource, sharedWitness, EntailsAll, Substitution.bounds]
  · exact Subtype.prod_congr (raise (.modal base (.close bad))) (raise (.modal base bad))

theorem algebra_witnesses : AlgebraSubsumes [] typeSource typeTarget ∧
    AlgebraSubsumes [] sharedSource sharedTarget :=
  ⟨type_ordinary_witness.to_algebra, shared_ordinary_witness.to_algebra⟩

end ModalityInference.ComparisonFrozenContextWitness
