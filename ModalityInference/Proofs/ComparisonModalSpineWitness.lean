import ModalityInference.ComparisonModalSpineRegression
import ModalityInference.Proofs.ComparisonContextWitnesses

namespace ModalityInference.ComparisonModalSpineRegression

def witness : Substitution := { modes := [(0, .compose .top bad)] }

theorem ordinary_witness : Subsumes [] source target := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · simp [Instantiates, source, witness]
  · simp [source, witness, EntailsAll, Substitution.bounds]
  · exact Subtype.composeRev

private theorem raise (a : Ty) : Subtype [] a (.modal a .top) :=
  Subtype.identityRev.trans (.congr .refl
    (.valid fun _ _ => ⟨Mode.identity, Mode.top, rfl, rfl, by decide⟩))

private theorem lower (a : Ty) : Subtype [] (.modal a .bottom) a :=
  (Subtype.congr .refl
    (.valid fun _ _ => ⟨Mode.bottom, Mode.identity, rfl, rfl, by decide⟩)).trans .identity

theorem mixed_ordinary_witness : Subsumes [] mixedSource mixedTarget := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · simp [Instantiates, mixedSource, witness]
  · simp [mixedSource, witness, EntailsAll, Substitution.bounds]
  · apply Subtype.prod_congr
    · exact Subtype.composeRev.trans (raise capsule)
    · exact Subtype.fn_congr ((lower capsule).trans .compose) .refl

theorem algebra_witnesses : AlgebraSubsumes [] source target ∧
    AlgebraSubsumes [] mixedSource mixedTarget :=
  ⟨ordinary_witness.to_algebra, mixed_ordinary_witness.to_algebra⟩

end ModalityInference.ComparisonModalSpineRegression
