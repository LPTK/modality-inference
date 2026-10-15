import ModalityInference.Proofs.ComparisonContextWitnesses

namespace ModalityInference.ComparisonStructuredCapsuleWitness

def bad : ModExpr := .leftResidual .epsilon .bottom
def partialA : Ty := .modal (.var (.rigid 0)) bad
def partialB : Ty := .modal (.var (.rigid 1)) bad
def q : ModExpr := .const Mode.absorbing
def pattern (x : Ty) : Ty := .prod (.modal x q) (.fn (.modal x .bottom) .unit)
def source : Scheme := { typeParams := [0], body := pattern (.var (.flex 0)) }
def upper : Ty := .prod partialA (.modal partialB q)
def lower : Ty := .prod (.modal partialA q) partialB
def target : Scheme := .mono (.prod (.modal upper q) (.fn (.modal lower q) .unit))
def image : Ty := .modal (.prod partialA partialB) q
def witness : Substitution := { types := [(0, image)] }

theorem absorb (a : Ty) (m : ModExpr) (hm : m = q ∨ m = .bottom) :
    Subtype [] (.modal (.modal a q) m) (.modal a q) ∧
      Subtype [] (.modal a q) (.modal (.modal a q) m) := by
  rcases hm with rfl | rfl
  all_goals constructor
  all_goals first
    | exact Subtype.compose.trans (.congr .refl
        (.valid fun _ _ => ⟨_, _, rfl, rfl, by decide⟩))
    | exact (Subtype.congr .refl
        (.valid fun _ _ => ⟨_, _, rfl, rfl, by decide⟩)).trans .composeRev

theorem upper_bound : Subtype [] (.modal image q) (.modal upper q) := by
  apply (absorb (.prod partialA partialB) q (Or.inl rfl)).1.trans
  exact Subtype.prod .refl (absorb partialB q (Or.inl rfl)).2

theorem lower_bound : Subtype [] (.modal lower q) (.modal image .bottom) := by
  apply Subtype.trans _ (absorb (.prod partialA partialB) .bottom (Or.inr rfl)).2
  exact Subtype.prod (absorb partialA q (Or.inl rfl)).1 .refl

theorem body_witness : Subtype [] (pattern image) target.body :=
  Subtype.prod_congr upper_bound (Subtype.fn_congr lower_bound .refl)

theorem ordinary_witness : Subsumes [] source target := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · simp [Instantiates, source, witness]
  · simp [source, witness, EntailsAll, Substitution.bounds]
  · exact body_witness

theorem algebra_witness : AlgebraSubsumes [] source target := ordinary_witness.to_algebra

end ModalityInference.ComparisonStructuredCapsuleWitness
