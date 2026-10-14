import ModalityInference.Proofs.GenerationCompletenessAtomic
import ModalityInference.Proofs.GenerationCompletenessLambda
import ModalityInference.Proofs.GenerationCompletenessBinary
import ModalityInference.Proofs.GenerationCompletenessUnary
import ModalityInference.Proofs.GenerationCompletenessElimination
import ModalityInference.Proofs.GenerationCompletenessSplit
import ModalityInference.Proofs.GenerationCompletenessReuse
import ModalityInference.Proofs.GenerationCompletenessDefinition

/-! Every ground instance of a declarative typing is represented by a successful
executable generation, preserving all earlier allocated identifiers. -/
namespace ModalityInference

theorem Typing.ground_complete {Δ Γ t a} (h : Typing Δ Γ t a) :
    GroundTypingComplete Δ Γ t a := by
  induction h
  case var => apply GroundTypingComplete.var <;> assumption
  case unit => exact GroundTypingComplete.unit
  case subs => apply GroundTypingComplete.subs <;> assumption
  case lam => apply GroundTypingComplete.lam <;> assumption
  case app => apply GroundTypingComplete.app <;> assumption
  case pair => apply GroundTypingComplete.pair <;> assumption
  case stackPair => apply GroundTypingComplete.stackPair <;> assumption
  case inl => apply GroundTypingComplete.inl; assumption
  case inr => apply GroundTypingComplete.inr; assumption
  case case => apply GroundTypingComplete.case <;> assumption
  case split => apply GroundTypingComplete.split <;> assumption
  case reuse Δ Γ Γ₁ Γ₂ Γ₃ Γ₂₃ t u v a b m k hj hk ht hu hv hkm hm it iu iv =>
    exact GroundTypingComplete.reuse hj hk ht hu hv hkm hm it iu iv
  case region => apply GroundTypingComplete.region; assumption
  case defn => apply GroundTypingComplete.defn <;> assumption

end ModalityInference
