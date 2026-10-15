import ModalityInference.SchemeSubsumption
import ModalityInference.Proofs.ComparisonDefinedInstances

/-! Totality of bound-only residuals is certified before structural reduction.
An absorbing witness can satisfy acted type bounds without ordering their
outer labels separately. -/
namespace ModalityInference.ComparisonDefinedBoundSuffix
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def r : ModExpr := .leftResidual (.var (.rigid 0)) .bottom
def X : Ty := .var (.flex 0)
def source : Scheme :=
  {typeParams := [0], bounds := [.sub (.modal (.modal X r) .top)
    (.modal (.modal X r) .bottom)], body := .unit}
def target : Scheme := {bounds := [.defined r],body := .unit}
def witness : Substitution := {types := [(0,.modal .unit (.const Mode.absorbing))]}

theorem admissible : SubsumesUnder [] source target := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · constructor
    · exact ⟨List.Perm.refl _, List.Perm.refl _⟩
    · constructor
      · intro v
        cases v with
        | rigid n => exact fun η hη c hc => False.elim (List.not_mem_nil hc)
        | flex n =>
          by_cases hn : n = 0
          · subst n
            intro η hη c hc
            change c ∈ [.defined (.const Mode.absorbing)] at hc
            cases List.mem_singleton.mp hc
            rfl
          · simp [Substitution.type, witness, List.lookup_cons,
              beq_eq_false_iff_ne.mpr hn, TypeExpr.DefinedUnder,
              TypeExpr.wellFormedBounds, ModeModels]
      · intro v η hη
        cases v <;> rfl
    · exact fun η hη c hc => False.elim (List.not_mem_nil hc)
  · intro c hc
    change c ∈ [.sub (.modal (.modal (.modal .unit (.const Mode.absorbing)) r) .top)
      (.modal (.modal (.modal .unit (.const Mode.absorbing)) r) .bottom)] at hc
    cases List.mem_singleton.mp hc
    have hr : Entails [.defined r] (.defined r) :=
      fun η hη => hη _ List.mem_cons_self
    refine ⟨?_, ?_, ?_⟩
    · exact Subtype.compose.trans (Subtype.compose.trans
        ((Subtype.congr .refl (Submode.valid (by
          intro η hη
          obtain ⟨r, he⟩ := Option.isSome_iff_exists.mp (hr η hη)
          simp [ModExpr.Below, ModExpr.eval, he, ModExpr.top, ModExpr.bottom,
            Mode.compose, Mode.absorbing, Mode.le]))).trans
          (Subtype.composeRev.trans Subtype.composeRev)))
    all_goals
      intro η hη c hc
      change c ∈ [.defined (.const Mode.absorbing), .defined r, .defined _] at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rfl
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hr η hη
      cases List.mem_singleton.mp hc
      rfl
  · exact .refl

theorem residual : Residual target.bounds := by trivial

theorem algebra_admissible : AlgebraSubsumesUnder [] source target :=
  admissible.to_algebra

#guard (checkSubsumption 20000 source target).isSuccess
#guard match checkSubsumption 20000 source (.mono .unit) with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonDefinedBoundSuffix
