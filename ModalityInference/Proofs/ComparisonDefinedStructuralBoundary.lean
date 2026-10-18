import ModalityInference.SchemeSubsumption
import ModalityInference.Proofs.ComparisonDefinedInstances

/-! A defined witness using a declared structural edge. The declared edge is
outside the residual-bound grammar of the executable completeness contract. -/
namespace ModalityInference.ComparisonDefinedStructuralBoundary
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def A : Ty := .var (.rigid 0)
def C : Ty := .var (.rigid 1)
def D : Ty := .var (.rigid 2)
def X : Ty := .var (.flex 0)
def source : Scheme := {typeParams := [0],bounds := [.sub A X],body := .prod X X}
def target : Scheme := {bounds := [.sub (.prod A A) (.prod C D)],body := .prod C D}
def witness : Substitution := {types := [(0,A)]}
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
            exact fun η hη c hc => False.elim (List.not_mem_nil hc)
          · simp [Substitution.type, witness, List.lookup_cons, beq_eq_false_iff_ne.mpr hn, A,
              TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]
      · intro v η hη
        cases v <;> rfl
    · exact fun η hη c hc => False.elim (List.not_mem_nil hc)
  · intro c hc
    change c ∈ [.sub A A] at hc
    rcases List.mem_singleton.mp hc with rfl
    exact ⟨.refl, fun _ _ _ h => False.elim (List.not_mem_nil h),
      fun _ _ _ h => False.elim (List.not_mem_nil h)⟩
  · apply Subtype.bound
    exact List.mem_singleton_self _

theorem algebra_admissible : AlgebraSubsumesUnder [] source target := admissible.to_algebra

theorem target_not_residual : ¬ Residual target.bounds := by
  intro h
  have hh := List.forall_iff_forall_mem.mp h (.sub (.prod A A) (.prod C D)) (by simp [target])
  obtain ⟨x,y,m,n,ha,hb⟩ := hh
  cases ha

#guard match checkSubsumption 20000 source target with
 | .success result => result.substitution.types.map Prod.fst == [0] &&
     result.substitution.modes.isEmpty
 | _ => false
end ModalityInference.ComparisonDefinedStructuralBoundary
