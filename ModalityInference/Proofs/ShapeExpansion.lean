import ModalityInference.Proofs.TypeElimination
import ModalityInference.Proofs.VariableOccurrences

namespace ModalityInference

inductive TypeHead where
  | unit | credit | prod | sum | fn
  deriving DecidableEq

def GroundTy.head : GroundTy → TypeHead
  | .unit _ => .unit
  | .credit _ => .credit
  | .prod .. => .prod
  | .sum .. => .sum
  | .fn .. => .fn

@[simp] theorem GroundTy.head_modal (a : GroundTy) (m : Mode) : (a.modal m).head = a.head := by
  cases a <;> rfl

theorem GroundOrder.head {a b} (h : GroundOrder a b) : a.head = b.head := by
  cases h <;> rfl

/-- Every shallow shape admits the requested ground type of that outer shape.
Only the shape's explicitly allocated type and modality variables change. -/
theorem Shape.realize_fresh {t shape ρ ground target} (h : Shape t shape)
    (ht : t.realize ρ = some ground) (hh : target.head = ground.head) :
    ∃ η, shape.realize η = some target ∧
      (∀ v, v ∉ shape.typeVars → η.types v = ρ.types v) ∧
      (∀ v, v ∉ shape.modVars → η.modes v = ρ.modes v) := by
  cases h
  case prod a b x y m hxy | sum a b x y m hxy | fn a b x y m hxy =>
    simp only [TypeExpr.realize, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ht
    obtain ⟨left, _, right, _, rfl⟩ := ht
    cases target <;> simp [GroundTy.head] at hh
    all_goals
      rename_i u v k
      refine ⟨⟨(fun w => if w = .flex x then u else if w = .flex y then v else ρ.types w),
        (fun w => if w = .flex m then k else ρ.modes w)⟩, ?_, ?_, ?_⟩
      · simp [TypeExpr.realize, ModExpr.eval, GroundTy.modal, Ne.symm hxy]
      · intro w hw
        simp only [TypeExpr.typeVars, Finset.mem_union, Finset.mem_singleton, not_or] at hw
        simp [hw.1, hw.2]
      · intro w hw
        simp_all [TypeExpr.modVars, ModExpr.vars]
  case unit m | credit m =>
    simp only [TypeExpr.realize, Option.some.injEq] at ht
    subst ground
    cases target <;> simp [GroundTy.head] at hh
    all_goals
      rename_i k
      refine ⟨{ρ with modes := fun w => if w = .flex m then k else ρ.modes w}, ?_, fun _ _ => rfl, ?_⟩
      · simp [TypeExpr.realize, ModExpr.eval, GroundTy.modal]
      · intro w hw
        simp_all [TypeExpr.modVars, ModExpr.vars]

end ModalityInference
