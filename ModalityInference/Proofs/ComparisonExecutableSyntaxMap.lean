import ModalityInference.ComparisonExecutableSyntax

/-! A map of executable data commutes with evaluation, independently of any
semantic model or invariant on arbitrary values in the target representation. -/
namespace ModalityInference.ComparisonExecutableSyntax

variable {M N V W : Type*}

structure DataMap (E : Data M V) (F : Data N W) (f : V → W) (g : M → N) : Prop where
  total : E.total = F.total
  control : ∀ m, g (E.control m) = F.control m
  shift : ∀ m x, f (E.shift m x) = F.shift (g m) (f x)
  prod : ∀ p x y, f (E.prod p x y) = F.prod p (f x) (f y)
  sum : ∀ p x y, f (E.sum p x y) = F.sum p (f x) (f y)
  fn : ∀ x y, f (E.fn x y) = F.fn (f x) (f y)
  join : ∀ x y, f (E.join x y) = F.join (f x) (f y)
  meet : ∀ x y, f (E.meet x y) = F.meet (f x) (f y)
  atom : ∀ v, f (E.atom v) = F.atom v
  unit : f E.unit = F.unit
  credit : f E.credit = F.credit
  bottom : f E.bottom = F.bottom
  frozen : E.frozen.map (fun row => (row.1,f row.2)) = F.frozen

namespace DataMap

variable {E : Data M V} {F : Data N W} {f : V → W} {g : M → N} (h : DataMap E F f g)

include h

theorem frozenValue (a : CompareTy) : f (E.frozenValue a) = F.frozenValue a := by
  rw [Data.frozenValue,Data.frozenValue,← h.frozen,List.find?_map]
  change f (((E.frozen.find? (fun row => decide (row.1 = a))).map Prod.snd).getD E.bottom) =
    (((E.frozen.find? (fun row => decide (row.1 = a))).map
      (fun row => (row.1,f row.2))).map Prod.snd).getD F.bottom
  cases E.frozen.find? (fun row => decide (row.1 = a)) with
  | none => exact h.bottom
  | some row => rfl

theorem eval_eq (a : CompareTy) (p : Option ModExpr) : f (E.eval a p) = F.eval a p := by
  induction a generalizing p with
  | var v => cases p <;> first | exact h.atom v | exact h.frozenValue _
  | unit => cases p <;> first | exact h.unit | exact h.frozenValue _
  | credit => cases p <;> first | exact h.credit | exact h.frozenValue _
  | prod a b iha ihb => exact (h.prod p _ _).trans (congrArg₂ _ (iha p) (ihb p))
  | sum a b iha ihb => exact (h.sum p _ _).trans (congrArg₂ _ (iha p) (ihb p))
  | fn a b iha ihb =>
    cases p with
    | some p => exact h.frozenValue _
    | none => exact (h.fn _ _).trans (congrArg₂ _ (iha none) (ihb none))
  | join a b iha ihb =>
    cases p with
    | some p => exact h.frozenValue _
    | none => exact (h.join _ _).trans (congrArg₂ _ (iha none) (ihb none))
  | meet a b iha ihb =>
    cases p with
    | some p => exact h.frozenValue _
    | none => exact (h.meet _ _).trans (congrArg₂ _ (iha none) (ihb none))
  | modal a m ih =>
    cases p with
    | some p => exact ih _
    | none => simp only [Data.eval,h.shift,h.control,ih,h.total]

theorem evalRaw_eq (a : Ty) : f (E.evalRaw a) = F.evalRaw a := h.eval_eq (.ofTy a) none

end DataMap
end ModalityInference.ComparisonExecutableSyntax
