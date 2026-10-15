import ModalityInference.Proofs.TypingAdmissibility

/-! Monotone predicates on modal type variables provide syntactic invariants
for subtyping. Constructed types impose no predicate on their head. -/
namespace ModalityInference

def TypeExpr.variablePredicate (P : TypeVar → Mode → Prop) (η : ModVar → Mode) :
    Ty → Mode → Prop
  | .var v, k => P v k
  | .modal a m, k => ∃ n, m.eval (some ∘ η) = some n ∧ a.variablePredicate P η (n.compose k)
  | _, _ => True

theorem TypeExpr.variablePredicate_mono {P : TypeVar → Mode → Prop} {η}
    (hP : ∀ v m n, m.le n = true → P v m → P v n)
    (a : Ty) {m n : Mode} (hmn : m.le n = true) :
    a.variablePredicate P η m → a.variablePredicate P η n := by
  induction a generalizing m n <;> simp only [variablePredicate]
  case var v => exact hP v m n hmn
  case modal a r ih =>
    exact fun ⟨k, hk, ha⟩ => ⟨k, hk, ih (Mode.compose_le_left k hmn) ha⟩
  all_goals exact id

theorem TypeExpr.variablePredicate_compose (a : Ty) (m n : ModExpr) (k : Mode)
    (P : TypeVar → Mode → Prop) (η : ModVar → Mode) :
    ((a.modal m).modal n).variablePredicate P η k ↔
      (a.modal (m.compose n)).variablePredicate P η k := by
  cases hm : m.eval (some ∘ η) <;> cases hn : n.eval (some ∘ η) <;>
    simp [variablePredicate, ModExpr.eval, hm, hn, Mode.compose_assoc]

theorem Subtype.variablePredicate {Δ a b} (h : Subtype Δ a b)
    {P : TypeVar → Mode → Prop} {η : ModVar → Mode}
    (hP : ∀ v m n, m.le n = true → P v m → P v n)
    (hη : ModeModels Δ η)
    (hb : ∀ a b, Constraint.sub a b ∈ Δ → ∀ k,
      a.variablePredicate P η k → b.variablePredicate P η k) :
    ∀ k, a.variablePredicate P η k → b.variablePredicate P η k := by
  induction h
  case congr a b m n hab hm ih =>
    obtain ⟨l, r, hl, hr, hle⟩ := hm.denote hη
    simp only [TypeExpr.variablePredicate, hl, hr, Option.some.injEq, exists_eq_left']
    exact fun k ha => b.variablePredicate_mono hP (Mode.compose_le_right k hle) (ih _ ha)
  case compose a m n => exact fun k => (a.variablePredicate_compose m n k P η).mp
  case composeRev a m n => exact fun k => (a.variablePredicate_compose m n k P η).mpr
  case fn a b c d m n _ _ hm _ _ =>
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
      ((Entails.defined_compose_iff.mp hm.defined.2).1 η hη)
    exact fun _ _ => ⟨r, hr, trivial⟩
  case prod | sum => exact fun _ ⟨r, hr, _⟩ => ⟨r, hr, trivial⟩
  case refl => exact fun _ => id
  case trans _ _ ihab ihbc => exact fun k ha => ihbc k (ihab k ha)
  case bound a b hc => exact hb a b hc
  case identity | identityRev =>
    simp [TypeExpr.variablePredicate, ModExpr.epsilon, ModExpr.eval]

end ModalityInference
