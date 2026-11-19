import ModalityInference.Proofs.ComparisonRawHeadRestriction

namespace ModalityInference.ComparisonRawHeadRestriction

/-- Lattice nodes have defined operands; other nodes may contain arbitrary
partial annotations. Public join-free types and all defined witnesses satisfy
this condition. -/
def GuardedLattice (Δ : Bounds) : CompareTy → Prop
  | .prod a b | .sum a b | .fn a b => GuardedLattice Δ a ∧ GuardedLattice Δ b
  | .modal a _ => GuardedLattice Δ a
  | .join a b | .meet a b => a.DefinedUnder Δ ∧ b.DefinedUnder Δ
  | _ => True

theorem GuardedLattice.ofTy (Δ : Bounds) (a : Ty) : GuardedLattice Δ (.ofTy a) := by
  induction a with
  | var | unit | credit => trivial
  | prod a b ia ib | sum a b ia ib | fn a b ia ib => exact ⟨ia,ib⟩
  | modal a m ih => exact ih

theorem GuardedLattice.of_defined {Δ a} (h : CompareTy.DefinedUnder a Δ) :
    GuardedLattice Δ a := by
  induction a with
  | var | unit | credit => trivial
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
      exact ⟨ia (CompareTy.definedUnder_fn_iff.mp h).1,
        ib (CompareTy.definedUnder_fn_iff.mp h).2⟩
  | modal a m ih => exact ih (CompareTy.definedUnder_modal_iff.mp h).1
  | join | meet => exact CompareTy.definedUnder_fn_iff.mp h


theorem oneHead_eq_heads {Δ a} (h : GuardedLattice Δ a) : oneHead Δ a = heads Δ a := by
  fun_induction oneHead Δ a with
  | case1 a m n ih => exact (ih h).trans (heads_compose Δ a m n).symm
  | case2 a m _ hm ih => exact (ih h).trans (heads_modal_total hm a).symm
  | case3 a m hn hm =>
    cases m <;> first | exact False.elim (hn _ _ rfl) | simp only [heads, if_neg hm]
  | case4 a _ _ hd => exact (heads_defined hd).symm
  | case5 a _ hn hd =>
    cases a with
    | modal a m => exact False.elim (hn a m rfl)
    | join a b => exact False.elim (hd (CompareTy.definedUnder_join_iff.mpr h))
    | meet a b => exact False.elim (hd (CompareTy.definedUnder_meet_iff.mpr h))
    | _ => simp only [heads, if_neg hd]

end ModalityInference.ComparisonRawHeadRestriction
