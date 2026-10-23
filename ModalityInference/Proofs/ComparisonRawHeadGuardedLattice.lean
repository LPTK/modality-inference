import ModalityInference.Proofs.ComparisonRawHeadSupport

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

end ModalityInference.ComparisonRawHeadRestriction
