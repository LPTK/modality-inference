import ModalityInference.Proofs.ComparisonPartialCarrierOperations
import ModalityInference.Proofs.ComparisonPartialCarrierUpperOperations

namespace ModalityInference.ComparisonPartialCarrier

structure Interpretation (Δ : Bounds) where
  lower : LowerIdeal Δ
  upper : UpperIdeal Δ

def BinaryImage (op : CompareTy → CompareTy → CompareTy)
    (S T : CompareTy → Prop) : CompareTy → Prop :=
  fun a => ∃ b c, S b ∧ T c ∧ a = op b c

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Carrier ideals retain partial modal barriers as literal type contexts. -/
def denote (Δ : Bounds) : CompareTy → Interpretation Δ
  | .var v => ⟨.principal Δ (.var v), .principal Δ (.var v)⟩
  | .unit => ⟨.principal Δ .unit, .principal Δ .unit⟩
  | .credit => ⟨.principal Δ .credit, .principal Δ .credit⟩
  | .prod a b =>
      ⟨.closure Δ (BinaryImage .prod (denote Δ a).lower.mem (denote Δ b).lower.mem),
       .closure Δ (BinaryImage .prod (denote Δ a).upper.mem (denote Δ b).upper.mem)⟩
  | .sum a b =>
      ⟨.closure Δ (BinaryImage .sum (denote Δ a).lower.mem (denote Δ b).lower.mem),
       .closure Δ (BinaryImage .sum (denote Δ a).upper.mem (denote Δ b).upper.mem)⟩
  | .fn a b =>
      ⟨.closure Δ (BinaryImage .fn (denote Δ a).upper.mem (denote Δ b).lower.mem),
       .closure Δ (BinaryImage .fn (denote Δ a).lower.mem (denote Δ b).upper.mem)⟩
  | .modal a m =>
      if Entails Δ (.defined m) then
        ⟨.closure Δ ((denote Δ a).lower.modalImage m),
         .closure Δ ((denote Δ a).upper.modalImage m)⟩
      else
        ⟨.closure Δ (fun t => Carrier Δ a ∧ t = .modal a m),
         .closure Δ (fun t => Carrier Δ a ∧ t = .modal a m)⟩
  | .join a b =>
      ⟨.closure Δ (fun t => (denote Δ a).lower.mem t ∨ (denote Δ b).lower.mem t),
       (denote Δ a).upper.inter (denote Δ b).upper⟩
  | .meet a b =>
      ⟨(denote Δ a).lower.inter (denote Δ b).lower,
       .closure Δ (fun t => (denote Δ a).upper.mem t ∨ (denote Δ b).upper.mem t)⟩

end

end ModalityInference.ComparisonPartialCarrier
