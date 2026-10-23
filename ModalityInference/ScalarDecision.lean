import ModalityInference.ModeBackend

/-! Completed scalar decisions use a structural bound for symbolic CNF
normalization. They do not enumerate modality valuations. -/
namespace ModalityInference.ScalarDecision

/-- Bounds both normalization fuel and the number of intermediate clauses. -/
def budget : BoolExpr → Nat
  | .const _ | .atom _ => 1
  | .and a b | .or a b | .imp a b =>
      budget a + budget b + budget a * budget b + 1

def formula (e : BoolExpr) : Bool :=
  match ConcreteBackend.decideFormula (budget e) e with
  | .success report => report.valid
  | _ => false

def entails (assumptions goals : Bounds) : Bool :=
  formula (.imp (boundsModeFormula assumptions) (boundsModeFormula goals))

def defined (Δ : Bounds) (m : ModExpr) : Bool := entails Δ [.defined m]

def submode (Δ : Bounds) (m n : ModExpr) : Bool := entails Δ [.mode m n]

end ModalityInference.ScalarDecision
