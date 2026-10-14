import ModalityInference.HornPropagation
import ModalityInference.Inference

/-! The polarized domain of ordinary inference. Modalities in inferred types are
monomials; residuals occur only in bounds. Both closure adjoints reverse polarity,
and lock capture is admitted only for a monomial argument. These distinctions
ensure that partial residual definedness remains in the Horn fragment. -/
namespace ModalityInference

namespace ModExpr

/-- Total expressions whose three Boolean coordinates use only conjunction. -/
def IsMonomial : ModExpr → Prop
  | .const _ | .var _ => True
  | .compose a b => a.IsMonomial ∧ b.IsMonomial
  | .close a | .closeInv a | .future a | .capture a => a.IsMonomial
  | _ => False

/-- Polarized residual syntax, closed under the executable closure conversion. -/
def IsPolar : Polarity → ModExpr → Prop
  | _, .const _ | _, .var _ => True
  | p, .compose a b => a.IsPolar p ∧ b.IsPolar p
  | .positive, .join a b => a.IsPolar .positive ∧ b.IsPolar .positive
  | .negative, .meet a b => a.IsPolar .negative ∧ b.IsPolar .negative
  | .positive, .leftResidual a b | .negative, .rightResidual a b =>
      a.IsPolar .positive ∧ b.IsPolar .negative
  | p, .close a | p, .closeInv a => a.IsPolar p.flip
  | p, .future a => a.IsPolar p
  | _, .capture a => a.IsMonomial
  | _, _ => False

end ModExpr

/-- The future coordinates use ordinary Boolean order; uniqueness reverses it. -/
def Projection.IsPolar (p : Polarity) (q : Projection) : Prop :=
  match p with
  | .positive => q.locality.IsPositive ∧ q.affinity.IsPositive ∧
      q.uniqueness.IsHorn ∧ q.defined.IsHorn
  | .negative => q.locality.IsHorn ∧ q.affinity.IsHorn ∧
      q.uniqueness.IsPositive ∧ q.defined.IsHorn

namespace TypeExpr

def IsMonomial : Ty → Prop
  | .var _ | .unit | .credit => True
  | .prod a b | .sum a b | .fn a b => a.IsMonomial ∧ b.IsMonomial
  | .modal a m => a.IsMonomial ∧ m.IsMonomial

def IsPolar (p : Polarity) : Ty → Prop
  | .var _ | .unit | .credit => True
  | .prod a b | .sum a b => a.IsPolar p ∧ b.IsPolar p
  | .fn a b => a.IsPolar p.flip ∧ b.IsPolar p
  | .modal a m => a.IsPolar p ∧ m.IsPolar p

end TypeExpr

/-- General polarized types support structural subtyping. -/
def Constraint.IsPolar : Constraint → Prop
  | .sub a b => a.IsPolar .positive ∧ b.IsPolar .negative
  | .mode a b => a.IsPolar .positive ∧ b.IsPolar .negative
  | .defined m => ∃ p, m.IsPolar p
  | .equal _ t => t.IsMonomial
  | .equiv a b => a.IsMonomial ∧ b.IsMonomial

/-- Ordinary inference keeps the stronger monomial type invariant through sharing,
locks, freshening, and substitution; its mode bounds may contain residuals. -/
def Constraint.IsInference : Constraint → Prop
  | .sub a b | .equiv a b => a.IsMonomial ∧ b.IsMonomial
  | .equal _ t => t.IsMonomial
  | c => c.IsPolar

def Bounds.IsPolar (cs : Bounds) : Prop := ∀ c ∈ cs, c.IsPolar

def Bounds.IsInference (cs : Bounds) : Prop := ∀ c ∈ cs, c.IsInference

structure Substitution.IsMonomial (s : Substitution) : Prop where
  types : ∀ n t, (n, t) ∈ s.types → t.IsMonomial
  modes : ∀ n m, (n, m) ∈ s.modes → m.IsMonomial

def Scheme.IsInference (s : Scheme) : Prop :=
  s.body.IsMonomial ∧ s.bounds.IsInference

def ContextEntry.IsInference : ContextEntry → Prop
  | .binding none => True
  | .binding (some s) => s.IsInference
  | .lock m => m.IsMonomial

def AlgorithmicContext.IsInference (Γ : AlgorithmicContext) : Prop :=
  ∀ e ∈ Γ, e.IsInference

def Context.IsInference (Γ : Context) : Prop :=
  ∀ s ∈ Γ, ∀ t, s = some t → t.IsInference

structure SolverState.IsInference (s : SolverState) : Prop where
  pending : s.pending.IsInference
  bounds : s.bounds.IsInference
  substitution : s.substitution.IsMonomial

def InferenceState.IsInference (s : InferenceState) : Prop := s.constraints.IsInference

end ModalityInference
