import ModalityInference.ComparisonShapes

/-! The comparison algebra adds guarded distributive equations to the shaped
lattice relation. Public schemes still use `Ty`; bare subtyping retains its
original rules for partial annotations. -/
namespace ModalityInference

namespace ComparisonAlgebra

def typeOp (join : Bool) (a b : CompareTy) : CompareTy :=
  if join then .join a b else .meet a b

def modeOp (join : Bool) (m n : ModExpr) : ModExpr :=
  if join then .join m n else .meet m n

def DefinedMode (Δ : Bounds) (m : ModExpr) : Prop :=
  ∀ σ, ModeModels Δ σ → m.WellFormed σ

/-- The declared assumptions justify both shape compatibility and definedness. -/
def Compatible (Δ : Bounds) (a b : CompareTy) : Prop :=
  (.join a b : CompareTy).WellShaped Δ ∧ a.DefinedUnder Δ ∧ b.DefinedUnder Δ

inductive Equation (Δ : Bounds) : CompareTy → CompareTy → Prop where
  | distrib {a b c} (p : Bool) : Compatible Δ a b → Compatible Δ a c →
      Equation Δ (typeOp p a (typeOp (!p) b c))
        (typeOp (!p) (typeOp p a b) (typeOp p a c))
  | modal {a b m} (p : Bool) : Compatible Δ a b → DefinedMode Δ m →
      Equation Δ (.modal (typeOp p a b) m) (typeOp p (.modal a m) (.modal b m))
  | scalar {a m n} (p : Bool) : a.WellShaped Δ → a.DefinedUnder Δ →
      DefinedMode Δ m → DefinedMode Δ n →
      Equation Δ (.modal a (modeOp p m n)) (typeOp p (.modal a m) (.modal a n))
  | prod {a b c d} (p : Bool) : Compatible Δ a c → Compatible Δ b d →
      Equation Δ (typeOp p (.prod a b) (.prod c d)) (.prod (typeOp p a c) (typeOp p b d))
  | sum {a b c d} (p : Bool) : Compatible Δ a c → Compatible Δ b d →
      Equation Δ (typeOp p (.sum a b) (.sum c d)) (.sum (typeOp p a c) (typeOp p b d))
  | fn {a b c d} (p : Bool) : Compatible Δ a c → Compatible Δ b d →
      Equation Δ (typeOp p (.fn a b) (.fn c d)) (.fn (typeOp (!p) a c) (typeOp p b d))

end ComparisonAlgebra

/-- The shaped comparison relation closed under the guarded comparison algebra.
The clamping rules use proved bounds on the middle operand. -/
inductive AlgebraSubtype (Δ : Bounds) : CompareTy → CompareTy → Prop where
  | shaped {a b} : ShapedSubtype Δ a b → AlgebraSubtype Δ a b
  | trans {a b c} : AlgebraSubtype Δ a b → AlgebraSubtype Δ b c → AlgebraSubtype Δ a c
  | equation {a b} : ComparisonAlgebra.Equation Δ a b → AlgebraSubtype Δ a b
  | equationRev {a b} : ComparisonAlgebra.Equation Δ a b → AlgebraSubtype Δ b a
  | congr {a b m n} : AlgebraSubtype Δ a b → Submode Δ m n →
      AlgebraSubtype Δ (.modal a m) (.modal b n)
  | prod {a b c d m} : AlgebraSubtype Δ (.modal a m) (.modal c m) →
      AlgebraSubtype Δ (.modal b m) (.modal d m) →
      AlgebraSubtype Δ (.modal (.prod a b) m) (.modal (.prod c d) m)
  | sum {a b c d m} : AlgebraSubtype Δ (.modal a m) (.modal c m) →
      AlgebraSubtype Δ (.modal b m) (.modal d m) →
      AlgebraSubtype Δ (.modal (.sum a b) m) (.modal (.sum c d) m)
  | fn {a b c d m n} : AlgebraSubtype Δ c a → AlgebraSubtype Δ b d →
      Submode Δ m (.compose n .top) →
      AlgebraSubtype Δ (.modal (.fn a b) m) (.modal (.fn c d) n)
  | joinLeast {a b c} : AlgebraSubtype Δ a c → AlgebraSubtype Δ b c →
      AlgebraSubtype Δ (.join a b) c
  | meetGreatest {a b c} : AlgebraSubtype Δ a b → AlgebraSubtype Δ a c →
      AlgebraSubtype Δ a (.meet b c)
  | clamp {b a t m} : ComparisonAlgebra.Compatible Δ b a →
      ComparisonAlgebra.Compatible Δ a t → ComparisonAlgebra.DefinedMode Δ m →
      AlgebraSubtype Δ b a → AlgebraSubtype Δ a t →
      AlgebraSubtype Δ (.modal a m) (.meet (.join a (.modal b m)) (.modal t m))
  | clampRev {b a t m} : ComparisonAlgebra.Compatible Δ b a →
      ComparisonAlgebra.Compatible Δ a t → ComparisonAlgebra.DefinedMode Δ m →
      AlgebraSubtype Δ b a → AlgebraSubtype Δ a t →
      AlgebraSubtype Δ (.meet (.join a (.modal b m)) (.modal t m)) (.modal a m)

def AlgebraEntails (Δ : Bounds) : CompareConstraint → Prop
  | .sub a b => AlgebraSubtype Δ a b ∧ a.DefinedUnder Δ ∧ b.DefinedUnder Δ
  | .mode a b => Submode Δ a b
  | .defined a => ∀ σ, ModeModels Δ σ → a.WellFormed σ
  | .equal v t => AlgebraSubtype Δ (.var v) t ∧ AlgebraSubtype Δ t (.var v) ∧
      t.DefinedUnder Δ
  | .equiv a b => AlgebraSubtype Δ a b ∧ AlgebraSubtype Δ b a ∧
      a.DefinedUnder Δ ∧ b.DefinedUnder Δ

def AlgebraEntailsAll (Δ : Bounds) (cs : CompareBounds) : Prop :=
  ∀ c ∈ cs, AlgebraEntails Δ c

/-- Exact source instantiation, declared shape assumptions, guarded source bounds,
and a separate bare body comparison are preserved. -/
def AlgebraSubsumes (Δ : Bounds) (source target : Scheme) : Prop :=
  let (nt, nm) := source.subsumptionIndices Δ target
  let (assumptions, t) := target.instantiate nt nm true
  let declared := Δ ++ assumptions.assumptions
  ∃ σ, CompareInstantiates source σ ∧ σ.WellShaped declared ∧
    AlgebraEntailsAll declared (σ.bounds source.bounds) ∧
    AlgebraSubtype declared (σ.ty source.body) (CompareTy.ofTy t)

end ModalityInference
