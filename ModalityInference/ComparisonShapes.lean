import ModalityInference.ComparisonTypes

/-! Shape compatibility for internal comparison witnesses. Only the supplied
ambient and target assumptions identify fixed names; source obligations do not
contribute shape equations. -/
namespace ModalityInference

inductive ComparisonShape where
  | var (name : TypeVar)
  | unit
  | credit
  | prod (left right : ComparisonShape)
  | sum (left right : ComparisonShape)
  | fn (domain codomain : ComparisonShape)
  deriving Repr, DecidableEq, BEq

namespace ComparisonShape

def ofTy : Ty → ComparisonShape
  | .var v => .var v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod (ofTy a) (ofTy b)
  | .sum a b => .sum (ofTy a) (ofTy b)
  | .fn a b => .fn (ofTy a) (ofTy b)
  | .modal a _ => ofTy a

def subst (ρ : TypeVar → ComparisonShape) : ComparisonShape → ComparisonShape
  | .var v => ρ v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod (a.subst ρ) (b.subst ρ)
  | .sum a b => .sum (a.subst ρ) (b.subst ρ)
  | .fn a b => .fn (a.subst ρ) (b.subst ρ)

def vars : ComparisonShape → List TypeVar
  | .var v => [v]
  | .unit | .credit => []
  | .prod a b | .sum a b | .fn a b => a.vars ++ b.vars

def pairs (Δ : Bounds) : List (ComparisonShape × ComparisonShape) :=
  Δ.flatMap fun c => match c with
    | .sub a b | .equiv a b => [(ofTy a, ofTy b)]
    | .equal v a => [(.var v, ofTy a)]
    | .mode _ _ | .defined _ => []

def Models (Δ : Bounds) (ρ : TypeVar → ComparisonShape) : Prop :=
  ∀ p ∈ pairs Δ, p.1.subst ρ = p.2.subst ρ

/-- Validity under declared shape equations keeps all names fixed parameters.
An inconsistent set of declared equations has no finite shape model. -/
def Equivalent (Δ : Bounds) (a b : ComparisonShape) : Prop :=
  ∀ ρ, Models Δ ρ → a.subst ρ = b.subst ρ

end ComparisonShape

namespace CompareTy

/-- The selected shape represents both branches of every well-shaped join or
meet. It is not a compatibility check by itself. -/
def shape : CompareTy → ComparisonShape
  | .var v => .var v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod a.shape b.shape
  | .sum a b => .sum a.shape b.shape
  | .fn a b => .fn a.shape b.shape
  | .modal a _ | .join a _ | .meet a _ => a.shape

def WellShaped (Δ : Bounds) : CompareTy → Prop
  | .var _ | .unit | .credit => True
  | .prod a b | .sum a b | .fn a b => WellShaped Δ a ∧ WellShaped Δ b
  | .modal a _ => WellShaped Δ a
  | .join a b | .meet a b =>
    WellShaped Δ a ∧ WellShaped Δ b ∧ ComparisonShape.Equivalent Δ a.shape b.shape

end CompareTy

def CompareSubstitution.WellShaped (Δ : Bounds) (σ : CompareSubstitution) : Prop :=
  ∀ entry ∈ σ.types, entry.2.WellShaped Δ

/-- Every intermediate comparison type must be well-shaped, not merely the
images of the final substitution. No distributivity or extrema are assumed. -/
inductive ShapedSubtype (Δ : Bounds) : CompareTy → CompareTy → Prop where
  | refl {a} : a.WellShaped Δ → ShapedSubtype Δ a a
  | trans {a b c} : ShapedSubtype Δ a b → ShapedSubtype Δ b c → ShapedSubtype Δ a c
  | bound {a b} : Constraint.sub a b ∈ Δ →
      ShapedSubtype Δ (CompareTy.ofTy a) (CompareTy.ofTy b)
  | identity {a} : a.WellShaped Δ → ShapedSubtype Δ (.modal a .epsilon) a
  | identityRev {a} : a.WellShaped Δ → ShapedSubtype Δ a (.modal a .epsilon)
  | compose {a m n} : a.WellShaped Δ →
      ShapedSubtype Δ (.modal (.modal a m) n) (.modal a (.compose m n))
  | composeRev {a m n} : a.WellShaped Δ →
      ShapedSubtype Δ (.modal a (.compose m n)) (.modal (.modal a m) n)
  | congr {a b m n} : ShapedSubtype Δ a b → Submode Δ m n →
      ShapedSubtype Δ (.modal a m) (.modal b n)
  | prod {a b c d m} : ShapedSubtype Δ (.modal a m) (.modal c m) →
      ShapedSubtype Δ (.modal b m) (.modal d m) →
      ShapedSubtype Δ (.modal (.prod a b) m) (.modal (.prod c d) m)
  | sum {a b c d m} : ShapedSubtype Δ (.modal a m) (.modal c m) →
      ShapedSubtype Δ (.modal b m) (.modal d m) →
      ShapedSubtype Δ (.modal (.sum a b) m) (.modal (.sum c d) m)
  | fn {a b c d m n} : ShapedSubtype Δ c a → ShapedSubtype Δ b d →
      Submode Δ m (.compose n .top) →
      ShapedSubtype Δ (.modal (.fn a b) m) (.modal (.fn c d) n)
  | credit {m n} : Submode Δ (.compose m (.const Mode.many)) n →
      ShapedSubtype Δ (.modal .credit m) (.modal .credit n)
  | joinLeft {a b} : (CompareTy.join a b).WellShaped Δ → ShapedSubtype Δ a (.join a b)
  | joinRight {a b} : (CompareTy.join a b).WellShaped Δ → ShapedSubtype Δ b (.join a b)
  | joinLeast {a b c} : ShapedSubtype Δ a c → ShapedSubtype Δ b c →
      ShapedSubtype Δ (.join a b) c
  | meetLeft {a b} : (CompareTy.meet a b).WellShaped Δ → ShapedSubtype Δ (.meet a b) a
  | meetRight {a b} : (CompareTy.meet a b).WellShaped Δ → ShapedSubtype Δ (.meet a b) b
  | meetGreatest {a b c} : ShapedSubtype Δ a b → ShapedSubtype Δ a c →
      ShapedSubtype Δ a (.meet b c)

def ShapedEntails (Δ : Bounds) : CompareConstraint → Prop
  | .sub a b => ShapedSubtype Δ a b ∧ a.DefinedUnder Δ ∧ b.DefinedUnder Δ
  | .mode a b => Submode Δ a b
  | .defined a => ∀ σ, ModeModels Δ σ → a.WellFormed σ
  | .equal v t => ShapedSubtype Δ (.var v) t ∧ ShapedSubtype Δ t (.var v) ∧
      t.DefinedUnder Δ
  | .equiv a b => ShapedSubtype Δ a b ∧ ShapedSubtype Δ b a ∧
      a.DefinedUnder Δ ∧ b.DefinedUnder Δ

def ShapedEntailsAll (Δ : Bounds) (cs : CompareBounds) : Prop :=
  ∀ c ∈ cs, ShapedEntails Δ c

def ShapedSubsumes (Δ : Bounds) (source target : Scheme) : Prop :=
  let (nt, nm) := source.subsumptionIndices Δ target
  let (assumptions, t) := target.instantiate nt nm true
  let declared := Δ ++ assumptions.assumptions
  ∃ σ, CompareInstantiates source σ ∧ σ.WellShaped declared ∧
    ShapedEntailsAll declared (σ.bounds source.bounds) ∧
    ShapedSubtype declared (σ.ty source.body) (CompareTy.ofTy t)

end ModalityInference
