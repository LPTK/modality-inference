import ModalityInference.Declarative

/-! Internal type witnesses for scheme comparison. Public schemes retain `Ty`;
the comparison relation admits finite joins and meets in its instantiations. -/
namespace ModalityInference

inductive CompareTy where
  | var (name : TypeVar)
  | unit
  | credit
  | prod (left right : CompareTy)
  | sum (left right : CompareTy)
  | fn (domain codomain : CompareTy)
  | modal (body : CompareTy) (mode : ModExpr)
  | join (left right : CompareTy)
  | meet (left right : CompareTy)
  deriving Repr, DecidableEq, BEq

namespace CompareTy
def ofTy : Ty → CompareTy
  | .var v => .var v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod (ofTy a) (ofTy b)
  | .sum a b => .sum (ofTy a) (ofTy b)
  | .fn a b => .fn (ofTy a) (ofTy b)
  | .modal a m => .modal (ofTy a) m

def subst (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr) : CompareTy → CompareTy
  | .var v => ts v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod (a.subst ts ms) (b.subst ts ms)
  | .sum a b => .sum (a.subst ts ms) (b.subst ts ms)
  | .fn a b => .fn (a.subst ts ms) (b.subst ts ms)
  | .modal a m => .modal (a.subst ts ms) (m.subst ms)
  | .join a b => .join (a.subst ts ms) (b.subst ts ms)
  | .meet a b => .meet (a.subst ts ms) (b.subst ts ms)

def wellFormedBounds : CompareTy → Bounds
  | .var _ | .unit | .credit => []
  | .prod a b | .sum a b | .fn a b | .join a b | .meet a b =>
    a.wellFormedBounds ++ b.wellFormedBounds
  | .modal a m => a.wellFormedBounds ++ [.defined m]

def DefinedUnder (a : CompareTy) (Δ : Bounds) : Prop :=
  ∀ σ, ModeModels Δ σ → ModeModels a.wellFormedBounds σ
end CompareTy

inductive CompareConstraint where
  | sub (left right : CompareTy)
  | mode (left right : ModExpr)
  | defined (expression : ModExpr)
  | equal (name : TypeVar) (type : CompareTy)
  | equiv (left right : CompareTy)
  deriving Repr, DecidableEq, BEq

abbrev CompareBounds := List CompareConstraint

def CompareConstraint.ofConstraint : Constraint → CompareConstraint
  | .sub a b => .sub (CompareTy.ofTy a) (CompareTy.ofTy b)
  | .mode a b => .mode a b
  | .defined a => .defined a
  | .equal v a => .equal v (CompareTy.ofTy a)
  | .equiv a b => .equiv (CompareTy.ofTy a) (CompareTy.ofTy b)

structure CompareSubstitution where
  types : List (Nat × CompareTy) := []
  modes : List (Nat × ModExpr) := []
  deriving Repr, DecidableEq

namespace CompareSubstitution
def type (s : CompareSubstitution) : TypeVar → CompareTy
  | .flex n => (s.types.lookup n).getD (.var (.flex n))
  | .rigid n => .var (.rigid n)

def mode (s : CompareSubstitution) : ModVar → ModExpr
  | .flex n => (s.modes.lookup n).getD (.var (.flex n))
  | .rigid n => .var (.rigid n)

def ty (s : CompareSubstitution) (t : Ty) : CompareTy :=
  (CompareTy.ofTy t).subst s.type s.mode

def constraint (s : CompareSubstitution) : Constraint → CompareConstraint
  | .sub a b => .sub (s.ty a) (s.ty b)
  | .mode a b => .mode (a.subst s.mode) (b.subst s.mode)
  | .defined a => .defined (a.subst s.mode)
  | .equal v t => match v with
    | .flex n => match s.types.lookup n with
      | none => .equal v (s.ty t)
      | some u => .equiv u (s.ty t)
    | .rigid _ => .equal v (s.ty t)
  | .equiv a b => .equiv (s.ty a) (s.ty b)

def bounds (s : CompareSubstitution) (cs : Bounds) : CompareBounds :=
  cs.map s.constraint

def ofSubstitution (s : Substitution) : CompareSubstitution :=
  { types := s.types.map fun (n, t) => (n, CompareTy.ofTy t), modes := s.modes }

/-- Comparison substitutions denote defined type and modality images under the
relevant bounds. Residual syntax is allowed when those bounds justify it. -/
structure WellFormedUnder (s : CompareSubstitution) (Δ : Bounds) : Prop where
  types : ∀ v, (s.type v).DefinedUnder Δ
  modes : ∀ v, Entails Δ (.defined (s.mode v))
end CompareSubstitution

/-- Exact domains keep all free identifiers and rigid target names fixed. -/
def CompareInstantiates (s : Scheme) (σ : CompareSubstitution) : Prop :=
  List.Perm (σ.types.map Prod.fst) s.typeParams ∧
    List.Perm (σ.modes.map Prod.fst) s.modParams

/-- The quantified domain condition, independently of image admissibility. -/
abbrev CompareInstanceDomain := CompareInstantiates

/-- A comparison instance replaces exactly the quantified names with defined
images and has a defined instantiated body under the ambient bounds. -/
structure CompareInstantiatesUnder (Δ : Bounds) (s : Scheme) (σ : CompareSubstitution) : Prop where
  domain : CompareInstanceDomain s σ
  images : σ.WellFormedUnder Δ
  body : (σ.ty s.body).DefinedUnder Δ

/-- Structural subtyping over finite comparison witnesses, with the same
modality theory and public assumptions as the original syntactic relation. -/
inductive CompareSubtype (Δ : Bounds) : CompareTy → CompareTy → Prop where
  | refl {a} : CompareSubtype Δ a a
  | trans {a b c} : CompareSubtype Δ a b → CompareSubtype Δ b c → CompareSubtype Δ a c
  | bound {a b} : Constraint.sub a b ∈ Δ → CompareSubtype Δ (CompareTy.ofTy a) (CompareTy.ofTy b)
  | identity {a} : CompareSubtype Δ (.modal a .epsilon) a
  | identityRev {a} : CompareSubtype Δ a (.modal a .epsilon)
  | compose {a m n} : CompareSubtype Δ (.modal (.modal a m) n) (.modal a (.compose m n))
  | composeRev {a m n} : CompareSubtype Δ (.modal a (.compose m n)) (.modal (.modal a m) n)
  | congr {a b m n} : CompareSubtype Δ a b → Submode Δ m n →
      CompareSubtype Δ (.modal a m) (.modal b n)
  | prod {a b c d m} : CompareSubtype Δ (.modal a m) (.modal c m) →
      CompareSubtype Δ (.modal b m) (.modal d m) →
      CompareSubtype Δ (.modal (.prod a b) m) (.modal (.prod c d) m)
  | sum {a b c d m} : CompareSubtype Δ (.modal a m) (.modal c m) →
      CompareSubtype Δ (.modal b m) (.modal d m) →
      CompareSubtype Δ (.modal (.sum a b) m) (.modal (.sum c d) m)
  | fn {a b c d m n} : CompareSubtype Δ c a → CompareSubtype Δ b d →
      Submode Δ m (.compose n .top) →
      CompareSubtype Δ (.modal (.fn a b) m) (.modal (.fn c d) n)
  | joinLeft {a b} : CompareSubtype Δ a (.join a b)
  | joinRight {a b} : CompareSubtype Δ b (.join a b)
  | joinLeast {a b c} : CompareSubtype Δ a c → CompareSubtype Δ b c →
      CompareSubtype Δ (.join a b) c
  | meetLeft {a b} : CompareSubtype Δ (.meet a b) a
  | meetRight {a b} : CompareSubtype Δ (.meet a b) b
  | meetGreatest {a b c} : CompareSubtype Δ a b → CompareSubtype Δ a c →
      CompareSubtype Δ a (.meet b c)

def CompareEntails (Δ : Bounds) : CompareConstraint → Prop
  | .sub a b => CompareSubtype Δ a b ∧ a.DefinedUnder Δ ∧ b.DefinedUnder Δ
  | .mode a b => Submode Δ a b
  | .defined a => ∀ σ, ModeModels Δ σ → a.WellFormed σ
  | .equal v t => CompareSubtype Δ (.var v) t ∧ CompareSubtype Δ t (.var v) ∧
      t.DefinedUnder Δ
  | .equiv a b => CompareSubtype Δ a b ∧ CompareSubtype Δ b a ∧
      a.DefinedUnder Δ ∧ b.DefinedUnder Δ

def CompareEntailsAll (Δ : Bounds) (cs : CompareBounds) : Prop :=
  ∀ c ∈ cs, CompareEntails Δ c

/-- Source bounds carry their definedness guards. The body comparison remains
a separate subtyping judgment, including for reflexive undefined annotations. -/
def CompareSubsumes (Δ : Bounds) (source target : Scheme) : Prop :=
  let (nt, nm) := source.subsumptionIndices Δ target
  let (assumptions, t) := target.instantiate nt nm true
  ∃ σ, CompareInstantiates source σ ∧
    CompareEntailsAll (Δ ++ assumptions.assumptions) (σ.bounds source.bounds) ∧
    CompareSubtype (Δ ++ assumptions.assumptions) (σ.ty source.body) (CompareTy.ofTy t)

end ModalityInference
