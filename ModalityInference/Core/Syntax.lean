import ModalityInference.Core.Mode

namespace ModalityInference

/-- The type grammar is parametric in the language of modality annotations. -/
inductive TypeExpr (M : Type) where
  | var (name : TypeVar)
  | unit
  | credit
  | prod (left right : TypeExpr M)
  | sum (left right : TypeExpr M)
  | fn (domain codomain : TypeExpr M)
  | modal (body : TypeExpr M) (mode : M)
  deriving Repr, DecidableEq, BEq

abbrev Ty := TypeExpr ModExpr
abbrev SourceTy := TypeExpr Modality

def TypeExpr.map (f : M → N) : TypeExpr M → TypeExpr N
  | .var v => .var v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod (a.map f) (b.map f)
  | .sum a b => .sum (a.map f) (b.map f)
  | .fn a b => .fn (a.map f) (b.map f)
  | .modal a m => .modal (a.map f) (f m)

inductive PolarTy : Polarity → Type where
  | var : TypeVar → PolarTy p
  | unit : PolarTy p
  | credit : PolarTy p
  | prod : PolarTy p → PolarTy p → PolarTy p
  | sum : PolarTy p → PolarTy p → PolarTy p
  | fn : PolarTy p.flip → PolarTy p → PolarTy p
  | modal : PolarTy p → PolarMod p → PolarTy p

def PolarTy.toTy : PolarTy p → Ty
  | .var v => .var v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod a.toTy b.toTy
  | .sum a b => .sum a.toTy b.toTy
  | .fn a b => .fn a.toTy b.toTy
  | .modal a m => .modal a.toTy m.toExpr

namespace TypeExpr
def typeVariables : Ty → List TypeVar
  | .var v => [v]
  | .unit | .credit => []
  | .prod a b | .sum a b | .fn a b => (a.typeVariables ++ b.typeVariables).dedup
  | .modal a _ => a.typeVariables
def modeVariables : Ty → List ModVar
  | .var _ | .unit | .credit => []
  | .prod a b | .sum a b | .fn a b => (a.modeVariables ++ b.modeVariables).dedup
  | .modal a m => (a.modeVariables ++ m.freeVariables).dedup
def typeVars : Ty → Finset TypeVar
  | .var v => {v}
  | .unit | .credit => ∅
  | .prod a b | .sum a b | .fn a b => a.typeVars ∪ b.typeVars
  | .modal a _ => a.typeVars
def modVars : Ty → Finset ModVar
  | .var _ | .unit | .credit => ∅
  | .prod a b | .sum a b | .fn a b => a.modVars ∪ b.modVars
  | .modal a m => a.modVars ∪ m.vars
def subst (ts : TypeVar → Ty) (ms : ModVar → ModExpr) : Ty → Ty
  | .var v => ts v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod (a.subst ts ms) (b.subst ts ms)
  | .sum a b => .sum (a.subst ts ms) (b.subst ts ms)
  | .fn a b => .fn (a.subst ts ms) (b.subst ts ms)
  | .modal a m => .modal (a.subst ts ms) (m.subst ms)
def outer : Ty → Ty × ModExpr
  | .modal a m => let (t, n) := a.outer; (t, .compose n m)
  | a => (a, .epsilon)
def size : Ty → Nat
  | .var _ | .unit | .credit => 1
  | .prod a b | .sum a b | .fn a b => a.size + b.size + 1
  | .modal a _ => a.size + 1
end TypeExpr

/-- A first-class constraint includes residual definedness, not just inequalities. -/
inductive Constraint where
  | sub (left right : Ty)
  | mode (left right : ModExpr)
  | defined (expression : ModExpr)
  | equal (name : TypeVar) (type : Ty)
  | equiv (left right : Ty)
  deriving Repr, DecidableEq, BEq

namespace Constraint
def typeVariables : Constraint → List TypeVar
  | .sub a b | .equiv a b => (a.typeVariables ++ b.typeVariables).dedup
  | .mode _ _ | .defined _ => []
  | .equal a b => (a :: b.typeVariables).dedup
def modeVariables : Constraint → List ModVar
  | .sub a b | .equiv a b => (a.modeVariables ++ b.modeVariables).dedup
  | .mode a b => (a.freeVariables ++ b.freeVariables).dedup
  | .defined a => a.freeVariables
  | .equal _ a => a.modeVariables
def typeVars : Constraint → Finset TypeVar
  | .sub a b | .equiv a b => a.typeVars ∪ b.typeVars
  | .mode _ _ | .defined _ => ∅
  | .equal a b => insert a b.typeVars
def modVars : Constraint → Finset ModVar
  | .sub a b | .equiv a b => a.modVars ∪ b.modVars
  | .mode a b => a.vars ∪ b.vars
  | .defined a => a.vars
  | .equal _ a => a.modVars
def subst (ts : TypeVar → Ty) (ms : ModVar → ModExpr) : Constraint → Constraint
  | .sub a b => .sub (a.subst ts ms) (b.subst ts ms)
  | .mode a b => .mode (a.subst ms) (b.subst ms)
  | .defined a => .defined (a.subst ms)
  | .equal a b => .equiv (ts a) (b.subst ts ms)
  | .equiv a b => .equiv (a.subst ts ms) (b.subst ts ms)
end Constraint

abbrev Bounds := List Constraint

/-- Definedness obligations for every modality in a type argument. -/
def TypeExpr.wellFormedBounds : Ty → Bounds
  | .var _ | .unit | .credit => []
  | .prod a b | .sum a b | .fn a b => a.wellFormedBounds ++ b.wellFormedBounds
  | .modal a m => a.wellFormedBounds ++ [.defined m]

def instantiationGuards (types : List Ty) (modes : List ModExpr) : Bounds :=
  types.flatMap TypeExpr.wellFormedBounds ++ modes.map Constraint.defined

def Bounds.typeVars (cs : Bounds) : Finset TypeVar := cs.foldl (· ∪ ·.typeVars) ∅
def Bounds.modVars (cs : Bounds) : Finset ModVar := cs.foldl (· ∪ ·.modVars) ∅
def Bounds.typeVariables (cs : Bounds) : List TypeVar := (cs.flatMap Constraint.typeVariables).dedup
def Bounds.modeVariables (cs : Bounds) : List ModVar := (cs.flatMap Constraint.modeVariables).dedup

structure Scheme where
  typeParams : List Nat := []
  modParams : List Nat := []
  bounds : Bounds := []
  body : Ty
  deriving Repr, DecidableEq, BEq

abbrev Context := List (Option Scheme)

def Context.restrict (Γ : Context) (used : Finset Nat) : Context :=
  Γ.mapIdx fun i s => if i ∈ used then s else none

structure Substitution where
  types : List (Nat × Ty) := []
  modes : List (Nat × ModExpr) := []
  deriving Repr, DecidableEq

namespace Substitution
def type (s : Substitution) : TypeVar → Ty
  | .flex n => (s.types.lookup n).getD (.var (.flex n))
  | .rigid n => .var (.rigid n)
def mode (s : Substitution) : ModVar → ModExpr
  | .flex n => (s.modes.lookup n).getD (.var (.flex n))
  | .rigid n => .var (.rigid n)
def ty (s : Substitution) (t : Ty) : Ty := t.subst s.type s.mode
def constraint (s : Substitution) : Constraint → Constraint
  | .equal v t => match v with
    | .flex n => match s.types.lookup n with
      | none => .equal v (s.ty t)
      | some u => .equiv u (s.ty t)
    | .rigid _ => .equal v (s.ty t)
  | c => c.subst s.type s.mode
def bounds (s : Substitution) (cs : Bounds) : Bounds := cs.map s.constraint
/-- Composition is `new ∘ old`; images in the old substitution are updated too. -/
def extendType (s : Substitution) (n : Nat) (t : Ty) : Substitution :=
  let one : Substitution := { types := [(n, t)] }
  { s with types := (n, t) :: ((s.types.filter (fun x => x.1 != n)).map (fun (v, u) => (v, one.ty u))) }
def compose (new old : Substitution) : Substitution :=
  { types := old.types.map (fun (v, t) => (v, new.ty t)) ++
      new.types.filter (fun (v, _) => !(old.types.map Prod.fst).contains v)
    modes := old.modes.map (fun (v, m) => (v, m.subst new.mode)) ++
      new.modes.filter (fun (v, _) => !(old.modes.map Prod.fst).contains v) }
end Substitution

def TypeVar.index : TypeVar → Nat
  | .flex n | .rigid n => n
def ModVar.index : ModVar → Nat
  | .flex n | .rigid n => n

namespace Scheme
def mono (t : Ty) : Scheme := ⟨[], [], [], t⟩
def freeTypes (s : Scheme) : Finset TypeVar :=
  (s.body.typeVars ∪ s.bounds.typeVars).filter fun v =>
    (match v with | .flex n => !s.typeParams.contains n | .rigid _ => true : Bool) = true
def freeModes (s : Scheme) : Finset ModVar :=
  (s.body.modVars ∪ s.bounds.modVars).filter fun v =>
    (match v with | .flex n => !s.modParams.contains n | .rigid _ => true : Bool) = true
def generalize (cs : Bounds) (t : Ty) : Scheme :=
  { typeParams := (t.typeVariables ++ cs.typeVariables).dedup.filterMap fun v =>
      match v with | .flex n => some n | .rigid _ => none
    modParams := (t.modeVariables ++ cs.modeVariables).dedup.filterMap fun v =>
      match v with | .flex n => some n | .rigid _ => none
    bounds := cs, body := t }
def freshSubstitution (s : Scheme) (nextT nextM : Nat) (rigid : Bool := false) : Substitution :=
  { types := s.typeParams.zipIdx |>.map fun (v, i) =>
      (v, .var (if rigid then .rigid (nextT + i) else .flex (nextT + i)))
    modes := s.modParams.zipIdx |>.map fun (v, i) =>
      (v, .var (if rigid then .rigid (nextM + i) else .flex (nextM + i))) }
def instantiate (s : Scheme) (nextT nextM : Nat) (rigid : Bool := false) : Bounds × Ty :=
  let σ := s.freshSubstitution nextT nextM rigid
  (σ.bounds s.bounds, σ.ty s.body)
/-- Starting indices for alpha-renaming, above the scheme and substitution. -/
def fresheningIndices (s : Scheme) (σ : Substitution) : Nat × Nat :=
  let tv := s.typeParams.map TypeVar.flex ++ s.body.typeVariables ++ s.bounds.typeVariables ++
    σ.types.flatMap (fun p => .flex p.1 :: p.2.typeVariables)
  let mv := s.modParams.map ModVar.flex ++ s.body.modeVariables ++ s.bounds.modeVariables ++
    σ.types.flatMap (fun p => p.2.modeVariables) ++
    σ.modes.flatMap (fun p => .flex p.1 :: p.2.freeVariables)
  let nt := tv.foldl (fun n v => max n (v.index + 1)) 0
  let nm := mv.foldl (fun n v => max n (v.index + 1)) 0
  (nt, nm)
/-- The binder renaming used by `subst`, exposed for transporting value metadata. -/
def binderRenaming (s : Scheme) (σ : Substitution) : Substitution :=
  let (nt, nm) := s.fresheningIndices σ
  s.freshSubstitution nt nm
/-- Action on the body of a scheme, including its renamed quantified variables. -/
def substitutionAction (s : Scheme) (σ : Substitution) : Substitution :=
  σ.compose (s.binderRenaming σ)
/-- Rename binders above both the scheme and substitution before applying it. -/
def subst (s : Scheme) (σ : Substitution) : Scheme :=
  let (nt, nm) := s.fresheningIndices σ
  let (cs, t) := s.instantiate nt nm
  { typeParams := (List.range s.typeParams.length).map (nt + ·)
    modParams := (List.range s.modParams.length).map (nm + ·)
    bounds := σ.bounds cs, body := σ.ty t }
def modal (s : Scheme) (m : ModExpr) : Scheme := { s with body := .modal s.body m }
end Scheme

inductive ContextEntry where
  | binding (scheme : Option Scheme)
  | lock (mode : ModExpr)
  deriving Repr, DecidableEq

abbrev AlgorithmicContext := List ContextEntry
abbrev Capture := Context

/-- Binders are de Bruijn indices. `split` binds credit, first, second at 0,1,2. -/
inductive Term (Annotation : Type) where
  | var (index : Nat)
  | unit
  | lam (annotation : Annotation) (body : Term Annotation)
  | app (function argument : Term Annotation)
  | pair (first second : Term Annotation)
  | stackPair (first second : Term Annotation)
  | inl (value : Term Annotation)
  | inr (value : Term Annotation)
  | defn (rhs body : Term Annotation)
  | split (scrutinee body : Term Annotation)
  | case (scrutinee left right : Term Annotation)
  | reuse (credit first second : Term Annotation)
  | region (body : Term Annotation)
  deriving Repr, DecidableEq

abbrev RawTerm := Term Unit
abbrev AnnotatedTerm := Term Capture

namespace Term
def mapAnnotation (f : A → B) : Term A → Term B
  | .var i => .var i
  | .unit => .unit
  | .lam a t => .lam (f a) (t.mapAnnotation f)
  | .app a b => .app (a.mapAnnotation f) (b.mapAnnotation f)
  | .pair a b => .pair (a.mapAnnotation f) (b.mapAnnotation f)
  | .stackPair a b => .stackPair (a.mapAnnotation f) (b.mapAnnotation f)
  | .inl a => .inl (a.mapAnnotation f)
  | .inr a => .inr (a.mapAnnotation f)
  | .defn a b => .defn (a.mapAnnotation f) (b.mapAnnotation f)
  | .split a b => .split (a.mapAnnotation f) (b.mapAnnotation f)
  | .case a b c => .case (a.mapAnnotation f) (b.mapAnnotation f) (c.mapAnnotation f)
  | .reuse a b c => .reuse (a.mapAnnotation f) (b.mapAnnotation f) (c.mapAnnotation f)
  | .region a => .region (a.mapAnnotation f)
def erase (t : Term A) : RawTerm := t.mapAnnotation fun _ => ()
def freeVars (depth : Nat := 0) : Term A → Finset Nat
  | .var i => if i < depth then ∅ else {i - depth}
  | .unit => ∅
  | .lam _ t => t.freeVars (depth + 1)
  | .app a b | .pair a b | .stackPair a b => a.freeVars depth ∪ b.freeVars depth
  | .inl a | .inr a | .region a => a.freeVars depth
  | .defn a b => a.freeVars depth ∪ b.freeVars (depth + 1)
  | .split a b => a.freeVars depth ∪ b.freeVars (depth + 3)
  | .case a b c => a.freeVars depth ∪ b.freeVars (depth + 1) ∪ c.freeVars (depth + 1)
  | .reuse a b c => a.freeVars depth ∪ b.freeVars depth ∪ c.freeVars depth
def Scoped (n : Nat) (t : Term A) : Prop := ∀ i ∈ t.freeVars, i < n
def liftRenaming (k : Nat) (ρ : Nat → Nat) (i : Nat) : Nat :=
  if i < k then i else ρ (i - k) + k
def rename (ρ : Nat → Nat) : Term A → Term A
  | .var i => .var (ρ i)
  | .unit => .unit
  | .lam a t => .lam a (t.rename (liftRenaming 1 ρ))
  | .app a b => .app (a.rename ρ) (b.rename ρ)
  | .pair a b => .pair (a.rename ρ) (b.rename ρ)
  | .stackPair a b => .stackPair (a.rename ρ) (b.rename ρ)
  | .inl a => .inl (a.rename ρ)
  | .inr a => .inr (a.rename ρ)
  | .defn a b => .defn (a.rename ρ) (b.rename (liftRenaming 1 ρ))
  | .split a b => .split (a.rename ρ) (b.rename (liftRenaming 3 ρ))
  | .case a b c => .case (a.rename ρ) (b.rename (liftRenaming 1 ρ)) (c.rename (liftRenaming 1 ρ))
  | .reuse a b c => .reuse (a.rename ρ) (b.rename ρ) (c.rename ρ)
  | .region a => .region (a.rename ρ)
def liftSubstitution (k : Nat) (σ : Nat → Term A) (i : Nat) : Term A :=
  if i < k then .var i else (σ (i - k)).rename (· + k)
def subst (σ : Nat → Term A) : Term A → Term A
  | .var i => σ i
  | .unit => .unit
  | .lam a t => .lam a (t.subst (liftSubstitution 1 σ))
  | .app a b => .app (a.subst σ) (b.subst σ)
  | .pair a b => .pair (a.subst σ) (b.subst σ)
  | .stackPair a b => .stackPair (a.subst σ) (b.subst σ)
  | .inl a => .inl (a.subst σ)
  | .inr a => .inr (a.subst σ)
  | .defn a b => .defn (a.subst σ) (b.subst (liftSubstitution 1 σ))
  | .split a b => .split (a.subst σ) (b.subst (liftSubstitution 3 σ))
  | .case a b c => .case (a.subst σ) (b.subst (liftSubstitution 1 σ)) (c.subst (liftSubstitution 1 σ))
  | .reuse a b c => .reuse (a.subst σ) (b.subst σ) (c.subst σ)
  | .region a => .region (a.subst σ)
end Term

end ModalityInference
