import ModalityInference.Core.Syntax

/-! Declarative judgments. None of these definitions refer to an executable solver.
The finite interpretation of modality formulas supplies their equational theory;
structural subtyping and typing remain inductively defined judgments.
-/

namespace ModalityInference

def ModeSatisfies (σ : ModVar → Mode) : Constraint → Prop
  | .mode a b => ModExpr.Below σ a b
  | .defined a => a.WellFormed σ
  | _ => True

def ModeModels (Δ : Bounds) (σ : ModVar → Mode) : Prop :=
  ∀ c ∈ Δ, ModeSatisfies σ c

inductive Submode (Δ : Bounds) : ModExpr → ModExpr → Prop where
  | valid {a b} : (∀ σ, ModeModels Δ σ → ModExpr.Below σ a b) → Submode Δ a b
  | lowerBound {a v} : Constraint.mode a (.var v) ∈ Δ → Submode Δ a (.var v)
  | upperBound {v b} : Constraint.mode (.var v) b ∈ Δ → Submode Δ (.var v) b
  | trans {a b c} : Submode Δ a b → Submode Δ b c → Submode Δ a c

inductive Subtype (Δ : Bounds) : Ty → Ty → Prop where
  | refl {a} : Subtype Δ a a
  | trans {a b c} : Subtype Δ a b → Subtype Δ b c → Subtype Δ a c
  | bound {a b} : Constraint.sub a b ∈ Δ → Subtype Δ a b
  | identity {a} : Subtype Δ (.modal a .epsilon) a
  | identityRev {a} : Subtype Δ a (.modal a .epsilon)
  | compose {a m n} : Subtype Δ (.modal (.modal a m) n) (.modal a (.compose m n))
  | composeRev {a m n} : Subtype Δ (.modal a (.compose m n)) (.modal (.modal a m) n)
  | congr {a b m n} : Subtype Δ a b → Submode Δ m n →
      Subtype Δ (.modal a m) (.modal b n)
  | prod {a b c d m} : Subtype Δ (.modal a m) (.modal c m) →
      Subtype Δ (.modal b m) (.modal d m) →
      Subtype Δ (.modal (.prod a b) m) (.modal (.prod c d) m)
  | sum {a b c d m} : Subtype Δ (.modal a m) (.modal c m) →
      Subtype Δ (.modal b m) (.modal d m) →
      Subtype Δ (.modal (.sum a b) m) (.modal (.sum c d) m)
  /-- Function modes compare only futures. The past is not a resource of the closure. -/
  | fn {a b c d m n} : Subtype Δ c a → Subtype Δ b d →
      Submode Δ m (.compose n .top) →
      Subtype Δ (.modal (.fn a b) m) (.modal (.fn c d) n)
  /-- Credits carry locality and uniqueness; the affinity of the old payload is irrelevant. -/
  | credit {m n} : Submode Δ (.compose m (.const Mode.many)) n →
      Subtype Δ (.modal .credit m) (.modal .credit n)

/-- Internal type constraints are meaningful only when every modality occurring
in them is defined under the ambient modality assumptions. -/
def TypeExpr.DefinedUnder (a : Ty) (Δ : Bounds) : Prop :=
  ∀ σ, ModeModels Δ σ → ModeModels a.wellFormedBounds σ

def Entails (Δ : Bounds) : Constraint → Prop
  | .sub a b => Subtype Δ a b ∧ a.DefinedUnder Δ ∧ b.DefinedUnder Δ
  | .mode a b => Submode Δ a b
  | .defined a => ∀ σ, ModeModels Δ σ → a.WellFormed σ
  | .equal v t => Subtype Δ (.var v) t ∧ Subtype Δ t (.var v) ∧ t.DefinedUnder Δ
  | .equiv a b => Subtype Δ a b ∧ Subtype Δ b a ∧ a.DefinedUnder Δ ∧ b.DefinedUnder Δ

def EntailsAll (Δ cs : Bounds) : Prop := ∀ c ∈ cs, Entails Δ c

/-- A constraint used as an assumption exposes equality directions and every
written modality's definedness, matching its ground satisfaction conditions. -/
def Constraint.assumptions : Constraint → Bounds
  | .sub a b => [.sub a b] ++ a.wellFormedBounds ++ b.wellFormedBounds
  | .equiv a b => [.sub a b, .sub b a] ++ a.wellFormedBounds ++ b.wellFormedBounds
  | .equal v t => [.sub (.var v) t, .sub t (.var v)] ++ t.wellFormedBounds
  | c => [c]

def Bounds.assumptions (cs : Bounds) : Bounds := cs.flatMap Constraint.assumptions

/-- Consistency includes type constraints, not only the modality fragment. -/
def BoundsSatisfiable (cs : Bounds) : Prop :=
  ∃ σ : Substitution, (σ.bounds cs).typeVariables = [] ∧
    (σ.bounds cs).modeVariables = [] ∧ EntailsAll [] (σ.bounds cs)

/-- Instantiations have exactly the quantified domain and never replace skolems. -/
def Instantiates (s : Scheme) (σ : Substitution) : Prop :=
  List.Perm (σ.types.map Prod.fst) s.typeParams ∧ List.Perm (σ.modes.map Prod.fst) s.modParams

def Scheme.freshTypeIndex (s : Scheme) : Nat :=
  (s.typeParams.map TypeVar.flex ++ s.body.typeVariables ++ s.bounds.typeVariables).foldl (fun n v => max n (v.index + 1)) 0
def Scheme.freshModeIndex (s : Scheme) : Nat :=
  (s.modParams.map ModVar.flex ++ s.body.modeVariables ++ s.bounds.modeVariables).foldl (fun n v => max n (v.index + 1)) 0

def Bounds.freshTypeIndex (Δ : Bounds) : Nat :=
  Δ.typeVariables.foldl (fun n v => max n (v.index + 1)) 0
def Bounds.freshModeIndex (Δ : Bounds) : Nat :=
  Δ.modeVariables.foldl (fun n v => max n (v.index + 1)) 0

/-- Skolems are fresh for ambient assumptions as well as both schemes. -/
def Scheme.subsumptionIndices (Δ : Bounds) (source target : Scheme) : Nat × Nat :=
  (max (max source.freshTypeIndex target.freshTypeIndex) Δ.freshTypeIndex,
   max (max source.freshModeIndex target.freshModeIndex) Δ.freshModeIndex)

/-- The target's universally quantified variables are rigid, including body-only
variables, and cannot be constrained by an existing ambient assumption.
Its bounds expose their equality directions and written definedness guards. -/
def Subsumes (Δ : Bounds) (source target : Scheme) : Prop :=
  let (nt, nm) := source.subsumptionIndices Δ target
  let (assumptions, t) := target.instantiate nt nm true
  ∃ σ, Instantiates source σ ∧ EntailsAll (Δ ++ assumptions.assumptions) (σ.bounds source.bounds) ∧
    Subtype (Δ ++ assumptions.assumptions) (σ.ty source.body) t

inductive ContextLe (Δ : Bounds) : Context → Context → Prop where
  | nil : ContextLe Δ [] []
  | drop {Γ Γ' s} : ContextLe Δ Γ Γ' → ContextLe Δ (s :: Γ) (none :: Γ')
  | keep {Γ Γ' s t} : ContextLe Δ Γ Γ' → Subsumes Δ s t →
      ContextLe Δ (some s :: Γ) (some t :: Γ')

inductive ContextJoin (Δ : Bounds) : Context → Context → Context → Prop where
  | nil : ContextJoin Δ [] [] []
  | unused {Γ Γ₁ Γ₂} : ContextJoin Δ Γ₁ Γ₂ Γ →
      ContextJoin Δ (none :: Γ₁) (none :: Γ₂) (none :: Γ)
  | left {Γ Γ₁ Γ₂ s} : ContextJoin Δ Γ₁ Γ₂ Γ →
      ContextJoin Δ (some s :: Γ₁) (none :: Γ₂) (some s :: Γ)
  | right {Γ Γ₁ Γ₂ s} : ContextJoin Δ Γ₁ Γ₂ Γ →
      ContextJoin Δ (none :: Γ₁) (some s :: Γ₂) (some s :: Γ)
  | shared {Γ Γ₁ Γ₂ s} : ContextJoin Δ Γ₁ Γ₂ Γ →
      s.FreshForBounds Δ →
      Subtype (Δ ++ s.bounds) (.modal s.body (.const Mode.aliased)) s.body →
      ContextJoin Δ (some s :: Γ₁) (some s :: Γ₂)
        (some (s.modal (.const Mode.many)) :: Γ)

inductive Lock (Δ : Bounds) (m : ModExpr) : Context → Context → Prop where
  | nil : Lock Δ m [] []
  | unused {Γ Γ'} : Lock Δ m Γ Γ' → Lock Δ m (none :: Γ) (none :: Γ')
  | keep {Γ Γ' s} : Lock Δ m Γ Γ' →
      s.FreshForBounds Δ → s.FreshForMode m →
      Subtype (Δ ++ s.bounds) s.body (.modal s.body (.future m)) →
      Lock Δ m (some s :: Γ) (some (s.modal (.capture m)) :: Γ')
  | unavailable {Γ Γ' s} : Lock Δ m Γ Γ' →
      (¬ Subtype (Δ ++ s.bounds) s.body (.modal s.body (.future m))) →
      Lock Δ m (some s :: Γ) (none :: Γ')

inductive Typing : Bounds → Context → AnnotatedTerm → Ty → Prop where
  | var {Δ Γ i s σ} : Γ[i]? = some (some s) → Instantiates s σ →
      EntailsAll Δ (σ.bounds s.bounds) → EntailsAll Δ (σ.ty s.body).wellFormedBounds →
      Typing Δ Γ (.var i) (σ.ty s.body)
  | unit {Δ Γ m} : Entails Δ (.defined m) → Typing Δ Γ .unit (.modal .unit m)
  | subs {Δ Γ Γ' t a b} : Typing Δ Γ t a → ContextLe Δ Γ' Γ → Subtype Δ a b →
      Typing Δ Γ' t b
  | lam {Δ Γ captured t a b m} : EntailsAll Δ a.wellFormedBounds →
      Entails Δ (.defined m) → Lock Δ m Γ captured →
      Typing Δ (some (Scheme.mono a) :: captured) t b →
      Typing Δ Γ (.lam (captured.restrict (t.freeVars 1)) t) (.modal (.fn a b) m)
  | app {Δ Γ Γ₁ Γ₂ f x a b} : ContextJoin Δ Γ₁ Γ₂ Γ →
      Typing Δ Γ₁ f (.fn a b) → Typing Δ Γ₂ x a → Typing Δ Γ (.app f x) b
  | pair {Δ Γ Γ₁ Γ₂ a b t u m} : ContextJoin Δ Γ₁ Γ₂ Γ →
      Typing Δ Γ₁ t (.modal a m) → Typing Δ Γ₂ u (.modal b m) →
      Typing Δ Γ (.pair t u) (.modal (.prod a b) m)
  | stackPair {Δ Γ Γ₁ Γ₂ a b t u m n} : ContextJoin Δ Γ₁ Γ₂ Γ →
      Typing Δ Γ₁ t (.modal a m) → Typing Δ Γ₂ u (.modal b m) →
      Submode Δ m n → Submode Δ (.const Mode.localLower) n →
      Typing Δ Γ (.stackPair t u) (.modal (.prod a b) n)
  | inl {Δ Γ a b t m} : EntailsAll Δ b.wellFormedBounds →
      Typing Δ Γ t (.modal a m) →
      Typing Δ Γ (.inl t) (.modal (.sum a b) m)
  | inr {Δ Γ a b t m} : EntailsAll Δ a.wellFormedBounds →
      Typing Δ Γ t (.modal b m) →
      Typing Δ Γ (.inr t) (.modal (.sum a b) m)
  | case {Δ Γ Γ₁ Γ₂ a b c t u v m} : ContextJoin Δ Γ₁ Γ₂ Γ →
      Typing Δ Γ₁ t (.modal (.sum a b) m) →
      Typing Δ (some (Scheme.mono (.modal a m)) :: Γ₂) u c →
      Typing Δ (some (Scheme.mono (.modal b m)) :: Γ₂) v c →
      Typing Δ Γ (.case t u v) c
  | split {Δ Γ Γ₁ Γ₂ a b c t u m} : ContextJoin Δ Γ₁ Γ₂ Γ →
      Typing Δ Γ₁ t (.modal (.prod a b) m) →
      Typing Δ (some (Scheme.mono (.modal .credit m)) ::
        some (Scheme.mono (.modal a m)) :: some (Scheme.mono (.modal b m)) :: Γ₂) u c →
      Typing Δ Γ (.split t u) c
  | reuse {Δ Γ Γ₁ Γ₂ Γ₃ Γ₂₃ t u v a b m k} : ContextJoin Δ Γ₂ Γ₃ Γ₂₃ →
      ContextJoin Δ Γ₁ Γ₂₃ Γ → Typing Δ Γ₁ t (.modal .credit k) →
      Typing Δ Γ₂ u (.modal a m) → Typing Δ Γ₃ v (.modal b m) →
      Submode Δ k (.const Mode.uniqueOnly) →
      Submode Δ (.compose k (.const Mode.many)) m →
      Typing Δ Γ (.reuse t u v) (.modal (.prod a b) m)
  | region {Δ Γ t a} : Typing Δ Γ t (.modal a (.const Mode.global)) →
      Typing Δ Γ (.region t) a
  /-- `rhs` is closed in term variables and is evaluated in the empty environment. -/
  | defn {Δ Γ rhs body a b rhsBounds} : Typing rhsBounds [] rhs a →
      BoundsSatisfiable rhsBounds →
      Typing Δ (some (Scheme.generalize rhsBounds a) :: Γ) body b →
      Typing Δ Γ (.defn rhs body) b

/-- Unannotated typing existentially supplies the proof-only capture metadata. -/
def RawTyping (Δ : Bounds) (Γ : Context) (t : RawTerm) (a : Ty) : Prop :=
  ∃ elaborated, elaborated.erase = t ∧ Typing Δ Γ elaborated a

end ModalityInference
