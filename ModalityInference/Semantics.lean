import ModalityInference.Declarative
import ModalityInference.Evaluation

/-! A concrete logical relation with a separate live world and allocation supplies.
Ownership is indexed by the complete type, so a unique container does not recover
ownership of an aliased field. Closure metadata records capture schemes, not just
outer modes. `References` independently tracks aliased as well as owned locations.
-/

namespace ModalityInference

inductive GroundTy where
  | unit (mode : Mode)
  | credit (mode : Mode)
  | prod (first second : GroundTy) (mode : Mode)
  | sum (left right : GroundTy) (mode : Mode)
  | fn (domain codomain : GroundTy) (mode : Mode)
  deriving Repr, DecidableEq

namespace GroundTy
def mode : GroundTy → Mode
  | .unit m | .credit m | .prod _ _ m | .sum _ _ m | .fn _ _ m => m
def modal (t : GroundTy) (n : Mode) : GroundTy := match t with
  | .unit m => .unit (m.compose n)
  | .credit m => .credit (m.compose n)
  | .prod a b m => .prod a b (m.compose n)
  | .sum a b m => .sum a b (m.compose n)
  | .fn a b m => .fn a b (m.compose n)
def reify : GroundTy → Ty
  | .unit m => .modal .unit (.const m)
  | .credit m => .modal .credit (.const m)
  | .prod a b m => .modal (.prod a.reify b.reify) (.const m)
  | .sum a b m => .modal (.sum a.reify b.reify) (.const m)
  | .fn a b m => .modal (.fn a.reify b.reify) (.const m)
end GroundTy

structure GroundAssignment where
  types : TypeVar → GroundTy
  modes : ModVar → Mode

def TypeExpr.realize (ρ : GroundAssignment) : Ty → Option GroundTy
  | .var v => some (ρ.types v)
  | .unit => some (.unit Mode.identity)
  | .credit => some (.credit Mode.identity)
  | .prod a b => return .prod (← a.realize ρ) (← b.realize ρ) Mode.identity
  | .sum a b => return .sum (← a.realize ρ) (← b.realize ρ) Mode.identity
  | .fn a b => return .fn (← a.realize ρ) (← b.realize ρ) Mode.identity
  | .modal a m => return (← a.realize ρ).modal (← m.eval (some ∘ ρ.modes))

def GroundSatisfies (ρ : GroundAssignment) : Constraint → Prop
  | .sub a b => ∃ x y, a.realize ρ = some x ∧ b.realize ρ = some y ∧
      Subtype [] x.reify y.reify
  | .mode a b => ModExpr.Below ρ.modes a b
  | .defined a => a.WellFormed ρ.modes
  | .equal v t => ∃ y, t.realize ρ = some y ∧
      Subtype [] (ρ.types v).reify y.reify ∧ Subtype [] y.reify (ρ.types v).reify
  | .equiv a b => ∃ x y, a.realize ρ = some x ∧ b.realize ρ = some y ∧
      Subtype [] x.reify y.reify ∧ Subtype [] y.reify x.reify
def GroundModels (ρ : GroundAssignment) (cs : Bounds) : Prop :=
  ∀ c ∈ cs, GroundSatisfies ρ c

/-- Only quantified variables may change. Variables absent from the scheme's
body must also stay fixed: they can still occur in a value's capture metadata. -/
def GroundInstantiates (ambient : GroundAssignment) (s : Scheme) (ρ : GroundAssignment) : Prop :=
  (∀ v, v ∉ s.typeParams.map TypeVar.flex → ρ.types v = ambient.types v) ∧
  (∀ v, v ∉ s.modParams.map ModVar.flex → ρ.modes v = ambient.modes v) ∧ GroundModels ρ s.bounds

inductive Owns : GroundAssignment → Value → GroundTy → Location → Prop where
  | credit {ρ l m} : m.unique = true → Owns ρ (.credit l) (.credit m) l
  | pairCell {ρ l x y a b m} : m.unique = true → Owns ρ (.pair l x y) (.prod a b m) l
  | pairFirst {ρ l x y a b m k} : Owns ρ x (a.modal m) k →
      Owns ρ (.pair l x y) (.prod a b m) k
  | pairSecond {ρ l x y a b m k} : Owns ρ y (b.modal m) k →
      Owns ρ (.pair l x y) (.prod a b m) k
  | inl {ρ v a b m l} : Owns ρ v (a.modal m) l → Owns ρ (.inl v) (.sum a b m) l
  | inr {ρ v a b m l} : Owns ρ v (b.modal m) l → Owns ρ (.inr v) (.sum a b m) l
  | closure {ρ γ captured body a b m s v ρ' t l} {i : Nat} :
      captured[i]? = some (some s) → γ[i]? = some v → GroundInstantiates ρ s ρ' →
      s.body.realize ρ' = some t → Owns ρ' v t l →
      Owns ρ (.closure γ captured body) (.fn a b m) l

def Support (ρ : GroundAssignment) (v : Value) (t : GroundTy) : Set Location :=
  {l | Owns ρ v t l}
def Separated (ρ : GroundAssignment) (v : Value) (a : GroundTy)
    (w : Value) (b : GroundTy) : Prop :=
  ∀ l, ¬ (Owns ρ v a l ∧ Owns ρ w b l)
def BindingOwns (ρ : GroundAssignment) (v : Value) (s : Scheme) (l : Location) : Prop :=
  ∃ ρ' t, GroundInstantiates ρ s ρ' ∧ s.body.realize ρ' = some t ∧ Owns ρ' v t l
def EnvironmentOwns (ρ : GroundAssignment) (γ : Environment) (Γ : Context) (l : Location) : Prop :=
  ∃ i : Nat, ∃ s v, Γ[i]? = some (some s) ∧ γ[i]? = some v ∧ BindingOwns ρ v s l
def WellSeparated (ρ : GroundAssignment) (γ : Environment) (Γ : Context) : Prop :=
  ∀ (i j : Nat) s t v w l, i ≠ j → Γ[i]? = some (some s) → Γ[j]? = some (some t) →
    γ[i]? = some v → γ[j]? = some w → ¬ (BindingOwns ρ v s l ∧ BindingOwns ρ w t l)

def HeapLocation : Location → Prop
  | .heap _ => True
  | .stack _ _ => False

/-- Structural recursion is on the ground type. Function clauses quantify over
live calling worlds and fresh supplies, and use the independent big-step relation. -/
def ValueInterpretation (ρ : GroundAssignment) (w : World) (t : GroundTy)
    (ambient : Mode) (v : Value) : Prop :=
  let m := t.mode.compose ambient
  w.ValidValue v ∧ match t, v with
  | .unit _, .unit => True
  | .credit _, .credit l => m.isLocal = true ∨ HeapLocation l
  | .prod a b _, .pair l x y =>
      (m.isLocal = true ∨ HeapLocation l) ∧
      ValueInterpretation ρ w a m x ∧ ValueInterpretation ρ w b m y ∧
      Separated ρ (.credit l) (.credit m) x (a.modal m) ∧
      Separated ρ (.credit l) (.credit m) y (b.modal m) ∧
      Separated ρ x (a.modal m) y (b.modal m)
  | .sum a _ _, .inl x => ValueInterpretation ρ w a m x
  | .sum _ b _, .inr x => ValueInterpretation ρ w b m x
  | .fn a b _, .closure γ captured body =>
      (m.isLocal = false → ∀ l, EnvironmentReferences γ l → HeapLocation l) ∧
      (m.once = false → ∀ l, ¬EnvironmentOwns ρ γ captured l) ∧
      (∀ (w' : World) x, (∀ v ∈ γ, w'.ValidValue v) →
        ValueInterpretation ρ w' a Mode.identity x →
        (∀ l, ¬ (EnvironmentOwns ρ γ captured l ∧ Owns ρ x a l)) →
        ∀ supplies, w'.Compatible supplies (x :: γ) →
        ∃ result, Eval supplies (x :: γ) body result ∧
          ValueInterpretation ρ w' b Mode.identity result ∧
          ∀ l, Owns ρ result b l →
            EnvironmentOwns ρ γ captured l ∨ Owns ρ x a l ∨ supplies.FreshLocation l)
  | _, _ => False

def SchemeInterpretation (ρ : GroundAssignment) (w : World) (s : Scheme) (v : Value) : Prop :=
  ∀ ρ' t, GroundInstantiates ρ s ρ' → s.body.realize ρ' = some t →
    ValueInterpretation ρ' w t Mode.identity v

def EnvironmentInterpretation (ρ : GroundAssignment) (w : World)
    (Γ : Context) (γ : Environment) : Prop :=
  (∀ (i : Nat) s, Γ[i]? = some (some s) →
    ∃ v, γ[i]? = some v ∧ SchemeInterpretation ρ w s v) ∧ WellSeparated ρ γ Γ

def SemanticEvaluation (ρ : GroundAssignment) (w : World) (Γ : Context)
    (γ : Environment) (term : AnnotatedTerm) (type : GroundTy) : Prop :=
  ∀ supplies, w.Compatible supplies γ →
    ∃ value, Eval supplies γ term value ∧ ValueInterpretation ρ w type Mode.identity value ∧
      ∀ l, Owns ρ value type l → EnvironmentOwns ρ γ Γ l ∨ supplies.FreshLocation l

/-- Executable support for first-order test values. Closures use `Owns`, whose
scheme-union interpretation is deliberately not replaced by a guessed instance. -/
def firstOrderSupport : Nat → Value → GroundTy → Option (List Location)
  | 0, _, _ => none
  | fuel + 1, v, t => match v, t with
    | .unit, .unit _ => some []
    | .credit l, .credit m => some (if m.unique then [l] else [])
    | .pair l x y, .prod a b m => do
      let xs ← firstOrderSupport fuel x (a.modal m)
      let ys ← firstOrderSupport fuel y (b.modal m)
      return ((if m.unique then [l] else []) ++ xs ++ ys).dedup
    | .inl x, .sum a _ m => firstOrderSupport fuel x (a.modal m)
    | .inr x, .sum _ b m => firstOrderSupport fuel x (b.modal m)
    | _, _ => none

end ModalityInference
