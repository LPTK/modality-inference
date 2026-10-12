import ModalityInference.Core.Syntax

namespace ModalityInference

structure Scope where
  types : Finset TypeVar := ∅
  modes : Finset ModVar := ∅

def ModExpr.Scoped (scope : Scope) (m : ModExpr) : Prop := m.vars ⊆ scope.modes
def TypeExpr.Scoped (scope : Scope) (t : Ty) : Prop :=
  t.typeVars ⊆ scope.types ∧ t.modVars ⊆ scope.modes
def Constraint.Scoped (scope : Scope) (c : Constraint) : Prop :=
  c.typeVars ⊆ scope.types ∧ c.modVars ⊆ scope.modes
def Scheme.Scoped (scope : Scope) (s : Scheme) : Prop :=
  s.typeParams.Nodup ∧ s.modParams.Nodup ∧
    s.freeTypes ⊆ scope.types ∧ s.freeModes ⊆ scope.modes

def Context.Scoped (scope : Scope) (Γ : Context) : Prop :=
  ∀ s, some s ∈ Γ → s.Scoped scope

def TypeExpr.rename (types : TypeVar → TypeVar) (modes : ModVar → ModVar) (t : Ty) : Ty :=
  t.subst (TypeExpr.var ∘ types) (ModExpr.var ∘ modes)
def Substitution.Scoped (source target : Scope) (σ : Substitution) : Prop :=
  (∀ v ∈ source.types, (σ.type v).Scoped target) ∧
  (∀ v ∈ source.modes, (σ.mode v).Scoped target)
def Substitution.Acyclic (σ : Substitution) : Prop :=
  (σ.types.map Prod.fst).Nodup ∧ (σ.modes.map Prod.fst).Nodup ∧
  (∀ n t, (n,t) ∈ σ.types → ∀ k ∈ σ.types.map Prod.fst, .flex k ∉ t.typeVars) ∧
  (∀ n m, (n,m) ∈ σ.modes → ∀ k ∈ σ.modes.map Prod.fst, .flex k ∉ m.vars)

/-- Validate the finite substitution invariant at an executable solver entry.
Stored images are simultaneous and contain no identifier in their own domain. -/
def Substitution.checkAcyclic (σ : Substitution) : Bool :=
  decide ((σ.types.map Prod.fst).Nodup ∧ (σ.modes.map Prod.fst).Nodup) &&
    σ.types.all (fun p => (σ.types.map Prod.fst).all (fun k => decide (TypeVar.flex k ∉ p.2.typeVars))) &&
    σ.modes.all (fun p => (σ.modes.map Prod.fst).all (fun k => decide (ModVar.flex k ∉ p.2.vars)))

def Context.subst (Γ : Context) (σ : Substitution) : Context :=
  Γ.map (Option.map (fun s => s.subst σ))

def Term.WellScoped (scope : Scope) : Nat → AnnotatedTerm → Prop
  | n, .var i => i < n
  | _, .unit => True
  | n, .lam Γ t => Γ.length = n ∧ Γ.Scoped scope ∧ t.WellScoped scope (n+1)
  | n, .app a b | n, .pair a b | n, .stackPair a b =>
      a.WellScoped scope n ∧ b.WellScoped scope n
  | n, .inl t | n, .inr t | n, .region t => t.WellScoped scope n
  | n, .defn rhs body => rhs.WellScoped scope 0 ∧ body.WellScoped scope (n+1)
  | n, .split t body => t.WellScoped scope n ∧ body.WellScoped scope (n+3)
  | n, .case t l r => t.WellScoped scope n ∧ l.WellScoped scope (n+1) ∧ r.WellScoped scope (n+1)
  | n, .reuse k a b => k.WellScoped scope n ∧ a.WellScoped scope n ∧ b.WellScoped scope n

end ModalityInference
