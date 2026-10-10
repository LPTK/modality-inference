import ModalityInference.Constraints

namespace ModalityInference

/-- Shallow expansion allocates distinct flexible variables at immediate children
and one flexible modality variable. `FreshFor` supplies ambient freshness. -/
inductive Shape : Ty → Ty → Prop where
  | unit {m} : Shape .unit (.modal .unit (.var (.flex m)))
  | credit {m} : Shape .credit (.modal .credit (.var (.flex m)))
  | prod {a b x y m} : x ≠ y →
      Shape (.prod a b) (.modal (.prod (.var (.flex x)) (.var (.flex y))) (.var (.flex m)))
  | sum {a b x y m} : x ≠ y →
      Shape (.sum a b) (.modal (.sum (.var (.flex x)) (.var (.flex y))) (.var (.flex m)))
  | fn {a b x y m} : x ≠ y →
      Shape (.fn a b) (.modal (.fn (.var (.flex x)) (.var (.flex y))) (.var (.flex m)))

/-- Abstract rewrite configurations omit scheduling and trace. Freshness and
substitution side conditions are explicit. No rule calls the executable step. -/
structure RewriteConfig where
  pending : Bounds
  bounds : Bounds := []
  substitution : Substitution := {}

def RewriteConfig.constraints (s : RewriteConfig) : Bounds := s.pending ++ s.bounds

def RewriteConfig.typeVars (s : RewriteConfig) : Finset TypeVar :=
  s.constraints.typeVars ∪ (s.substitution.types.flatMap
    (fun (n,t) => .flex n :: t.typeVariables)).toFinset
def RewriteConfig.modVars (s : RewriteConfig) : Finset ModVar :=
  s.constraints.modVars ∪ (s.substitution.types.flatMap (fun p => p.2.modeVariables) ++
    s.substitution.modes.flatMap (fun (n,m) => .flex n :: m.freeVariables)).toFinset

def FreshFor (old : Constraint) (fresh : Ty) (s : RewriteConfig) : Prop :=
  (∀ v ∈ fresh.typeVars, v ∉ old.typeVars ∪ s.typeVars) ∧
  (∀ v ∈ fresh.modVars, v ∉ old.modVars ∪ s.modVars)

inductive Rewrites : RewriteConfig → RewriteConfig → Prop where
  | equivalence {cs ds : Bounds} {s : RewriteConfig} :
      (∀ Δ, EntailsAll Δ cs ↔ EntailsAll Δ ds) →
      Rewrites {s with pending := cs ++ s.pending} {s with pending := ds ++ s.pending}
  | discharge {c : Constraint} {s : RewriteConfig} : Entails s.bounds c →
      Rewrites {s with pending := c :: s.pending} s
  | reduce {cs ds : Bounds} {s : RewriteConfig} : ConstraintReduction cs ds →
      Rewrites {s with pending := cs ++ s.pending} {s with pending := ds ++ s.pending}
  | record {c : Constraint} {s : RewriteConfig} : c ∉ s.bounds →
      Rewrites {s with pending := c :: s.pending} {s with bounds := c :: s.bounds}
  | hyp {c : Constraint} {s : RewriteConfig} : c ∈ s.bounds → Rewrites {s with pending := c :: s.pending} s
  | expandLeft {v t shape m n} {s : RewriteConfig} : Shape t shape →
      FreshFor (.sub (.modal (.var (.flex v)) m) (.modal t n)) shape s →
      Rewrites {s with pending := .sub (.modal (.var (.flex v)) m) (.modal t n) :: s.pending}
        {s with pending := .equal (.flex v) shape :: .sub (.modal (.var (.flex v)) m) (.modal t n) :: s.pending}
  | expandRight {v t shape m n} {s : RewriteConfig} : Shape t shape →
      FreshFor (.sub (.modal t m) (.modal (.var (.flex v)) n)) shape s →
      Rewrites {s with pending := .sub (.modal t m) (.modal (.var (.flex v)) n) :: s.pending}
        {s with pending := .equal (.flex v) shape :: .sub (.modal t m) (.modal (.var (.flex v)) n) :: s.pending}
  | substitute {v : Nat} {t : Ty} {s : RewriteConfig} : .flex v ∉ t.typeVars →
      v ∉ s.substitution.types.map Prod.fst →
      Rewrites {s with pending := .equal (.flex v) t :: s.pending}
        {pending := (Substitution.mk [(v,t)] []).bounds s.constraints
         bounds := []
         substitution := s.substitution.extendType v t}
  | propagate {a b c} {s : RewriteConfig} : Constraint.mode a b ∈ s.bounds → Constraint.mode b c ∈ s.bounds →
      Constraint.mode a c ∉ s.constraints →
      Rewrites s {s with pending := .mode a c :: s.pending}
  | permute {cs ds : Bounds} {s : RewriteConfig} : cs.Perm ds →
      Rewrites {s with pending := cs} {s with pending := ds}

inductive RewriteStar : RewriteConfig → RewriteConfig → Prop where
  | refl {s} : RewriteStar s s
  | step {s t u} : Rewrites s t → RewriteStar t u → RewriteStar s u

/-- Residual form includes well-formedness and projected modality obligations. -/
def Residual : Bounds → Prop := List.Forall fun c => match c with
  | .sub a b => ∃ x y m n, a.outer = (.var x, m) ∧ b.outer = (.var y, n)
  | .mode _ _ | .defined _ => True
  | _ => False

end ModalityInference
