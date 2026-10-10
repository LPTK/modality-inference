import ModalityInference.Constraints

namespace ModalityInference

/-- Shallow expansion allocates variables only at immediate children. -/
inductive Shape : Ty → Ty → Prop where
  | unit {m} : Shape .unit (.modal .unit m)
  | credit {m} : Shape .credit (.modal .credit m)
  | prod {a b x y m} : Shape (.prod a b) (.modal (.prod (.var x) (.var y)) m)
  | sum {a b x y m} : Shape (.sum a b) (.modal (.sum (.var x) (.var y)) m)
  | fn {a b x y m} : Shape (.fn a b) (.modal (.fn (.var x) (.var y)) m)

/-- Abstract rewrite configurations omit scheduling and trace. Freshness and
substitution side conditions are explicit. No rule calls the executable step. -/
structure RewriteConfig where
  pending : Bounds
  bounds : Bounds := []
  substitution : Substitution := {}

def RewriteConfig.constraints (s : RewriteConfig) : Bounds := s.pending ++ s.bounds

def FreshFor (old fresh : Ty) (s : RewriteConfig) : Prop :=
  (∀ v ∈ fresh.typeVars, v ∉ old.typeVars ∪ s.constraints.typeVars) ∧
  (∀ v ∈ fresh.modVars, v ∉ old.modVars ∪ s.constraints.modVars)

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
  | expandLeft {v t shape m n} {s : RewriteConfig} : Shape t shape → FreshFor (.var (.flex v)) shape s →
      Rewrites {s with pending := .sub (.modal (.var (.flex v)) m) (.modal t n) :: s.pending}
        {s with pending := .equal (.flex v) shape :: .sub (.modal (.var (.flex v)) m) (.modal t n) :: s.pending}
  | expandRight {v t shape m n} {s : RewriteConfig} : Shape t shape → FreshFor (.var (.flex v)) shape s →
      Rewrites {s with pending := .sub (.modal t m) (.modal (.var (.flex v)) n) :: s.pending}
        {s with pending := .equal (.flex v) shape :: .sub (.modal t m) (.modal (.var (.flex v)) n) :: s.pending}
  | substitute {v : Nat} {t : Ty} {s : RewriteConfig} : .flex v ∉ t.typeVars →
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
  | .sub a b => ∃ x y m n, a = .modal (.var x) m ∧ b = .modal (.var y) n
  | .mode _ _ | .defined _ => True
  | _ => False

end ModalityInference
