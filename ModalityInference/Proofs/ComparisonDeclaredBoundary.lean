import ModalityInference.Proofs.ReductionEntailment

namespace ModalityInference.ComparisonDeclaredBoundary

/-- Top-level syntax, retaining fixed variable identity and ignoring outer actions. -/
inductive Root where
  | var (name : TypeVar)
  | unit | credit | prod | sum | fn
  deriving DecidableEq

def root : Ty → Root
  | .var v => .var v
  | .unit => .unit
  | .credit => .credit
  | .prod _ _ => .prod
  | .sum _ _ => .sum
  | .fn _ _ => .fn
  | .modal a _ => root a

/-- A path leaves its initial constructor through one literal declared endpoint.
The outside action is guarded; partial syntax inside the bound is preserved. -/
def Exit (Δ : Bounds) (s t : Ty) : Prop :=
  ∃ a b q, Constraint.sub a b ∈ Δ ∧ root s = root a ∧ root a ≠ root b ∧
    Entails Δ (.defined q) ∧ Subtype Δ s (.modal a q) ∧ Subtype Δ (.modal b q) t

private theorem defined_compose {Δ : Bounds} {m n : ModExpr}
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n)) :
    Entails Δ (.defined (.compose m n)) := by
  intro η hη
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hm η hη)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hn η hη)
  simp [ModExpr.WellFormed, ModExpr.eval, hx, hy]

theorem root_eq_or_exit {Δ : Bounds} {s t : Ty} (h : Subtype Δ s t) :
    root s = root t ∨ Exit Δ s t := by
  induction h with
  | refl => exact .inl rfl
  | trans hab hbc iha ihb =>
      rcases iha with he | ⟨a,b,q,hb,hs,hr,hq,hl,hu⟩
      · rcases ihb with he' | ⟨a,b,q,hb,hs,hr,hq,hl,hu⟩
        · exact .inl (he.trans he')
        · exact .inr ⟨a,b,q,hb,he.trans hs,hr,hq,.trans hab hl,hu⟩
      · exact .inr ⟨a,b,q,hb,hs,hr,hq,hl,.trans hu hbc⟩
  | bound hb =>
      rename_i a b
      by_cases he : root a = root b
      · exact .inl he
      · exact .inr ⟨_,_,.epsilon,hb,rfl,he,(fun _ _ => rfl),.identityRev,.identity⟩
  | identity | identityRev | compose | composeRev => exact .inl rfl
  | congr hab hmode ih =>
      rcases ih with he | ⟨a,b,q,hb,hs,hr,hq,hl,hu⟩
      · exact .inl he
      · refine .inr ⟨a,b,.compose q _,hb,hs,hr,
          defined_compose hq hmode.defined.1, ?_, ?_⟩
        · exact .trans (.congr hl (.refl hmode.defined.1)) .compose
        · exact .trans .composeRev (.congr hu hmode)
  | prod | sum | fn => exact .inl rfl

/-- Different top constructors force an actual declared-bound crossing. -/
theorem exit_of_root_ne {Δ : Bounds} {s t : Ty} (h : Subtype Δ s t)
    (hne : root s ≠ root t) : Exit Δ s t :=
  (root_eq_or_exit h).resolve_left hne

end ModalityInference.ComparisonDeclaredBoundary
