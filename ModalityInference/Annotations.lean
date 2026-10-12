import ModalityInference.Evaluation

/-! Transport of proof annotations, including annotations inside captured values.
These operations preserve runtime structure; their metatheory is in `Proofs`.
-/
namespace ModalityInference

def AnnotatedTerm.substTypes (t : AnnotatedTerm) (σ : Substitution) : AnnotatedTerm :=
  t.mapAnnotation fun Γ => Γ.map (Option.map (fun s => s.subst σ))

def Value.mapAnnotation (f : Capture → Capture) : Value → Value
  | .unit => .unit
  | .credit l => .credit l
  | .pair l a b => .pair l (a.mapAnnotation f) (b.mapAnnotation f)
  | .inl a => .inl (a.mapAnnotation f)
  | .inr a => .inr (a.mapAnnotation f)
  | .closure γ Γ t => .closure (γ.map (Value.mapAnnotation f)) (f Γ) (t.mapAnnotation f)

def Value.substTypes (v : Value) (σ : Substitution) : Value :=
  v.mapAnnotation fun Γ => Γ.map (Option.map (fun s => s.subst σ))

/-- A captured polymorphic value follows the renaming of its own scheme. The
closure body and its capture schemes follow the surrounding substitution. -/
def Value.substCapturedTypes : Value → Substitution → Value
  | .unit, _ => .unit
  | .credit l, _ => .credit l
  | .pair l a b, σ => .pair l (a.substCapturedTypes σ) (b.substCapturedTypes σ)
  | .inl a, σ => .inl (a.substCapturedTypes σ)
  | .inr a, σ => .inr (a.substCapturedTypes σ)
  | .closure γ Γ t, σ =>
    .closure ((γ.map Value.substCapturedTypes).mapIdx fun i subst =>
      subst (match Γ[i]? with
        | some (some s) => s.substitutionAction σ
        | _ => σ))
      (Γ.map (Option.map (fun s => s.subst σ))) (t.substTypes σ)

/-- Keep quantified names attached to the value whose metadata they bind. -/
structure SchemeValue where
  scheme : Scheme
  value : Value
  deriving Repr

def SchemeValue.subst (p : SchemeValue) (σ : Substitution) : SchemeValue :=
  ⟨p.scheme.subst σ, p.value.substCapturedTypes (p.scheme.substitutionAction σ)⟩

end ModalityInference
