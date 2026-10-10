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

end ModalityInference
