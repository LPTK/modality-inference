import ModalityInference.Declarative

/-! Direct declarative typing for terms without capture annotations.
Closure capture is determined by the context lock and the lambda body; it is not
part of the source syntax. The annotated judgment provides proof witnesses for
resource reasoning, and is equivalent to this judgment after erasure.
-/

namespace ModalityInference

/-- Source typing uses the paper's lambda syntax, its lock and context
premises, and scheme instances with defined images and bodies. -/
inductive SourceTyping : Bounds → Context → RawTerm → Ty → Prop where
  | var {Δ Γ i s σ} : Γ[i]? = some (some s) → InstantiatesUnder Δ s σ →
      EntailsAll Δ (σ.bounds s.bounds) →
      SourceTyping Δ Γ (.var i) (σ.ty s.body)
  | unit {Δ Γ m} : Entails Δ (.defined m) → SourceTyping Δ Γ .unit (.modal .unit m)
  | subs {Δ Γ Γ' t a b} : SourceTyping Δ Γ t a → ContextLe Δ Γ' Γ → Subtype Δ a b →
      SourceTyping Δ Γ' t b
  | lam {Δ Γ captured t a b m} : EntailsAll Δ a.wellFormedBounds →
      Entails Δ (.defined m) → Lock Δ m Γ captured →
      SourceTyping Δ (some (Scheme.mono a) :: captured) t b →
      SourceTyping Δ Γ (.lam () t) (.modal (.fn a b) m)
  | app {Δ Γ Γ₁ Γ₂ f x a b} : ContextJoin Δ Γ₁ Γ₂ Γ →
      SourceTyping Δ Γ₁ f (.fn a b) → SourceTyping Δ Γ₂ x a → SourceTyping Δ Γ (.app f x) b
  | pair {Δ Γ Γ₁ Γ₂ a b t u m} : ContextJoin Δ Γ₁ Γ₂ Γ →
      SourceTyping Δ Γ₁ t (.modal a m) → SourceTyping Δ Γ₂ u (.modal b m) →
      SourceTyping Δ Γ (.pair t u) (.modal (.prod a b) m)
  | stackPair {Δ Γ Γ₁ Γ₂ a b t u m n} : ContextJoin Δ Γ₁ Γ₂ Γ →
      SourceTyping Δ Γ₁ t (.modal a m) → SourceTyping Δ Γ₂ u (.modal b m) →
      Submode Δ m n → Submode Δ (.const Mode.localLower) n →
      SourceTyping Δ Γ (.stackPair t u) (.modal (.prod a b) n)
  | inl {Δ Γ a b t m} : EntailsAll Δ b.wellFormedBounds →
      SourceTyping Δ Γ t (.modal a m) →
      SourceTyping Δ Γ (.inl t) (.modal (.sum a b) m)
  | inr {Δ Γ a b t m} : EntailsAll Δ a.wellFormedBounds →
      SourceTyping Δ Γ t (.modal b m) →
      SourceTyping Δ Γ (.inr t) (.modal (.sum a b) m)
  | case {Δ Γ Γ₁ Γ₂ a b c t u v m} : ContextJoin Δ Γ₁ Γ₂ Γ →
      SourceTyping Δ Γ₁ t (.modal (.sum a b) m) →
      SourceTyping Δ (some (Scheme.mono (.modal a m)) :: Γ₂) u c →
      SourceTyping Δ (some (Scheme.mono (.modal b m)) :: Γ₂) v c →
      SourceTyping Δ Γ (.case t u v) c
  | split {Δ Γ Γ₁ Γ₂ a b c t u m} : ContextJoin Δ Γ₁ Γ₂ Γ →
      SourceTyping Δ Γ₁ t (.modal (.prod a b) m) →
      SourceTyping Δ (some (Scheme.mono (.modal .credit m)) ::
        some (Scheme.mono (.modal a m)) :: some (Scheme.mono (.modal b m)) :: Γ₂) u c →
      SourceTyping Δ Γ (.split t u) c
  | reuse {Δ Γ Γ₁ Γ₂ Γ₃ Γ₂₃ t u v a b m k} : ContextJoin Δ Γ₂ Γ₃ Γ₂₃ →
      ContextJoin Δ Γ₁ Γ₂₃ Γ → SourceTyping Δ Γ₁ t (.modal .credit k) →
      SourceTyping Δ Γ₂ u (.modal a m) → SourceTyping Δ Γ₃ v (.modal b m) →
      Submode Δ k (.const Mode.uniqueOnly) →
      Submode Δ (.compose k (.const Mode.many)) m →
      SourceTyping Δ Γ (.reuse t u v) (.modal (.prod a b) m)
  | region {Δ Γ t a} : SourceTyping Δ Γ t (.modal a (.const Mode.global)) →
      SourceTyping Δ Γ (.region t) a
  /-- `rhs` is closed in term variables and is evaluated in the empty environment. -/
  | defn {Δ Γ rhs body a b rhsBounds} : SourceTyping rhsBounds [] rhs a →
      BoundsSatisfiable rhsBounds →
      SourceTyping Δ (some (Scheme.generalize rhsBounds a) :: Γ) body b →
      SourceTyping Δ Γ (.defn rhs body) b

end ModalityInference
