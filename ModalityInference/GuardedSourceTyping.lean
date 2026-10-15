import ModalityInference.Declarative

/-! Source typing with defined scheme instances and guarded context replacement. -/

namespace ModalityInference

/-- Context weakening leaves a binding unchanged or supplies a comparison whose
source instance has defined images and body. Unused bindings may be dropped. -/
inductive GuardedContextLe (Δ : Bounds) : Context → Context → Prop where
  | nil : GuardedContextLe Δ [] []
  | drop {Γ Γ' s} : GuardedContextLe Δ Γ Γ' →
      GuardedContextLe Δ (s :: Γ) (none :: Γ')
  | same {Γ Γ' s} : GuardedContextLe Δ Γ Γ' →
      GuardedContextLe Δ (some s :: Γ) (some s :: Γ')
  | keep {Γ Γ' s t} : GuardedContextLe Δ Γ Γ' → SubsumesUnder Δ s t →
      GuardedContextLe Δ (some s :: Γ) (some t :: Γ')

/-- Direct source typing with guarded comparisons at every changed context binding. -/
inductive GuardedSourceTyping : Bounds → Context → RawTerm → Ty → Prop where
  | var {Δ Γ i s σ} : Γ[i]? = some (some s) → InstantiatesUnder Δ s σ →
      EntailsAll Δ (σ.bounds s.bounds) →
      GuardedSourceTyping Δ Γ (.var i) (σ.ty s.body)
  | unit {Δ Γ m} : Entails Δ (.defined m) → GuardedSourceTyping Δ Γ .unit (.modal .unit m)
  | subs {Δ Γ Γ' t a b} : GuardedSourceTyping Δ Γ t a → GuardedContextLe Δ Γ' Γ → Subtype Δ a b →
      GuardedSourceTyping Δ Γ' t b
  | lam {Δ Γ captured t a b m} : EntailsAll Δ a.wellFormedBounds →
      Entails Δ (.defined m) → Lock Δ m Γ captured →
      GuardedSourceTyping Δ (some (Scheme.mono a) :: captured) t b →
      GuardedSourceTyping Δ Γ (.lam () t) (.modal (.fn a b) m)
  | app {Δ Γ Γ₁ Γ₂ f x a b} : ContextJoin Δ Γ₁ Γ₂ Γ →
      GuardedSourceTyping Δ Γ₁ f (.fn a b) → GuardedSourceTyping Δ Γ₂ x a → GuardedSourceTyping Δ Γ (.app f x) b
  | pair {Δ Γ Γ₁ Γ₂ a b t u m} : ContextJoin Δ Γ₁ Γ₂ Γ →
      GuardedSourceTyping Δ Γ₁ t (.modal a m) → GuardedSourceTyping Δ Γ₂ u (.modal b m) →
      GuardedSourceTyping Δ Γ (.pair t u) (.modal (.prod a b) m)
  | stackPair {Δ Γ Γ₁ Γ₂ a b t u m n} : ContextJoin Δ Γ₁ Γ₂ Γ →
      GuardedSourceTyping Δ Γ₁ t (.modal a m) → GuardedSourceTyping Δ Γ₂ u (.modal b m) →
      Submode Δ m n → Submode Δ (.const Mode.localLower) n →
      GuardedSourceTyping Δ Γ (.stackPair t u) (.modal (.prod a b) n)
  | inl {Δ Γ a b t m} : EntailsAll Δ b.wellFormedBounds →
      GuardedSourceTyping Δ Γ t (.modal a m) →
      GuardedSourceTyping Δ Γ (.inl t) (.modal (.sum a b) m)
  | inr {Δ Γ a b t m} : EntailsAll Δ a.wellFormedBounds →
      GuardedSourceTyping Δ Γ t (.modal b m) →
      GuardedSourceTyping Δ Γ (.inr t) (.modal (.sum a b) m)
  | case {Δ Γ Γ₁ Γ₂ a b c t u v m} : ContextJoin Δ Γ₁ Γ₂ Γ →
      GuardedSourceTyping Δ Γ₁ t (.modal (.sum a b) m) →
      GuardedSourceTyping Δ (some (Scheme.mono (.modal a m)) :: Γ₂) u c →
      GuardedSourceTyping Δ (some (Scheme.mono (.modal b m)) :: Γ₂) v c →
      GuardedSourceTyping Δ Γ (.case t u v) c
  | split {Δ Γ Γ₁ Γ₂ a b c t u m} : ContextJoin Δ Γ₁ Γ₂ Γ →
      GuardedSourceTyping Δ Γ₁ t (.modal (.prod a b) m) →
      GuardedSourceTyping Δ (some (Scheme.mono (.modal .credit m)) ::
        some (Scheme.mono (.modal a m)) :: some (Scheme.mono (.modal b m)) :: Γ₂) u c →
      GuardedSourceTyping Δ Γ (.split t u) c
  | reuse {Δ Γ Γ₁ Γ₂ Γ₃ Γ₂₃ t u v a b m k} : ContextJoin Δ Γ₂ Γ₃ Γ₂₃ →
      ContextJoin Δ Γ₁ Γ₂₃ Γ → GuardedSourceTyping Δ Γ₁ t (.modal .credit k) →
      GuardedSourceTyping Δ Γ₂ u (.modal a m) → GuardedSourceTyping Δ Γ₃ v (.modal b m) →
      Submode Δ k (.const Mode.uniqueOnly) →
      Submode Δ (.compose k (.const Mode.many)) m →
      GuardedSourceTyping Δ Γ (.reuse t u v) (.modal (.prod a b) m)
  | region {Δ Γ t a} : GuardedSourceTyping Δ Γ t (.modal a (.const Mode.global)) →
      GuardedSourceTyping Δ Γ (.region t) a
  /-- `rhs` is closed in term variables and is evaluated in the empty environment. -/
  | defn {Δ Γ rhs body a b rhsBounds} : GuardedSourceTyping rhsBounds [] rhs a →
      BoundsSatisfiable rhsBounds →
      GuardedSourceTyping Δ (some (Scheme.generalize rhsBounds a) :: Γ) body b →
      GuardedSourceTyping Δ Γ (.defn rhs body) b

end ModalityInference
