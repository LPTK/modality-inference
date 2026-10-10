import ModalityInference.Declarative

/-! Relational constraint generation. Fresh choices and constraint order are not
fixed by this specification; it never calls `generate`, `infer`, or `solve`.
-/
namespace ModalityInference

inductive Lookup : AlgorithmicContext → Nat → Scheme → Prop where
  | here {Γ s} : Lookup (.binding (some s) :: Γ) 0 s
  | there {Γ i s t} : Lookup Γ i s → Lookup (.binding t :: Γ) (i+1) s
  | locked {Γ i s m} : Lookup Γ i s →
      Lookup (.lock m :: Γ) i
        {s with body := .modal s.body (.capture m)
                bounds := s.bounds ++ [.sub s.body (.modal s.body (.future m))]}

inductive UsageSplit : AlgorithmicContext → AlgorithmicContext → AlgorithmicContext → Prop where
  | nil : UsageSplit [] [] []
  | lock {Γ Γ₁ Γ₂ m} : UsageSplit Γ Γ₁ Γ₂ →
      UsageSplit (.lock m :: Γ) (.lock m :: Γ₁) (.lock m :: Γ₂)
  | drop {Γ Γ₁ Γ₂ s} : UsageSplit Γ Γ₁ Γ₂ →
      UsageSplit (.binding s :: Γ) (.binding none :: Γ₁) (.binding none :: Γ₂)
  | left {Γ Γ₁ Γ₂ s} : UsageSplit Γ Γ₁ Γ₂ →
      UsageSplit (.binding s :: Γ) (.binding s :: Γ₁) (.binding none :: Γ₂)
  | right {Γ Γ₁ Γ₂ s} : UsageSplit Γ Γ₁ Γ₂ →
      UsageSplit (.binding s :: Γ) (.binding none :: Γ₁) (.binding s :: Γ₂)
  | share {Γ Γ₁ Γ₂ s shared} : UsageSplit Γ Γ₁ Γ₂ →
      shared = {s with
        body := .modal s.body (.const Mode.aliased)
        bounds := s.bounds ++ [.sub s.body (.modal s.body (.const Mode.many))]} →
      UsageSplit (.binding (some s) :: Γ)
        (.binding (some shared) :: Γ₁) (.binding (some shared) :: Γ₂)

/-- An independent relational solve interface. Its semantic and principal-solution
obligations are stated in `Proofs`; no executable result is assumed here. -/
def Solves (cs residual : Bounds) (σ : Substitution) : Prop :=
  EntailsAll residual (σ.bounds cs) ∧ BoundsSatisfiable residual

inductive Generates : AlgorithmicContext → RawTerm → Ty → Bounds → Prop where
  | var {Γ i s σ} : Lookup Γ i s → Instantiates s σ →
      Generates Γ (.var i) (σ.ty s.body) (σ.bounds s.bounds)
  | unit {Γ} : Generates Γ .unit (.modal .unit .bottom) []
  | lam {Γ t a b m cs} :
      Generates (.binding (some (.mono a)) :: .lock m :: Γ) t b cs →
      Generates Γ (.lam () t) (.modal (.fn a b) m) cs
  | app {Γ Γ₁ Γ₂ f x a b c m cs ds} : UsageSplit Γ Γ₁ Γ₂ →
      Generates Γ₁ f a cs → Generates Γ₂ x b ds →
      Generates Γ (.app f x) c (cs ++ ds ++ [.sub a (.modal (.fn b c) m)])
  | pair {Γ Γ₁ Γ₂ x y a b c d m cs ds} : UsageSplit Γ Γ₁ Γ₂ →
      Generates Γ₁ x a cs → Generates Γ₂ y b ds →
      Generates Γ (.pair x y) (.modal (.prod c d) m)
        (cs ++ ds ++ [.sub a (.modal c m), .sub b (.modal d m)])
  | stackPair {Γ Γ₁ Γ₂ x y a b c d m cs ds} : UsageSplit Γ Γ₁ Γ₂ →
      Generates Γ₁ x a cs → Generates Γ₂ y b ds →
      Generates Γ (.stackPair x y) (.modal (.prod c d) m)
        (cs ++ ds ++ [.sub a (.modal c m), .sub b (.modal d m), .mode (.const Mode.localLower) m])
  | inl {Γ x a b c m cs} : Generates Γ x a cs →
      Generates Γ (.inl x) (.modal (.sum b c) m) (cs ++ [.sub a (.modal b m)])
  | inr {Γ x a b c m cs} : Generates Γ x a cs →
      Generates Γ (.inr x) (.modal (.sum b c) m) (cs ++ [.sub a (.modal c m)])
  | split {Γ Γ₁ Γ₂ x body a b c d m cs ds} : UsageSplit Γ Γ₁ Γ₂ →
      Generates Γ₁ x a cs →
      Generates (.binding (some (.mono (.modal .credit m))) ::
        .binding (some (.mono (.modal b m))) :: .binding (some (.mono (.modal c m))) :: Γ₂)
        body d ds →
      Generates Γ (.split x body) d (cs ++ ds ++ [.sub a (.modal (.prod b c) m)])
  | case {Γ Γ₁ Γ₂ x l r a b c d e f m cs ds es} : UsageSplit Γ Γ₁ Γ₂ →
      Generates Γ₁ x a cs →
      Generates (.binding (some (.mono (.modal b m))) :: Γ₂) l d ds →
      Generates (.binding (some (.mono (.modal c m))) :: Γ₂) r e es →
      Generates Γ (.case x l r) f
        (cs ++ ds ++ es ++ [.sub a (.modal (.sum b c) m), .sub d f, .sub e f])
  | reuse {Γ Γ₁ Γ₂ Γ₃ Γ₂₃ k x y a b c d e m n cs ds es} :
      UsageSplit Γ Γ₁ Γ₂₃ → UsageSplit Γ₂₃ Γ₂ Γ₃ →
      Generates Γ₁ k a cs → Generates Γ₂ x b ds → Generates Γ₃ y c es →
      Generates Γ (.reuse k x y) (.modal (.prod d e) m)
        (cs ++ ds ++ es ++ [.sub a (.modal .credit n), .mode n (.const Mode.uniqueOnly),
          .sub b (.modal d m), .sub c (.modal e m), .mode (.compose n (.const Mode.many)) m])
  | region {Γ t a b cs} : Generates Γ t a cs →
      Generates Γ (.region t) b (cs ++ [.sub a (.modal b (.const Mode.global))])
  | defn {Γ rhs body a b cs ds residual σ} : rhs.freeVars = ∅ →
      Generates [] rhs a cs → Solves cs residual σ →
      Generates (.binding (some (Scheme.generalize residual (σ.ty a))) :: Γ) body b ds →
      Generates Γ (.defn rhs body) b ds

end ModalityInference
