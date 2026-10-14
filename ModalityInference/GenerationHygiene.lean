import ModalityInference.Generation

/-! The scope condition on an independent generation derivation: a symbolic lock
is outside every captured scheme's quantifiers. Fresh executable allocation will
establish this condition; it is not a restriction on source terms. -/
namespace ModalityInference

def AlgorithmicContext.FreshForMode (Γ : AlgorithmicContext) (m : ModExpr) : Prop :=
  ∀ s, .binding (some s) ∈ Γ → s.FreshForMode m

/-- Scope evidence for the generation rules. A lambda's lock must not be captured
when lookup instantiates a polymorphic binding below it. -/
inductive Generates.Hygienic : {Γ : AlgorithmicContext} → {t : RawTerm} →
    {a : Ty} → {cs : Bounds} → Generates Γ t a cs → Prop where
  | var {Γ i s σ} (hl : Lookup Γ i s) (hi : Instantiates s σ) : Hygienic (.var hl hi)
  | unit {Γ} : Hygienic (.unit (Γ := Γ))
  | lam {Γ t a b m cs}
      {h : Generates (.binding (some (.mono (.var (.flex a)))) :: .lock (.var (.flex m)) :: Γ) t b cs} :
      AlgorithmicContext.FreshForMode Γ (.var (.flex m)) → Hygienic h → Hygienic (.lam h)
  | app {Γ Γ₁ Γ₂ f x a b c m cs ds} (hj : UsageSplit Γ Γ₁ Γ₂)
      {hf : Generates Γ₁ f a cs} {hx : Generates Γ₂ x b ds} :
      Hygienic hf → Hygienic hx → Hygienic (.app (c := c) (m := m) hj hf hx)
  | pair {Γ Γ₁ Γ₂ x y a b c d m cs ds} (hj : UsageSplit Γ Γ₁ Γ₂)
      {hx : Generates Γ₁ x a cs} {hy : Generates Γ₂ y b ds} :
      Hygienic hx → Hygienic hy → Hygienic (.pair (c := c) (d := d) (m := m) hj hx hy)
  | stackPair {Γ Γ₁ Γ₂ x y a b c d m cs ds} (hj : UsageSplit Γ Γ₁ Γ₂)
      {hx : Generates Γ₁ x a cs} {hy : Generates Γ₂ y b ds} :
      Hygienic hx → Hygienic hy → Hygienic (.stackPair (c := c) (d := d) (m := m) hj hx hy)
  | inl {Γ x a b c m cs} {hx : Generates Γ x a cs} :
      Hygienic hx → Hygienic (.inl (b := b) (c := c) (m := m) hx)
  | inr {Γ x a b c m cs} {hx : Generates Γ x a cs} :
      Hygienic hx → Hygienic (.inr (b := b) (c := c) (m := m) hx)
  | split {Γ Γ₁ Γ₂ x body a b c d m cs ds} (hj : UsageSplit Γ Γ₁ Γ₂)
      {hx : Generates Γ₁ x a cs}
      {hb : Generates (.binding (some (.mono (.modal .credit m))) ::
        .binding (some (.mono (.modal b m))) :: .binding (some (.mono (.modal c m))) :: Γ₂)
        body d ds} :
      Hygienic hx → Hygienic hb → Hygienic (.split hj hx hb)
  | case {Γ Γ₁ Γ₂ x l r a b c d e f m cs ds es} (hj : UsageSplit Γ Γ₁ Γ₂)
      {hx : Generates Γ₁ x a cs}
      {hl : Generates (.binding (some (.mono (.modal b m))) :: Γ₂) l d ds}
      {hr : Generates (.binding (some (.mono (.modal c m))) :: Γ₂) r e es} :
      Hygienic hx → Hygienic hl → Hygienic hr → Hygienic (.case (f := f) hj hx hl hr)
  | reuse {Γ Γ₁ Γ₂ Γ₃ Γ₂₃ k x y a b c d e m n cs ds es}
      (h1 : UsageSplit Γ Γ₁ Γ₂₃) (h2 : UsageSplit Γ₂₃ Γ₂ Γ₃)
      {hk : Generates Γ₁ k a cs} {hx : Generates Γ₂ x b ds} {hy : Generates Γ₃ y c es} :
      Hygienic hk → Hygienic hx → Hygienic hy →
      Hygienic (.reuse (d := d) (e := e) (m := m) (n := n) h1 h2 hk hx hy)
  | region {Γ t a b cs} {h : Generates Γ t a cs} : Hygienic h → Hygienic (.region (b := b) h)
  | defn {Γ rhs body a b cs ds residual σ} (hc : rhs.freeVars = ∅)
      {hr : Generates [] rhs a cs} (hs : Solves cs residual σ)
      {hb : Generates (.binding (some (Scheme.generalize residual (σ.ty a))) :: Γ) body b ds} :
      Hygienic hr → Hygienic hb → Hygienic (.defn hc hr hs hb)

end ModalityInference
