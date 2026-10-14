import ModalityInference.Declarative

/-! Direct declarative typing for terms without capture annotations.
Closure capture is determined by the context lock and the lambda body; it is not
part of the source syntax. The annotated judgment provides proof witnesses for
resource reasoning, and is equivalent to this judgment after erasure.
-/

namespace ModalityInference

/-- Source typing uses the paper's lambda syntax and retains the same lock,
context, freshness, and definedness premises as the annotated judgment. -/
inductive SourceTyping : Bounds → Context → RawTerm → Ty → Prop where
  | var {Δ Γ i s σ} : Γ[i]? = some (some s) → Instantiates s σ →
      EntailsAll Δ (σ.bounds s.bounds) → EntailsAll Δ (σ.ty s.body).wellFormedBounds →
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

/-- Erasing proof annotations preserves every declarative typing rule. -/
theorem Typing.source {Δ Γ t a} (h : Typing Δ Γ t a) :
    SourceTyping Δ Γ t.erase a := by
  induction h with
  | var hl hi hb hw => exact .var hl hi hb hw
  | unit hm => exact .unit hm
  | subs _ hc hs ih => exact .subs ih hc hs
  | lam ha hm hl _ ih => exact .lam ha hm hl ih
  | app hj _ _ ihf ihx => exact .app hj ihf ihx
  | pair hj _ _ iht ihu => exact .pair hj iht ihu
  | stackPair hj _ _ hm hn iht ihu => exact .stackPair hj iht ihu hm hn
  | inl hw _ ih => exact .inl hw ih
  | inr hw _ ih => exact .inr hw ih
  | case hj _ _ _ iht ihu ihv => exact .case hj iht ihu ihv
  | split hj _ _ iht ihu => exact .split hj iht ihu
  | reuse hj hj' _ _ _ hk hm iht ihu ihv => exact .reuse hj hj' iht ihu ihv hk hm
  | region _ ih => exact .region ih
  | defn _ hs _ ihr ihb => exact .defn ihr hs ihb

/-- Direct source derivations admit proof-only capture witnesses. -/
theorem SourceTyping.to_rawTyping {Δ Γ t a} (h : SourceTyping Δ Γ t a) :
    RawTyping Δ Γ t a := by
  induction h with
  | var hl hi hb hw => exact ⟨_, rfl, .var hl hi hb hw⟩
  | unit hm => exact ⟨_, rfl, .unit hm⟩
  | subs _ hc hs ih =>
    exact ih.elim fun t ht => ⟨t, ht.1, .subs ht.2 hc hs⟩
  | lam ha hm hl _ ih =>
    exact ih.elim fun t ht => ⟨.lam _ t, congrArg (Term.lam ()) ht.1, .lam ha hm hl ht.2⟩
  | app hj _ _ ihf ihx =>
    exact ihf.elim fun f hf => ihx.elim fun x hx =>
      ⟨.app f x, congrArg₂ Term.app hf.1 hx.1, .app hj hf.2 hx.2⟩
  | pair hj _ _ iht ihu =>
    exact iht.elim fun t ht => ihu.elim fun u hu =>
      ⟨.pair t u, congrArg₂ Term.pair ht.1 hu.1, .pair hj ht.2 hu.2⟩
  | stackPair hj _ _ hm hn iht ihu =>
    exact iht.elim fun t ht => ihu.elim fun u hu =>
      ⟨.stackPair t u, congrArg₂ Term.stackPair ht.1 hu.1, .stackPair hj ht.2 hu.2 hm hn⟩
  | inl hw _ ih =>
    exact ih.elim fun t ht => ⟨.inl t, congrArg Term.inl ht.1, .inl hw ht.2⟩
  | inr hw _ ih =>
    exact ih.elim fun t ht => ⟨.inr t, congrArg Term.inr ht.1, .inr hw ht.2⟩
  | case hj _ _ _ iht ihu ihv =>
    exact iht.elim fun t ht => ihu.elim fun u hu => ihv.elim fun v hv =>
      ⟨.case t u v, congrArg₂ (fun t (uv : RawTerm × RawTerm) => Term.case t uv.1 uv.2)
        ht.1 (congrArg₂ Prod.mk hu.1 hv.1), .case hj ht.2 hu.2 hv.2⟩
  | split hj _ _ iht ihu =>
    exact iht.elim fun t ht => ihu.elim fun u hu =>
      ⟨.split t u, congrArg₂ Term.split ht.1 hu.1, .split hj ht.2 hu.2⟩
  | reuse hj hj' _ _ _ hk hm iht ihu ihv =>
    exact iht.elim fun t ht => ihu.elim fun u hu => ihv.elim fun v hv =>
      ⟨.reuse t u v, congrArg₂ (fun t (uv : RawTerm × RawTerm) => Term.reuse t uv.1 uv.2)
        ht.1 (congrArg₂ Prod.mk hu.1 hv.1), .reuse hj hj' ht.2 hu.2 hv.2 hk hm⟩
  | region _ ih =>
    exact ih.elim fun t ht => ⟨.region t, congrArg Term.region ht.1, .region ht.2⟩
  | defn _ hs _ ihr ihb =>
    exact ihr.elim fun rhs hr => ihb.elim fun body hb =>
      ⟨.defn rhs body, congrArg₂ Term.defn hr.1 hb.1, .defn hr.2 hs hb.2⟩

/-- A proof annotation witness yields the direct source derivation. -/
theorem SourceTyping.of_rawTyping {Δ Γ t a} (h : RawTyping Δ Γ t a) :
    SourceTyping Δ Γ t a :=
  h.elim fun _ ht => ht.1 ▸ ht.2.source

/-- Proof annotations do not alter which source terms are typable. -/
theorem sourceTyping_iff_rawTyping {Δ Γ t a} :
    SourceTyping Δ Γ t a ↔ RawTyping Δ Γ t a :=
  ⟨SourceTyping.to_rawTyping, SourceTyping.of_rawTyping⟩

end ModalityInference
