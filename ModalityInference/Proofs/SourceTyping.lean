import ModalityInference.SourceTyping
import ModalityInference.Proofs.DefinedInstantiation

/-! The source and annotated typing judgments describe the same source terms.
Unused substitution images can be replaced by defined identities, so the source
instance discipline is preserved by erasing proof annotations. -/
namespace ModalityInference

private theorem body_guards {Δ : Bounds} (a : Ty) (h : a.DefinedUnder Δ) :
    EntailsAll Δ a.wellFormedBounds := by
  have hg : ∀ c ∈ a.wellFormedBounds, ∃ m, c = .defined m := by
    induction a <;> simp_all [TypeExpr.wellFormedBounds, or_imp]
  intro c hc
  obtain ⟨m, rfl⟩ := hg c hc
  exact fun η hη => h η hη (.defined m) hc

/-- Erasing proof annotations preserves every declarative typing rule. -/
theorem Typing.source {Δ Γ t a} (h : Typing Δ Γ t a) :
    SourceTyping Δ Γ t.erase a := by
  induction h with
  | @var Δ Γ i s σ hl hi hb hw =>
    have hd : (σ.ty s.body).DefinedUnder Δ := fun _ hη => hw.modeModels hη
    obtain ⟨τ, hτ, he, hb'⟩ := hi.exists_under hb hd
    rw [← he]
    exact .var hl hτ (by simpa only [hb'] using hb)
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
  | @var Δ Γ i s σ hl hi hb =>
    exact ⟨_, rfl, .var hl hi.domain hb
      (body_guards _ hi.body)⟩
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
