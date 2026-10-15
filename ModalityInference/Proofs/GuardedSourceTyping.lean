import ModalityInference.GuardedSourceTyping
import ModalityInference.Proofs.ConstraintModels
import ModalityInference.Proofs.SourceTyping

/-! Guarded source derivations preserve the existing resource-semantics judgment. -/
namespace ModalityInference

theorem SubsumesUnder.to_subsumes {Δ : Bounds} {s t : Scheme}
    (h : SubsumesUnder Δ s t) : Subsumes Δ s t := by
  obtain ⟨σ, hi, hb, ht⟩ := h
  exact ⟨σ, hi.domain, hb, ht⟩

theorem GuardedContextLe.to_contextLe {Δ Γ Γ'} (h : GuardedContextLe Δ Γ Γ') :
    ContextLe Δ Γ Γ' := by
  induction h with
  | nil => exact .nil
  | drop _ ih => exact .drop ih
  | @same Γ Γ' s _ ih =>
    refine .keep ih ⟨s.freshSubstitution (s.subsumptionIndices Δ s).1
      (s.subsumptionIndices Δ s).2 true, ?_, ?_, .refl⟩
    · simp [Instantiates, Scheme.freshSubstitution, List.map_map, Function.comp_def]
    · intro c hc
      exact c.assumptions_entail fun d hd =>
        List.mem_append_right Δ (List.mem_flatMap.mpr ⟨c, hc, hd⟩)
  | keep _ hs ih => exact .keep ih hs.to_subsumes

theorem GuardedContextLe.refl (Γ : Context) (Δ : Bounds) : GuardedContextLe Δ Γ Γ := by
  induction Γ with
  | nil => exact .nil
  | cons entry Γ ih =>
    cases entry with
    | none => exact .drop ih
    | some s => exact .same ih


theorem GuardedSourceTyping.to_sourceTyping {Δ Γ t a}
    (h : GuardedSourceTyping Δ Γ t a) : SourceTyping Δ Γ t a := by
  induction h with
  | var hl hi hb => exact .var hl hi hb
  | unit hm => exact .unit hm
  | subs _ hc hs ih => exact .subs ih hc.to_contextLe hs
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

theorem GuardedSourceTyping.to_rawTyping {Δ Γ t a}
    (h : GuardedSourceTyping Δ Γ t a) : RawTyping Δ Γ t a :=
  h.to_sourceTyping.to_rawTyping

theorem GuardedSourceTyping.weakening {Δ Γ Γ' t a}
    (h : GuardedSourceTyping Δ Γ t a) (hc : GuardedContextLe Δ Γ' Γ) :
    GuardedSourceTyping Δ Γ' t a := .subs h hc .refl

/-- Proof annotations may be carried through generation independently of the
source judgment; the guarded derivation itself uses only the erased term. -/
abbrev GuardedTyping (Δ : Bounds) (Γ : Context) (t : AnnotatedTerm) (a : Ty) : Prop :=
  GuardedSourceTyping Δ Γ t.erase a

def GuardedRawTyping (Δ : Bounds) (Γ : Context) (t : RawTerm) (a : Ty) : Prop :=
  ∃ elaborated, elaborated.erase = t ∧ GuardedTyping Δ Γ elaborated a

theorem GuardedRawTyping.weakening {Δ Γ Γ' t a}
    (h : GuardedRawTyping Δ Γ t a) (hc : GuardedContextLe Δ Γ' Γ) :
    GuardedRawTyping Δ Γ' t a := by
  obtain ⟨u, he, ht⟩ := h
  exact ⟨u, he, ht.weakening hc⟩

theorem GuardedRawTyping.source {Δ Γ t a} (h : GuardedRawTyping Δ Γ t a) :
    GuardedSourceTyping Δ Γ t a := by
  obtain ⟨u, he, ht⟩ := h
  exact he ▸ ht

end ModalityInference
