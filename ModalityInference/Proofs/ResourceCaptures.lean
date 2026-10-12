import ModalityInference.Proofs.TypingInstances
import ModalityInference.Proofs.ContextRestriction

/-! Actual capture references are live, and global locks exclude stack references.
Used-binding admissibility is supplied by the whole-language typing invariant. -/
namespace ModalityInference

theorem mem_trimEnvironment {γ : Environment} {used : Finset Nat} {v : Value}
    (h : v ∈ trimEnvironment γ used) : v = .unit ∨ ∃ i ∈ used, γ[i]? = some v := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  cases he : γ[i]? <;> simp [trimEnvironment, List.getElem?_mapIdx, he] at hi
  split_ifs at hi with hu <;> aesop

theorem ResourceEnvironmentInterpretation.trim_valid {ρ w γ reserved used} {Γ : Context}
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ.restrict used) γ reserved)
    (hused : ∀ i ∈ used, ∃ s, Γ[i]? = some (some s) ∧ s.Realizable ρ) :
    ∀ v ∈ trimEnvironment γ used, w.ValidValue v := by
  intro v hv
  rcases mem_trimEnvironment hv with rfl | ⟨i, hi, hvalue⟩
  · exact fun l hl => nomatch hl
  · obtain ⟨s, hs, hr⟩ := hused i hi
    exact let ⟨v', hv', hri⟩ := hγ.1 i s (Context.restrict_present.mpr ⟨hi, hs⟩)
      (Option.some.inj (hv'.symm.trans hvalue)) ▸ hri.valid hr

theorem ResourceSchemeInterpretation.capture_global {ρ w m v reserved n} {s : Scheme}
    (h : ResourceSchemeInterpretation ρ w (s.modal (.capture m)) v reserved)
    (hs : s.Realizable ρ) (hf : s.FreshForMode m)
    (hm : m.eval (some ∘ ρ.modes) = some n) (hn : n.isLocal = false) :
    ∀ l, References v l → HeapLocation l := by
  obtain ⟨η, a, hη, ha⟩ := hs
  obtain ⟨owned, _, hv⟩ := h.2 η (a.modal n.capture) hη
    (by simp [Scheme.modal, TypeExpr.realize, ModExpr.eval, ha, hη.eval_fresh hf, hm])
  exact (ResourceInterpretation.modal_iff.mp hv).global_references
    (by simp [Mode.compose, Mode.capture, hn])

theorem Lock.trim_global {ρ w Δ m Γ Γ' γ reserved used n}
    (h : Lock Δ m Γ Γ')
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ'.restrict used) γ reserved)
    (hused : ∀ i ∈ used, ∃ s, Γ'[i]? = some (some s) ∧ s.Realizable ρ)
    (hm : m.eval (some ∘ ρ.modes) = some n) (hn : n.isLocal = false) :
    ∀ l, EnvironmentReferences (trimEnvironment γ used) l → HeapLocation l := by
  rintro l ⟨v, hv, hl⟩
  rcases mem_trimEnvironment hv with rfl | ⟨i, hi, hvalue⟩
  · cases hl
  · obtain ⟨t, ht, hr⟩ := hused i hi
    obtain ⟨s, hs, he, _, hf, _⟩ := h.kept ht
    obtain ⟨v', hv', hri⟩ := hγ.1 i t (Context.restrict_present.mpr ⟨hi, ht⟩)
    exact (he ▸ hri).capture_global (he ▸ hr).of_modal hf hm hn l
      ((Option.some.inj (hvalue.symm.trans hv')) ▸ hl)

end ModalityInference
