import ModalityInference.Proofs.Allocation

/-! Evaluation returns references only from its input environment or supply.
The theorem covers every constructor and does not require a typing derivation. -/
namespace ModalityInference

@[simp] theorem EnvironmentReferences.cons {γ : Environment} {v : Value} {l : Location} :
    EnvironmentReferences (v :: γ) l ↔ References v l ∨ EnvironmentReferences γ l := by
  simp [EnvironmentReferences, or_and_right, exists_or]

@[simp] theorem EnvironmentReferences.nil {l : Location} : ¬ EnvironmentReferences [] l := by
  simp [EnvironmentReferences]

theorem Eval.references {s γ t v} (h : Eval s γ t v) :
    ∀ l, References v l → EnvironmentReferences γ l ∨ s.FreshLocation l := by
  induction h
  case app s γ f a γ' captured body va v _ _ _ ihf iha ihbody =>
    intro l hl
    exact (ihbody l hl).elim
      (fun he => (EnvironmentReferences.cons.mp he).elim
        (fun hx => (iha l hx).imp_right Supplies.fresh_branch)
        (fun hc => (ihf l (References.closure_iff.mpr hc)).imp_right Supplies.fresh_branch))
      (fun hf => Or.inr (Supplies.fresh_branch hf))
  case split s γ a body loc x y v _ _ iha ihbody =>
    intro l hl
    rcases ihbody l hl with he | hf
    · simp only [EnvironmentReferences.cons] at he
      rcases he with hc | hx | hy | he
      · cases hc
        exact (iha _ .pairCell).imp_right Supplies.fresh_branch
      · exact (iha _ (.pairLeft hx)).imp_right Supplies.fresh_branch
      · exact (iha _ (.pairRight hy)).imp_right Supplies.fresh_branch
      · exact Or.inl he
    · exact Or.inr (Supplies.fresh_branch hf)
  case lam s γ captured body =>
    intro l hl
    obtain ⟨v, hv, hr⟩ := References.closure_iff.mp hl
    rcases mem_trimEnvironment hv with rfl | ⟨i, hi, hvalue⟩
    · cases hr
    · exact Or.inl ⟨v, List.mem_of_getElem? hvalue, hr⟩
  case defn s γ rhs body a b _ _ ihr ihb =>
    intro l hl
    exact (ihb l hl).elim
      (fun he => (EnvironmentReferences.cons.mp he).elim
        (fun hx => Or.inr (Supplies.fresh_branch ((ihr l hx).resolve_left EnvironmentReferences.nil)))
        Or.inl)
      (fun hf => Or.inr (Supplies.fresh_branch hf))
  case caseLeft s γ a b c x v _ _ iha ihbody =>
    intro l hl
    exact (ihbody l hl).elim
      (fun he => (EnvironmentReferences.cons.mp he).elim
        (fun hx => (iha l (.inl hx)).imp_right Supplies.fresh_branch) Or.inl)
      (fun hf => Or.inr (Supplies.fresh_branch hf))
  case caseRight s γ a b c x v _ _ iha ihbody =>
    intro l hl
    exact (ihbody l hl).elim
      (fun he => (EnvironmentReferences.cons.mp he).elim
        (fun hx => (iha l (.inr hx)).imp_right Supplies.fresh_branch) Or.inl)
      (fun hf => Or.inr (Supplies.fresh_branch hf))
  case reuse s γ a b c loc x y _ _ _ ihc ihx ihy =>
    intro l hl
    cases hl
    case pairCell => exact (ihc _ .credit).imp_right Supplies.fresh_branch
    case pairLeft hx => exact (ihx _ hx).imp_right Supplies.fresh_branch
    case pairRight hy => exact (ihy _ hy).imp_right Supplies.fresh_branch
  case pair s γ a b va vb _ _ iha ihb =>
    intro l hl
    cases hl
    case pairCell => exact Or.inr ⟨0, by simp [Supply.at]⟩
    case pairLeft hx => exact (iha _ hx).imp_right (Supplies.fresh_afterHeap ∘ Supplies.fresh_branch)
    case pairRight hy => exact (ihb _ hy).imp_right (Supplies.fresh_afterHeap ∘ Supplies.fresh_branch)
  case stackPair s γ a b va vb _ _ iha ihb =>
    intro l hl
    cases hl
    case pairCell => exact Or.inr (Or.inl ⟨rfl, 0, by simp [Supply.at]⟩)
    case pairLeft hx => exact (iha _ hx).imp_right (Supplies.fresh_afterStack ∘ Supplies.fresh_branch)
    case pairRight hy => exact (ihb _ hy).imp_right (Supplies.fresh_afterStack ∘ Supplies.fresh_branch)
  case var _ _ _ v hv => exact fun _ hl => Or.inl ⟨v, List.mem_of_getElem? hv, hl⟩
  case unit => exact fun _ hl => nomatch hl
  case inl _ _ _ _ _ ih => exact fun l hl => match hl with | .inl hx => ih l hx
  case inr _ _ _ _ _ ih => exact fun l hl => match hl with | .inr hx => ih l hx
  case region _ _ _ _ _ ih => exact fun l hl => (ih l hl).imp_right Supplies.fresh_enter

theorem Eval.not_fresh_branch {s : Supplies} {γ t v k i j} {w : World}
    (h : Eval (s.branch k i) γ t v) (hs : w.Compatible s γ)
    (hi : i < k) (hj : j < k) (hij : i ≠ j) :
    ∀ l, References v l → ¬(s.branch k j).FreshLocation l := by
  intro l hl hf
  exact (h.references l hl).elim
    (fun he => hs.2.2.2 l he (Supplies.fresh_branch hf))
    (fun he => Set.disjoint_left.mp (s.fresh_branch_disjoint hs.1 hi hj hij) he hf)

end ModalityInference
