import ModalityInference.Proofs.ResourceContexts

/-! Every free term variable in a typing derivation has an available binding.
This includes subsumption, locked captures, all elimination binders, and closed definitions. -/
namespace ModalityInference

theorem Term.mem_freeVars_add (t : Term A) (d k i : Nat) :
    i ∈ t.freeVars (d + k) ↔ i + k ∈ t.freeVars d := by
  induction t generalizing d <;> simp_all [Term.freeVars]
  all_goals try simp_all only [Nat.add_right_comm d k 1, Nat.add_right_comm d k 3]
  split_ifs <;> simp_all <;> omega

theorem ContextLe.right_present {Δ Γ Γ'} (h : ContextLe Δ Γ Γ')
    {i : Nat} {s : Scheme} (hi : Γ'[i]? = some (some s)) :
    ∃ t, Γ[i]? = some (some t) := by
  induction h generalizing i
  all_goals cases i <;> simp_all

theorem Typing.freeVars_present {Δ Γ t a} (h : Typing Δ Γ t a)
    {i : Nat} (hi : i ∈ t.freeVars) : ∃ s, Γ[i]? = some (some s) := by
  induction h generalizing i
  case lam Δ Γ captured t a b m _ _ hlock _ ih =>
    obtain ⟨s, hs⟩ := ih ((t.mem_freeVars_add 0 1 i).mp hi)
    exact let ⟨s', hs', _⟩ := hlock.kept (i := i) (t := s) (by simpa using hs)
      ⟨s', hs'⟩
  case split Δ Γ Γ₁ Γ₂ a b c t u m hj _ _ iht ihu =>
    rcases Finset.mem_union.mp hi with hi | hi
    · exact let ⟨s, hs⟩ := iht hi; hj.left_present hs
    · obtain ⟨s, hs⟩ := ihu ((u.mem_freeVars_add 0 3 i).mp hi)
      exact hj.right_present (i := i) (s := s) (by simpa using hs)
  case case Δ Γ Γ₁ Γ₂ a b c t u v m hj _ _ _ iht ihu ihv =>
    rcases Finset.mem_union.mp hi with hi | hi
    · rcases Finset.mem_union.mp hi with hi | hi
      · exact let ⟨s, hs⟩ := iht hi; hj.left_present hs
      · obtain ⟨s, hs⟩ := ihu ((u.mem_freeVars_add 0 1 i).mp hi)
        exact hj.right_present (i := i) (s := s) (by simpa using hs)
    · obtain ⟨s, hs⟩ := ihv ((v.mem_freeVars_add 0 1 i).mp hi)
      exact hj.right_present (i := i) (s := s) (by simpa using hs)
  case defn Δ Γ rhs body a b rhsBounds _ _ _ ihr ihb =>
    rcases Finset.mem_union.mp hi with hi | hi
    · simpa using ihr hi
    · simpa using ihb ((body.mem_freeVars_add 0 1 i).mp hi)
  case reuse Δ Γ Γ₁ Γ₂ Γ₃ Γ₂₃ t u v a b m k hj hj' _ _ _ _ _ iht ihu ihv =>
    simp only [Term.freeVars, Finset.mem_union] at hi
    exact hi.elim (fun h => h.elim
      (fun h => let ⟨s, hs⟩ := iht h; hj'.left_present hs)
      (fun h => let ⟨s, hs⟩ := ihu h
                let ⟨s', hs'⟩ := hj.left_present hs
                hj'.right_present hs'))
      (fun h => let ⟨s, hs⟩ := ihv h
                let ⟨s', hs'⟩ := hj.right_present hs
                hj'.right_present hs')
  all_goals try simp_all [Term.freeVars]
  case subs _ _ _ _ _ _ _ hctx _ ih =>
    exact let ⟨s, hs⟩ := ih hi; hctx.right_present hs
  case app _ _ _ _ _ _ _ _ hj _ _ iht ihu
     | pair _ _ _ _ _ _ _ _ _ hj _ _ iht ihu
     | stackPair _ _ _ _ _ _ _ _ _ _ hj _ _ _ _ iht ihu =>
    exact hi.elim
      (fun h => let ⟨s, hs⟩ := iht h; hj.left_present hs)
      (fun h => let ⟨s, hs⟩ := ihu h; hj.right_present hs)

theorem Typing.scoped {Δ Γ t a} (h : Typing Δ Γ t a) : t.Scoped Γ.length := by
  intro i hi
  obtain ⟨s, hs⟩ := h.freeVars_present hi
  exact (List.getElem?_eq_some_iff.mp hs).choose

theorem Typing.closed {Δ t a} (h : Typing Δ [] t a) : t.freeVars = ∅ := by
  exact Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => (Nat.not_lt_zero i) (h.scoped i hi))

end ModalityInference
