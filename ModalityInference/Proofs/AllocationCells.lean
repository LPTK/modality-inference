import ModalityInference.Proofs.Allocation

/-! Reserving a cell removes it from subsequent allocation, including every
future region. Compatible supplies remain compatible after that reservation. -/
namespace ModalityInference

theorem Supply.start_not_tail {s : Supply} (hs : 0 < s.stride) (n : Nat) :
    s.start ≠ s.tail.at n := by
  intro he
  rw [Supply.tail_at] at he
  have he' : s.at 0 = s.at (n + 1) := (by simp [Supply.at] : s.at 0 = s.start).trans he
  have := s.at_injective hs he'
  omega

theorem Supplies.heap_fresh (s : Supplies) : s.FreshLocation (.heap s.heap.start) :=
  ⟨0, by simp [Supply.at]⟩

theorem Supplies.stack_fresh (s : Supplies) :
    s.FreshLocation (.stack s.currentFrame s.stack.start) :=
  Or.inl ⟨rfl, 0, by simp [Supply.at]⟩

theorem Supplies.heap_not_fresh_afterHeap {s : Supplies} (hs : s.Valid) :
    ¬s.afterHeap.FreshLocation (.heap s.heap.start) := by
  rintro ⟨n, he⟩
  exact s.heap.start_not_tail hs.1 n he

theorem Supplies.stack_not_fresh_afterStack {s : Supplies} (hs : s.Valid) :
    ¬s.afterStack.FreshLocation (.stack s.currentFrame s.stack.start) := by
  rintro (⟨_, n, he⟩ | ⟨n, he⟩)
  · exact s.stack.start_not_tail hs.2.1 n he
  · exact hs.2.2.2 n he.symm

theorem World.Compatible.afterHeap {w : World} {s γ} (hs : w.Compatible s γ) :
    w.Compatible s.afterHeap γ :=
  ⟨hs.1, hs.2.1, hs.2.2.1, fun l hl hf => hs.2.2.2 l hl (Supplies.fresh_afterHeap hf)⟩

theorem World.Compatible.afterStack {w : World} {s γ} (hs : w.Compatible s γ) :
    w.Compatible s.afterStack γ :=
  ⟨hs.1, hs.2.1, hs.2.2.1, fun l hl hf => hs.2.2.2 l hl (Supplies.fresh_afterStack hf)⟩

theorem World.Compatible.disjoint_fresh_cell {w : World} {s γ}
    (hs : w.Compatible s γ) {remaining : Supplies} {l m} {available owned : Resources}
    (hf : s.FreshLocation l) (hn : ¬remaining.FreshLocation l)
    (ha : ∀ l ∈ available, EnvironmentReferences γ l)
    (ho : owned ⊆ available ∪ {l | remaining.FreshLocation l}) :
    Disjoint (cellResources m l) owned := by
  apply Set.disjoint_left.mpr
  intro k hk ho'
  obtain rfl := Set.mem_singleton_iff.mp (cellResources_subset m l hk)
  exact (ho ho').elim (fun he => hs.2.2.2 _ (ha _ he) hf) hn

end ModalityInference
