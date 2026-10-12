import ModalityInference.Proofs.ResourceCaptures

/-! Supply restriction, branch disjointness, and preservation of compatibility.
Fresh future frames are partitioned along with heap and current-frame cells. -/
namespace ModalityInference

@[simp] theorem Supply.slice_at (s : Supply) (k i n : Nat) :
    (s.slice k i).at n = s.at (i + k * n) := by
  simp [Supply.slice, Supply.at, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

@[simp] theorem Supply.tail_at (s : Supply) (n : Nat) :
    s.tail.at n = s.at (n + 1) := by
  simp [Supply.tail, Supply.at, Nat.mul_add, Nat.add_assoc, Nat.add_comm]

theorem Supplies.fresh_branch {s : Supplies} {k i l} (h : (s.branch k i).FreshLocation l) :
    s.FreshLocation l := by
  cases l <;> simp only [Supplies.FreshLocation, Supplies.branch, Supply.slice_at] at h ⊢
  all_goals aesop

theorem Supplies.fresh_afterHeap {s : Supplies} {l} (h : s.afterHeap.FreshLocation l) :
    s.FreshLocation l := by
  cases l <;> simp only [Supplies.FreshLocation, Supplies.afterHeap, Supply.tail_at] at h ⊢
  all_goals aesop

theorem Supplies.fresh_afterStack {s : Supplies} {l} (h : s.afterStack.FreshLocation l) :
    s.FreshLocation l := by
  cases l <;> simp only [Supplies.FreshLocation, Supplies.afterStack, Supply.tail_at] at h ⊢
  all_goals aesop

theorem Supplies.fresh_enter {s : Supplies} {l} (h : s.enter.FreshLocation l) :
    s.FreshLocation l := by
  cases l <;> simp only [Supplies.FreshLocation, Supplies.enter, Supply.tail_at] at h ⊢
  case heap => exact h
  case stack =>
    exact h.elim
      (fun ⟨hf, _⟩ => Or.inr ⟨0, by simpa [Supply.at] using hf⟩)
      (fun ⟨n, hf⟩ => Or.inr ⟨n + 1, hf⟩)

theorem Supply.at_injective {s : Supply} (h : 0 < s.stride) : Function.Injective s.at := by
  intro i j he
  exact Nat.eq_of_mul_eq_mul_left h (Nat.add_left_cancel he)

theorem Supply.slice_disjoint {s : Supply} (hs : 0 < s.stride) {k i j : Nat}
    (hi : i < k) (hj : j < k) (hij : i ≠ j) (n m : Nat) :
    (s.slice k i).at n ≠ (s.slice k j).at m := by
  intro he
  have he' : i + k * n = j + k * m := s.at_injective hs (by simpa using he)
  exact hij (by
    simpa [Nat.add_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using congrArg (fun n => n % k) he')

theorem Supplies.fresh_branch_disjoint {s : Supplies} (hs : s.Valid) {k i j : Nat}
    (hi : i < k) (hj : j < k) (hij : i ≠ j) :
    Disjoint {l | (s.branch k i).FreshLocation l} {l | (s.branch k j).FreshLocation l} := by
  apply Set.disjoint_left.mpr
  intro l hleft hright
  cases l <;> simp only [Set.mem_setOf_eq, Supplies.FreshLocation, Supplies.branch] at hleft hright
  case stack f c =>
    rcases hleft with ⟨hfi, ni, hci⟩ | ⟨ni, hfi⟩ <;>
      rcases hright with ⟨hfj, nj, hcj⟩ | ⟨nj, hfj⟩
    · exact s.stack.slice_disjoint hs.2.1 hi hj hij ni nj (hci.symm.trans hcj)
    · exact hs.2.2.2 (j + k * nj) (by simpa using hfj.symm.trans hfi)
    · exact hs.2.2.2 (i + k * ni) (by simpa using hfi.symm.trans hfj)
    · exact s.frames.slice_disjoint hs.2.2.1 hi hj hij ni nj (hfi.symm.trans hfj)
  case heap c =>
    obtain ⟨ni, hi'⟩ := hleft
    obtain ⟨nj, hj'⟩ := hright
    exact s.heap.slice_disjoint hs.1 hi hj hij ni nj (hi'.symm.trans hj')

theorem Supplies.Valid.branch {s : Supplies} (hs : s.Valid) {k : Nat} (hk : 0 < k) (i : Nat) :
    (s.branch k i).Valid :=
  ⟨Nat.mul_pos hs.1 hk, Nat.mul_pos hs.2.1 hk, Nat.mul_pos hs.2.2.1 hk,
    fun n => by simpa [Supplies.branch] using hs.2.2.2 (i + k * n)⟩

theorem World.Compatible.branch {w : World} {s γ} (hs : w.Compatible s γ)
    {k : Nat} (hk : 0 < k) (i : Nat) : w.Compatible (s.branch k i) γ :=
  ⟨hs.1.branch hk i, hs.2.1,
    fun n => by simpa [Supplies.branch] using hs.2.2.1 (i + k * n),
    fun l hl hf => hs.2.2.2 l hl (Supplies.fresh_branch hf)⟩

theorem World.Compatible.empty {w : World} {s γ} (hs : w.Compatible s γ) :
    w.Compatible s [] :=
  ⟨hs.1, hs.2.1, hs.2.2.1, fun _ ⟨_, hv, _⟩ => nomatch hv⟩

theorem World.Compatible.of_references {w : World} {s γ δ} (hs : w.Compatible s γ)
    (hδ : ∀ l, EnvironmentReferences δ l → EnvironmentReferences γ l) :
    w.Compatible s δ :=
  ⟨hs.1, hs.2.1, hs.2.2.1, fun l hl => hs.2.2.2 l (hδ l hl)⟩

theorem World.Compatible.cons {w : World} {s γ v} (hs : w.Compatible s γ)
    (hv : ∀ l, References v l → ¬s.FreshLocation l) : w.Compatible s (v :: γ) :=
  ⟨hs.1, hs.2.1, hs.2.2.1, fun l ⟨u, hu, hr⟩ hf =>
    (List.mem_cons.mp hu).elim (fun he => hv l (he ▸ hr) hf)
      (fun hu => hs.2.2.2 l ⟨u, hu, hr⟩ hf)⟩

end ModalityInference
