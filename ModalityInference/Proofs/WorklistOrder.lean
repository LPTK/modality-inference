import ModalityInference.Proofs.TypeOrientation
import ModalityInference.Proofs.SolverUnbound
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.Prod.Lex

/-! A well-founded multiset order for ordinary worklist reductions. -/
namespace ModalityInference
namespace WorklistOrder

abbrev Rank := Lex (Nat × Lex (Nat × Lex (Nat × Nat)))

def rank (c : Constraint) : Rank :=
  let m := ModeOrientation.rank c.normalize
  toLex (c.typeRank, toLex (m.1, toLex m.2))

theorem rank_type {c d : Constraint} (h : d.typeRank < c.typeRank) : rank d < rank c :=
  Prod.Lex.left _ _ h

theorem rank_mode {c d : Constraint} (ht : d.typeRank = c.typeRank)
    (h : ModeOrientation.Lt (ModeOrientation.rank d.normalize) (ModeOrientation.rank c.normalize)) :
    rank d < rank c := Prod.lex_def.mpr (.inr ⟨ht, h⟩)

def measure (cs : Bounds) : Multiset Rank := ↑(cs.map rank)

def Lt (ds cs : Bounds) : Prop := Multiset.IsDershowitzMannaLT (measure ds) (measure cs)

theorem wellFounded : WellFounded Lt :=
  InvImage.wf measure Multiset.wellFounded_isDershowitzMannaLT

theorem replace_head {c : Constraint} {ds rest : Bounds}
    (h : ∀ d ∈ ds, rank d < rank c) : Lt (ds ++ rest) (c :: rest) := by
  refine ⟨measure rest, measure ds, {rank c}, by simp, ?_, ?_, ?_⟩
  · simp [measure, List.map_append, add_comm]
  · change (↑(rank c :: rest.map rank) : Multiset Rank) = ↑(rest.map rank) + {rank c}
    rw [add_comm, Multiset.singleton_add]
    rfl
  · intro r hr
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (show r ∈ ds.map rank from hr)
    exact ⟨rank c, by simp, h d hd⟩

theorem tail (c : Constraint) (rest : Bounds) : Lt rest (c :: rest) :=
  replace_head (ds := []) (by simp)

theorem stepMode_decreases {s : SolverState} {a b t c}
    (he : c.normalize = .mode a b) (h : stepMode s a b = .success t) :
    Lt t.pending (c :: s.pending) := by
  obtain ⟨u, hu, hp, _⟩ := stepMode_separate_pending h
  rw [hp]
  apply replace_head
  intro d hd
  have hdm := (stepMode_modality_pending hu d hd).resolve_left (by simp)
  have hlt := (ModeOrientation.stepMode_normalized_decreases hu d hd).resolve_left (by simp)
  apply rank_mode
  · rw [(Constraint.typeRank_zero d).mpr hdm, ← Constraint.normalize_typeRank c, he]
    rfl
  · simpa only [he] using hlt

theorem stepType_decreases_or_clears {s : SolverState} (hs : s.Fresh) {a b t c}
    (ha : a.Bounded s.nextType s.nextMode) (hb : b.Bounded s.nextType s.nextMode)
    (hf : ∀ k ∈ s.substitution.types.map Prod.fst,
      .flex k ∉ a.typeVars ∧ .flex k ∉ b.typeVars)
    (he : c.normalize = .sub a b) (h : stepType s a b = .success t) :
    t.ClearsSeen ∨ Lt t.pending (c :: s.pending) := by
  rcases stepType_prefix_decreases_or_clears hs ha hb hf h with ht | ⟨ds, hp, hr⟩
  · exact .inl ht
  · right
    rw [hp]
    apply replace_head
    intro d hd
    apply rank_type
    simpa only [← he, Constraint.normalize_typeRank] using hr d hd

end WorklistOrder

theorem solverStep_progress {s t : SolverState} (hf : s.Fresh) (hu : s.Unbound)
    (hσ : s.substitution.Acyclic) (hp : s.pending ≠ []) (h : solverStep s = .success t) :
    t.ClearsSeen ∨ t.substitution ≠ s.substitution ∨ WorklistOrder.Lt t.pending s.pending := by
  simp only [solverStep, bind, pure, RunResult.bind] at h
  repeat' split at h
  case h_2 =>
    rename_i pending c rest hpend hseen normalized a b he
    have hfix := (hu.pending c (by simp [hpend])).fixed hu.modes
    have hh := WorklistOrder.stepType_decreases_or_clears
      (hf.advance hpend (by simp))
      (he ▸ hf.normalized_head hpend).1 (he ▸ hf.normalized_head hpend).2
      (s.substitution.normalized_sub_fresh hσ he) (hfix ▸ he) h
    exact hh.imp_right (fun hl => .inr (by simpa only [hpend] using hl))
  case h_3 =>
    rename_i pending c rest hpend hseen normalized a b he
    have hfix := (hu.pending c (by simp [hpend])).fixed hu.modes
    exact .inr (.inr (by simpa only [hpend] using WorklistOrder.stepMode_decreases (hfix ▸ he) h))
  all_goals cases h
  all_goals try exact False.elim (hp ‹s.pending = []›)
  case h_2.isFalse.isFalse.refl =>
    rename_i pending c rest hpend hseen normalized a v n he hrefl hoccurs
    right; left
    intro heq
    obtain ⟨hn, _⟩ := s.substitution.normalized_equal_fresh hσ he
    have hlen := congrArg (fun σ : Substitution => (σ.types.map Prod.fst).length) heq
    simp only [Substitution.extendType_keys _ hn, List.length_cons, Nat.succ_ne_self] at hlen
  all_goals right; right
  all_goals rw [‹s.pending = _ :: _›]
  all_goals try exact WorklistOrder.tail _ _
  case h_1.refl.h.h =>
    rename_i pending c rest hpend hseen normalized a b he
    have hfix := (hu.pending c (by simp [hpend])).fixed hu.modes
    apply WorklistOrder.replace_head
    intro d hd
    apply WorklistOrder.rank_type
    rw [← Constraint.normalize_typeRank c, ← hfix, he]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp [Constraint.typeRank, Nat.add_comm]
  case h_2.isFalse.isTrue.refl.h.h =>
    rename_i pending c rest hpend hseen normalized a v n he hrefl hoccurs
    have hfix := (hu.pending c (by simp [hpend])).fixed hu.modes
    apply WorklistOrder.replace_head
    intro d hd
    apply WorklistOrder.rank_type
    rw [← Constraint.normalize_typeRank c, ← hfix, he]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp [Constraint.typeRank, TypeExpr.shapeSize, Nat.add_comm]

end ModalityInference
