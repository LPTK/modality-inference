import ModalityInference.Proofs.SolverLocalSoundness
import ModalityInference.Proofs.VariableOccurrences
import Mathlib.Order.WithBot

/-! A well-founded rank decreases for every new obligation emitted by `stepMode`,
including after normalization. This excludes cycles among modality descendants;
type expansion, substitution and whole-worklist termination are separate obligations. -/
namespace ModalityInference

def ModVar.priority : ModVar → WithTop Nat
  | .flex n => n
  | .rigid _ => ⊤

private def priorityStep (acc : Option Nat) (v : ModVar) : Option Nat :=
  match v, acc with
  | .rigid _, _ => acc
  | .flex n, none => some n
  | .flex n, some k => some (min n k)

private theorem priority_step (acc : Option Nat) (v : ModVar) :
    (priorityStep acc v : WithTop Nat) = min (α := WithTop Nat) acc v.priority := by
  cases v <;> cases acc <;> simp [priorityStep, ModVar.priority,
    WithTop.none_eq_top, WithTop.some_eq_coe, min_comm]

def ModExpr.priority (m : ModExpr) : WithTop Nat := m.minVar

private theorem priority_fold_le (xs : List ModVar) (p acc : WithTop Nat) :
    p ≤ xs.foldl (fun (acc : WithTop Nat) v => min (α := WithTop Nat) acc v.priority) acc ↔
      p ≤ acc ∧ ∀ v ∈ xs, p ≤ v.priority := by
  induction xs generalizing acc <;> simp_all [List.foldl, and_assoc]

theorem ModExpr.le_priority (m : ModExpr) (p : WithTop Nat) :
    p ≤ m.priority ↔ ∀ v ∈ m.vars, p ≤ v.priority := by
  have he := List.foldl_hom (fun acc : Option Nat => (acc : WithTop Nat))
    (g₁ := priorityStep) (g₂ := fun (acc : WithTop Nat) v => min (α := WithTop Nat) acc v.priority)
    (l := m.freeVariables) (init := none) (fun acc v => (priority_step acc v).symm)
  refine (congrArg (fun q : WithTop Nat => p ≤ q) he).symm.to_iff.trans ?_
  simpa using priority_fold_le m.freeVariables p ⊤

private theorem priority_union {m a b : ModExpr} (h : m.vars = a.vars ∪ b.vars) :
    m.priority = min (α := WithTop Nat) a.priority b.priority := by
  apply eq_of_forall_le_iff
  simp [ModExpr.le_priority, h, or_imp, forall_and]

@[simp] theorem ModExpr.priority_const (m : Mode) : (.const m : ModExpr).priority = ⊤ := rfl
@[simp] theorem ModExpr.priority_var (v : ModVar) : (.var v : ModExpr).priority = v.priority := by
  cases v <;> rfl
@[simp] theorem ModExpr.priority_compose (a b : ModExpr) :
    (ModExpr.compose a b).priority = min (α := WithTop Nat) a.priority b.priority := priority_union rfl
@[simp] theorem ModExpr.priority_meet (a b : ModExpr) :
    (ModExpr.meet a b).priority = min (α := WithTop Nat) a.priority b.priority := priority_union rfl
@[simp] theorem ModExpr.priority_join (a b : ModExpr) :
    (ModExpr.join a b).priority = min (α := WithTop Nat) a.priority b.priority := priority_union rfl
@[simp] theorem ModExpr.priority_leftResidual (a b : ModExpr) :
    (ModExpr.leftResidual a b).priority = min (α := WithTop Nat) a.priority b.priority := priority_union rfl
@[simp] theorem ModExpr.priority_rightResidual (a b : ModExpr) :
    (ModExpr.rightResidual a b).priority = min (α := WithTop Nat) a.priority b.priority := priority_union rfl
@[simp] theorem ModExpr.priority_close (a : ModExpr) : (ModExpr.close a).priority = a.priority := rfl
@[simp] theorem ModExpr.priority_closeInv (a : ModExpr) : (ModExpr.closeInv a).priority = a.priority := rfl
@[simp] theorem ModExpr.priority_future (a : ModExpr) : (ModExpr.future a).priority = a.priority := rfl
@[simp] theorem ModExpr.priority_capture (a : ModExpr) : (ModExpr.capture a).priority = a.priority := rfl

theorem ModExpr.minimumLE_iff (x y : Option Nat) :
    minimumLE x y = true ↔ (show WithTop Nat from x) ≤ y := by
  cases x <;> cases y <;> simp [minimumLE, WithTop.none_eq_top, WithTop.some_eq_coe]

def ModExpr.nodes : ModExpr → Nat
  | .const _ | .var _ => 1
  | .compose a b | .meet a b | .join a b | .leftResidual a b | .rightResidual a b =>
      a.nodes + b.nodes + 1
  | .close a | .closeInv a | .future a | .capture a => a.nodes + 1

theorem ModExpr.nodes_pos (m : ModExpr) : 0 < m.nodes := by
  cases m <;> simp [ModExpr.nodes]

theorem ModExpr.vars_empty_of_eval_none {m : ModExpr} {k : Mode}
    (h : m.eval (fun _ => none) = some k) : m.vars = ∅ := by
  induction m generalizing k <;> simp only [ModExpr.eval, bind, pure,
    Option.bind_eq_some_iff] at h
  case const => rfl
  case var => cases h
  all_goals rcases h with ⟨_, ha, h⟩
  all_goals try rcases h with ⟨_, hb, _⟩
  all_goals simp_all [ModExpr.vars]

@[simp] theorem ModExpr.foldConstants_vars (m : ModExpr) : m.foldConstants.vars = m.vars := by
  unfold ModExpr.foldConstants
  split
  · next k hk => exact (vars_empty_of_eval_none hk).symm
  · split
    all_goals first | rfl | (split <;> simp_all [beq_iff_eq, ModExpr.vars])

theorem ModExpr.foldConstants_nodes (m : ModExpr) : m.foldConstants.nodes ≤ m.nodes := by
  unfold ModExpr.foldConstants
  split
  · exact m.nodes_pos
  · split
    all_goals first | exact Nat.le_refl _ | (split <;> simp [ModExpr.nodes]; omega)

@[simp] theorem ModExpr.normalize_vars (m : ModExpr) : m.normalize.vars = m.vars := by
  induction m <;> simp_all [ModExpr.normalize, ModExpr.vars]

theorem ModExpr.normalize_nodes (m : ModExpr) : m.normalize.nodes ≤ m.nodes := by
  induction m <;> simp only [ModExpr.normalize]
  all_goals first | exact Nat.le_refl _ | apply le_trans (foldConstants_nodes _)
  all_goals simp only [ModExpr.nodes]
  all_goals omega

@[simp] theorem ModExpr.normalize_priority (m : ModExpr) : m.normalize.priority = m.priority := by
  apply eq_of_forall_le_iff
  simp [ModExpr.le_priority]

namespace ModeOrientation

abbrev Rank := Nat × Nat × Nat
abbrev Lt : Rank → Rank → Prop := Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

def pairRank (na nb : Nat) (a b : WithTop Nat) : Rank :=
  (na + nb + 1, if a = b then 0 else 1, if a ≤ b then na else nb)

/-- First count syntax nodes, then distinguish unequal least flexible variables,
then count nodes on the side with the smaller minimum (left on a tie).
Constraints outside modality solving have rank zero. -/
def rank : Constraint → Rank
  | .mode a b => pairRank a.nodes b.nodes a.priority b.priority
  | .defined a => (a.nodes, 0, 0)
  | _ => (0, 0, 0)

theorem rank_wellFounded : WellFounded Lt :=
  Nat.lt_wfRel.wf.prod_lex (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)

theorem lt_trans {r s t : Rank} (hrs : Lt r s) (hst : Lt s t) : Lt r t := by
  simp only [Prod.lex_def] at *
  omega

private theorem move_left (na nb nc : Nat) (a b c : WithTop Nat)
    (hab : a ≤ b) (hac : a ≤ c) :
    Lt (pairRank na (nb + nc + 1) a (min b c))
      (pairRank (na + nb + 1) nc (min a b) c) := by
  simp only [pairRank, min_eq_left hab, if_pos hac, if_pos (le_min hab hac), Prod.lex_def]
  have ht : a = c → a = min b c := fun h => h.trans (min_eq_right (h ▸ hab)).symm
  split_ifs <;> try omega
  exact False.elim (‹a ≠ min b c› (ht ‹a = c›))

private theorem move_right (na nb nc : Nat) (a b c : WithTop Nat)
    (hba : b < a) (hbc : b ≤ c) :
    Lt (pairRank (na + nc + 1) nb (min a c) b)
      (pairRank na (nb + nc + 1) a (min b c)) := by
  simp only [pairRank, min_eq_left hbc, if_neg (ne_of_gt hba),
    if_neg (not_le_of_gt hba), Prod.lex_def]
  split_ifs <;> try omega
  exact False.elim (‹min a c ≠ b› (le_antisymm ‹min a c ≤ b› (le_min (le_of_lt hba) hbc)))

private theorem across_right (na nb nc : Nat) (a b c : WithTop Nat)
    (hba : b < a) (hbc : b < c) :
    Lt (pairRank (na + nc + 1) nb (min a c) b)
      (pairRank (na + nb + 1) nc (min a b) c) := by
  simp only [pairRank, min_eq_right (le_of_lt hba), if_neg (ne_of_lt hbc),
    if_pos (le_of_lt hbc), if_neg (ne_of_gt (lt_min hba hbc)),
    if_neg (not_le_of_gt (lt_min hba hbc)), Prod.lex_def, lt_self_iff_false, false_or, true_and]
  omega

private theorem across_left (na nb nc : Nat) (a b c : WithTop Nat)
    (hba : b < a) (hbc : b < c) :
    Lt (pairRank nb (na + nc + 1) b (min a c))
      (pairRank na (nb + nc + 1) a (min b c)) := by
  simp only [pairRank, min_eq_left (le_of_lt hbc), if_neg (ne_of_gt hba),
    if_neg (not_le_of_gt hba), if_neg (ne_of_lt (lt_min hba hbc)),
    if_pos (le_of_lt (lt_min hba hbc)), Prod.lex_def, lt_self_iff_false, false_or, true_and]
  omega

theorem sub1 (a b c : ModExpr) (hab : a.priority ≤ b.priority) (hac : a.priority ≤ c.priority) :
    Lt (rank (.mode a (.compose b c))) (rank (.mode (.leftResidual a b) c)) := by
  simpa [rank, ModExpr.nodes] using move_left a.nodes b.nodes c.nodes _ _ _ hab hac

theorem left1 (a b c : ModExpr) (hab : a.priority ≤ b.priority) (hac : a.priority ≤ c.priority) :
    Lt (rank (.mode a (.rightResidual b c))) (rank (.mode (.compose a b) c)) := by
  simpa [rank, ModExpr.nodes] using move_left a.nodes b.nodes c.nodes _ _ _ hab hac

theorem left2 (a b c : ModExpr) (hba : b.priority ≤ a.priority) (hbc : b.priority ≤ c.priority) :
    Lt (rank (.mode b (.rightResidual a c))) (rank (.mode (.compose a b) c)) := by
  simpa [rank, ModExpr.nodes, Nat.add_comm, min_comm] using
    move_left b.nodes a.nodes c.nodes _ _ _ hba hbc

theorem sub2 (a b c : ModExpr) (hba : b.priority < a.priority) (hbc : b.priority < c.priority) :
    Lt (rank (.mode (.leftResidual a c) b)) (rank (.mode (.leftResidual a b) c)) := by
  simpa [rank, ModExpr.nodes] using across_right a.nodes b.nodes c.nodes _ _ _ hba hbc

theorem right1 (a b c : ModExpr) (hba : b.priority < a.priority) (hbc : b.priority ≤ c.priority) :
    Lt (rank (.mode (.leftResidual a c) b)) (rank (.mode a (.compose b c))) := by
  simpa [rank, ModExpr.nodes] using move_right a.nodes b.nodes c.nodes _ _ _ hba hbc

theorem right2 (a b c : ModExpr) (hca : c.priority < a.priority) (hcb : c.priority < b.priority) :
    Lt (rank (.mode (.leftResidual a b) c)) (rank (.mode a (.compose b c))) := by
  simpa [rank, ModExpr.nodes, Nat.add_comm, min_comm] using
    move_right a.nodes c.nodes b.nodes _ _ _ hca (le_of_lt hcb)

theorem imp1 (a b c : ModExpr) (hca : c.priority < a.priority) (hcb : c.priority ≤ b.priority) :
    Lt (rank (.mode (.compose a b) c)) (rank (.mode a (.rightResidual b c))) := by
  simpa [rank, ModExpr.nodes, Nat.add_comm, min_comm] using
    move_right a.nodes c.nodes b.nodes _ _ _ hca hcb

theorem imp2 (a b c : ModExpr) (hba : b.priority < a.priority) (hbc : b.priority < c.priority) :
    Lt (rank (.mode b (.rightResidual a c))) (rank (.mode a (.rightResidual b c))) := by
  simpa [rank, ModExpr.nodes] using across_left a.nodes b.nodes c.nodes _ _ _ hba hbc

theorem close (a b : ModExpr) (hab : a.priority < b.priority) :
    Lt (rank (.mode (.closeInv b) a)) (rank (.mode (.close a) b)) := by
  simp only [rank, ModExpr.nodes, ModExpr.priority_close, ModExpr.priority_closeInv,
    pairRank, if_neg (ne_of_lt hab), if_pos (le_of_lt hab), if_neg (ne_of_gt hab),
    if_neg (not_le_of_gt hab), Prod.lex_def, lt_self_iff_false, false_or, true_and]
  omega

private theorem first_lt {r s : Rank} (h : r.1 < s.1) : Lt r s :=
  Prod.lex_def.mpr (.inl h)

theorem normalize_rank (c : Constraint) :
    rank c.normalize = rank c ∨ Lt (rank c.normalize) (rank c) := by
  cases c <;> try exact .inl rfl
  case mode a b =>
    have ha := a.normalize_nodes
    have hb := b.normalize_nodes
    by_cases h : a.normalize.nodes + b.normalize.nodes = a.nodes + b.nodes
    · have ha' : a.normalize.nodes = a.nodes := by omega
      have hb' : b.normalize.nodes = b.nodes := by omega
      exact .inl (by simp [Constraint.normalize, rank, ha', hb'])
    · apply Or.inr
      apply first_lt
      change a.normalize.nodes + b.normalize.nodes + 1 < a.nodes + b.nodes + 1
      omega
  case defined a =>
    rcases eq_or_lt_of_le a.normalize_nodes with h | h
    · exact .inl (by simp [Constraint.normalize, rank, h])
    · exact .inr (first_lt h)

theorem normalize_decreases {c d : Constraint} (h : Lt (rank c) (rank d)) :
    Lt (rank c.normalize) (rank d) := by
  rcases normalize_rank c with he | hl
  · rw [he]
    exact h
  · exact lt_trans hl h

theorem defined_left (a b : ModExpr) : Lt (rank (.defined a)) (rank (.mode a b)) := by
  apply first_lt
  change a.nodes < a.nodes + b.nodes + 1
  omega

theorem defined_right (a b : ModExpr) : Lt (rank (.defined b)) (rank (.mode a b)) := by
  apply first_lt
  change b.nodes < a.nodes + b.nodes + 1
  omega

theorem join_left (a b c : ModExpr) : Lt (rank (.mode a c)) (rank (.mode (.join a b) c)) := by
  apply first_lt
  change a.nodes + c.nodes + 1 < a.nodes + b.nodes + 1 + c.nodes + 1
  omega

theorem join_right (a b c : ModExpr) : Lt (rank (.mode b c)) (rank (.mode (.join a b) c)) := by
  apply first_lt
  change b.nodes + c.nodes + 1 < a.nodes + b.nodes + 1 + c.nodes + 1
  omega

theorem meet_left (a b c : ModExpr) : Lt (rank (.mode a b)) (rank (.mode a (.meet b c))) := by
  apply first_lt
  change a.nodes + b.nodes + 1 < a.nodes + (b.nodes + c.nodes + 1) + 1
  omega

theorem meet_right (a b c : ModExpr) : Lt (rank (.mode a c)) (rank (.mode a (.meet b c))) := by
  apply first_lt
  change a.nodes + c.nodes + 1 < a.nodes + (b.nodes + c.nodes + 1) + 1
  omega

private theorem emitted {s : SolverState} {r cs parent}
    (h : ∀ c ∈ cs, Lt (rank c) (rank parent)) :
    ∀ c ∈ (s.emit r cs).pending, c ∈ s.pending ∨ Lt (rank c) (rank parent) :=
  fun c hc => (List.mem_append.mp hc).elim (fun hm => .inr (h c hm)) Or.inl

theorem stepMode_decreases {s a b t} (h : stepMode s a b = .success t) :
    ∀ c ∈ t.pending, c ∈ s.pending ∨ Lt (rank c) (rank (.mode a b)) := by
  simp only [stepMode, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h
  all_goals first | exact fun _ hc => Or.inl hc | apply emitted
  all_goals simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, or_imp, forall_and, forall_eq]
  all_goals repeat' apply And.intro
  all_goals first
    | exact defined_left _ _
    | exact defined_right _ _
    | exact join_left _ _ _
    | exact join_right _ _ _
    | exact meet_left _ _ _
    | exact meet_right _ _ _
    | skip
  all_goals simp_all only [Bool.and_eq_true, bne_iff_ne, ModExpr.minimumLE_iff]
  case h_5.isTrue.refl.h.right => apply sub1 <;> simp_all [ModExpr.priority]
  case h_5.isFalse.isTrue.refl.h.right =>
    apply sub2 <;> simp_all [ModExpr.priority, lt_iff_le_and_ne]
  case h_6.isTrue.refl.h.right =>
    apply imp1 <;> simp_all [ModExpr.priority, lt_iff_le_and_ne]
  case h_6.isFalse.isTrue.refl.h.right =>
    apply imp2 <;> simp_all [ModExpr.priority, lt_iff_le_and_ne]
  case h_7.isTrue.refl.h.right => apply left1 <;> simp_all [ModExpr.priority]
  case h_7.isFalse.isTrue.refl.h.right => apply left2 <;> simp_all [ModExpr.priority]
  case h_8.isTrue.refl.h.right =>
    apply right1 <;> simp_all [ModExpr.priority, lt_iff_le_and_ne]
  case h_8.isFalse.isTrue.refl.h.right =>
    apply right2 <;> simp_all [ModExpr.priority, lt_iff_le_and_ne]
  case h_9.isTrue.refl.h.right =>
    apply close
    simp_all [ModExpr.priority, lt_iff_le_and_ne]

theorem stepMode_normalized_decreases {s a b t} (h : stepMode s a b = .success t) :
    ∀ c ∈ t.pending, c ∈ s.pending ∨ Lt (rank c.normalize) (rank (.mode a b)) := by
  intro c hc
  exact (stepMode_decreases h c hc).imp_right normalize_decreases

end ModeOrientation
end ModalityInference
