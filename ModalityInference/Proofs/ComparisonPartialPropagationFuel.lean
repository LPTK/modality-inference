import ModalityInference.ComparisonPartialPropagation
import Mathlib.Data.List.Count

namespace ModalityInference.ComparisonPartialPropagation

theorem saturate_monotone {mode : ModExpr → ModExpr → Bool} {left right : CompareTy}
    {small large : Nat} {g : Graph} {result : Option Certificate}
    (hle : small ≤ large) (h : saturate mode left right small g = .success result) :
    saturate mode left right large g = .success result := by
  induction small generalizing large g with
  | zero => cases h
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      simp only [saturate] at h ⊢
      split at h
      · next found he => simpa only [he] using h
      · next he =>
        split at h
        · next hc => simpa only [hc, ↓reduceIte] using h
        · next hc =>
          simp only [hc]
          exact ih (by omega) h

def occupancy (xs : Array (Option Certificate)) : Nat := xs.toList.countP Option.isSome

theorem occupancy_le (xs : Array (Option Certificate)) : occupancy xs ≤ xs.size :=
  List.countP_le_length

theorem fold_count (xs : List (Option Certificate)) (n : Nat) :
    xs.foldl (fun k c => if c.isSome then k + 1 else k) n =
      n + xs.countP Option.isSome := by
  induction xs generalizing n with
  | nil => simp
  | cons a xs ih =>
    cases a <;> simp [List.foldl, ih, Nat.add_assoc, Nat.add_comm]

theorem count_eq (g : Graph) : g.count = occupancy g.edges := by
  simp [Graph.count, occupancy, ← Array.foldl_toList, fold_count]

theorem occupancy_set (xs : Array (Option Certificate)) (i : Nat) (c : Certificate) :
    occupancy xs ≤ occupancy (xs.set! i (some c)) := by
  simp only [occupancy, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  by_cases hi : i < xs.toList.length
  · rw [List.countP_set hi]
    simp only [Option.isSome_some, ↓reduceIte]
    split <;> omega
  · simp [List.set_eq_of_length_le (by omega : xs.toList.length ≤ i)]


def Progress (a b : Graph) : Prop :=
  a.nodes = b.nodes ∧ a.edges.size = b.edges.size ∧ a.count ≤ b.count

theorem Progress.refl (g : Graph) : Progress g g := ⟨rfl, rfl, Nat.le_refl _⟩

theorem Progress.trans {a b c : Graph} (hab : Progress a b) (hbc : Progress b c) :
    Progress a c := ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, hab.2.2.trans hbc.2.2⟩

theorem progress_set (g : Graph) (i : Nat) (c : Certificate) :
    Progress g {g with edges := g.edges.set! i (some c)} := by
  refine ⟨rfl, ?_, ?_⟩
  · simp
  · simpa only [count_eq] using occupancy_set g.edges i c

theorem add_progress (g : Graph) (c : Certificate) : Progress g (g.add c) := by
  unfold Graph.add
  dsimp only
  split
  · exact progress_set g _ c
  · exact .refl _

theorem fold_progress {α : Type} (xs : List α) (f : Graph → α → Graph)
    (hf : ∀g x, Progress g (f g x)) (g : Graph) : Progress g (xs.foldl f g) := by
  induction xs generalizing g with
  | nil => exact .refl _
  | cons a xs ih => exact (hf g a).trans (ih (f g a))


def stepGraph : ForInStep Graph → Graph
  | .done g | .yield g => g

theorem forIn_progress {α : Type} (xs : List α)
    (f : α → Graph → Id (ForInStep Graph))
    (hf : ∀x g, Progress g (stepGraph (f x g))) (g : Graph) :
    Progress g ((forIn xs g f).run) := by
  induction xs generalizing g with
  | nil => exact .refl _
  | cons a xs ih =>
    have ha := hf a g
    cases he : f a g with
    | done next => simpa [List.forIn_cons, he, stepGraph] using ha
    | yield next =>
      have hn : Progress g next := by simpa [he, stepGraph] using ha
      simpa [List.forIn_cons, he] using hn.trans (ih next)

theorem closeTransitive_progress (g : Graph) : Progress g g.closeTransitive := by
  simp only [Graph.closeTransitive, Std.Range.forIn_eq_forIn_range', Id.run, bind, pure]
  apply forIn_progress
  intro k g
  dsimp only [stepGraph]
  apply forIn_progress
  intro i g
  split
  · next a he =>
    dsimp only [stepGraph]
    apply forIn_progress
    intro j g
    split
    · split
      · exact progress_set g _ _
      · exact .refl _
    · exact .refl _
  · exact .refl _


theorem step_progress (mode : ModExpr → ModExpr → Bool) (g : Graph) :
    Progress g (g.step mode) := by
  apply (closeTransitive_progress g).trans
  simp only [Graph.step, ← Array.forIn_toList, Id.run, bind, pure]
  apply forIn_progress
  intro a g
  dsimp only [stepGraph]
  apply forIn_progress
  intro b g
  split
  · split
    · exact add_progress g _
    · exact .refl _
  · exact .refl _


theorem count_le (g : Graph) : g.count ≤ g.edges.size := by
  rw [count_eq]
  exact occupancy_le _

theorem saturate_finite {mode : ModExpr → ModExpr → Bool} {left right : CompareTy}
    {budget : Nat} {g : Graph} (space : g.edges.size - g.count < budget) :
    ∃ result, saturate mode left right budget g = .success result := by
  induction budget generalizing g with
  | zero => omega
  | succ budget ih =>
    cases he : g.get left right with
    | some certificate => exact ⟨some certificate, by simp [saturate, he]⟩
    | none =>
      by_cases hc : (g.step mode).count = g.count
      · exact ⟨none, by simp [saturate, he, hc]⟩
      · have hp := step_progress mode g
        have hbound := count_le g
        have hnext := count_le (g.step mode)
        have hspace : (g.step mode).edges.size - (g.step mode).count < budget := by
          have hsize := hp.2.1
          have hcount := hp.2.2
          omega
        obtain ⟨result, hr⟩ := ih hspace
        exact ⟨result, by simpa [saturate, he, hc] using hr⟩

theorem saturate_finite_bound (mode : ModExpr → ModExpr → Bool) (left right : CompareTy)
    (g : Graph) :
    ∃ result, saturate mode left right (g.edges.size + 1) g = .success result :=
  saturate_finite (by omega)

theorem initialGraph_size (assumptions : Bounds) (vertices : List CompareTy) :
    (initialGraph assumptions vertices).edges.size = vertices.length * vertices.length := by
  have h : Progress (Graph.empty vertices) (initialGraph assumptions vertices) := by
    unfold initialGraph
    exact fold_progress _ Graph.add add_progress _
  simpa [Graph.empty] using h.2.1.symm

/-- Each strict propagation round fills a previously empty matrix cell. The
phase therefore stabilizes independently of how many derivations exist. -/
theorem saturate_initial_finite (mode : ModExpr → ModExpr → Bool) (left right : CompareTy)
    (assumptions : Bounds) (vertices : List CompareTy) :
    ∃ result, saturate mode left right (vertices.length * vertices.length + 1)
      (initialGraph assumptions vertices) = .success result := by
  simpa only [initialGraph_size] using
    saturate_finite_bound mode left right (initialGraph assumptions vertices)

end ModalityInference.ComparisonPartialPropagation
