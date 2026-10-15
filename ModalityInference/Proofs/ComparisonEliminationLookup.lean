import ModalityInference.Proofs.ComparisonGroupExtraction
import ModalityInference.Proofs.ComparisonElimination

/-! The combined substitution retains each group's exact reconstructed image. -/
namespace ModalityInference.ComparisonElimination

private theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => simp at hx
  | cons hr h ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, hr⟩ := ih hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

private theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => simp at hy
  | cons hr h ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨x, hx, hr⟩ := ih hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

private theorem zip_values_unique {α β : Type} {keys : List α} {values : List β}
    (hn : keys.Nodup) {key : α} {a b : β}
    (ha : (key, a) ∈ keys.zip values) (hb : (key, b) ∈ keys.zip values) : a = b := by
  induction keys generalizing values with
  | nil => simp at ha
  | cons k keys ih =>
    cases values with
    | nil => simp at ha
    | cons v values =>
      have hn := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ha with hheadA | htailA
      · cases hheadA
        rcases List.mem_cons.mp hb with hheadB | htailB
        · exact (Prod.mk.inj hheadB).2.symm
        · exact False.elim (hn.1 (List.of_mem_zip htailB).1)
      · rcases List.mem_cons.mp hb with hheadB | htailB
        · cases hheadB
          exact False.elim (hn.1 (List.of_mem_zip htailA).1)
        · exact ih hn.2 htailA htailB

private theorem lookup_of_unique {β : Type} {entries : List (Nat × β)} {n : Nat} {value : β}
    (hmem : (n, value) ∈ entries)
    (hunique : ∀ other, (n, other) ∈ entries → other = value) : entries.lookup n = some value := by
  induction entries with
  | nil => simp at hmem
  | cons entry entries ih =>
    rcases entry with ⟨key, image⟩
    by_cases he : n = key
    · have hv := hunique image (by simp [he])
      simp [he, hv]
    · have ht : (n, value) ∈ entries := (List.mem_cons.mp hmem).resolve_left (by
        intro hx
        exact he (congrArg Prod.fst hx))
      have hne : (n == key) = false := beq_eq_false_iff_ne.mpr he
      simpa only [List.lookup_cons, hne] using
        ih ht (fun other ho => hunique other (List.mem_cons_of_mem _ ho))

theorem GroupTrace.image_mem {fuel assumptions required g output}
    (trace : GroupTrace fuel assumptions required g output) (i : Fin g.leaves.length) :
    (g.leaves[i], trace.reduction.images[i]) ∈ output.types := by
  rw [trace.types_eq]
  apply List.mem_iff_getElem.mpr
  refine ⟨i.val, ?_, ?_⟩
  · simp [List.length_zip, i.isLt]
  · simp

theorem run_group_image {fuel p shapes templates reduced result groups g output}
    (h : run fuel p shapes templates reduced = .success result)
    (hc : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hn : (templates.leaves.map (·.name)).Nodup)
    (hname : ∀ a ∈ templates.leaves, ∀ b ∈ templates.leaves, a.name = b.name → a = b)
    (hg : g ∈ groups) (trace : GroupTrace fuel p.assumptions reduced.modes g output)
    (hgo : group fuel p.assumptions reduced.modes g = .success output)
    (i : Fin g.leaves.length) :
    result.types.lookup g.leaves[i] = some trace.reduction.images[i] := by
  obtain ⟨gs, outputs, hcollect, houtputs, htypes, _⟩ := run_spec h
  have hgs : gs = groups := RunResult.success.inj (hcollect.symm.trans hc)
  subst gs
  obtain ⟨own, hown, he⟩ := forall₂_mem_left houtputs hg
  have heq : own = output := RunResult.success.inj (he.symm.trans hgo)
  subst own
  apply lookup_of_unique
  · rw [htypes]
    exact List.mem_flatMap.mpr ⟨output, hown, trace.image_mem i⟩
  · intro other ho
    rw [htypes] at ho
    obtain ⟨another, hanother, hentry⟩ := List.mem_flatMap.mp ho
    obtain ⟨otherGroup, hotherGroup, hrun⟩ := forall₂_mem_right houtputs hanother
    have hleaf : g.leaves[i] ∈ otherGroup.leaves := by
      rw [← group_domain hrun]
      exact List.mem_map_of_mem hentry
    have hgroup := ComparisonGroups.collect_leaf_shared hc hname hg hotherGroup
      (List.getElem_mem _) hleaf
    subst otherGroup
    have hresult : another = output := RunResult.success.inj (hrun.symm.trans hgo)
    subst another
    rw [trace.types_eq] at hentry
    apply zip_values_unique (ComparisonGroups.collect_leaves_nodup hc hn g hg) hentry
    exact trace.types_eq ▸ trace.image_mem i

end ModalityInference.ComparisonElimination
