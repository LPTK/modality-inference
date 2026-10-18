import ModalityInference.Proofs.ComparisonSignedCanonical

/-! Exact atom provenance for symbolic signed canonical assignment. Only tuple
coordinates are eliminated; every retained parameter is an original parameter. -/
namespace ModalityInference.ComparisonSignedCanonical
open ComparisonPropagation ComparisonSignedRelations

private theorem append_atoms {left right : CNF} {v : Nat} :
    v∈CNFPropagation.atoms (left++right) ↔
      v∈CNFPropagation.atoms left ∨ v∈CNFPropagation.atoms right := by
  simp [CNFPropagation.atoms]

private theorem rename_atoms {f : Nat→Nat} {cs : CNF} {v : Nat}
    (h : v∈CNFPropagation.atoms (rename f cs)) : ∃w∈CNFPropagation.atoms cs,f w=v := by
  obtain ⟨c,hc,p,hp⟩ := CNFPropagation.mem_atoms.mp h
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  obtain ⟨⟨w,q⟩,hw,he⟩ := List.mem_map.mp hp
  cases he
  exact ⟨w,CNFPropagation.mem_atoms.mpr ⟨d,hd,q,hw⟩,rfl⟩

private theorem join_atoms {left right : CNF} {v : Nat}
    (h : v∈CNFPropagation.atoms (join left right)) :
    v∈CNFPropagation.atoms left ∨ v∈CNFPropagation.atoms right := by
  have hs := join_supported (domain:=CNFPropagation.atoms left++CNFPropagation.atoms right)
    (left:=left) (right:=right)
    (fun v hv=>List.mem_append_left _ hv) (fun v hv=>List.mem_append_right _ hv)
  exact List.mem_append.mp (hs v h)

private theorem negate_atoms {cs : CNF} {v : Nat}
    (h : v∈CNFPropagation.atoms (negate cs)) : v∈CNFPropagation.atoms cs := by
  induction cs with
  | nil => simp [negate,CNFPropagation.atoms] at h
  | cons c cs ih =>
    rcases join_atoms h with hl|hr
    · obtain ⟨d,hd,p,hp⟩ := CNFPropagation.mem_atoms.mp hl
      obtain ⟨⟨w,q⟩,hw,rfl⟩ := List.mem_map.mp hd
      have he : (v,p)=(w,!q) := by simpa only [List.mem_singleton] using hp
      cases he
      exact CNFPropagation.mem_atoms.mpr ⟨c,List.mem_cons_self,q,hw⟩
    · obtain ⟨d,hd,p,hp⟩ := CNFPropagation.mem_atoms.mp (ih hr)
      exact CNFPropagation.mem_atoms.mpr ⟨d,List.mem_cons_of_mem _ hd,p,hp⟩

theorem flip_atoms {lane sign : Nat} {cs : CNF} {v : Nat}
    (h : v∈CNFPropagation.atoms (flip lane sign cs)) : v∈CNFPropagation.atoms cs := by
  obtain ⟨c,hc,p,hp⟩ := CNFPropagation.mem_atoms.mp h
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  obtain ⟨⟨w,q⟩,hw,he⟩ := List.mem_map.mp hp
  have hv : w=v := congrArg Prod.fst he
  subst v
  exact CNFPropagation.mem_atoms.mpr ⟨d,hd,q,hw⟩

theorem plug_atoms {sign : Nat} {left right : Bool} {cs : CNF} {v : Nat}
    (h : v∈CNFPropagation.atoms (plug sign left right cs)) :
    ∃w∈CNFPropagation.atoms cs,v=(if w%3=1 then 3*(w/3) else w) := by
  obtain ⟨c,hc,p,hp⟩ := CNFPropagation.mem_atoms.mp h
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  obtain ⟨⟨w,q⟩,hw,he⟩ := List.mem_map.mp hp
  refine ⟨w,CNFPropagation.mem_atoms.mpr ⟨d,hd,q,hw⟩,?_⟩
  have hv := congrArg Prod.fst he
  by_cases h0 : w%3=0
  · simpa [plugLiteral,h0] using hv.symm
  · by_cases h1 : w%3=1
    · simpa [plugLiteral,h0,h1] using hv.symm
    · simpa [plugLiteral,h0,h1] using hv.symm

theorem quantify_atoms {lane : Nat} {cs : CNF} {v : Nat}
    (h : v∈CNFPropagation.atoms (quantify lane cs)) :
    v∈CNFPropagation.atoms cs ∧ v%3≠lane := by
  obtain ⟨ho,hn⟩ := project_atoms h
  refine ⟨ho,?_⟩
  intro he
  exact hn (by simp [ho,he])

/-- Relational composition retains literal atom identities outside its eliminated
middle tuple. In particular parameter slots are preserved verbatim. -/
theorem compose_atoms {left right : CNF} {v : Nat}
    (h : v∈CNFPropagation.atoms (compose left right)) :
    v∈CNFPropagation.atoms left ∨ v∈CNFPropagation.atoms right := by
  obtain ⟨w,hw,rfl⟩ := rename_atoms h
  obtain ⟨hw,hn⟩ := project_atoms hw
  have hm : w%4≠1 := by
    intro he
    exact hn (by simp [intermediate,hw,he])
  rcases append_atoms.mp hw with hl|hr
  · obtain ⟨z,hz,rfl⟩ := rename_atoms hl
    apply Or.inl
    have he : retained (first z)=z := by
      have hz : z%3<3 := Nat.mod_lt _ (by omega)
      rcases (by omega : z%3=0 ∨ z%3=1 ∨ z%3=2) with h|h|h
      all_goals simp [first,retained,h] at hm ⊢
      all_goals omega
    simpa only [he] using hz
  · obtain ⟨z,hz,rfl⟩ := rename_atoms hr
    apply Or.inr
    have he : retained (second z)=z := by
      have hz : z%3<3 := Nat.mod_lt _ (by omega)
      rcases (by omega : z%3=0 ∨ z%3=1 ∨ z%3=2) with h|h|h
      all_goals simp [second,retained,h] at hm ⊢
      all_goals omega
    simpa only [he] using hz

theorem less_atoms {width v : Nat} (h : v∈CNFPropagation.atoms (less width)) :
    v%3≠2 ∧ v/3<width := by
  induction width with
  | zero => simp [less,CNFPropagation.atoms] at h
  | succ n ih =>
    rcases join_atoms h with hl|hr
    · have he : v=3*n ∨ v=3*n+1 := by simpa [CNFPropagation.atoms] using hl
      rcases he with rfl|rfl <;> simp
      omega
    · rcases append_atoms.mp hr with hl|hr
      · have he : v=3*n ∨ v=3*n+1 := by
          simp [CNFPropagation.atoms] at hl
          tauto
        rcases he with rfl|rfl <;> simp
        omega
      · obtain ⟨hm,hi⟩ := ih hr
        exact ⟨hm,by omega⟩

theorem difference_atoms {sign v : Nat} {cs : CNF}
    (h : v∈CNFPropagation.atoms (difference sign cs)) : v∈CNFPropagation.atoms cs := by
  rcases append_atoms.mp h with h|h
  · exact h
  · exact flip_atoms (negate_atoms h)

theorem bad_atoms {width sign v : Nat} {cs : CNF}
    (h : v∈CNFPropagation.atoms (bad width sign cs)) :
    v∈CNFPropagation.atoms cs ∨ (v%3≠2 ∧ v/3<width) := by
  rcases compose_atoms h with h|h
  · exact .inl (difference_atoms h)
  · exact .inr (less_atoms (negate_atoms h))

/-- Canonical assignment has only input and shared-parameter observations. -/
theorem assignment_atoms {width sign v : Nat} {cs : CNF}
    (h : v∈CNFPropagation.atoms (assignment width sign cs)) :
    v%3≠1 ∧ (v∈CNFPropagation.atoms cs ∨ (v%3=0 ∧ v/3<width)) := by
  obtain ⟨ho,hn⟩ := quantify_atoms h
  refine ⟨hn,?_⟩
  rcases append_atoms.mp ho with h|h
  · rcases append_atoms.mp h with h|h
    · exact .inl (flip_atoms h)
    · exact .inl (negate_atoms h)
  · rcases bad_atoms (negate_atoms h) with h|⟨hm,hi⟩
    · exact .inl h
    · exact .inr ⟨by omega,hi⟩

/-- The residual feasibility formula mentions only original shared parameters. -/
theorem consistent_atoms {sign v : Nat} {cs : CNF}
    (h : v∈CNFPropagation.atoms (consistent sign cs)) :
    v%3=2 ∧ v∈CNFPropagation.atoms cs := by
  obtain ⟨ho,hn⟩ := quantify_atoms (negate_atoms h)
  have hp {left right : Bool} (h : v∈CNFPropagation.atoms (plug sign left right cs)) :
      v%3=2 ∧ v∈CNFPropagation.atoms cs := by
    obtain ⟨w,hw,he⟩ := plug_atoms h
    by_cases h1 : w%3=1
    · simp only [h1,if_true] at he
      have := congrArg (fun n=>n%3) he
      simp at this
      exact False.elim (hn this)
    · simp only [h1,if_false] at he
      subst v
      exact ⟨by omega,hw⟩
  exact (append_atoms.mp ho).elim hp hp


theorem diagonal_atoms {width v : Nat}
    (h : v∈CNFPropagation.atoms (diagonal width)) : v%3≠2 ∧ v/3<width := by
  obtain ⟨c,hc,p,hp⟩ := CNFPropagation.mem_atoms.mp h
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi : i<width := List.mem_range.mp hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp
  all_goals rcases hp with ⟨rfl,_⟩|⟨rfl,_⟩ <;> simp <;> omega

private theorem iterate_atoms {n v : Nat} {edges reached : CNF}
    (h : v∈CNFPropagation.atoms (iterate edges n reached)) :
    v∈CNFPropagation.atoms reached ∨ v∈CNFPropagation.atoms edges := by
  induction n generalizing reached with
  | zero => exact .inl h
  | succ n ih =>
    rcases ih h with h|h
    · rcases join_atoms h with h|h
      · exact .inl h
      · exact compose_atoms h
    · exact .inr h

/-- Closure adds only finite tuple coordinates, never new parameter atoms. -/
theorem closure_atoms {width v : Nat} {edges : CNF}
    (h : v∈CNFPropagation.atoms (closure width edges)) :
    v∈CNFPropagation.atoms edges ∨ (v%3≠2 ∧ v/3<width) := by
  rw [closure,saturate_eq_iterate] at h
  rcases iterate_atoms h with h|h
  · exact .inr (diagonal_atoms h)
  · exact .inl h

theorem closure_assignment_atoms {width sign v : Nat} {edges : CNF}
    (hs : ∀v∈CNFPropagation.atoms edges,v%3≠2 → v/3<width)
    (h : v∈CNFPropagation.atoms (assignment width sign (closure width edges))) :
    (v%3=0 ∧ v/3<width) ∨ (v%3=2 ∧ v∈CNFPropagation.atoms edges) := by
  obtain ⟨hn,ho⟩ := assignment_atoms h
  rcases ho with ho|ho
  · rcases closure_atoms ho with ho|⟨hm,hi⟩
    · by_cases hp : v%3=2
      · exact .inr ⟨hp,ho⟩
      · exact .inl ⟨by omega,hs v ho hp⟩
    · exact .inl ⟨by omega,hi⟩
  · exact .inl ho

theorem closure_consistent_atoms {width sign v : Nat} {edges : CNF}
    (h : v∈CNFPropagation.atoms (consistent sign (closure width edges))) :
    v%3=2 ∧ v∈CNFPropagation.atoms edges := by
  obtain ⟨hm,ho⟩ := consistent_atoms h
  rcases closure_atoms ho with ho|⟨hn,_⟩
  · exact ⟨hm,ho⟩
  · exact False.elim (hn hm)

end ModalityInference.ComparisonSignedCanonical
