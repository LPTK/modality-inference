import ModalityInference.Proofs.ComparisonStructuralControls

/-! Signed basis controls and their lattice polynomials remain inside the
modal grammar of the same finite heads. -/
namespace ModalityInference.ComparisonControls

private theorem list_generated {b : Basis} (isJoin : Bool)
    (head : CompareTy) (rest : List CompareTy) (hh : ∀a∈head::rest, a∈b.heads) :
    ∃g : Generated b, g.term =
      (if isJoin then ComparisonInterpolation.join head rest else ComparisonInterpolation.meet head rest) := by
  induction rest generalizing head with
  | nil => exact ⟨.head head (hh _ List.mem_cons_self), by cases isJoin <;> rfl⟩
  | cons next rest ih =>
    obtain ⟨g, hg⟩ := ih next (fun a ha => hh a (List.mem_cons_of_mem _ ha))
    cases isJoin
    · exact ⟨.meet (.head head (hh _ List.mem_cons_self)) g,
        by simpa only [Generated.term, ComparisonInterpolation.meet] using congrArg (CompareTy.meet head) hg⟩
    · exact ⟨.join (.head head (hh _ List.mem_cons_self)) g,
        by simpa only [Generated.term, ComparisonInterpolation.join] using congrArg (CompareTy.join head) hg⟩

private theorem modal_generated {b : Basis} {a : CompareTy} (h : ∃g : Generated b, g.term=a)
    (m : ModExpr) (hm : ∀v∈m.freeVariables, v∈b.modes) :
    ∃g : Generated b, g.term=.modal a m := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨.modal g m hm, rfl⟩

/-- Every signed control is built from the original finite heads. -/
theorem Basis.types_generated (b : Basis) {a : CompareTy} (ha : a∈b.types) :
    ∃g : Generated b, g.term=a := by
  have hlo : ∃g : Generated b, g.term=b.bottom := by
    exact modal_generated (list_generated false b.head b.rest (fun _ => id))
      (.const Mode.bottom) (by simp [ModExpr.freeVariables])
  have hhi : ∃g : Generated b, g.term=b.top := by
    exact modal_generated (list_generated true b.head b.rest (fun _ => id))
      (.const Mode.top) (by simp [ModExpr.freeVariables])
  obtain ⟨key, hk, rfl⟩ := List.mem_map.mp ha
  cases key with
  | head a =>
    exact ⟨.head a (by simpa [Basis.keys] using hk), rfl⟩
  | bottom => exact hlo
  | top => exact hhi
  | raised => exact modal_generated hlo (.const Mode.top) (by simp [ModExpr.freeVariables])
  | localFloor => exact modal_generated hhi (.const Mode.global) (by simp [ModExpr.freeVariables])
  | affineFloor => exact modal_generated hhi (.const Mode.many) (by simp [ModExpr.freeVariables])
  | control c =>
    have hc : c ∈ b.modes.flatMap controls := by simpa [Basis.keys] using hk
    obtain ⟨v, hv, hc⟩ := List.mem_flatMap.mp hc
    apply modal_generated
    · split <;> assumption
    · intro w hw
      have hw' := (ModExpr.mem_freeVariables _ _).mp hw
      rw [control_vars] at hw'
      have he := Finset.mem_singleton.mp hw'
      exact he ▸ ((controls_name_mem hc).symm ▸ hv)

/-- Lattice closure can be embedded in any modal grammar containing its atoms. -/
theorem LatticeForm.generated {as : List CompareTy} {a : CompareTy} {b : Basis}
    (ha : LatticeForm as a) (hs : ∀t∈as, ∃g : Generated b, g.term=t) :
    ∃g : Generated b, g.term=a := by
  induction ha with
  | atom ha => exact hs _ ha
  | join hl hr ihl ihr =>
    obtain ⟨l, rfl⟩ := ihl
    obtain ⟨r, rfl⟩ := ihr
    exact ⟨.join l r, rfl⟩
  | meet hl hr ihl ihr =>
    obtain ⟨l, rfl⟩ := ihl
    obtain ⟨r, rfl⟩ := ihr
    exact ⟨.meet l r, rfl⟩

end ModalityInference.ComparisonControls
