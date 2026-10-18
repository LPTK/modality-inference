import ModalityInference.ComparisonLatticeCompiler
import ModalityInference.Proofs.ComparisonStructuralLattice

/-! Exact symbolic clauses and algebraic reconstruction for finite lattice
forms over common-shape structural bases. -/
namespace ModalityInference.ComparisonLatticeCompiler

open ComparisonAlgebra ComparisonControls ComparisonPropagation ComparisonStructuralLattice

theorem compile_atom {b : Basis} {a : CompareTy} (ha : a ∈ b.types) :
    compile b a = some [[(b.types.idxOf a, true)]] := by
  cases a <;> simp [compile, ha]

theorem compile_complete {b : Basis} {a : CompareTy} (ha : LatticeForm b.types a) :
    ∃ clauses, compile b a = some clauses := by
  induction ha with
  | atom ha => exact ⟨_, compile_atom ha⟩
  | @join a c ha hc iha ihc =>
    by_cases hm : CompareTy.join a c ∈ b.types
    · exact ⟨_, compile_atom hm⟩
    · obtain ⟨left, hl⟩ := iha
      obtain ⟨right, hr⟩ := ihc
      simp [compile, hm, hl, hr]
  | @meet a c ha hc iha ihc =>
    by_cases hm : CompareTy.meet a c ∈ b.types
    · exact ⟨_, compile_atom hm⟩
    · obtain ⟨left, hl⟩ := iha
      obtain ⟨right, hr⟩ := ihc
      simp [compile, hm, hl, hr]

theorem compile_polynomial {b : Basis} {a : CompareTy} {clauses : CNF}
    (h : compile b a = some clauses) : LatticeForm b.types a ∧ Polynomial b clauses := by
  induction a generalizing clauses
  all_goals
    simp only [compile] at h
    split at h
    next hatom =>
      have hm := List.contains_iff_mem.mp hatom
      cases Option.some.inj h
      exact ⟨.atom hm, .atom (List.idxOf_lt_length_of_mem hm)⟩
    next hnot =>
      first
      | contradiction
      | rename_i a c iha ihc
        cases hl : compile b a <;> simp [hl] at h
        rename_i left
        cases hr : compile b c <;> simp [hr] at h
        rename_i right
        subst clauses
        first
        | exact ⟨.join (iha hl).1 (ihc hr).1, (iha hl).2.join (ihc hr).2⟩
        | exact ⟨.meet (iha hl).1 (ihc hr).1, (iha hl).2.meet (ihc hr).2⟩

theorem basisValue_index {basis : List CompareTy} {a : CompareTy}
    (ha : a ∈ basis) (value : CompareTy → Bool) :
    basisValue basis value (basis.idxOf a) = value a := by
  have hi := List.idxOf_lt_length_of_mem ha
  have he : basis[basis.idxOf a] = a := by
    simpa only [List.idxOf, beq_iff_eq] using
      (List.findIdx_getElem (xs := basis) (p := (· == a)) (w := hi))
  simp [basisValue, List.getElem?_eq_getElem hi, he]


theorem compile_value {b : Basis} {a : CompareTy} {clauses : CNF}
    (h : compile b a = some clauses) (value : CompareTy → Bool)
    (hj : ∀x y, value (.join x y) = (value x || value y))
    (hm : ∀x y, value (.meet x y) = (value x && value y)) :
    CNFHolds (basisValue b.types value) clauses ↔ value a = true := by
  induction a generalizing clauses
  all_goals
    simp only [compile] at h
    split at h
    next hatom =>
      have ha := List.contains_iff_mem.mp hatom
      cases Option.some.inj h
      simp [CNFHolds, ClauseHolds, basisValue_index ha value]
    next hnot =>
      first
      | contradiction
      | rename_i a c iha ihc
        cases hl : compile b a <;> simp [hl] at h
        rename_i left
        cases hr : compile b c <;> simp [hr] at h
        rename_i right
        subst clauses
        first
        | rw [join_correct, iha hl, ihc hr, hj, Bool.or_eq_true]
        | rw [meet_correct, iha hl, ihc hr, hm, Bool.and_eq_true]

theorem compile_correct {Δ : Bounds} {shape : ComparisonShape} {b : Basis}
    (hb : ∀t∈b.types, Representable Δ shape t)
    {a : CompareTy} {clauses : CNF} (h : compile b a = some clauses) :
    ∃ t, reify b.types clauses = some t ∧ Representable Δ shape t ∧ Equiv Δ t a := by
  obtain ⟨ha, hp⟩ := compile_polynomial h
  obtain ⟨t, ht⟩ := hp.reify
  have hat := ComparisonStructuralLattice.lattice_representable hb ha
  have htt : Representable Δ shape t := reify_property ht (Representable Δ shape)
    hb (fun _ _ => representable_typeOp true)
    (fun _ _ => representable_typeOp false)
  have he (f : LatticeHom (Order Δ shape) Bool) : booleanValue f t = booleanValue f a := by
    exact Bool.eq_iff_iff.mpr ((reify_correct ht (booleanValue f)
      (booleanValue_join f) (booleanValue_meet f)).trans
      (compile_value h (booleanValue f) (booleanValue_join f) (booleanValue_meet f)))
  refine ⟨t, ht, htt, ?_, ?_⟩
  · apply (subtype_iff_boolean_observers (represented htt) (represented hat)).mpr
    intro f
    simpa only [booleanValue_represented f _ htt, booleanValue_represented f _ hat] using
      le_of_eq (he f)
  · apply (subtype_iff_boolean_observers (represented hat) (represented htt)).mpr
    intro f
    simpa only [booleanValue_represented f _ htt, booleanValue_represented f _ hat] using
      le_of_eq (he f).symm

end ModalityInference.ComparisonLatticeCompiler
