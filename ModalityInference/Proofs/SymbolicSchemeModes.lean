import ModalityInference.SymbolicSchemeModes
import ModalityInference.Proofs.SymbolicModes

/-! Exact domains, symbolic actions, and scope of the finite modality witness. -/
namespace ModalityInference.SymbolicSchemeModes

theorem entries_keys {flex} {s : SymbolicModes.Elimination flex} {parameters ms}
    (h : entries s parameters = some ms) : ms.map Prod.fst = parameters.map Prod.fst := by
  induction parameters generalizing ms
  case nil => cases h; rfl
  case cons p rest ih =>
    rcases p with ⟨key, v⟩
    cases hm : s.mode v <;> cases hr : entries s rest <;> simp [entries, hm, hr] at h
    cases h; simp [ih hr]

theorem entries_lookup {flex} {s : SymbolicModes.Elimination flex} {parameters ms}
    (h : entries s parameters = some ms) (key : Nat) :
    ms.lookup key = (parameters.lookup key).bind s.mode := by
  induction parameters generalizing ms
  case nil => cases h; rfl
  case cons p rest ih =>
    rcases p with ⟨k, v⟩
    cases hm : s.mode v <;> cases hr : entries s rest <;> simp [entries, hm, hr] at h
    cases h
    by_cases hk : key = k
    · subst k; simp [hm]
    · have hb : (key == k) = false := by simpa using hk
      simp [List.lookup_cons, hb, ih hr]

theorem entries_supported {flex} {s : SymbolicModes.Elimination flex} {parameters ms}
    (h : entries s parameters = some ms) :
    ∀ p ∈ parameters, (s.mode p.2).isSome = true := by
  induction parameters generalizing ms
  case nil => simp
  case cons p rest ih =>
    rcases p with ⟨k, v⟩
    cases hm : s.mode v <;> cases hr : entries s rest <;> simp [entries, hm, hr] at h
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [hm]
    · exact ih hr p hp

theorem assemble_domain {flex} {s : SymbolicModes.Elimination flex} {parameters σ}
    (h : assemble s parameters = some σ) :
    σ.types = [] ∧ σ.modes.map Prod.fst = parameters.map Prod.fst := by
  cases he : entries s parameters <;> simp [assemble, he] at h
  cases h
  exact ⟨rfl, entries_keys he⟩

theorem assemble_lookup {flex} {s : SymbolicModes.Elimination flex} {parameters σ}
    (h : assemble s parameters = some σ) (key : Nat) :
    σ.modes.lookup key = (parameters.lookup key).bind s.mode := by
  cases he : entries s parameters <;> simp [assemble, he] at h
  cases h
  exact entries_lookup he key

theorem assemble_action {flex} {s : SymbolicModes.Elimination flex} {parameters σ key v}
    (h : assemble s parameters = some σ) (hv : parameters.lookup key = some v) :
    s.mode v = some (σ.mode (.flex key)) := by
  cases he : entries s parameters <;> simp [assemble, he] at h
  cases h
  have hl := entries_lookup he key
  rw [hv, Option.bind_some] at hl
  obtain ⟨xs, ys, hp, _⟩ := List.lookup_eq_some_iff.mp hv
  have hs := entries_supported he (key, v) (by rw [hp]; simp)
  cases hm : s.mode v <;> simp_all [Substitution.mode]

theorem assemble_action_eval {flex} {s : SymbolicModes.Elimination flex} {parameters σ key v}
    (h : assemble s parameters = some σ) (hv : parameters.lookup key = some v)
    (η : ModVar → Mode) :
    (σ.mode (.flex key)).eval (some ∘ η) = some
      ⟨(s.substitute (v.atomIndex 0)).eval (encodeModes η),
        (s.substitute (v.atomIndex 1)).eval (encodeModes η),
        (s.substitute (v.atomIndex 2)).eval (encodeModes η)⟩ :=
  SymbolicModes.Elimination.mode_eval (assemble_action h hv) η

theorem assemble_fixed {flex} {s : SymbolicModes.Elimination flex} {parameters σ key}
    (h : assemble s parameters = some σ) (hv : parameters.lookup key = none) :
    σ.mode (.flex key) = .var (.flex key) := by
  simp [Substitution.mode, assemble_lookup h key, hv]

/-- Every selected image is total; unselected parameters and all rigid variables
retain their original variable expression. -/
theorem assemble_wellFormed {flex} {s : SymbolicModes.Elimination flex} {parameters σ}
    (h : assemble s parameters = some σ) (η : ModVar → Mode) (v : ModVar) :
    (σ.mode v).WellFormed η := by
  cases v
  case rigid => rfl
  case flex key =>
    cases hv : parameters.lookup key
    case none => rw [assemble_fixed h hv]; rfl
    case some v => simp [ModExpr.WellFormed, assemble_action_eval h hv η]

theorem entries_complete {flex} {s : SymbolicModes.Elimination flex} {parameters}
    (h : ∀ p ∈ parameters, (s.mode p.2).isSome = true) :
    ∃ ms, entries s parameters = some ms := by
  induction parameters
  case nil => exact ⟨[], rfl⟩
  case cons p rest ih =>
    rcases p with ⟨key, v⟩
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (h (key, v) (by simp))
    obtain ⟨ms, hms⟩ := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    exact ⟨(key, m) :: ms, by simp [entries, hm, hms]⟩

theorem assemble_iff {flex} (s : SymbolicModes.Elimination flex) (parameters : List (Nat × ModVar)) :
    (∃ σ, assemble s parameters = some σ) ↔
      ∀ p ∈ parameters, (s.mode p.2).isSome = true := by
  constructor
  · rintro ⟨σ, h⟩
    cases he : entries s parameters <;> simp [assemble, he] at h
    exact entries_supported he
  · intro h
    obtain ⟨ms, he⟩ := entries_complete h
    exact ⟨{modes := ms}, by simp [assemble, he]⟩

theorem atomVariable_reencode (i : Nat) :
    (SymbolicModes.atomVariable i).atomIndex (i % 3) = i := by
  by_cases h : i / 3 % 2 = 0 <;>
    simp [SymbolicModes.atomVariable, h, ModVar.atomIndex] <;> omega

theorem substitute_no_flexible_atoms {flex e s}
    (h : SymbolicModes.eliminate flex e = some s) {v : Nat} (hv : v ∈ flex) :
    ∀ i ∈ (s.substitute v).atoms, i ∉ flex := by
  obtain ⟨j, hj⟩ := HornPropagation.atomFin_exists hv
  simpa [SymbolicModes.Elimination.substitute, hj] using
    (SymbolicModes.eliminate_no_flexible_atoms h).1 j

theorem reify_excludes {flex e s}
    (h : SymbolicModes.eliminate flex e = some s) {v : Nat} (hv : v ∈ flex)
    {axis m} (hr : SymbolicModes.reify axis (s.substitute v) = some m) {w : ModVar}
    (hw : ∀ a < 3, w.atomIndex a ∈ flex) : w ∉ m.vars := by
  intro hm
  obtain ⟨i, hi, he⟩ := SymbolicModes.reify_variables hr w hm
  apply substitute_no_flexible_atoms h hv i hi
  have ha := hw (i % 3) (Nat.mod_lt _ (by decide))
  rwa [← he, atomVariable_reencode] at ha

theorem mode_excludes {flex e s}
    (h : SymbolicModes.eliminate flex e = some s) {v m} (hm : s.mode v = some m)
    (hv : ∀ a < 3, v.atomIndex a ∈ flex) {w : ModVar}
    (hw : ∀ a < 3, w.atomIndex a ∈ flex) : w ∉ m.vars := by
  cases hl : SymbolicModes.reify .locality (s.substitute (v.atomIndex 0)) <;>
    cases ha : SymbolicModes.reify .affinity (s.substitute (v.atomIndex 1)) <;>
    cases hu : SymbolicModes.reify .uniqueness (s.substitute (v.atomIndex 2)) <;>
    simp [SymbolicModes.Elimination.mode, hl, ha, hu] at hm
  cases hm
  simp only [ModExpr.vars, Finset.mem_union, not_or]
  exact ⟨reify_excludes h (hv 0 (by decide)) hl hw,
    reify_excludes h (hv 1 (by decide)) ha hw,
    reify_excludes h (hv 2 (by decide)) hu hw⟩

/-- An assembled image mentions no variable whose three coordinates were
eliminated. Ambient variables outside that domain remain available. -/
theorem assemble_excludes {flex e s parameters σ key v}
    (he : SymbolicModes.eliminate flex e = some s)
    (ha : assemble s parameters = some σ) (hv : parameters.lookup key = some v)
    (hcoords : ∀ a < 3, v.atomIndex a ∈ flex) {w : ModVar}
    (hw : ∀ a < 3, w.atomIndex a ∈ flex) : w ∉ (σ.mode (.flex key)).vars :=
  mode_excludes he (assemble_action ha hv) hcoords hw

end ModalityInference.SymbolicSchemeModes
