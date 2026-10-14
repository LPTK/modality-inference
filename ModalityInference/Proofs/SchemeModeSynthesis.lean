import ModalityInference.SchemeModeSynthesis
import ModalityInference.Proofs.ModalSynthesis

/-! The finite modality substitution acts exactly like the synthesized coordinate
witness. The full original formula therefore holds under its actual modal action. -/
namespace ModalityInference.SchemeModeSynthesis

theorem atomIndex_injective {v w : ModVar} {a b : Nat} (ha : a < 3) (hb : b < 3)
    (h : v.atomIndex a = w.atomIndex b) : v = w ∧ a = b := by
  cases v <;> cases w <;> simp [ModVar.atomIndex] at h ⊢ <;> omega

theorem mem_atoms_iff {modeIds : List Nat} {v : ModVar} {a : Nat} (ha : a < 3) :
    v.atomIndex a ∈ atoms modeIds ↔ ∃ n ∈ modeIds, v = .flex n := by
  simp only [atoms, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨n, hn, b, hb, he⟩
    exact ⟨n, hn, (atomIndex_injective ha hb he.symm).1⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, a, ha, rfl⟩

@[simp] theorem mem_atoms_flex {modeIds : List Nat} {n a : Nat} (ha : a < 3) :
    (ModVar.flex n).atomIndex a ∈ atoms modeIds ↔ n ∈ modeIds := by
  simp [mem_atoms_iff ha]

@[simp] theorem not_mem_atoms_rigid {modeIds : List Nat} {n a : Nat} (ha : a < 3) :
    (ModVar.rigid n).atomIndex a ∉ atoms modeIds := by
  simp [mem_atoms_iff ha]

theorem parameters_lookup {modeIds : List Nat} {n : Nat} (hn : n ∈ modeIds) :
    (parameters modeIds).lookup n = some (.flex n) := by
  induction modeIds with
  | nil => simp at hn
  | cons m ms ih =>
    by_cases he : n = m
    · subst n
      simp [parameters]
    · have hb : (n == m) = false := by simpa using he
      simpa [parameters, List.lookup_cons, hb] using ih ((List.mem_cons.mp hn).resolve_left he)

theorem parameters_lookup_none {modeIds : List Nat} {n : Nat} (hn : n ∉ modeIds) :
    (parameters modeIds).lookup n = none := by
  induction modeIds with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.mem_cons, not_or] at hn
    have hb : (n == m) = false := by simpa using hn.1
    simpa [parameters, List.lookup_cons, hb] using ih hn.2

theorem run_spec {fuel modeIds formula result}
    (h : run fuel modeIds formula = .success result) :
    ∃ images : SymbolicModes.Elimination (atoms modeIds),
      ModalSynthesis.synthesize fuel (atoms modeIds) formula = .success images ∧
      SymbolicSchemeModes.assemble images (parameters modeIds) = some result.substitution ∧
      result.flexibleAtoms = atoms modeIds ∧
      result.query = SymbolicCNF.substitute images.substitute formula := by
  unfold run at h
  cases hs : ModalSynthesis.synthesize fuel (atoms modeIds) formula <;>
    simp [hs, bind, pure, RunResult.bind] at h
  rename_i images
  cases ha : SymbolicSchemeModes.assemble images (parameters modeIds) <;> simp [ha] at h
  cases h
  exact ⟨images, rfl, ha, rfl, rfl⟩

theorem run_query_valid {fuel modeIds formula result}
    (h : run fuel modeIds formula = .success result) (ρ : Nat → Bool) :
    result.query.eval ρ = true := by
  obtain ⟨images, hs, _, _, hq⟩ := run_spec h
  rw [hq, SymbolicCNF.substitute_eval]
  exact ModalSynthesis.synthesize_sound hs ρ

theorem run_domain {fuel modeIds formula result}
    (h : run fuel modeIds formula = .success result) :
    result.substitution.types = [] ∧ result.substitution.modes.map Prod.fst = modeIds ∧
      result.flexibleAtoms = atoms modeIds := by
  obtain ⟨images, _, ha, hatoms, _⟩ := run_spec h
  have hd := SymbolicSchemeModes.assemble_domain ha
  exact ⟨hd.1, by simpa [parameters, List.map_map, Function.comp_def] using hd.2, hatoms⟩

theorem run_excludes {fuel modeIds formula result}
    (h : run fuel modeIds formula = .success result) {n w : Nat}
    (hn : n ∈ modeIds) (hw : w ∈ modeIds) :
    ModVar.flex w ∉ (result.substitution.mode (.flex n)).vars := by
  obtain ⟨images, hs, ha, _, _⟩ := run_spec h
  exact ModalSynthesis.assemble_excludes hs ha (parameters_lookup hn)
    (fun a ha => (mem_atoms_flex ha).mpr hn) (fun a ha => (mem_atoms_flex ha).mpr hw)

theorem images_fixed {flex : List Nat} (images : SymbolicModes.Elimination flex)
    {i : Nat} (hi : i ∉ flex) : images.substitute i = .atom i := by
  cases hf : ConcreteBackend.atomFin flex i with
  | none => simp [SymbolicModes.Elimination.substitute, hf]
  | some j =>
    have hj : flex[j.val] = i := ConcreteBackend.atomFin_lookup hf
    exact (hi (hj ▸ List.getElem_mem j.isLt)).elim

theorem encodeModes_projectedModes (ρ : Nat → Bool) : encodeModes (projectedModes ρ) = ρ := by
  funext i
  have hi := congrArg ρ (SymbolicSchemeModes.atomVariable_reencode i)
  have hr : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  all_goals simpa [encodeModes, projectedModes, SymbolicModes.atomVariable, hr] using hi

theorem projected_images_fixed {flex : List Nat} (images : SymbolicModes.Elimination flex)
    (η : ModVar → Mode) {v : ModVar} (hv : ∀ a < 3, v.atomIndex a ∉ flex) :
    projectedModes (fun i => (images.substitute i).eval (encodeModes η)) v = η v := by
  simpa [projectedModes, images_fixed images (hv 0 (by decide)),
    images_fixed images (hv 1 (by decide)), images_fixed images (hv 2 (by decide)),
    BoolExpr.eval] using congrFun (projectedModes_encodeModes η) v

/-- Every assembled image, including the identity action outside its finite
domain, evaluates to the three synthesized Boolean coordinates. -/
theorem assemble_eval {modeIds : List Nat} {images : SymbolicModes.Elimination (atoms modeIds)}
    {σ : Substitution} (ha : SymbolicSchemeModes.assemble images (parameters modeIds) = some σ)
    (η : ModVar → Mode) (v : ModVar) :
    (σ.mode v).eval (some ∘ η) =
      some (projectedModes (fun i => (images.substitute i).eval (encodeModes η)) v) := by
  cases v with
  | flex n =>
    by_cases hn : n ∈ modeIds
    · exact SymbolicSchemeModes.assemble_action_eval ha (parameters_lookup hn) η
    · rw [SymbolicSchemeModes.assemble_fixed ha (parameters_lookup_none hn)]
      simpa [ModExpr.eval] using congrArg some
        (projected_images_fixed images η (fun a ha => by simpa [mem_atoms_flex ha] using hn)).symm
  | rigid n =>
    simpa [Substitution.mode, ModExpr.eval] using congrArg some
      (projected_images_fixed images η (fun a ha => not_mem_atoms_rigid ha)).symm

/-- The original formula is true under the actual finite `ModExpr` substitution,
with all images defined. No Boolean-only witness is needed by the caller. -/
theorem run_actual {fuel modeIds formula result}
    (h : run fuel modeIds formula = .success result) (η : ModVar → Mode) :
    ∃ τ : ModVar → Mode,
      (∀ v, (result.substitution.mode v).eval (some ∘ η) = some (τ v)) ∧
      formula.eval (encodeModes τ) = true := by
  obtain ⟨images, hs, ha, _, _⟩ := run_spec h
  refine ⟨projectedModes (fun i => (images.substitute i).eval (encodeModes η)),
    assemble_eval ha η, ?_⟩
  rw [encodeModes_projectedModes]
  exact ModalSynthesis.synthesize_sound hs (encodeModes η)

theorem run_actual_valid {fuel modeIds formula result}
    (h : run fuel modeIds formula = .success result) {η τ : ModVar → Mode}
    (hτ : ∀ v, (result.substitution.mode v).eval (some ∘ η) = some (τ v)) :
    formula.eval (encodeModes τ) = true := by
  obtain ⟨τ', hτ', hvalid⟩ := run_actual h η
  have he : τ = τ' := by
    funext v
    exact Option.some.inj ((hτ v).symm.trans (hτ' v))
  simpa [he] using hvalid

theorem run_query_excludes {fuel modeIds formula result}
    (h : run fuel modeIds formula = .success result) {i : Nat}
    (hi : i ∈ result.flexibleAtoms) : i ∉ result.query.atoms := by
  obtain ⟨images, hs, _, hatoms, hq⟩ := run_spec h
  rw [hatoms] at hi
  rw [hq]
  intro hq
  obtain ⟨v, _, hv⟩ := SymbolicCNF.substitute_atoms hq
  by_cases hf : v ∈ atoms modeIds
  · exact (ModalSynthesis.synthesize_support hs hv).2 hf hi
  · rw [images_fixed images hf] at hv
    have hiv : i = v := by simpa [BoolExpr.atoms] using hv
    exact hf (hiv ▸ hi)

theorem run_of_synthesize {fuel modeIds formula images}
    (h : ModalSynthesis.synthesize fuel (atoms modeIds) formula = .success images) :
    ∃ result, run fuel modeIds formula = .success result := by
  obtain ⟨σ, ha⟩ := ModalSynthesis.synthesize_assembles h (parameters modeIds)
  exact ⟨⟨σ, atoms modeIds, SymbolicCNF.substitute images.substitute formula⟩,
    by simp [run, h, ha, bind, pure, RunResult.bind]⟩

theorem run_complete {modeIds : List Nat} {formula : BoolExpr}
    {s : (Nat → Bool) → Nat → Bool} (hs : ModalSynthesis.Uniform ModalSynthesis.locality (atoms modeIds) s)
    (h : ∀ ρ, formula.eval (s ρ) = true) :
    ∃ n, ∀ fuel ≥ n, ∃ result, run fuel modeIds formula = .success result := by
  obtain ⟨n, hn⟩ := ModalSynthesis.synthesize_complete hs h
  exact ⟨n, fun fuel hf => let ⟨_, hr⟩ := hn fuel hf; run_of_synthesize hr⟩

theorem run_iff (modeIds : List Nat) (formula : BoolExpr) :
    (∃ fuel result, run fuel modeIds formula = .success result) ↔
      ∃ s, ModalSynthesis.Uniform ModalSynthesis.locality (atoms modeIds) s ∧
        ∀ ρ, formula.eval (s ρ) = true := by
  constructor
  · rintro ⟨fuel, result, h⟩
    obtain ⟨images, hs, _, _, _⟩ := run_spec h
    exact (ModalSynthesis.synthesize_iff _ _).mp ⟨fuel, images, hs⟩
  · rintro ⟨s, hs, h⟩
    obtain ⟨n, hn⟩ := run_complete hs h
    obtain ⟨result, hr⟩ := hn n le_rfl
    exact ⟨n, result, hr⟩

theorem run_monotone {n modeIds formula result}
    (h : run n modeIds formula = .success result) :
    ∀ fuel ≥ n, run fuel modeIds formula = .success result := by
  intro fuel hf
  obtain ⟨images, hs, ha, hatoms, hq⟩ := run_spec h
  have hs' := ModalSynthesis.synthesize_monotone hs fuel hf
  cases result
  simp_all [run, bind, pure, RunResult.bind]

theorem run_terminates (modeIds : List Nat) (formula : BoolExpr) :
    ∃ n, ∀ fuel ≥ n, run fuel modeIds formula ≠ .exhausted := by
  obtain ⟨n, hn⟩ := ModalSynthesis.synthesize_terminates (atoms modeIds) formula
  refine ⟨n, fun fuel hf => ?_⟩
  cases hs : ModalSynthesis.synthesize fuel (atoms modeIds) formula with
  | exhausted => exact (hn fuel hf hs).elim
  | rejected message => simp [run, hs, bind, RunResult.bind]
  | success images =>
    obtain ⟨result, hr⟩ := run_of_synthesize hs
    simp [hr]

end ModalityInference.SchemeModeSynthesis
