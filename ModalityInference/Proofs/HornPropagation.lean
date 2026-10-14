import ModalityInference.HornPropagation
import ModalityInference.Proofs.ModeWitness

/-! Direct Horn translation and least-model consistency, without CNF or
assignment search. Unsupported syntax has an explicit domain predicate. -/
namespace ModalityInference.HornPropagation

theorem positive_eval {atoms e r} (h : positive atoms e = some r)
    (σ : Nat → Bool) (env : Mapping Bool atoms.length)
    (hσ : ∀ v i, ConcreteBackend.atomFin atoms v = some i → env.get i = σ v) :
    LeftExpr.eval env r = e.eval σ := by
  induction e generalizing r
  case and a b iha ihb | or a b iha ihb =>
    cases ha : positive atoms a <;> cases hb : positive atoms b <;>
      simp [positive, ha, hb] at h
    all_goals cases h; simp only [LeftExpr.eval, BoolExpr.eval, iha ha, ihb hb]; rfl
  case const b => cases h; rfl
  case imp => cases h
  case atom v =>
    cases hi : ConcreteBackend.atomFin atoms v <;> simp [positive, hi] at h
    cases h; exact hσ _ _ hi

theorem horn_eval {atoms e r} (h : horn atoms e = some r)
    (σ : Nat → Bool) (env : Mapping Bool atoms.length)
    (hσ : ∀ v i, ConcreteBackend.atomFin atoms v = some i → env.get i = σ v) :
    RightExpr.eval env r = e.eval σ := by
  induction e generalizing r
  case imp a b iha ihb =>
    cases ha : positive atoms a <;> cases hb : horn atoms b <;>
      simp [horn, ha, hb] at h
    cases h
    simp only [RightExpr.eval, BoolExpr.eval, positive_eval ha σ env hσ, ihb hb]
    cases a.eval σ <;> cases b.eval σ <;> rfl
  case and a b iha ihb =>
    cases ha : horn atoms a <;> cases hb : horn atoms b <;> simp [horn, ha, hb] at h
    cases h; simp only [RightExpr.eval, BoolExpr.eval, iha ha, ihb hb]; rfl
  case const b => cases h; rfl
  case or => cases h
  case atom v =>
    cases hi : ConcreteBackend.atomFin atoms v <;> simp [horn, hi] at h
    cases h; exact hσ _ _ hi

theorem atomFin_exists {atoms : List Nat} {v} (hv : v ∈ atoms) :
    ∃ i, ConcreteBackend.atomFin atoms v = some i := by
  have hi := List.idxOf_lt_length_iff.mpr hv
  exact ⟨⟨atoms.idxOf v, hi⟩, by simp [ConcreteBackend.atomFin, hi]⟩

theorem positive_sound {atoms e r} (h : positive atoms e = some r) :
    e.IsPositive := by
  induction e generalizing r
  case and a b iha ihb | or a b iha ihb =>
    cases ha : positive atoms a <;> cases hb : positive atoms b <;>
      simp [positive, ha, hb] at h
    all_goals first | exact .and (iha ha) (ihb hb) | exact .or (iha ha) (ihb hb)
  case const => exact .const _
  case atom => exact .atom _
  case imp => cases h

theorem horn_sound {atoms e r} (h : horn atoms e = some r) : e.IsHorn := by
  induction e generalizing r
  case imp a b iha ihb =>
    cases ha : positive atoms a <;> cases hb : horn atoms b <;>
      simp [horn, ha, hb] at h
    exact .imp (positive_sound ha) (ihb hb)
  case and a b iha ihb =>
    cases ha : horn atoms a <;> cases hb : horn atoms b <;> simp [horn, ha, hb] at h
    exact .and (iha ha) (ihb hb)
  case const => exact .const _
  case atom => exact .atom _
  case or => cases h

theorem positive_complete {atoms e} (h : e.IsPositive)
    (hmem : ∀ v ∈ e.atoms, v ∈ atoms) : ∃ r, positive atoms e = some r := by
  induction h
  case const b => exact ⟨.const b, rfl⟩
  case atom v =>
    obtain ⟨i, hi⟩ := atomFin_exists (hmem v (by simp [BoolExpr.atoms]))
    exact ⟨.var i, by simp [positive, hi]⟩
  case and a b ha hb iha ihb =>
    have hmem' : (∀ v ∈ a.atoms, v ∈ atoms) ∧ (∀ v ∈ b.atoms, v ∈ atoms) := by
      simpa [BoolExpr.atoms, or_imp, forall_and] using hmem
    obtain ⟨ra, hra⟩ := iha hmem'.1
    obtain ⟨rb, hrb⟩ := ihb hmem'.2
    exact ⟨.meet ra rb, by simp [positive, hra, hrb]⟩
  case or a b ha hb iha ihb =>
    have hmem' : (∀ v ∈ a.atoms, v ∈ atoms) ∧ (∀ v ∈ b.atoms, v ∈ atoms) := by
      simpa [BoolExpr.atoms, or_imp, forall_and] using hmem
    obtain ⟨ra, hra⟩ := iha hmem'.1
    obtain ⟨rb, hrb⟩ := ihb hmem'.2
    exact ⟨.join ra rb, by simp [positive, hra, hrb]⟩

theorem horn_complete {atoms e} (h : e.IsHorn)
    (hmem : ∀ v ∈ e.atoms, v ∈ atoms) : ∃ r, horn atoms e = some r := by
  induction h
  case const b => exact ⟨.const b, rfl⟩
  case atom v =>
    obtain ⟨i, hi⟩ := atomFin_exists (hmem v (by simp [BoolExpr.atoms]))
    exact ⟨.var i, by simp [horn, hi]⟩
  case and a b ha hb iha ihb =>
    have hmem' : (∀ v ∈ a.atoms, v ∈ atoms) ∧ (∀ v ∈ b.atoms, v ∈ atoms) := by
      simpa [BoolExpr.atoms, or_imp, forall_and] using hmem
    obtain ⟨ra, hra⟩ := iha hmem'.1
    obtain ⟨rb, hrb⟩ := ihb hmem'.2
    exact ⟨.meet ra rb, by simp [horn, hra, hrb]⟩
  case imp a b ha hb ihb =>
    have hmem' : (∀ v ∈ a.atoms, v ∈ atoms) ∧ (∀ v ∈ b.atoms, v ∈ atoms) := by
      simpa [BoolExpr.atoms, or_imp, forall_and] using hmem
    obtain ⟨ra, hra⟩ := positive_complete ha hmem'.1
    obtain ⟨rb, hrb⟩ := ihb hmem'.2
    exact ⟨.imply ra rb, by simp [horn, hra, hrb]⟩

theorem horn_domain_iff (e : BoolExpr) :
    (∃ r, horn (domain e) e = some r) ↔ e.IsHorn := by
  exact ⟨fun ⟨_, h⟩ => horn_sound h,
    fun h => horn_complete h (fun _ hv => List.mem_mergeSort.mpr hv)⟩

theorem Model.eval_matches (atoms : List Nat) (env : Mapping Bool atoms.length)
    {v i} (hi : ConcreteBackend.atomFin atoms v = some i) :
    env.get i = (Model.mk atoms env).eval v := by simp [Model.eval, hi]

theorem horn_eval_model {atoms e r} (h : horn atoms e = some r)
    (env : Mapping Bool atoms.length) :
    RightExpr.eval env r = e.eval (Model.mk atoms env).eval :=
  horn_eval h _ _ (fun _ _ hi => Model.eval_matches atoms env hi)

theorem horn_satisfiable_iff {atoms e r} (h : horn atoms e = some r) :
    (∃ σ, e.eval σ = true) ↔ ∃ env, RightExpr.eval env r = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    let env : Mapping Bool atoms.length := Vector.ofFn fun i => σ atoms[i]
    refine ⟨env, ?_⟩
    rw [horn_eval h σ env]
    · exact hσ
    · intro v i hi
      simpa [env, Vector.get] using congrArg σ (ConcreteBackend.atomFin_lookup hi)
  · rintro ⟨env, he⟩
    exact ⟨(Model.mk atoms env).eval, (horn_eval_model h env).symm.trans he⟩

theorem hornSolve_satisfiable_iff (r : RightExpr Bool n) :
    RightExpr.eval (RightExpr.hornSolve true r) r = true ↔
      ∃ env, RightExpr.eval env r = true := by
  constructor
  · exact fun h => ⟨_, h⟩
  · rintro ⟨env, he⟩
    have h := RightExpr.hornSolve_sufficient r true ⟨env, by simp [he]⟩
    exact Bool.le_iff_imp.mp h rfl

theorem checkFormula_success_iff {fuel e model} :
    checkFormula fuel e = .success model ↔
      requiredFuel e ≤ fuel ∧ ∃ r, horn (domain e) e = some r ∧
        RightExpr.eval (RightExpr.hornSolve true r) r = true ∧
        model = ⟨domain e, RightExpr.hornSolve true r⟩ := by
  by_cases hf : fuel < requiredFuel e
  · simp [checkFormula, hf, Nat.not_le.mpr hf]
  · have hle : requiredFuel e ≤ fuel := Nat.le_of_not_gt hf
    cases hr : horn (domain e) e with
    | none => simp [checkFormula, hf, hr]
    | some r =>
      cases he : RightExpr.eval (RightExpr.hornSolve true r) r <;>
        simp [checkFormula, hf, hr, hle, he]
      exact eq_comm

theorem checkFormula_sound {fuel e model} (h : checkFormula fuel e = .success model) :
    e.eval model.eval = true := by
  obtain ⟨_, r, hr, he, rfl⟩ := checkFormula_success_iff.mp h
  exact (horn_eval_model hr _).symm.trans he

theorem checkFormula_supported {fuel e model} (h : checkFormula fuel e = .success model) :
    e.IsHorn := by
  obtain ⟨_, r, hr, _⟩ := checkFormula_success_iff.mp h
  exact horn_sound hr

theorem checkFormula_complete {e} (hh : e.IsHorn) (he : ∃ σ, e.eval σ = true) :
    ∃ model, ∀ fuel, requiredFuel e ≤ fuel → checkFormula fuel e = .success model := by
  obtain ⟨r, hr⟩ := (horn_domain_iff e).mpr hh
  have hs := (hornSolve_satisfiable_iff r).mpr ((horn_satisfiable_iff hr).mp he)
  exact ⟨⟨domain e, RightExpr.hornSolve true r⟩,
    fun _ hf => checkFormula_success_iff.mpr ⟨hf, r, hr, hs, rfl⟩⟩

theorem checkFormula_satisfiable_iff {e fuel} (hh : e.IsHorn)
    (hf : requiredFuel e ≤ fuel) :
    (∃ model, checkFormula fuel e = .success model) ↔ ∃ σ, e.eval σ = true := by
  constructor
  · rintro ⟨model, hm⟩
    exact ⟨model.eval, checkFormula_sound hm⟩
  · intro he
    obtain ⟨model, hm⟩ := checkFormula_complete hh he
    exact ⟨model, hm fuel hf⟩

theorem checkFormula_not_exhausted {e fuel} (hf : requiredFuel e ≤ fuel) :
    checkFormula fuel e ≠ .exhausted := by
  cases hr : horn (domain e) e with
  | none => simp [checkFormula, Nat.not_lt.mpr hf, hr]
  | some r =>
    cases he : RightExpr.eval (RightExpr.hornSolve true r) r <;>
      simp [checkFormula, Nat.not_lt.mpr hf, hr, he]

theorem checkFormula_rejected_iff {e fuel} (hh : e.IsHorn)
    (hf : requiredFuel e ≤ fuel) :
    checkFormula fuel e = .rejected "inconsistent modality bounds" ↔
      ¬ ∃ σ, e.eval σ = true := by
  obtain ⟨r, hr⟩ := (horn_domain_iff e).mpr hh
  have hs := (hornSolve_satisfiable_iff r).trans (horn_satisfiable_iff hr).symm
  simp only [checkFormula, if_neg (Nat.not_lt.mpr hf), hr]
  cases he : RightExpr.eval (RightExpr.hornSolve true r) r <;> simp_all

theorem checkFormula_mono {e fuel more model} (hf : fuel ≤ more)
    (h : checkFormula fuel e = .success model) :
    checkFormula more e = .success model := by
  obtain ⟨hf', hs⟩ := checkFormula_success_iff.mp h
  exact checkFormula_success_iff.mpr ⟨hf'.trans hf, hs⟩

theorem checkFormula_stable {e fuel more} (hf : fuel ≤ more)
    (h : checkFormula fuel e ≠ .exhausted) : checkFormula more e = checkFormula fuel e := by
  have hf' : requiredFuel e ≤ fuel := by
    by_contra hn
    exact h (by simp [checkFormula, Nat.lt_of_not_ge hn])
  simp [checkFormula, Nat.not_lt.mpr hf', Nat.not_lt.mpr (hf'.trans hf)]

/-- The returned witness is the fixed point of the actual propagation update. -/
theorem checkFormula_fixpoint {e fuel model} (h : checkFormula fuel e = .success model) :
    ∃ r, horn model.atoms e = some r ∧
      RightExpr.update model.values true r = model.values := by
  obtain ⟨_, r, hr, _, rfl⟩ := checkFormula_success_iff.mp h
  exact ⟨r, hr, RightExpr.hornSolve_fixpoint true r⟩

/-- Every satisfying valuation lies above the returned Boolean witness. -/
theorem checkFormula_least {e fuel model} (h : checkFormula fuel e = .success model)
    {σ : Nat → Bool} (hs : e.eval σ = true) (v : Nat) : model.eval v ≤ σ v := by
  obtain ⟨_, r, hr, _, rfl⟩ := checkFormula_success_iff.mp h
  let env : Mapping Bool (domain e).length := Vector.ofFn fun i => σ (domain e)[i]
  have he : RightExpr.eval env r = true := by
    rw [horn_eval hr σ env]
    · exact hs
    · intro w i hi
      simpa [env, Vector.get] using congrArg σ (ConcreteBackend.atomFin_lookup hi)
  have hle := RightExpr.hornSolve_minimal r env true (by simp [he])
  cases hi : ConcreteBackend.atomFin (domain e) v with
  | none => simp [Model.eval, hi]
  | some i =>
    have hm : env.get i = σ v := by
      simpa [env, Vector.get] using congrArg σ (ConcreteBackend.atomFin_lookup hi)
    simpa [Model.eval, hi, hm] using hle i

/-- Every activated atomic conclusion is already present in the valuation.
Conjunction visits both obligations; implication adds its positive premise to
those that activate the conclusion. Constant conclusions are checked separately. -/
def AtomicObligations (env : Mapping Bool n) (c : Bool) : RightExpr Bool n → Prop
  | .const _ => True
  | .var i => c ≤ env.get i
  | .meet a b => AtomicObligations env c a ∧ AtomicObligations env c b
  | .imply a b => AtomicObligations env (c ⊓ LeftExpr.eval env a) b

theorem update_le_iff_atomicObligations (r : RightExpr Bool n)
    (env : Mapping Bool n) (c : Bool) :
    RightExpr.update env c r ≤ env ↔ AtomicObligations env c r := by
  induction r generalizing c
  case var i =>
    constructor
    · intro h
      have hi := h i
      simp only [RightExpr.update, Mapping.get_update_same] at hi
      exact le_trans le_sup_right hi
    · intro h j
      by_cases hj : j = i
      · subst j
        simpa only [RightExpr.update, Mapping.get_update_same, sup_le_iff, le_refl, true_and]
          using h
      · simp only [RightExpr.update, Mapping.get_update_diff env i j c hj, le_refl]
  case const b => exact ⟨fun _ => trivial, fun _ _ => le_refl _⟩
  case meet a b iha ihb =>
    constructor
    · intro h
      refine ⟨(iha c).mp ?_, (ihb c).mp ?_⟩
      · intro i
        have hi := h i
        simp only [RightExpr.update, Mapping.get_sup] at hi
        exact le_trans le_sup_left hi
      · intro i
        have hi := h i
        simp only [RightExpr.update, Mapping.get_sup] at hi
        exact le_trans le_sup_right hi
    · rintro ⟨ha, hb⟩ i
      simpa only [RightExpr.update, Mapping.get_sup] using
        sup_le ((iha c).mpr ha i) ((ihb c).mpr hb i)
  case imply a b ih => exact ih _

theorem update_fixed_iff_atomicObligations (r : RightExpr Bool n)
    (env : Mapping Bool n) (c : Bool) :
    RightExpr.update env c r = env ↔ AtomicObligations env c r := by
  constructor
  · intro h
    apply (update_le_iff_atomicObligations r env c).mp
    rw [h]
  · intro h
    have hle := (update_le_iff_atomicObligations r env c).mpr h
    apply Vector.ext
    intro i hi
    exact le_antisymm (hle ⟨i, hi⟩) (RightExpr.update_le r env c ⟨i, hi⟩)

/-- Saturating atomic bounds and discharging the activated constant tests is
exactly satisfaction. This includes nested implications without distributing
positive disjunctions or generating new residual expressions. -/
theorem eval_iff_atomicObligations_and_constants (r : RightExpr Bool n)
    (env : Mapping Bool n) (c : Bool) :
    c ≤ RightExpr.eval env r ↔
      AtomicObligations env c r ∧ c ≤ RightExpr.eval_for_consts env r := by
  constructor
  · intro h
    exact ⟨(update_fixed_iff_atomicObligations r env c).mp
      (RightExpr.update_fixpoint r env c h),
      h.trans (RightExpr.eval_le_eval_for_consts r env)⟩
  · rintro ⟨ha, hc⟩
    exact RightExpr.fixpoint_and_consts_sufficient r env c
      ((update_fixed_iff_atomicObligations r env c).mpr ha) hc

theorem checkFormula_saturated {e fuel model} (h : checkFormula fuel e = .success model) :
    ∃ r, horn model.atoms e = some r ∧ AtomicObligations model.values true r ∧
      RightExpr.eval_for_consts model.values r = true := by
  obtain ⟨_, r, hr, he, rfl⟩ := checkFormula_success_iff.mp h
  have hs := (eval_iff_atomicObligations_and_constants r (RightExpr.hornSolve true r) true).mp
    (by simp [he])
  exact ⟨r, hr, hs.1, Bool.le_iff_imp.mp hs.2 rfl⟩

end ModalityInference.HornPropagation
