import ModalityInference.ScalarDecision
import ModalityInference.Proofs.BackendComplete
import ModalityInference.Proofs.Projection
import ModalityInference.Proofs.Subtyping

/-! The structural budget completes the existing symbolic scalar backend,
including false validity results and guarded partial modality expressions. -/
namespace ModalityInference.ScalarDecision

private theorem clean_length (cs : CNF) : (cleanCNF cs).length ≤ cs.length := by
  exact (List.dedup_sublist _).length_le.trans ((List.length_filter_le _ _).trans (by simp))

theorem normalize_complete (e : BoolExpr) (positive : Bool) (fuel : Nat)
    (hf : budget e ≤ fuel) :
    ∃ cs, toCNF fuel positive e = .success cs ∧ cs.length ≤ budget e := by
  induction e generalizing positive fuel with
  | const b => cases fuel <;> cases b <;> cases positive <;> simp_all [budget,toCNF]
  | atom v => cases fuel <;> simp_all [budget,toCNF]
  | and a b ia ib | or a b ia ib =>
    cases fuel with
    | zero => simp [budget] at hf
    | succ fuel =>
      obtain ⟨ca,ha,hla⟩ := ia positive fuel (by simp only [budget] at hf; omega)
      obtain ⟨cb,hb,hlb⟩ := ib positive fuel (by simp only [budget] at hf; omega)
      have hm := Nat.mul_le_mul hla hlb
      have hp : ¬ ca.length * cb.length > fuel + 1 := by simp only [budget] at hf; omega
      cases positive <;> simp [toCNF,ha,hb,bind,pure,RunResult.bind,cnfOr,hp]
      all_goals apply (clean_length _).trans
      all_goals simp [List.length_flatMap,budget]
      all_goals omega
  | imp a b ia ib =>
    cases fuel with
    | zero => simp [budget] at hf
    | succ fuel =>
      obtain ⟨ca,ha,hla⟩ := ia (!positive) fuel (by simp only [budget] at hf; omega)
      obtain ⟨cb,hb,hlb⟩ := ib positive fuel (by simp only [budget] at hf; omega)
      have hm := Nat.mul_le_mul hla hlb
      have hp : ¬ ca.length * cb.length > fuel + 1 := by simp only [budget] at hf; omega
      cases positive <;> simp only [Bool.not_true,Bool.not_false] at ha
      all_goals simp [toCNF,ha,hb,bind,pure,RunResult.bind,cnfOr,hp]
      all_goals apply (clean_length _).trans
      all_goals simp [List.length_flatMap,budget]
      all_goals omega

/-- A false validity bit is a successful decision; exhaustion and internal
atom-domain rejection are impossible at the structural budget. -/
theorem backend_complete (e : BoolExpr) (fuel : Nat) (hf : budget e ≤ fuel) :
    ∃ report, ConcreteBackend.decideFormula fuel e = .success report := by
  obtain ⟨cs,hcs,_⟩ := normalize_complete e true fuel hf
  have hc : ∀ clause ∈ cs, ∀ literal ∈ clause,
      literal.1 ∈ e.atoms.mergeSort (· ≤ ·) := by
    intro clause hcl literal hl
    simpa using toCNF_literal hcs hcl hl
  obtain ⟨valid,hvalid⟩ := ConcreteBackend.decideClauses_complete hc true
  exact ⟨⟨e.atoms.mergeSort (· ≤ ·),cs,valid⟩,by
    simp [ConcreteBackend.decideFormula,hcs,hvalid,bind,pure,RunResult.bind]⟩

theorem formula_correct (e : BoolExpr) : formula e = true ↔ ∀ σ, e.eval σ = true := by
  obtain ⟨report,hr⟩ := backend_complete e (budget e) le_rfl
  simpa only [formula,hr] using ConcreteBackend.decideFormula_correct hr

theorem entails_correct (assumptions goals : Bounds) :
    entails assumptions goals = true ↔ ∀ η, ModeModels assumptions η → ModeModels goals η := by
  rw [entails,formula_correct]
  simp only [BoolExpr.eval_imp_true,boundsModeFormula_correct]
  exact ⟨fun h η => by simpa only [projectedModes_encodeModes] using h (encodeModes η),
    fun h σ => h (projectedModes σ)⟩

theorem defined_correct (Δ : Bounds) (m : ModExpr) :
    defined Δ m = true ↔ Entails Δ (.defined m) := by
  simpa only [defined,ModeModels,List.mem_singleton,forall_eq,ModeSatisfies,Entails]
    using entails_correct Δ [.defined m]

theorem submode_correct (Δ : Bounds) (m n : ModExpr) :
    submode Δ m n = true ↔ Submode Δ m n := by
  rw [submode,entails_correct]
  simp only [ModeModels,List.mem_singleton,forall_eq,ModeSatisfies]
  exact ⟨Submode.valid,fun h η hη => h.denote hη⟩

end ModalityInference.ScalarDecision
