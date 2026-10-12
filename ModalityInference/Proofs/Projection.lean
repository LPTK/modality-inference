import ModalityInference.Proofs.Backend
import ModalityInference.Declarative

/-! Correctness of all three Boolean projections, including partial-modality guards. -/
namespace ModalityInference

def Projection.eval (σ : Nat → Bool) (p : Projection) : Option Mode :=
  if p.defined.eval σ then
    some ⟨p.locality.eval σ, p.affinity.eval σ, p.uniqueness.eval σ⟩
  else none

def projectedModes (σ : Nat → Bool) (v : ModVar) : Mode :=
  ⟨σ (v.atomIndex 0), σ (v.atomIndex 1), σ (v.atomIndex 2)⟩

def encodeModes (η : ModVar → Mode) (i : Nat) : Bool :=
  let v := if i / 3 % 2 = 0 then ModVar.flex (i / 6) else ModVar.rigid (i / 6)
  match i % 3 with
  | 0 => (η v).isLocal
  | 1 => (η v).once
  | _ => (η v).unique

theorem projectedModes_encodeModes (η : ModVar → Mode) : projectedModes (encodeModes η) = η := by
  have quotient (n : Nat) : n * 6 / 3 = n * 2 := by omega
  funext v
  cases v <;> simp [projectedModes, encodeModes, ModVar.atomIndex, Nat.add_mul,
    Nat.mul_assoc, Nat.mul_comm, Nat.add_div, Nat.add_mod, Nat.mul_mod, quotient]

theorem ModExpr.project_correct (e : ModExpr) (σ : Nat → Bool) :
    e.project.eval σ = e.eval (some ∘ projectedModes σ) := by
  induction e with
  | leftResidual a b iha ihb =>
    simp only [ModExpr.project, ModExpr.eval, ← iha, ← ihb]
    simp [Projection.eval, BoolExpr.all, BoolExpr.eval, Mode.leftResidual]
    cases (a.project.defined.eval σ) <;> cases (b.project.defined.eval σ) <;> simp
  | const m => rfl
  | var v => rfl
  | compose a b iha ihb | meet a b iha ihb | join a b iha ihb =>
    simp only [ModExpr.project, ModExpr.eval, ← iha, ← ihb]
    cases ha : a.project.defined.eval σ <;> cases hb : b.project.defined.eval σ <;>
      simp [Projection.eval, BoolExpr.eval, ha, hb, Mode.compose, Mode.meet, Mode.join]
  | rightResidual a b iha ihb =>
    simp only [ModExpr.project, ModExpr.eval, ← iha, ← ihb]
    simp [Projection.eval, BoolExpr.all, BoolExpr.eval, Mode.rightResidual]
    cases (a.project.defined.eval σ) <;> cases (b.project.defined.eval σ) <;> simp
  | close a ih | closeInv a ih | future a ih | capture a ih =>
    simp only [ModExpr.project, ModExpr.eval, ← ih]
    cases ha : a.project.defined.eval σ <;>
      simp [Projection.eval, BoolExpr.eval, ha, Mode.close, Mode.closeInv, Mode.future, Mode.capture]

theorem modeFormula_correct (a b : ModExpr) (σ : Nat → Bool) :
    (modeFormula a b).eval σ = true ↔ ModExpr.Below (projectedModes σ) a b := by
  simp only [ModExpr.Below, ← a.project_correct σ, ← b.project_correct σ]
  cases ha : a.project.defined.eval σ <;> cases hb : b.project.defined.eval σ <;>
    simp [modeFormula, Projection.eval, BoolExpr.eval, BoolExpr.all, Mode.le, ha, hb, and_assoc]

theorem ModExpr.project_defined (a : ModExpr) (σ : Nat → Bool) :
    a.project.defined.eval σ = true ↔ a.WellFormed (projectedModes σ) := by
  simp only [ModExpr.WellFormed, ← a.project_correct σ]
  cases ha : a.project.defined.eval σ <;> simp [Projection.eval, ha]

theorem constraintModeFormula_correct (c : Constraint) (σ : Nat → Bool) :
    (constraintModeFormula c).eval σ = true ↔ ModeSatisfies (projectedModes σ) c := by
  cases c <;> simp [constraintModeFormula, ModeSatisfies, BoolExpr.eval,
    modeFormula_correct, ModExpr.project_defined]

theorem boundsModeFormula_correct (cs : Bounds) (σ : Nat → Bool) :
    (boundsModeFormula cs).eval σ = true ↔ ModeModels cs (projectedModes σ) := by
  induction cs <;>
    simp_all [boundsModeFormula, BoolExpr.all, BoolExpr.eval, ModeModels,
      constraintModeFormula_correct]

theorem BoolExpr.eval_imp_true (a b : BoolExpr) (σ : Nat → Bool) :
    (.imp a b : BoolExpr).eval σ = true ↔ (a.eval σ = true → b.eval σ = true) := by
  simp only [BoolExpr.eval]
  cases (a.eval σ) <;> cases (b.eval σ) <;> decide

theorem ConcreteBackend.entails_correct {fuel assumptions goals report}
    (h : ConcreteBackend.entails fuel assumptions goals = .success report) :
    report.valid = true ↔ ∀ η, ModeModels assumptions η → ModeModels goals η := by
  rw [ConcreteBackend.decideFormula_correct h]
  simp only [BoolExpr.eval_imp_true, boundsModeFormula_correct]
  exact ⟨fun h η => by simpa only [projectedModes_encodeModes] using h (encodeModes η),
    fun h σ => h (projectedModes σ)⟩

/-- A positive executable modality query yields the independent declarative judgment. -/
theorem ConcreteBackend.entails_submode {fuel Δ a b report}
    (h : ConcreteBackend.entails fuel Δ [.mode a b] = .success report)
    (hv : report.valid = true) : Submode Δ a b := by
  exact .valid fun η hη => ((ConcreteBackend.entails_correct h).mp hv η hη)
    (.mode a b) (by simp)

end ModalityInference
