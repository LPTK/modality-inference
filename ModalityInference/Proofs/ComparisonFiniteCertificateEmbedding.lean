import ModalityInference.ComparisonFiniteCertificate
import ModalityInference.Proofs.ComparisonExecutableRangeAgreement
import ModalityInference.Proofs.ComparisonExecutableControls
import ModalityInference.Proofs.ComparisonObserverMachineCheck
import ModalityInference.Proofs.ComparisonObserverMachineModeTransport
import ModalityInference.Proofs.ComparisonBalancedProjection

/-! Successful finite checks supply the original-context range algebra and
its order-reflecting lattice embedding in finite control coordinates. -/
namespace ModalityInference.ComparisonFiniteCertificate

open ComparisonFiniteControlEncoding ComparisonObserverMachineCheck
  ComparisonObserverMachine ComparisonObserverFiniteRange ComparisonRelativeCoordinates

@[simp] theorem shadow_eq (Δ : Bounds) : shadow Δ = ComparisonBalancedProjection.shapeShadow Δ := rfl

namespace Candidate

variable {Δ : Bounds} {names : List ModVar} (C : Candidate Δ names)

abbrev Nodes := ComparisonObserverMachineCheck.nodes C.types C.modes C.machine
abbrev Range := ComparisonObserverFiniteRange.Value C.Nodes

theorem machine_checked (h : C.structureCheck = true) :
    ComparisonObserverMachineCheck.check (shadow Δ) C.types C.modes C.machine = true := by
  simp only [structureCheck,Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem embedding_checked (h : C.structureCheck = true) : C.embeddingCheck = true := by
  simp only [structureCheck,Bool.and_eq_true] at h
  exact h.1.2

theorem machine_laws (h : C.structureCheck = true) :
    ModalValid Δ C.Nodes ∧ RangeClosed Δ C.Nodes ∧ Coherent Δ C.Nodes :=
  ComparisonObserverMachineModeTransport.certified_modes
    (fun η hη => (ComparisonBalancedProjection.modeModels_shadow Δ η).mp hη)
    (by simpa only [shadow_eq] using ComparisonObserverMachineCheck.check_sound (C.machine_checked h))

def modal (h : C.structureCheck = true) : ModalValid Δ C.Nodes := (C.machine_laws h).1

def range (h : C.structureCheck = true) : RangeClosed Δ C.Nodes := (C.machine_laws h).2.1

def coherent (h : C.structureCheck = true) : Coherent Δ C.Nodes := (C.machine_laws h).2.2

def semanticOperations (h : C.structureCheck = true) :=
  ComparisonExecutableRangeAgreement.semanticOperations (C.range h) order (· * ·) expression expression_defined
    (C.pair C.prodRows) (C.pair C.sumRows) C.function

theorem embedding_valid (h : C.structureCheck = true) :
    ComparisonExecutableAgreement.Valid (C.semanticOperations h)
      (fun x => C.defined (ComparisonObserverRangeEncoding.pack x)) := by
  apply (ComparisonExecutableRangeAgreement.check_correct (C.range h) order (· * ·) expression expression_defined
    (C.pair C.prodRows) (C.pair C.sumRows) C.function (indices Δ names) C.obs
    (fun m => List.mem_map.mpr ⟨m.index,by simp,rfl⟩) (by simp [obs]) C.defined).mp
  exact C.embedding_checked h

def embedding (h : C.structureCheck = true) :
    LatticeHom C.Range (ComparisonRelativeCoordinates.Coordinates (Code Δ names) (Fin C.observations → Bool)) :=
  (C.embedding_valid h).embedding (fun _ _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[simp] theorem embedding_apply (h : C.structureCheck = true) (x : C.Range)
    (m : Code Δ names) (o : Fin C.observations) :
    C.embedding h x m o = C.defined (ComparisonObserverRangeEncoding.pack x) m o := rfl

theorem embedding_reflect (h : C.structureCheck = true) {x y : C.Range}
    (hxy : C.embedding h x ≤ C.embedding h y) : x ≤ y :=
  (C.embedding_valid h).embedding_reflect (fun _ _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun x y => ComparisonObserverRangeEncoding.le_correct _ _ |>.trans
      (ComparisonObserverRangeEncoding.pack_le x y)) hxy

theorem embedding_shift (h : C.structureCheck = true) (m : Code Δ names) (x : C.Range) :
    shift ComparisonExecutableControls.mul_mono m (C.embedding h x) =
      C.embedding h (ComparisonFiniteControlRange.action (C.modal h) (C.range h) (decode m) x) := by
  have ha := (C.embedding_valid h).action m x
  have he := ComparisonExecutableRangeAgreement.modal_decode (C.range h) (C.modal h) m x
  ext n o
  change C.defined (ComparisonObserverRangeEncoding.pack x) (m * n) o = _
  rw [← he]
  exact congrFun (congrFun ha n) o

end Candidate
end ModalityInference.ComparisonFiniteCertificate
