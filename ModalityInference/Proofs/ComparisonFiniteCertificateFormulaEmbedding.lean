import ModalityInference.ComparisonFiniteCertificateFormula
import ModalityInference.Proofs.ComparisonExecutableAgreementFormula
import ModalityInference.Proofs.ComparisonObserverRangeFormula

/-! Symbolic constructor operations and the defined embedding check evaluate
exactly to the corresponding fields of the decoded finite certificate. -/
namespace ModalityInference.ComparisonFiniteCertificateFormula.Fields

open ComparisonFiniteCertificate ComparisonFiniteControlEncoding

variable {Δ : Bounds} {names : List ModVar} {states tags observations : Nat}
  (F : Fields Δ names states tags observations)
  (types : List TypeVar) (modes : List ModVar) (world : Nat → Bool)

theorem definedAt_eval (x : ComparisonObserverRangeFormula.Bits states) :
    ComparisonExecutableAgreementFormula.decode world (F.definedAt x) =
      (F.decode types modes world).defined (ComparisonObserverRangeFormula.eval x world) :=
  funext fun m => funext fun o =>
    ComparisonObserverRangeFormula.lookup_eval (fun v => F.defined v m o) x world

theorem pair_eval (selected : Selection Δ names tags) (x y : Vector Δ names observations) :
    ComparisonExecutableAgreementFormula.decode world (F.pair selected x y) =
      (F.decode types modes world).pair
        (ComparisonExecutableTableFormula.selected (rows Δ names tags) selected world)
        (ComparisonExecutableAgreementFormula.decode world x)
        (ComparisonExecutableAgreementFormula.decode world y) :=
  funext fun m => funext fun o => ComparisonExecutableTableFormula.extend_eval
    (List.finRange observations) F.embed order false false world
    (rows Δ names tags) selected m (x m) (y m) o

theorem function_eval (x y : Vector Δ names observations) :
    ComparisonExecutableAgreementFormula.decode world (F.function x y) =
      (F.decode types modes world).function
        (ComparisonExecutableAgreementFormula.decode world x)
        (ComparisonExecutableAgreementFormula.decode world y) :=
  funext fun m => funext fun o => ComparisonExecutableTableFormula.extend_eval
    (List.finRange observations) F.embed ComparisonExecutableControls.future true false world
    (rows Δ names tags) F.fnRows m (x 1) (y 1) o

theorem images_realizes :
    ComparisonExecutableAgreementFormula.Realizes world (F.images modes)
      (F.decode types modes world).operations F.defined := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_,
    fun x y => F.pair_eval types modes world F.prodRows (F.defined x) (F.defined y),
    fun x y => F.pair_eval types modes world F.sumRows (F.defined x) (F.defined y),
    fun x y => F.function_eval types modes world (F.defined x) (F.defined y)⟩
  · intro m x
    simpa only [images, ComparisonObserverRangeFormula.modal_eval] using
      F.definedAt_eval types modes world (ComparisonObserverRangeFormula.modal F.machine modes
        (expression m) (fun i => .const (x i)))
  · intro x y
    simpa only [images, ComparisonObserverRangeFormula.op_eval] using
      F.definedAt_eval types modes world (ComparisonObserverRangeFormula.op F.machine .prod
        (fun i => .const (x i)) (fun i => .const (y i)))
  · intro x y
    simpa only [images, ComparisonObserverRangeFormula.op_eval] using
      F.definedAt_eval types modes world (ComparisonObserverRangeFormula.op F.machine .sum
        (fun i => .const (x i)) (fun i => .const (y i)))
  · intro x y
    simpa only [images, ComparisonObserverRangeFormula.op_eval] using
      F.definedAt_eval types modes world (ComparisonObserverRangeFormula.op F.machine .fn
        (fun i => .const (x i)) (fun i => .const (y i)))

theorem embeddingCheck_eval :
    (F.embeddingCheck modes).eval world = (F.decode types modes world).embeddingCheck := by
  simpa only [embeddingCheck, Candidate.embeddingCheck, ComparisonObserverRangeEncoding.vectors,
    ComparisonObserverRangeFormula.admitted_eval] using
    ComparisonExecutableAgreementFormula.check_eval world
      (ComparisonObserverRangeEncoding.allBits states) (indices Δ names) (List.finRange observations)
      (fun x => ComparisonObserverRangeFormula.admitted F.machine (fun i => .const (x i)))
      (F.images modes) (F.decode types modes world).operations F.defined
      (F.images_realizes types modes world)

end ModalityInference.ComparisonFiniteCertificateFormula.Fields
