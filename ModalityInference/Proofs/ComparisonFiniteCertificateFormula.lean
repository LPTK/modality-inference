import ModalityInference.ComparisonFiniteCertificateFormula
import ModalityInference.Proofs.ComparisonExecutableTableFormula
import ModalityInference.Proofs.ComparisonExecutableSyntaxMap
import ModalityInference.Proofs.ComparisonFiniteCertificateFormulaEmbedding
import ModalityInference.Proofs.ComparisonFiniteCertificateSoundness

/-! The symbolic finite-certificate validator evaluates to the original
executable validator under the same field assignment. -/
namespace ModalityInference.ComparisonFiniteCertificateFormula

open ComparisonFiniteCertificate ComparisonFiniteControlEncoding ComparisonExecutableTables
  ComparisonObserverMachineFormula

theorem literalSelection_selected {Δ names tags} (ordinary : Selection Δ names tags)
    (literals : List (ModExpr × Selection Δ names tags)) (p : Option ModExpr) (world : Nat → Bool) :
    ComparisonExecutableTableFormula.selected (rows Δ names tags)
      (literalSelection ordinary literals p) world =
    literalRows (ComparisonExecutableTableFormula.selected (rows Δ names tags) ordinary world)
      (literals.map fun r =>
        (r.1,ComparisonExecutableTableFormula.selected (rows Δ names tags) r.2 world)) p := by
  cases p with
  | none => rfl
  | some p =>
    cases h : literals.find? (fun row => decide (row.1 = p)) <;>
      simp [literalSelection, literalRows, List.find?_map, Function.comp_def, h,
        ComparisonExecutableTableFormula.selected, BoolExpr.eval]

namespace Fields

variable {Δ : Bounds} {names : List ModVar} {states tags observations : Nat}
  (F : Fields Δ names states tags observations) (types : List TypeVar) (modes : List ModVar)
  (world : Nat → Bool)

theorem tablesCheck_eval : (F.tablesCheck).eval world = (F.decode types modes world).tablesCheck := by
  simp only [tablesCheck, tableCheck, BoolExpr.eval, all_map_eval,
    ComparisonExecutableTableFormula.check_eval, Candidate.tablesCheck, decode, Candidate.obs,
    List.all_map, Function.comp_def]

theorem monotoneCheck_eval (x : Vector Δ names observations) :
    (monotoneCheck x).eval world = (F.decode types modes world).monotoneCheck
      (ComparisonExecutableAgreementFormula.decode world x) := by
  simp only [monotoneCheck, BoolExpr.eval, all_map_eval,
    ComparisonExecutableTableFormula.below_eval, Candidate.monotoneCheck, Candidate.obs, decode]
  rfl

theorem dataMap : ComparisonExecutableSyntax.DataMap (F.data types) (F.decode types modes world).data
    (ComparisonExecutableAgreementFormula.decode world) id := by
  refine ⟨rfl, (fun _ => rfl), (fun _ _ => rfl), ?_, ?_,
    F.function_eval types modes world, (fun _ _ => rfl), (fun _ _ => rfl), ?_,
    F.definedAt_eval types modes world (ComparisonObserverRangeFormula.unit F.machine),
    F.definedAt_eval types modes world (ComparisonObserverRangeFormula.credit F.machine), rfl, rfl⟩
  · intro p x y
    simpa only [data, Candidate.data, Candidate.prodAt, decode, literalSelection_selected] using
      F.pair_eval types modes world (literalSelection F.prodRows F.prodLiterals p) x y
  · intro p x y
    simpa only [data, Candidate.data, Candidate.sumAt, decode, literalSelection_selected] using
      F.pair_eval types modes world (literalSelection F.sumRows F.sumLiterals p) x y
  · intro v
    simpa only [ComparisonObserverRangeFormula.atom_eval] using
      F.definedAt_eval types modes world (ComparisonObserverRangeFormula.atom F.machine types v)

theorem eval_eq (a : CompareTy) (p : Option ModExpr) :
    ComparisonExecutableAgreementFormula.decode world ((F.data types).eval a p) =
      (F.decode types modes world).data.eval a p := (F.dataMap types modes world).eval_eq a p

theorem evalRaw_eq (a : Ty) :
    ComparisonExecutableAgreementFormula.decode world ((F.data types).evalRaw a) =
      (F.decode types modes world).data.evalRaw a := (F.dataMap types modes world).evalRaw_eq a

theorem boundsCheck_eval : (F.boundsCheck types).eval world = (F.decode types modes world).boundsCheck := by
  simp only [boundsCheck, all_map_eval, Candidate.boundsCheck]
  congr 1
  funext c
  cases c <;> simp only [BoolExpr.eval, ComparisonExecutableAgreementFormula.vectorBelow_eval,
    F.evalRaw_eq types modes world, Candidate.obs, decode]

theorem structureCheck_eval :
    (F.structureCheck types modes).eval world = (F.decode types modes world).structureCheck := by
  simp only [structureCheck, BoolExpr.eval, ComparisonObserverMachineFormula.query_eval,
    F.tablesCheck_eval types modes world, F.embeddingCheck_eval types modes world,
    all_map_eval, F.monotoneCheck_eval types modes world, Candidate.structureCheck, decode,
    List.all_map, Function.comp_def]

theorem check_eval : (F.check types modes).eval world = (F.decode types modes world).check := by
  simp only [check, BoolExpr.eval, F.structureCheck_eval types modes world,
    F.boundsCheck_eval types modes world, Candidate.check]

theorem separates_eval (a b : CompareTy) :
    (F.separates types modes a b).eval world = (F.decode types modes world).separates a b := by
  simp only [separates, BoolExpr.eval, F.check_eval types modes world,
    ComparisonExecutableAgreementFormula.vectorBelow_eval, F.eval_eq types modes world,
    Candidate.separates, Candidate.obs, decode, Bool.or_false]

theorem separates_sound {a b : CompareTy} (h : (F.separates types modes a b).eval world = true) :
    ¬ AlgebraSubtype Δ a b :=
  (F.decode types modes world).separates_sound ((F.separates_eval types modes world a b) ▸ h)

end Fields
end ModalityInference.ComparisonFiniteCertificateFormula
