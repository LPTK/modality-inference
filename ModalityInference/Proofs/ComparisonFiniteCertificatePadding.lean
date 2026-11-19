import ModalityInference.ComparisonFiniteCertificatePadding
import ModalityInference.Proofs.ComparisonFiniteCertificateChecks
import ModalityInference.Proofs.ComparisonExecutableSyntaxMap

/-! Padding preserves the original coordinate computations and certificate
checks, including empty carriers. -/
namespace ModalityInference.ComparisonFiniteCertificate

open ComparisonExecutableTables ComparisonFiniteControlEncoding

namespace Padding

@[simp] theorem tagEmbed_castLE {O : Type} {old size : Nat} (h : old ≤ size)
    (embed : Fin old → O → Bool) (a : Fin old) : tagEmbed embed (a.castLE h) = embed a := by
  simp [tagEmbed, a.isLt]

theorem tagRows_check {M O : Type} {old size : Nat} (h : old ≤ size)
    (obs : List O) (embed : Fin old → O → Bool) (le : M → M → Bool) (p q : Bool)
    (rs : List (Row M (Fin old))) :
    ComparisonExecutableTables.check obs (tagEmbed (size := size) embed) le p q (rs.map (tagRow h)) =
      ComparisonExecutableTables.check obs embed le p q rs := by
  simp only [ComparisonExecutableTables.check, List.all_map, Function.comp_def, compatible,
    tagRow, tagEmbed_castLE]

theorem tagRows_extend {M O : Type} {old size : Nat} (h : old ≤ size)
    (obs : List O) (embed : Fin old → O → Bool) (le : M → M → Bool) (p q : Bool)
    (rs : List (Row M (Fin old))) (m : M) (x y : O → Bool) :
    extend obs (tagEmbed (size := size) embed) le p q (rs.map (tagRow h)) m x y =
      extend obs embed le p q rs m x y := by
  funext o
  simp only [extend, List.any_map, Function.comp_def, tagRow, tagEmbed_castLE]

theorem tagRows_literalRows {Δ names old size} (h : old ≤ size)
    (ordinary : List (Row (Code Δ names) (Fin old)))
    (literals : List (ModExpr × List (Row (Code Δ names) (Fin old)))) (p : Option ModExpr) :
    literalRows (ordinary.map (tagRow h)) (literals.map fun r => (r.1,r.2.map (tagRow h))) p =
      (literalRows ordinary literals p).map (tagRow h) := by
  cases p with
  | none => rfl
  | some p =>
    cases hf : literals.find? (fun r => decide (r.1 = p)) <;>
      simp [literalRows, List.find?_map, Function.comp_def, hf]

@[simp] theorem zeroExtend_castLE {old size : Nat} (h : old ≤ size)
    (x : Fin old → Bool) (i : Fin old) : zeroExtend (size := size) x (i.castLE h) = x i := by
  simp [zeroExtend, i.isLt]

theorem zeroExtend_le_iff {old size : Nat} (h : old ≤ size) (x y : Fin old → Bool) :
    zeroExtend (size := size) x ≤ zeroExtend y ↔ x ≤ y := by
  constructor
  · exact fun hh i => by simpa only [zeroExtend_castLE] using hh (i.castLE h)
  · intro hh i
    by_cases hi : i.val < old
    · simpa only [zeroExtend, hi, ↓reduceDIte] using hh ⟨i.val,hi⟩
    · simp [zeroExtend, hi]

theorem below_zeroExtend {old size : Nat} (h : old ≤ size) (x y : Fin old → Bool) :
    below (List.finRange size) (zeroExtend x) (zeroExtend y) = below (List.finRange old) x y := by
  apply Bool.eq_iff_iff.mpr
  simpa only [below_correct (List.finRange size) (by simp),
    below_correct (List.finRange old) (by simp)] using zeroExtend_le_iff h x y

theorem direction_zeroExtend {old size : Nat} (h : old ≤ size) (p : Bool) (x y : Fin old → Bool) :
    direction (List.finRange size) p (zeroExtend x) (zeroExtend y) =
      direction (List.finRange old) p x y := by
  cases p <;> simp only [direction, ↓reduceIte, below_zeroExtend h]

theorem check_zeroExtend {M A : Type} {old size : Nat} (h : old ≤ size)
    (embed : A → Fin old → Bool) (le : M → M → Bool) (p q : Bool) (rs : List (Row M A)) :
    ComparisonExecutableTables.check (List.finRange size) (fun a => zeroExtend (embed a)) le p q rs =
      ComparisonExecutableTables.check (List.finRange old) embed le p q rs := by
  simp only [ComparisonExecutableTables.check, compatible, direction_zeroExtend h, below_zeroExtend h]

theorem extend_zeroExtend {M A : Type} {old size : Nat} (h : old ≤ size)
    (embed : A → Fin old → Bool) (le : M → M → Bool) (p q : Bool) (rs : List (Row M A))
    (m : M) (x y : Fin old → Bool) :
    extend (List.finRange size) (fun a => zeroExtend (embed a)) le p q rs m (zeroExtend x) (zeroExtend y) =
      zeroExtend (extend (List.finRange old) embed le p q rs m x y) := by
  funext i
  simp only [extend, direction_zeroExtend h]
  by_cases hi : i.val < old
  · simp only [zeroExtend, hi, ↓reduceDIte, extend]
  · simp [zeroExtend, hi]

theorem vectorEq_zeroExtend {M : Type} {old size : Nat} (h : old ≤ size)
    (indices : List M) (x y : M → Fin old → Bool) :
    ComparisonExecutableAgreement.vectorEq indices (List.finRange size)
      (fun m => zeroExtend (x m)) (fun m => zeroExtend (y m)) =
      ComparisonExecutableAgreement.vectorEq indices (List.finRange old) x y := by
  apply Bool.eq_iff_iff.mpr
  simp only [ComparisonExecutableAgreement.vectorEq, List.all_eq_true, List.mem_finRange,
    forall_true_left, beq_iff_eq]
  constructor
  · exact fun hh m hm i => by simpa only [zeroExtend_castLE] using hh m hm (i.castLE h)
  · intro hh m hm i
    by_cases hi : i.val < old
    · simpa only [zeroExtend, hi, ↓reduceDIte] using hh m hm ⟨i.val,hi⟩
    · simp [zeroExtend, hi]

theorem vectorBelow_zeroExtend {M : Type} {old size : Nat} (h : old ≤ size)
    (indices : List M) (x y : M → Fin old → Bool) :
    ComparisonExecutableAgreement.vectorBelow indices (List.finRange size)
      (fun m => zeroExtend (x m)) (fun m => zeroExtend (y m)) =
      ComparisonExecutableAgreement.vectorBelow indices (List.finRange old) x y := by
  simp only [ComparisonExecutableAgreement.vectorBelow, below_zeroExtend h]

theorem coordinates_join {Δ names old size} (x y : Coordinates Δ names old) :
    (fun m o => coordinates (size := size) x m o || coordinates y m o) =
      coordinates (fun m o => x m o || y m o) := by
  funext m o
  by_cases hi : o.val < old <;> simp [coordinates, zeroExtend, hi]

theorem coordinates_meet {Δ names old size} (x y : Coordinates Δ names old) :
    (fun m o => coordinates (size := size) x m o && coordinates y m o) =
      coordinates (fun m o => x m o && y m o) := by
  funext m o
  by_cases hi : o.val < old <;> simp [coordinates, zeroExtend, hi]

theorem coordinates_shift {Δ names old size} (x : Coordinates Δ names old) (m : Code Δ names) :
    (fun n => coordinates (size := size) x (m * n)) = coordinates (fun n => x (m * n)) := rfl

theorem vectorEq_coordinates {Δ names old size} (h : old ≤ size)
    (xs : List (Code Δ names)) (x y : Coordinates Δ names old) :
    ComparisonExecutableAgreement.vectorEq xs (List.finRange size) (coordinates x) (coordinates y) =
      ComparisonExecutableAgreement.vectorEq xs (List.finRange old) x y :=
  vectorEq_zeroExtend h xs x y

theorem vectorBelow_coordinates {Δ names old size} (h : old ≤ size)
    (xs : List (Code Δ names)) (x y : Coordinates Δ names old) :
    ComparisonExecutableAgreement.vectorBelow xs (List.finRange size) (coordinates x) (coordinates y) =
      ComparisonExecutableAgreement.vectorBelow xs (List.finRange old) x y :=
  vectorBelow_zeroExtend h xs x y

end Padding

namespace Candidate

variable {Δ : Bounds} {names : List ModVar} (C : Candidate Δ names)
  {tags : Nat} (h : C.tags ≤ tags)

@[simp] theorem padTags_tags : (C.padTags h).tags = tags := rfl

theorem padTags_pair (rs : List (Row (Code Δ names) (Fin C.tags))) :
    (C.padTags h).pair (rs.map (Padding.tagRow h)) = C.pair rs := by
  funext x y m
  exact Padding.tagRows_extend h C.obs C.embed order false false rs m (x m) (y m)

theorem padTags_function : (C.padTags h).function = C.function := by
  funext x y m
  exact Padding.tagRows_extend h C.obs C.embed ComparisonExecutableControls.future true false
    C.fnRows m (x 1) (y 1)

theorem padTags_prodAt (p : Option ModExpr) :
    (C.padTags h).prodAt p = (C.prodAt p).map (Padding.tagRow h) :=
  Padding.tagRows_literalRows h C.prodRows C.prodLiterals p

theorem padTags_sumAt (p : Option ModExpr) :
    (C.padTags h).sumAt p = (C.sumAt p).map (Padding.tagRow h) :=
  Padding.tagRows_literalRows h C.sumRows C.sumLiterals p

theorem padTags_data : (C.padTags h).data = C.data := by
  simp only [data, C.padTags_prodAt h, C.padTags_sumAt h, C.padTags_pair h, C.padTags_function h]
  rfl

theorem padTags_operations : (C.padTags h).operations = C.operations := by
  simp only [operations, show (C.padTags h).prodRows = C.prodRows.map (Padding.tagRow h) from rfl,
    show (C.padTags h).sumRows = C.sumRows.map (Padding.tagRow h) from rfl,
    C.padTags_pair h, C.padTags_function h]
  rfl

theorem padTags_tablesCheck : (C.padTags h).tablesCheck = C.tablesCheck := by
  simp only [tablesCheck, padTags, List.all_map, Function.comp_def, Padding.tagRows_check h]
  rfl

theorem padTags_embeddingCheck : (C.padTags h).embeddingCheck = C.embeddingCheck := by
  simp only [embeddingCheck, C.padTags_operations h]
  rfl

theorem padTags_structureCheck : (C.padTags h).structureCheck = C.structureCheck := by
  simp only [structureCheck, C.padTags_tablesCheck h, C.padTags_embeddingCheck h]
  rfl

theorem padTags_boundsCheck : (C.padTags h).boundsCheck = C.boundsCheck := by
  simp only [boundsCheck, C.padTags_data h]
  rfl

theorem padTags_check : (C.padTags h).check = C.check := by
  simp only [check, C.padTags_structureCheck h, C.padTags_boundsCheck h]

theorem padTags_separates (a b : CompareTy) :
    (C.padTags h).separates a b = C.separates a b := by
  simp only [separates, C.padTags_check h, C.padTags_data h]
  rfl

end Candidate

namespace Candidate

variable {Δ : Bounds} {names : List ModVar} (C : Candidate Δ names)
  {observations : Nat} (h : C.observations ≤ observations)

@[simp] theorem padObservations_observations : (C.padObservations h).observations = observations := rfl

theorem padObservations_pair (rs : List (Row (Code Δ names) (Fin C.tags)))
    (x y : Coordinates Δ names C.observations) :
    (C.padObservations h).pair rs (Padding.coordinates x) (Padding.coordinates y) =
      Padding.coordinates (C.pair rs x y) := by
  funext m
  exact Padding.extend_zeroExtend h C.embed order false false rs m (x m) (y m)

theorem padObservations_function (x y : Coordinates Δ names C.observations) :
    (C.padObservations h).function (Padding.coordinates x) (Padding.coordinates y) =
      Padding.coordinates (C.function x y) := by
  funext m
  exact Padding.extend_zeroExtend h C.embed ComparisonExecutableControls.future true false
    C.fnRows m (x 1) (y 1)

theorem padObservations_dataMap :
    ComparisonExecutableSyntax.DataMap C.data (C.padObservations h).data
      (Padding.coordinates (size := observations)) id := by
  refine ⟨rfl,(fun _ => rfl),(fun _ _ => rfl),?_,?_,
    (fun x y => (C.padObservations_function h x y).symm),?_,?_,
    (fun _ => rfl),rfl,rfl,?_,rfl⟩
  · exact fun p x y => (C.padObservations_pair h (C.prodAt p) x y).symm
  · exact fun p x y => (C.padObservations_pair h (C.sumAt p) x y).symm
  · intro x y
    funext m o
    by_cases hi : o.val < C.observations <;> simp [Padding.coordinates, Padding.zeroExtend, hi, data]
  · intro x y
    funext m o
    by_cases hi : o.val < C.observations <;> simp [Padding.coordinates, Padding.zeroExtend, hi, data]
  · funext m o
    simp [Padding.coordinates, Padding.zeroExtend, data]

theorem padObservations_eval (a : CompareTy) (p : Option ModExpr) :
    (C.padObservations h).data.eval a p = Padding.coordinates (C.data.eval a p) :=
  ((C.padObservations_dataMap h).eval_eq a p).symm

theorem padObservations_evalRaw (a : Ty) :
    (C.padObservations h).data.evalRaw a = Padding.coordinates (C.data.evalRaw a) :=
  ((C.padObservations_dataMap h).evalRaw_eq a).symm

theorem padObservations_monotoneCheck (x : Coordinates Δ names C.observations) :
    (C.padObservations h).monotoneCheck (Padding.coordinates x) = C.monotoneCheck x := by
  simp only [monotoneCheck, obs, C.padObservations_observations h,
    Padding.coordinates, Padding.below_zeroExtend h]

theorem padObservations_tablesCheck : (C.padObservations h).tablesCheck = C.tablesCheck := by
  simp only [tablesCheck, padObservations, obs, Padding.check_zeroExtend h]

theorem padObservations_embeddingCheck :
    (C.padObservations h).embeddingCheck = C.embeddingCheck := by
  simp only [embeddingCheck, ComparisonExecutableAgreement.check,
    ComparisonExecutableAgreement.indexCheck, ComparisonExecutableAgreement.latticeCheck,
    ComparisonExecutableAgreement.reflectCheck, ComparisonExecutableAgreement.actionCheck,
    ComparisonExecutableAgreement.constructorCheck, operations,
    ComparisonExecutableRangeAgreement.rawOperations]
  simp only [show (C.padObservations h).machine = C.machine from rfl,
    show (C.padObservations h).modes = C.modes from rfl,
    show (C.padObservations h).defined = (fun x => Padding.coordinates (C.defined x)) from rfl,
    show (C.padObservations h).prodRows = C.prodRows from rfl,
    show (C.padObservations h).sumRows = C.sumRows from rfl,
    Padding.coordinates_join, Padding.coordinates_meet, Padding.coordinates_shift,
    C.padObservations_pair h, C.padObservations_function h]
  simp only [obs, C.padObservations_observations h, Padding.vectorEq_coordinates h,
    Padding.vectorBelow_coordinates h, Padding.coordinates, Padding.below_zeroExtend h]
  rfl

theorem padObservations_structureCheck :
    (C.padObservations h).structureCheck = C.structureCheck := by
  simp only [structureCheck, C.padObservations_tablesCheck h, C.padObservations_embeddingCheck h,
    show (C.padObservations h).frozen = C.frozen.map (fun r => (r.1,Padding.coordinates r.2)) from rfl,
    List.all_map, Function.comp_def, C.padObservations_monotoneCheck h]
  rfl

theorem padObservations_boundsCheck : (C.padObservations h).boundsCheck = C.boundsCheck := by
  simp only [boundsCheck, C.padObservations_evalRaw h, obs, C.padObservations_observations h,
    Padding.vectorBelow_coordinates h]

theorem padObservations_check : (C.padObservations h).check = C.check := by
  simp only [check, C.padObservations_structureCheck h, C.padObservations_boundsCheck h]

theorem padObservations_separates (a b : CompareTy) :
    (C.padObservations h).separates a b = C.separates a b := by
  simp only [separates, C.padObservations_check h, C.padObservations_eval h,
    obs, C.padObservations_observations h, Padding.vectorBelow_coordinates h]

end Candidate
end ModalityInference.ComparisonFiniteCertificate
