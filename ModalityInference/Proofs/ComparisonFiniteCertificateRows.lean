import ModalityInference.ComparisonFiniteCertificateRows
import ModalityInference.Proofs.ComparisonFiniteCertificateTables

/-! Row canonicalization preserves table membership and every executable
operation, while bounding each table by the size of the finite row universe. -/
namespace ModalityInference.ComparisonFiniteCertificate

open ComparisonFiniteControlEncoding ComparisonExecutableTables

variable {Δ : Bounds} {names : List ModVar} {tags : Nat}

theorem canonicalRows_mem (rows : List (Row (Code Δ names) (Fin tags)))
    (row : Row (Code Δ names) (Fin tags)) : row ∈ canonicalRows rows ↔ row ∈ rows := by
  cases row
  simp [canonicalRows, allRows, index_mem]

theorem allRows_length {M A : Type*} (ms : List M) (as : List A) :
    (allRows ms as).length = ms.length * as.length ^ 3 := by
  simp [allRows, List.length_flatMap, pow_succ, Nat.mul_assoc]

theorem canonicalRows_length (rows : List (Row (Code Δ names) (Fin tags))) :
    (canonicalRows rows).length ≤ (labels Δ names).length * tags ^ 3 := by
  calc
    _ ≤ (allRows (indices Δ names) (List.finRange tags)).length := List.length_filter_le _ _
    _ = _ := by simp only [allRows_length, indices, List.length_map, List.length_finRange]

theorem canonicalRows_nil : canonicalRows ([] : List (Row (Code Δ names) (Fin tags))) = [] := by
  simp [canonicalRows]

theorem canonicalRows_check {O : Type*} (obs : List O) (embed : Fin tags → O → Bool)
    (le : Code Δ names → Code Δ names → Bool) (p q : Bool)
    (rows : List (Row (Code Δ names) (Fin tags))) :
    ComparisonExecutableTables.check obs embed le p q (canonicalRows rows) =
      ComparisonExecutableTables.check obs embed le p q rows :=
  Bool.eq_iff_iff.mpr (by simp only [ComparisonExecutableTables.check, List.all_eq_true,
    canonicalRows_mem])

theorem canonicalRows_extend {O : Type*} (obs : List O) (embed : Fin tags → O → Bool)
    (le : Code Δ names → Code Δ names → Bool) (p q : Bool)
    (rows : List (Row (Code Δ names) (Fin tags))) (m : Code Δ names) (x y : O → Bool) :
    extend obs embed le p q (canonicalRows rows) m x y = extend obs embed le p q rows m x y :=
  funext fun _ => Bool.eq_iff_iff.mpr (by simp only [extend, List.any_eq_true, canonicalRows_mem])

theorem canonicalRows_literalRows (ordinary : List (Row (Code Δ names) (Fin tags)))
    (literals : List (ModExpr × List (Row (Code Δ names) (Fin tags)))) (p : Option ModExpr) :
    literalRows (canonicalRows ordinary) (literals.map fun row => (row.1,canonicalRows row.2)) p =
      canonicalRows (literalRows ordinary literals p) := by
  cases p with
  | none => rfl
  | some p =>
    simp only [literalRows, List.find?_map]
    cases h : literals.find? (fun row => decide (row.1 = p)) <;>
      simp [Function.comp_def, h, canonicalRows_nil]

namespace Candidate

variable (C : Candidate Δ names)

theorem canonicalizeRows_prodRows : C.canonicalizeRows.prodRows = canonicalRows C.prodRows := rfl

theorem canonicalizeRows_sumRows : C.canonicalizeRows.sumRows = canonicalRows C.sumRows := rfl

theorem canonicalizeRows_pair (rows : List (Row (Code Δ names) (Fin C.tags))) :
    C.canonicalizeRows.pair (canonicalRows rows) = C.pair rows :=
  funext fun x => funext fun y => funext fun m =>
    canonicalRows_extend C.obs C.embed order false false rows m (x m) (y m)

theorem canonicalizeRows_function : C.canonicalizeRows.function = C.function :=
  funext fun x => funext fun y => funext fun m =>
    canonicalRows_extend C.obs C.embed ComparisonExecutableControls.future true false
      C.fnRows m (x 1) (y 1)

theorem canonicalizeRows_prodAt (p : Option ModExpr) :
    C.canonicalizeRows.prodAt p = canonicalRows (C.prodAt p) :=
  canonicalRows_literalRows C.prodRows C.prodLiterals p

theorem canonicalizeRows_sumAt (p : Option ModExpr) :
    C.canonicalizeRows.sumAt p = canonicalRows (C.sumAt p) :=
  canonicalRows_literalRows C.sumRows C.sumLiterals p

theorem canonicalizeRows_data : C.canonicalizeRows.data = C.data := by
  simp only [data, canonicalizeRows_prodAt, canonicalizeRows_sumAt,
    canonicalizeRows_pair, canonicalizeRows_function]
  rfl

theorem canonicalizeRows_operations : C.canonicalizeRows.operations = C.operations := by
  simp only [operations, canonicalizeRows_prodRows, canonicalizeRows_sumRows,
    canonicalizeRows_pair, canonicalizeRows_function]
  rfl

theorem canonicalizeRows_tablesCheck : C.canonicalizeRows.tablesCheck = C.tablesCheck := by
  simp only [tablesCheck, canonicalizeRows, canonicalRows_check, List.all_map,
    Function.comp_def]
  rfl

theorem canonicalizeRows_embeddingCheck : C.canonicalizeRows.embeddingCheck = C.embeddingCheck := by
  simp only [embeddingCheck, canonicalizeRows_operations]
  rfl

theorem canonicalizeRows_structureCheck : C.canonicalizeRows.structureCheck = C.structureCheck := by
  simp only [structureCheck, canonicalizeRows_tablesCheck, canonicalizeRows_embeddingCheck]
  rfl

theorem canonicalizeRows_boundsCheck : C.canonicalizeRows.boundsCheck = C.boundsCheck := by
  simp only [boundsCheck, canonicalizeRows_data]
  rfl

theorem canonicalizeRows_check : C.canonicalizeRows.check = C.check := by
  simp only [check, canonicalizeRows_structureCheck, canonicalizeRows_boundsCheck]

theorem canonicalizeRows_eval (a : CompareTy) (p : Option ModExpr) :
    C.canonicalizeRows.data.eval a p = C.data.eval a p := by rw [canonicalizeRows_data]

theorem canonicalizeRows_separates (a b : CompareTy) :
    C.canonicalizeRows.separates a b = C.separates a b := by
  simp only [separates, canonicalizeRows_check, canonicalizeRows_data]
  rfl

theorem canonicalizeRows_prodRows_length :
    C.canonicalizeRows.prodRows.length ≤ (labels Δ names).length * C.tags ^ 3 :=
  canonicalRows_length C.prodRows

theorem canonicalizeRows_sumRows_length :
    C.canonicalizeRows.sumRows.length ≤ (labels Δ names).length * C.tags ^ 3 :=
  canonicalRows_length C.sumRows

theorem canonicalizeRows_fnRows_length :
    C.canonicalizeRows.fnRows.length ≤ (labels Δ names).length * C.tags ^ 3 :=
  canonicalRows_length C.fnRows

theorem canonicalizeRows_prodLiteralRows_length {row}
    (hrow : row ∈ C.canonicalizeRows.prodLiterals) :
    row.2.length ≤ (labels Δ names).length * C.tags ^ 3 := by
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp hrow
  exact canonicalRows_length original.2

theorem canonicalizeRows_sumLiteralRows_length {row}
    (hrow : row ∈ C.canonicalizeRows.sumLiterals) :
    row.2.length ≤ (labels Δ names).length * C.tags ^ 3 := by
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp hrow
  exact canonicalRows_length original.2

theorem canonicalizeRows_literalKeys :
    C.canonicalizeRows.prodLiterals.map Prod.fst = C.prodLiterals.map Prod.fst ∧
    C.canonicalizeRows.sumLiterals.map Prod.fst = C.sumLiterals.map Prod.fst := by
  simp [canonicalizeRows, List.map_map]

end Candidate

end ModalityInference.ComparisonFiniteCertificate
