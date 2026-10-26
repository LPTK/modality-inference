import ModalityInference.ComparisonFiniteCertificate
import ModalityInference.Proofs.ComparisonExecutableControls
import ModalityInference.Proofs.ComparisonExecutableCoordinateOperations
import ModalityInference.Proofs.ComparisonRelativeSyntax

/-! Passing the finite table and frozen-value checks constructs the ordered
coordinate model's structural data. Its defined base values are supplied by
the separate embedding check. -/
namespace ModalityInference.ComparisonFiniteCertificate

open ComparisonFiniteControlEncoding ComparisonExecutableTables
  ComparisonExecutableControls ComparisonRelativeTables

variable {Δ : Bounds} {names : List ModVar}

theorem index_mem (m : Code Δ names) : m ∈ indices Δ names :=
  List.mem_map.mpr ⟨m.index,List.mem_finRange _,by cases m; rfl⟩

namespace Candidate

variable (C : Candidate Δ names)

abbrev OrderedCoordinates := ComparisonRelativeCoordinates.Coordinates
  (Code Δ names) (Fin C.observations → Bool)

theorem obs_mem (o : Fin C.observations) : o ∈ C.obs := List.mem_finRange _

theorem names_valid (h : C.structureCheck = true) : Δ.modVars ⊆ names.toFinset :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).1).1

theorem tables_valid (h : C.structureCheck = true) : C.tablesCheck = true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).2

theorem frozen_valid (h : C.structureCheck = true) {row} (hr : row ∈ C.frozen) :
    C.monotoneCheck row.2 = true :=
  List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 row hr

theorem monotoneCheck_correct (x : Coordinates Δ names C.observations) :
    C.monotoneCheck x = true ↔ Monotone x := by
  simp only [monotoneCheck,List.all_eq_true,index_mem,true_implies,Bool.or_eq_true,
    Bool.not_eq_true',Bool.eq_false_iff,ne_eq,below_correct C.obs C.obs_mem,
    or_iff_not_imp_left,not_not]
  rfl

theorem literalRows_valid (ordinary : List (Row (Code Δ names) (Fin C.tags)))
    (literals : List (ModExpr × List (Row (Code Δ names) (Fin C.tags))))
    (ho : ComparisonExecutableTables.check C.obs C.embed order false false ordinary = true)
    (hl : ∀ row ∈ literals, ComparisonExecutableTables.check C.obs C.embed order false false row.2 = true)
    (p : Option ModExpr) :
    ComparisonExecutableTables.check C.obs C.embed order false false (literalRows ordinary literals p) = true := by
  cases p with
  | none => exact ho
  | some p =>
    simp only [literalRows]
    cases hf : literals.find? (fun row => decide (row.1 = p)) with
    | none => rfl
    | some row => simpa only [Option.map_some,Option.getD_some] using hl row (List.mem_of_find?_eq_some hf)

theorem table_checks (h : C.structureCheck = true) :
    ComparisonExecutableTables.check C.obs C.embed order false false C.prodRows = true ∧
    ComparisonExecutableTables.check C.obs C.embed order false false C.sumRows = true ∧
    ComparisonExecutableTables.check C.obs C.embed future true false C.fnRows = true ∧
    (∀ row ∈ C.prodLiterals, ComparisonExecutableTables.check C.obs C.embed order false false row.2 = true) ∧
    (∀ row ∈ C.sumLiterals, ComparisonExecutableTables.check C.obs C.embed order false false row.2 = true) := by
  simpa only [tablesCheck,Bool.and_eq_true,List.all_eq_true,and_assoc] using C.tables_valid h

theorem prodAt_valid (h : C.structureCheck = true) (p : Option ModExpr) :
    ComparisonExecutableTables.check C.obs C.embed order false false (C.prodAt p) = true :=
  C.literalRows_valid C.prodRows C.prodLiterals (C.table_checks h).1 (C.table_checks h).2.2.2.1 p

theorem sumAt_valid (h : C.structureCheck = true) (p : Option ModExpr) :
    ComparisonExecutableTables.check C.obs C.embed order false false (C.sumAt p) = true :=
  C.literalRows_valid C.sumRows C.sumLiterals (C.table_checks h).2.1 (C.table_checks h).2.2.2.2 p

theorem fn_valid (h : C.structureCheck = true) :
    ComparisonExecutableTables.check C.obs C.embed future true false C.fnRows = true :=
  (C.table_checks h).2.2.1

def prodTable (h : C.structureCheck = true) (p : Option ModExpr) :
    IndexedTable C.embed (Code Δ names) false false :=
  ComparisonExecutableTables.table C.obs C.obs_mem C.embed order false false (C.prodAt p)
    order_refl order_trans (C.prodAt_valid h p)

def sumTable (h : C.structureCheck = true) (p : Option ModExpr) :
    IndexedTable C.embed (Code Δ names) false false :=
  ComparisonExecutableTables.table C.obs C.obs_mem C.embed order false false (C.sumAt p)
    order_refl order_trans (C.sumAt_valid h p)

def fnTable (h : C.structureCheck = true) : IndexedTable C.embed (Code Δ names) true false :=
  ComparisonExecutableTables.table C.obs C.obs_mem C.embed future true false C.fnRows
    future_refl future_trans (C.fn_valid h)

@[simp] theorem prodTable_le (h : C.structureCheck = true) (p : Option ModExpr) (m n : Code Δ names) :
    (C.prodTable h p).le m n ↔ m ≤ n := Iff.rfl

@[simp] theorem sumTable_le (h : C.structureCheck = true) (p : Option ModExpr) (m n : Code Δ names) :
    (C.sumTable h p).le m n ↔ m ≤ n := Iff.rfl

@[simp] theorem fnTable_le (h : C.structureCheck = true) (m n : Code Δ names) :
    (C.fnTable h).le m n ↔ future m n = true := Iff.rfl

def frozenValues (h : C.structureCheck = true) : List (CompareTy × C.OrderedCoordinates) :=
  C.frozen.attach.map fun row =>
    (row.val.1,⟨row.val.2,(C.monotoneCheck_correct row.val.2).mp (C.frozen_valid h row.property)⟩)

theorem frozenValues_map (h : C.structureCheck = true) :
    (C.frozenValues h).map (fun row => (row.1,fun m => row.2 m)) = C.frozen := by
  simp only [frozenValues,List.map_map,Function.comp_def,OrderHom.coe_mk]
  exact List.attach_map_subtype_val _

def model (h : C.structureCheck = true)
    (atom : TypeVar → C.OrderedCoordinates) (unit credit : C.OrderedCoordinates) :
    ComparisonRelativeSyntax.Model Δ (Code Δ names) (Fin C.tags) (Fin C.observations) C.embed where
  mul_mono := mul_mono
  prodTable := C.prodTable h
  prod_order := fun _ {_ _} hmn => hmn
  sumTable := C.sumTable h
  sum_order := fun _ {_ _} hmn => hmn
  fnTable := C.fnTable h
  fn_order := order_future
  fn_post := future_post
  controls := controlMap (C.names_valid h)
  atom := atom
  unit := unit
  credit := credit
  frozen := C.frozenValues h

end Candidate
end ModalityInference.ComparisonFiniteCertificate
