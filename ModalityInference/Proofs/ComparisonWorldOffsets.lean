import ModalityInference.ComparisonWorldOffsets
import ModalityInference.Proofs.ComparisonWorldClauses

/-! Disjoint selector offsets preserve clause separation. Offsets count complete
world clauses, so concatenated endpoint queries share one scalar compilation. -/
namespace ModalityInference.ComparisonWorldOffsets
open ComparisonWorldClauses

@[simp] theorem nominal_zero (cs : List WorldClause) : nominal 0 cs=ComparisonWorldClauses.nominal cs := by
  simp [nominal,ComparisonWorldClauses.nominal]
@[simp] theorem scalar_zero (cs : List WorldClause) : scalar 0 cs=ComparisonWorldClauses.scalar cs := by
  simp [scalar,ComparisonWorldClauses.scalar]
@[simp] theorem choices_zero (cs : List WorldClause) : choices 0 cs=ComparisonWorldClauses.choices cs := by
  simp [choices,ComparisonWorldClauses.choices]

private theorem nominal_zip (offset : Nat) (cs : List WorldClause) :
    nominal offset cs=(cs.zipIdx offset).map (fun (c,i)=>selected i 0 c) := by
  rw [List.zipIdx_eq_map_add]
  simp [nominal,List.map_map]
private theorem scalar_zip (offset : Nat) (cs : List WorldClause) :
    scalar offset cs=(cs.zipIdx offset).flatMap (fun (c,i)=>
      ((blocks c).filter (· != 0)).map fun b=>selected i b c) := by
  rw [List.zipIdx_eq_map_add]
  simp [scalar,List.flatMap_map]
private theorem choices_zip (offset : Nat) (cs : List WorldClause) :
    choices offset cs=(cs.zipIdx offset).map (fun (c,i)=>(blocks c).map fun b=>(selectorAtom i b,true)) := by
  rw [List.zipIdx_eq_map_add]
  simp [choices,List.map_map]

theorem nominal_append (offset : Nat) (left right : List WorldClause) :
    nominal offset (left++right)=nominal offset left++nominal (offset+left.length) right := by
  simp only [nominal_zip,List.zipIdx_append,List.map_append]
theorem scalar_append (offset : Nat) (left right : List WorldClause) :
    scalar offset (left++right)=scalar offset left++scalar (offset+left.length) right := by
  simp only [scalar_zip,List.zipIdx_append,List.flatMap_append]
theorem choices_append (offset : Nat) (left right : List WorldClause) :
    choices offset (left++right)=choices offset left++choices (offset+left.length) right := by
  simp only [choices_zip,List.zipIdx_append,List.map_append]

def shiftChoice (offset : Nat) (choice : Nat → Bool) (v : Nat) : Bool :=
  choice (selectorAtom (offset+(Nat.unpair v).1) (Nat.unpair v).2)

@[simp] theorem shiftChoice_selector (offset : Nat) (choice : Nat → Bool) (i b : Nat) :
    shiftChoice offset choice (selectorAtom i b)=choice (selectorAtom (offset+i) b) := by
  simp [shiftChoice,selectorAtom]

theorem nominal_correct (offset : Nat) (choice value : Nat → Bool) (cs : List WorldClause) :
    CNFHolds (selectedValue choice value) (nominal offset cs) ↔
      CNFHolds (selectedValue (shiftChoice offset choice) value) (ComparisonWorldClauses.nominal cs) := by
  simp only [nominal,ComparisonWorldClauses.nominal,CNFHolds,List.forall_mem_map,selected_correct,shiftChoice_selector]

theorem scalar_correct (offset : Nat) (choice value : Nat → Bool) (cs : List WorldClause) :
    CNFHolds (selectedValue choice value) (scalar offset cs) ↔
      CNFHolds (selectedValue (shiftChoice offset choice) value) (ComparisonWorldClauses.scalar cs) := by
  simp only [scalar,ComparisonWorldClauses.scalar,CNFHolds,List.forall_mem_flatMap,
    List.forall_mem_map,selected_correct,shiftChoice_selector]

theorem choices_correct (offset : Nat) (choice : Nat → Bool) (cs : List WorldClause) :
    CNFHolds choice (choices offset cs) ↔
      CNFHolds (shiftChoice offset choice) (ComparisonWorldClauses.choices cs) := by
  simp only [choices,ComparisonWorldClauses.choices,CNFHolds,List.forall_mem_map]
  apply forall_congr' fun ci=>imp_congr_right fun _=>?_
  constructor
  · rintro ⟨v,p,hv,hp⟩
    obtain ⟨b,hb,he⟩:=List.mem_map.mp hv
    cases he
    exact ⟨selectorAtom ci.2 b,true,List.mem_map.mpr ⟨b,hb,rfl⟩,by simpa using hp⟩
  · rintro ⟨v,p,hv,hp⟩
    obtain ⟨b,hb,he⟩:=List.mem_map.mp hv
    cases he
    exact ⟨selectorAtom (offset+ci.2) b,true,List.mem_map.mpr ⟨b,hb,rfl⟩,by simpa using hp⟩

theorem selector_ranges_disjoint {offset leftSize i j b c : Nat}
    (hi : i<leftSize) : selectorAtom (offset+i) b≠selectorAtom (offset+leftSize+j) c := by
  intro h
  have he:=congrArg (fun v=>(Nat.unpair v).1) h
  simp only [selectorAtom,Nat.unpair_pair] at he
  omega

end ModalityInference.ComparisonWorldOffsets
