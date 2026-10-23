import ModalityInference.Proofs.ComparisonExecutableTables

/-! Every indexed table on finite tags and controls has a finite row-list
presentation accepted by the executable checks. The extraction is a proof of
representability; candidate validation uses only the supplied list. -/
namespace ModalityInference.ComparisonExecutableTables

open ComparisonRelativeTables

variable {M A O : Type*}

theorem allRows_mem (indices : List M) (tags : List A)
    (hi : ∀ m, m ∈ indices) (ha : ∀ a, a ∈ tags) (m : M) (a b c : A) :
    Row.mk m a b c ∈ allRows indices tags :=
  List.mem_flatMap.mpr ⟨m,hi m,List.mem_flatMap.mpr ⟨a,ha a,
    List.mem_flatMap.mpr ⟨b,ha b,List.mem_map.mpr ⟨c,ha c,rfl⟩⟩⟩⟩

noncomputable def serialize (indices : List M) (tags : List A)
    {embed : A → O → Bool} {p q : Bool} (T : IndexedTable embed M p q) : List (Row M A) :=
  (allRows indices tags).filter fun r => @decide ((T.table r.index).entry r.left r.right r.result)
    (Classical.propDecidable _)

theorem serialize_entry (indices : List M) (tags : List A)
    (hi : ∀ m, m ∈ indices) (ha : ∀ a, a ∈ tags)
    {embed : A → O → Bool} {p q : Bool} (T : IndexedTable embed M p q)
    (m : M) (a b c : A) :
    Row.mk m a b c ∈ serialize indices tags T ↔ (T.table m).entry a b c := by
  simp only [serialize,List.mem_filter,decide_eq_true_eq,allRows_mem indices tags hi ha,true_and]

theorem serialize_checked (observations : List O) (ho : ∀ o, o ∈ observations)
    (indices : List M) (tags : List A) (hi : ∀ m, m ∈ indices) (ha : ∀ a, a ∈ tags)
    (embed : A → O → Bool) (le : M → M → Bool) (p q : Bool)
    (T : IndexedTable embed M p q) (hle : ∀ m n, le m n = true ↔ T.le m n) :
    check observations embed le p q (serialize indices tags T) = true :=
  check_of_table observations ho embed le p q _ T hle (serialize_entry indices tags hi ha T)

theorem serialize_extend (observations : List O) (ho : ∀ o, o ∈ observations)
    (indices : List M) (tags : List A) (hi : ∀ m, m ∈ indices) (ha : ∀ a, a ∈ tags)
    (embed : A → O → Bool) (le : M → M → Bool) (p q : Bool)
    (T : IndexedTable embed M p q) (hle : ∀ m n, le m n = true ↔ T.le m n)
    (m : M) (x y : O → Bool) :
    extend observations embed le p q (serialize indices tags T) m x y = T.extend m x y :=
  extend_eq_of_table observations ho embed le p q _ T hle (serialize_entry indices tags hi ha T) m x y

end ModalityInference.ComparisonExecutableTables
