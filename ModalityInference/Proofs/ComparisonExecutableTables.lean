import ModalityInference.ComparisonExecutableTables
import ModalityInference.Proofs.ComparisonRelativeTables

/-! The finite checks exactly certify the indexed-table conditions, and their
executable extension agrees with the semantic extension at every input. -/
namespace ModalityInference.ComparisonExecutableTables

open ComparisonRelativeTables

variable {M A O : Type*} (observations : List O) (hobs : ∀ o, o ∈ observations)

include hobs

theorem below_correct (x y : O → Bool) : below observations x y = true ↔ x ≤ y := by
  simp only [below,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true']
  constructor
  · intro h o
    exact Bool.le_iff_imp.mpr (fun hx => (h o (hobs o)).resolve_left (by simp [hx]))
  · intro h o _
    cases hx : x o
    · exact Or.inl rfl
    · exact Or.inr (Bool.le_iff_imp.mp (h o) hx)

theorem direction_correct (p : Bool) (x y : O → Bool) :
    direction observations p x y = true ↔ Direction p x y := by
  cases p <;> exact below_correct observations hobs _ _

theorem compatible_correct (embed : A → O → Bool) (le : M → M → Bool)
    (p q : Bool) (a b : Row M A) :
    compatible observations embed le p q a b = true ↔
      (le a.index b.index = true → Direction p (embed a.left) (embed b.left) →
        Direction q (embed a.right) (embed b.right) → embed a.result ≤ embed b.result) := by
  simp only [compatible,Bool.or_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,Bool.and_eq_true,
    below_correct observations hobs,direction_correct observations hobs]
  tauto

theorem check_correct (embed : A → O → Bool) (le : M → M → Bool)
    (p q : Bool) (rows : List (Row M A)) :
    check observations embed le p q rows = true ↔
      ∀ a ∈ rows, ∀ b ∈ rows, le a.index b.index = true →
        Direction p (embed a.left) (embed b.left) →
        Direction q (embed a.right) (embed b.right) → embed a.result ≤ embed b.result := by
  simp only [check,List.all_eq_true,compatible_correct observations hobs]

def table (embed : A → O → Bool) (le : M → M → Bool) (p q : Bool)
    (rows : List (Row M A)) (hrefl : ∀ m, le m m = true)
    (htrans : ∀ {m n r}, le m n = true → le n r = true → le m r = true)
    (hcheck : check observations embed le p q rows = true) : IndexedTable embed M p q where
  table m := {
    entry a b c := Row.mk m a b c ∈ rows
    mono := by
      intro a b c x y z ha hb hx hy
      exact (check_correct observations hobs embed le p q rows).mp hcheck
        _ ha _ hb (hrefl m) hx hy }
  le m n := le m n = true
  refl := hrefl
  trans := htrans
  cross_mono := by
    intro m n a b c x y z hmn ha hb hx hy
    exact (check_correct observations hobs embed le p q rows).mp hcheck
      _ ha _ hb hmn hx hy

theorem extend_eq (embed : A → O → Bool) (le : M → M → Bool) (p q : Bool)
    (rows : List (Row M A)) (hrefl : ∀ m, le m m = true)
    (htrans : ∀ {m n r}, le m n = true → le n r = true → le m r = true)
    (hcheck : check observations embed le p q rows = true) (m : M) (x y : O → Bool) :
    extend observations embed le p q rows m x y =
      (table observations hobs embed le p q rows hrefl htrans hcheck).extend m x y := by
  funext o
  apply Bool.eq_iff_iff.mpr
  simp only [extend,List.any_eq_true,Bool.and_eq_true,direction_correct observations hobs,
    IndexedTable.extend,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨r,a,b,c⟩,hr,⟨⟨hl,ha⟩,hb⟩,hc⟩
    exact ⟨r,a,b,c,hl,hr,ha,hb,hc⟩
  · rintro ⟨r,a,b,c,hl,hr,ha,hb,hc⟩
    exact ⟨⟨r,a,b,c⟩,hr,⟨⟨hl,ha⟩,hb⟩,hc⟩

theorem check_of_table (embed : A → O → Bool) (le : M → M → Bool) (p q : Bool)
    (rows : List (Row M A)) (T : IndexedTable embed M p q)
    (hle : ∀ m n, le m n = true ↔ T.le m n)
    (hrows : ∀ m a b c, Row.mk m a b c ∈ rows ↔ (T.table m).entry a b c) :
    check observations embed le p q rows = true := by
  apply (check_correct observations hobs embed le p q rows).mpr
  intro a ha b hb hl hx hy
  exact T.cross_mono ((hle _ _).mp hl)
    ((hrows ..).mp ha) ((hrows ..).mp hb) hx hy

theorem extend_eq_of_table (embed : A → O → Bool) (le : M → M → Bool) (p q : Bool)
    (rows : List (Row M A)) (T : IndexedTable embed M p q)
    (hle : ∀ m n, le m n = true ↔ T.le m n)
    (hrows : ∀ m a b c, Row.mk m a b c ∈ rows ↔ (T.table m).entry a b c)
    (m : M) (x y : O → Bool) :
    extend observations embed le p q rows m x y = T.extend m x y := by
  funext o
  apply Bool.eq_iff_iff.mpr
  simp only [extend,List.any_eq_true,Bool.and_eq_true,direction_correct observations hobs,
    IndexedTable.extend,decide_eq_true_eq,hle]
  constructor
  · rintro ⟨⟨r,a,b,c⟩,hr,⟨⟨hl,ha⟩,hb⟩,hc⟩
    exact ⟨r,a,b,c,hl,(hrows ..).mp hr,ha,hb,hc⟩
  · rintro ⟨r,a,b,c,hl,hr,ha,hb,hc⟩
    exact ⟨⟨r,a,b,c⟩,(hrows ..).mpr hr,⟨⟨hl,ha⟩,hb⟩,hc⟩

end ModalityInference.ComparisonExecutableTables
