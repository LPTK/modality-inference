import ModalityInference.Proofs.ComparisonExecutableTableSerialization

/-! Renaming finite controls, tags, and observations preserves table entries
and extensions. This transports the finite-model existence construction to
ordinary finite index types without adding semantic tests to a certificate. -/
namespace ModalityInference.ComparisonExecutableTableTransport

open ComparisonRelativeTables

variable {M N A B O Q : Type*}

def pull (eo : Q ≃ O) (x : O → Bool) : Q → Bool := fun q => x (eo q)

theorem pull_le_iff (eo : Q ≃ O) (x y : O → Bool) : pull eo x ≤ pull eo y ↔ x ≤ y := by
  constructor
  · intro h o
    simpa only [pull,Equiv.apply_symm_apply] using h (eo.symm o)
  · intro h q
    exact h (eo q)

theorem pull_direction_iff (eo : Q ≃ O) (p : Bool) (x y : O → Bool) :
    Direction p (pull eo x) (pull eo y) ↔ Direction p x y := by
  cases p <;> exact pull_le_iff eo _ _

def transport {embed : A → O → Bool} {p q : Bool} (T : IndexedTable embed M p q)
    (em : N ≃ M) (ea : B ≃ A) (eo : Q ≃ O) :
    IndexedTable (fun b => pull eo (embed (ea b))) N p q where
  table n := {
    entry a b c := (T.table (em n)).entry (ea a) (ea b) (ea c)
    mono := fun ha hb hx hy => (pull_le_iff eo _ _).mpr
      ((T.table (em n)).mono ha hb ((pull_direction_iff eo p _ _).mp hx)
        ((pull_direction_iff eo q _ _).mp hy)) }
  le n n' := T.le (em n) (em n')
  refl n := T.refl (em n)
  trans := T.trans
  cross_mono := fun h ha hb hx hy => (pull_le_iff eo _ _).mpr
    (T.cross_mono h ha hb ((pull_direction_iff eo p _ _).mp hx)
      ((pull_direction_iff eo q _ _).mp hy))

theorem transport_extend {embed : A → O → Bool} {p q : Bool} (T : IndexedTable embed M p q)
    (em : N ≃ M) (ea : B ≃ A) (eo : Q ≃ O) (n : N) (x y : O → Bool) :
    (transport T em ea eo).extend n (pull eo x) (pull eo y) = pull eo (T.extend (em n) x y) := by
  funext o
  apply Bool.eq_iff_iff.mpr
  simp only [IndexedTable.extend,decide_eq_true_eq,pull,transport]
  simp only [pull_direction_iff]
  constructor
  · rintro ⟨r,a,b,c,hl,hr,ha,hb,hc⟩
    exact ⟨em r,ea a,ea b,ea c,hl,hr,ha,hb,hc⟩
  · rintro ⟨r,a,b,c,hl,hr,ha,hb,hc⟩
    refine ⟨em.symm r,ea.symm a,ea.symm b,ea.symm c,?_⟩
    simpa only [Equiv.apply_symm_apply] using And.intro hl ⟨hr,ha,hb,hc⟩

end ModalityInference.ComparisonExecutableTableTransport
