import ModalityInference.Proofs.ComparisonExecutableTableTransport
import ModalityInference.Proofs.ComparisonRelativeCoordinates

/-! Finite renaming of coordinate arrays preserves order, lattice operations,
shifts, and the differently indexed pair and function extensions. -/
namespace ModalityInference.ComparisonExecutableTableTransport

open ComparisonRelativeTables ComparisonRelativeCoordinates

variable {M N A B O Q : Type*} [PartialOrder M] [PartialOrder N]

def coordinates (em : N ≃o M) (eo : Q ≃ O) :
    LatticeHom (Coordinates M (O → Bool)) (Coordinates N (Q → Bool)) where
  toFun X := ⟨fun n => pull eo (X (em n)),fun _ _ h q => X.monotone (em.monotone h) (eo q)⟩
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

theorem coordinates_le_iff (em : N ≃o M) (eo : Q ≃ O)
    (X Y : Coordinates M (O → Bool)) : coordinates em eo X ≤ coordinates em eo Y ↔ X ≤ Y := by
  constructor
  · intro h m o
    have hh := h (em.symm m) (eo.symm o)
    change X (em (em.symm m)) (eo (eo.symm o)) ≤ Y (em (em.symm m)) (eo (eo.symm o)) at hh
    simpa only [OrderIso.apply_symm_apply,Equiv.apply_symm_apply] using hh
  · intro h n q
    exact h (em n) (eo q)

theorem coordinates_inverse (em : N ≃o M) (eo : Q ≃ O)
    (X : Coordinates M (O → Bool)) : coordinates em.symm eo.symm (coordinates em eo X) = X := by
  ext m o
  simp [coordinates,pull]

theorem coordinates_shift [CommMonoid M] [CommMonoid N]
    (hmul : ∀ m : M, Monotone (m * ·)) (hnmul : ∀ n : N, Monotone (n * ·))
    (em : N ≃o M) (hmap : ∀ m n, em (m * n) = em m * em n) (eo : Q ≃ O)
    (n : N) (X : Coordinates M (O → Bool)) :
    coordinates em eo (shift hmul (em n) X) = shift hnmul n (coordinates em eo X) := by
  ext r o
  exact congrArg (fun m => X m (eo o)) (hmap n r).symm

theorem coordinates_pair {embed : A → O → Bool}
    (T : IndexedTable embed M false false) (hle : ∀ {m n}, m ≤ n → T.le m n)
    (em : N ≃o M) (ea : B ≃ A) (eo : Q ≃ O)
    (X Y : Coordinates M (O → Bool)) :
    pair (transport T em.toEquiv ea eo) (fun h => hle (em.monotone h))
      (coordinates em eo X) (coordinates em eo Y) = coordinates em eo (pair T hle X Y) := by
  ext n o
  exact congrFun (transport_extend T em.toEquiv ea eo n (X (em n)) (Y (em n))) o

theorem coordinates_fn [One M] [One N] {embed : A → O → Bool}
    (T : IndexedTable embed M true false) (hle : ∀ {m n}, m ≤ n → T.le m n)
    (em : N ≃o M) (hone : em 1 = 1) (ea : B ≃ A) (eo : Q ≃ O)
    (X Y : Coordinates M (O → Bool)) :
    fn (transport T em.toEquiv ea eo) (fun h => hle (em.monotone h))
      (coordinates em eo X) (coordinates em eo Y) = coordinates em eo (fn T hle X Y) := by
  ext n o
  change (transport T em.toEquiv ea eo).extend n (pull eo (X (em 1))) (pull eo (Y (em 1))) o = _
  rw [hone,transport_extend]
  rfl

end ModalityInference.ComparisonExecutableTableTransport
