import ModalityInference.Proofs.ComparisonObserverProfileExtension

/-! A finite family of genuine children represents all restricted transfer,
range, and boundary profiles. Finiteness concerns observations, while every
representative remains an observer of the complete original algebra. -/
namespace ModalityInference.ComparisonObserverRepresentatives

open ComparisonAlgebra ComparisonObserverGluing ComparisonObserverProfiles
  ComparisonObserverProfileExtension

abbrev Key (names : Finset ModVar) (boundary : List CompareTy) :=
  (Fin (generators names).length → Bool × Bool) ×
    (Bool × Bool) × (Fin boundary.length → Bool)

noncomputable def key {Δ names} (hs : Δ.modVars ⊆ names) (g : Child Δ)
    (boundary : List CompareTy) : Key names boundary := by
  classical
  exact ⟨fun i => (g.transition.apply (generators names)[i] false,
      g.transition.apply (generators names)[i] true),
    (decide ((restrictedChild hs g).Range false),
      decide ((restrictedChild hs g).Range true)),
    fun i => booleanValue
      (restrictedChild hs g).observer boundary[i]⟩

theorem key_profile {Δ names} (hs : Δ.modVars ⊆ names) {g h : Child Δ}
    {boundary : List CompareTy} (he : key hs g boundary = key hs h boundary) :
    childProfile hs g boundary = childProfile hs h boundary := by
  unfold childProfile
  congr 1
  case e_transfer =>
    apply List.ext_getElem
    · simp [profile]
    · intro i hi _
      simpa [profile, key] using congrFun (congrArg Prod.fst he)
        ⟨i, by simpa [profile] using hi⟩
  case e_range => exact congrArg (fun k => k.2.1) he
  case e_values =>
    apply List.ext_getElem
    · simp
    · intro i hi _
      simpa [key] using congrFun (congrArg (fun k => k.2.2) he)
        ⟨i, by simpa using hi⟩

theorem key_card (names : Finset ModVar) (boundary : List CompareTy) :
    Fintype.card (Key names boundary) =
      2 ^ (2 * (8 + 10 * names.card) + 2 + boundary.length) := by
  simp only [Key, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, generators_length]
  simp [Nat.pow_add, Nat.pow_mul, Nat.pow_two, Nat.mul_assoc]

abbrev RealizedKey {Δ : Bounds} {names : Finset ModVar}
    (hs : Δ.modVars ⊆ names) (boundary : List CompareTy) :=
  {k : Key names boundary // ∃ g : Child Δ, key hs g boundary = k}

noncomputable def representative {Δ : Bounds} {names : Finset ModVar} {hs : Δ.modVars ⊆ names}
    {boundary : List CompareTy} (k : RealizedKey hs boundary) : Child Δ :=
  Classical.choose k.property

theorem representative_key {Δ : Bounds} {names : Finset ModVar} {hs : Δ.modVars ⊆ names}
    {boundary : List CompareTy} (k : RealizedKey hs boundary) :
    key hs (representative k) boundary = k.val := Classical.choose_spec k.property

noncomputable def representatives {Δ names} (hs : Δ.modVars ⊆ names)
    (boundary : List CompareTy) : Finset (Child Δ) := by
  classical
  exact Finset.univ.image (fun k : RealizedKey hs boundary =>
    restrictedChild hs (representative k))

theorem representatives_card {Δ : Bounds} {names : Finset ModVar} (hs : Δ.modVars ⊆ names)
    (boundary : List CompareTy) :
    (representatives hs boundary).card ≤
      2 ^ (2 * (8 + 10 * names.card) + 2 + boundary.length) := by
  classical
  calc
    (representatives hs boundary).card ≤ Fintype.card (RealizedKey hs boundary) :=
      (Finset.card_image_le).trans_eq (Finset.card_univ)
    _ ≤ Fintype.card (Key names boundary) := Fintype.card_subtype_le _
    _ = _ := key_card names boundary

/-- One genuine representative agrees on every guarded transfer, both exact
range fibers, and every requested boundary value. -/
theorem representatives_cover {Δ names} (hs : Δ.modVars ⊆ names)
    (boundary : List CompareTy) (g : Child Δ) :
    ∃ r ∈ representatives hs boundary,
      (∀ m, Entails Δ (.defined m) → ∀ x,
        (restrictedChild hs g).transition.apply m x = r.transition.apply m x) ∧
      (∀ x, (restrictedChild hs g).Range x ↔ r.Range x) ∧
      (∀ a ∈ boundary, booleanValue (restrictedChild hs g).observer a =
        booleanValue r.observer a) := by
  classical
  let k : RealizedKey hs boundary := ⟨key hs g boundary, g, rfl⟩
  have he : childProfile hs g boundary = childProfile hs (representative k) boundary :=
    key_profile hs (representative_key k).symm
  refine ⟨restrictedChild hs (representative k), ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  · exact fun _ hm x => childProfile_action hs he hm x
  · exact fun _ => ⟨childProfile_range hs he, childProfile_range hs he.symm⟩
  · exact fun _ ha => childProfile_value hs he ha

end ModalityInference.ComparisonObserverRepresentatives
