import ModalityInference.Proofs.ComparisonObserverRepresentatives

/-! Restricting unused modality names is idempotent, including the full
transition and exact ranges of restricted genuine observers. -/
namespace ModalityInference.ComparisonObserverRepresentatives

open ComparisonAlgebra ComparisonObserverGluing ComparisonObserverProfiles
  ComparisonObserverProfileExtension ComparisonModeRestriction

theorem restrict_mode_fixed {names : Finset ModVar} {m : ModExpr}
    (hs : m.vars ⊆ names) : m.subst (restrict names) = m := by
  rw [m.subst_congr (τ := ModExpr.var) (fun v hv => by simp [restrict, hs hv])]
  exact m.subst_id

theorem restrict_mode_idempotent (names : Finset ModVar) (m : ModExpr) :
    (m.subst (restrict names)).subst (restrict names) = m.subst (restrict names) :=
  restrict_mode_fixed (restrict_support names m)

theorem restrictedType_idempotent (names : Finset ModVar) (a : CompareTy) :
    restrictedType names (restrictedType names a) = restrictedType names a :=
  restrictedType_fixed (restrict_type_support names a)

theorem restrictedChild_transfer_fixed {Δ names} (hs : Δ.modVars ⊆ names)
    (g : Child Δ) (m : ModExpr) (x : Bool) :
    (restrictedChild hs g).transition.apply (m.subst (restrict names)) x =
      (restrictedChild hs g).transition.apply m x :=
  congrArg (fun q => g.transition.apply q x) (restrict_mode_idempotent names m)

theorem restrictedChild_value_idempotent {Δ names} (hs : Δ.modVars ⊆ names)
    (g : Child Δ) {a : CompareTy} (ha : Representable Δ .unit a) :
    booleanValue (restrictedChild hs (restrictedChild hs g)).observer a =
      booleanValue (restrictedChild hs g).observer a := by
  change booleanValue (restrictedObserver hs (restrictedObserver hs g.observer)) a =
    booleanValue (restrictedObserver hs g.observer) a
  rw [restrictedObserver_booleanValue hs _ ha,
    restrictedObserver_booleanValue hs _ (restricted_representable hs ha),
    restrictedObserver_booleanValue hs _ ha, restrictedType_idempotent]

theorem restrictedChild_range_idempotent {Δ names} (hs : Δ.modVars ⊆ names)
    (g : Child Δ) (x : Bool) :
    (restrictedChild hs (restrictedChild hs g)).Range x ↔
      (restrictedChild hs g).Range x := by
  constructor
  · exact restrictedChild_range hs (restrictedChild hs g)
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hv := restrictedChild_value_idempotent hs g
      (show Representable Δ .unit a.type from ⟨a.shaped, a.defined, a.shape_eq⟩)
    rw [booleanValue_carrier, booleanValue_carrier] at hv
    exact hv.trans ha

theorem representatives_transfer_fixed {Δ names} (hs : Δ.modVars ⊆ names)
    {boundary : List CompareTy} {g : Child Δ} (hg : g ∈ representatives hs boundary)
    (m : ModExpr) (x : Bool) :
    g.transition.apply (m.subst (restrict names)) x = g.transition.apply m x := by
  classical
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hg
  exact restrictedChild_transfer_fixed hs (representative k) m x

theorem representatives_range_fixed {Δ names} (hs : Δ.modVars ⊆ names)
    {boundary : List CompareTy} {g : Child Δ} (hg : g ∈ representatives hs boundary)
    (x : Bool) : (restrictedChild hs g).Range x ↔ g.Range x := by
  classical
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hg
  exact restrictedChild_range_idempotent hs (representative k) x

end ModalityInference.ComparisonObserverRepresentatives
