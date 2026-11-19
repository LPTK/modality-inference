import ModalityInference.Proofs.ComparisonRawCarrierInterpretation

namespace ModalityInference.ComparisonRawCarrierRestriction

open ComparisonRawCarrierIdeals

/-- Every declared raw subtype edge lies inside the fixed capsule boundary. -/
def Covers (Δ : Bounds) (K : Set Token) : Prop :=
  ∀ a b, Constraint.sub a b ∈ Δ → Carrier Δ K (.ofTy a) ∧ Carrier Δ K (.ofTy b)

theorem Related.bound {Δ K a b} (hc : Covers Δ K) (h : Constraint.sub a b ∈ Δ) :
    Related Δ K (.ofTy a) (.ofTy b) :=
  .of_derivation (.atom (hc a b h).1 (hc a b h).2 (.bound h))

theorem Related.equation {Δ K a b} (h : ComparisonAlgebra.Equation Δ a b) :
    Related Δ K a b :=
  .of_derivation (.atom (carrier_defined (ComparisonDefinedCovers.equation_defined h).1)
    (carrier_defined (ComparisonDefinedCovers.equation_defined h).2) (.equation h))

theorem Related.equationRev {Δ K a b} (h : ComparisonAlgebra.Equation Δ a b) :
    Related Δ K b a :=
  .of_derivation (.atom (carrier_defined (ComparisonDefinedCovers.equation_defined h).2)
    (carrier_defined (ComparisonDefinedCovers.equation_defined h).1) (.equationRev h))

theorem Related.joinLeft {Δ K a b} : Related Δ K a (.join a b) :=
  ⟨fun _ h => .base ((denote Δ K a).lower.carrier h) ((denote Δ K a).lower.shaped h) (.inl h),
    fun _ h => h.1⟩

theorem Related.joinRight {Δ K a b} : Related Δ K b (.join a b) :=
  ⟨fun _ h => .base ((denote Δ K b).lower.carrier h) ((denote Δ K b).lower.shaped h) (.inr h),
    fun _ h => h.2⟩

theorem Related.meetLeft {Δ K a b} : Related Δ K (.meet a b) a :=
  ⟨fun _ h => h.1,
    fun _ h => .base ((denote Δ K a).upper.carrier h) ((denote Δ K a).upper.shaped h) (.inl h)⟩

theorem Related.meetRight {Δ K a b} : Related Δ K (.meet a b) b :=
  ⟨fun _ h => h.2,
    fun _ h => .base ((denote Δ K b).upper.carrier h) ((denote Δ K b).upper.shaped h) (.inr h)⟩

theorem Related.joinLeast {Δ K a b c} (ha : Related Δ K a c) (hb : Related Δ K b c) :
    Related Δ K (.join a b) c :=
  ⟨fun _ h => h.lift _ (denote Δ K c).lower
      (fun {t} ht _ _ => ht.elim (ha.1 t) (hb.1 t)),
    fun _ h => ⟨ha.2 _ h, hb.2 _ h⟩⟩

theorem Related.meetGreatest {Δ K a b c} (hb : Related Δ K a b) (hc : Related Δ K a c) :
    Related Δ K a (.meet b c) :=
  ⟨fun _ h => ⟨hb.1 _ h, hc.1 _ h⟩,
    fun _ h => h.lift _ (denote Δ K a).upper
      (fun {t} ht _ _ => ht.elim (hb.2 t) (hc.2 t))⟩

theorem Related.clamp {Δ K b a t m}
    (hba : ComparisonAlgebra.Compatible Δ b a)
    (hat : ComparisonAlgebra.Compatible Δ a t) (hm : ComparisonAlgebra.DefinedMode Δ m)
    (h₁ : Related Δ K b a) (h₂ : Related Δ K a t) :
    Related Δ K (.modal a m) (.meet (.join a (.modal b m)) (.modal t m)) :=
  .of_derivation (.clamp hba hat hm
    (h₁.derivation (carrier_defined hba.2.1) (carrier_defined hba.2.2) hba.1.1 hba.1.2.1)
    (h₂.derivation (carrier_defined hat.2.1) (carrier_defined hat.2.2) hat.1.1 hat.1.2.1))

theorem Related.clampRev {Δ K b a t m}
    (hba : ComparisonAlgebra.Compatible Δ b a)
    (hat : ComparisonAlgebra.Compatible Δ a t) (hm : ComparisonAlgebra.DefinedMode Δ m)
    (h₁ : Related Δ K b a) (h₂ : Related Δ K a t) :
    Related Δ K (.meet (.join a (.modal b m)) (.modal t m)) (.modal a m) :=
  .of_derivation (.clampRev hba hat hm
    (h₁.derivation (carrier_defined hba.2.1) (carrier_defined hba.2.2) hba.1.1 hba.1.2.1)
    (h₂.derivation (carrier_defined hat.2.1) (carrier_defined hat.2.2) hat.1.1 hat.1.2.1))

def edgeSupport (Δ : Bounds) : Constraint → Set Token
  | .sub a b => support Δ (.ofTy a) none ∪ support Δ (.ofTy b) none
  | _ => ∅

def contextSupport (Δ : Bounds) : Bounds → Set Token
  | [] => ∅
  | c :: cs => edgeSupport Δ c ∪ contextSupport Δ cs

theorem edgeSupport_finite (Δ : Bounds) (c : Constraint) : (edgeSupport Δ c).Finite := by
  cases c <;> first
    | exact (support_finite _ _ _).union (support_finite _ _ _)
    | exact Set.finite_empty

theorem contextSupport_finite (Δ Γ : Bounds) : (contextSupport Δ Γ).Finite := by
  induction Γ with
  | nil => exact Set.finite_empty
  | cons c cs ih => exact (edgeSupport_finite Δ c).union ih

theorem edgeSupport_subset {Δ Γ c} (h : c ∈ Γ) : edgeSupport Δ c ⊆ contextSupport Δ Γ := by
  induction Γ with
  | nil => exact False.elim (List.not_mem_nil h)
  | cons d ds ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Set.subset_union_left
    · exact (ih h).trans Set.subset_union_right

/-- A finite capsule boundary determined only by the declared subtype edges
and the two endpoints being compared. -/
def boundary (Δ : Bounds) (a b : CompareTy) : Set Token :=
  contextSupport Δ Δ ∪ support Δ a none ∪ support Δ b none

theorem boundary_finite (Δ : Bounds) (a b : CompareTy) : (boundary Δ a b).Finite :=
  ((contextSupport_finite Δ Δ).union (support_finite Δ a none)).union (support_finite Δ b none)

theorem boundary_covers (Δ : Bounds) (a b : CompareTy) : Covers Δ (boundary Δ a b) :=
  fun _ _ h => ⟨(Set.subset_union_left.trans (edgeSupport_subset h)).trans
    (Set.subset_union_left.trans Set.subset_union_left),
    (Set.subset_union_right.trans (edgeSupport_subset h)).trans
    (Set.subset_union_left.trans Set.subset_union_left)⟩

theorem boundary_left (Δ : Bounds) (a b : CompareTy) : Carrier Δ (boundary Δ a b) a :=
  Set.subset_union_right.trans Set.subset_union_left

theorem boundary_right (Δ : Bounds) (a b : CompareTy) : Carrier Δ (boundary Δ a b) b :=
  Set.subset_union_right

end ModalityInference.ComparisonRawCarrierRestriction
