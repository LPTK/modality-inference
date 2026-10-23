import ModalityInference.Proofs.ComparisonRawHeadGuardedLattice

/-! Finite partial-head support for a boundary term. Products and sums retain
their whole head and pass the literal suffix to both operands. Total suffixes
inspect function and lattice operands; partial suffixes freeze those heads. -/
namespace ModalityInference.ComparisonRawHeadRestriction

open ComparisonPartialStructuredCapsule

noncomputable section
attribute [local instance] Classical.propDecidable

def Suffix.HeadEquivalent (Δ : Bounds) (left right : Suffix) : Prop :=
  (left.total Δ ↔ right.total Δ) ∧
    ∀ a, heads Δ (left.apply a) = heads Δ (right.apply a)

theorem heads_prepend (Δ : Bounds) (suffix : Suffix) (m : ModExpr) (a : CompareTy) :
    heads Δ ((suffix.prepend m).apply a) = heads Δ (suffix.apply (.modal a m)) := by
  cases suffix with
  | none => rfl
  | some n => exact heads_compose Δ a m n

theorem Suffix.HeadEquivalent.prepend {Δ : Bounds} {left right : Suffix}
    (h : Suffix.HeadEquivalent Δ left right) (m : ModExpr) :
    Suffix.HeadEquivalent Δ (left.prepend m) (right.prepend m) := by
  constructor
  · rw [Suffix.total_prepend, Suffix.total_prepend, h.1]
  · intro a
    rw [heads_prepend, heads_prepend]
    exact h.2 (.modal a m)

theorem Suffix.headEquivalent_none {Δ : Bounds} {suffix : Suffix}
    (h : suffix.total Δ) : Suffix.HeadEquivalent Δ suffix none := by
  refine ⟨by simp only [Suffix.total]; exact iff_true_intro h, ?_⟩
  intro a
  cases suffix with
  | none => rfl
  | some m => exact heads_modal_total h a

/-- The current product or sum head is retained in addition to the inherited
operand heads. There is no closure under constructing new products or sums. -/
def support (Δ : Bounds) : CompareTy → Suffix → Set CompareTy
  | .modal a m, suffix => support Δ a (suffix.prepend m)
  | .prod a b, suffix =>
      heads Δ (suffix.apply (.prod a b)) ∪ (support Δ a suffix ∪ support Δ b suffix)
  | .sum a b, suffix =>
      heads Δ (suffix.apply (.sum a b)) ∪ (support Δ a suffix ∪ support Δ b suffix)
  | .fn a b, suffix =>
      heads Δ (suffix.apply (.fn a b)) ∪
        if suffix.total Δ then support Δ a none ∪ support Δ b none else ∅
  | .join a b, suffix =>
      heads Δ (suffix.apply (.join a b)) ∪
        if suffix.total Δ then support Δ a none ∪ support Δ b none else ∅
  | .meet a b, suffix =>
      heads Δ (suffix.apply (.meet a b)) ∪
        if suffix.total Δ then support Δ a none ∪ support Δ b none else ∅
  | a, suffix => heads Δ (suffix.apply a)

theorem support_suffix_congr {Δ : Bounds} {left right : Suffix}
    (h : Suffix.HeadEquivalent Δ left right) (a : CompareTy) :
    support Δ a left = support Δ a right := by
  induction a generalizing left right with
  | modal a m ih => exact ih (h.prepend m)
  | prod a b ia ib | sum a b ia ib => simp only [support, h.2, ia h, ib h]
  | fn a b ia ib | join a b ia ib | meet a b ia ib => simp only [support, h.1, h.2]
  | var | unit | credit => exact h.2 _

theorem support_total {Δ : Bounds} {suffix : Suffix} (h : suffix.total Δ) (a : CompareTy) :
    support Δ a suffix = support Δ a none := support_suffix_congr (Suffix.headEquivalent_none h) a

theorem support_modal_total {Δ : Bounds} {m : ModExpr} (h : Entails Δ (.defined m))
    (a : CompareTy) : support Δ (.modal a m) none = support Δ a none :=
  support_total (suffix := some m) h a

theorem support_compose (Δ : Bounds) (a : CompareTy) (m n : ModExpr) :
    support Δ (.modal a (.compose m n)) none =
      support Δ (.modal (.modal a m) n) none := rfl

theorem heads_subset_support (Δ : Bounds) (a : CompareTy) (suffix : Suffix) :
    heads Δ (suffix.apply a) ⊆ support Δ a suffix := by
  induction a generalizing suffix with
  | modal a m ih =>
      simpa only [support, heads_prepend] using ih (suffix.prepend m)
  | prod | sum | fn | join | meet => exact Set.subset_union_left
  | var | unit | credit => exact Set.Subset.rfl

theorem support_finite (Δ : Bounds) (a : CompareTy) (suffix : Suffix) :
    (support Δ a suffix).Finite := by
  induction a generalizing suffix with
  | modal a m ih => exact ih _
  | prod a b ia ib | sum a b ia ib => exact (heads_finite _ _).union ((ia _).union (ib _))
  | fn a b ia ib | join a b ia ib | meet a b ia ib =>
      apply (heads_finite _ _).union
      split
      · exact (ia _).union (ib _)
      · exact Set.finite_empty
  | var | unit | credit => exact heads_finite _ _

theorem support_defined {Δ : Bounds} {a : CompareTy} (h : a.DefinedUnder Δ) :
    support Δ a none = ∅ := by
  induction a with
  | modal a m ih =>
      rw [support_modal_total (CompareTy.definedUnder_modal_iff.mp h).2,
        ih (CompareTy.definedUnder_modal_iff.mp h).1]
  | prod a b ia ib | sum a b ia ib =>
      have hd := CompareTy.definedUnder_prod_iff.mp h
      simp only [support, Suffix.apply, heads_defined h, ia hd.1, ib hd.2, Set.empty_union]
  | fn a b ia ib | join a b ia ib | meet a b ia ib =>
      have hd := CompareTy.definedUnder_fn_iff.mp h
      simp only [support, Suffix.apply, Suffix.total, ↓reduceIte,
        heads_defined h, ia hd.1, ib hd.2, Set.empty_union]
  | var | unit | credit => exact heads_defined h

theorem heads_nonLattice (Δ : Bounds) (a : CompareTy) :
    ∀ h ∈ heads Δ a, NonLattice h := by
  fun_induction heads Δ a with
  | case1 _ _ _ ih | case2 _ _ _ _ ih => exact ih
  | case3 => simp only [Set.mem_singleton_iff, forall_eq, NonLattice]
  | case4 _ _ ia ib | case5 _ _ ia ib =>
    intro x hx
    exact hx.elim (ia x) (ib x)
  | case6 => exact fun _ hx => False.elim hx
  | case7 a _ _ hj hm _ =>
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    cases x <;> first | trivial | exact False.elim (hj _ _ rfl) | exact False.elim (hm _ _ rfl)

theorem generator_of_support {Δ H a suffix} (hg : GuardedLattice Δ a)
    (h : support Δ a suffix ⊆ H) : Generator Δ H (suffix.apply a) := by
  intro x hx
  have hs : GuardedLattice Δ (suffix.apply a) := by cases suffix <;> exact hg
  rw [oneHead_eq_heads hs] at hx
  exact ⟨h ((heads_subset_support Δ a suffix) hx), heads_nonLattice Δ _ x hx⟩

theorem carrier_of_support {Δ H a suffix} (hg : GuardedLattice Δ a)
    (h : support Δ a suffix ⊆ H) : Carrier Δ H (suffix.apply a) :=
  (generator_of_support hg h).carrier

theorem support_prod_children {Δ H a b suffix}
    (h : support Δ (.prod a b) suffix ⊆ H) :
    support Δ a suffix ⊆ H ∧ support Δ b suffix ⊆ H :=
  Set.union_subset_iff.mp (Set.union_subset_iff.mp h).2

theorem support_sum_children {Δ H a b suffix}
    (h : support Δ (.sum a b) suffix ⊆ H) :
    support Δ a suffix ⊆ H ∧ support Δ b suffix ⊆ H :=
  Set.union_subset_iff.mp (Set.union_subset_iff.mp h).2

theorem support_fn_children {Δ H a b suffix} (hs : suffix.total Δ)
    (h : support Δ (.fn a b) suffix ⊆ H) :
    support Δ a none ⊆ H ∧ support Δ b none ⊆ H := by
  simpa only [support, if_pos hs, Set.union_subset_iff] using (Set.union_subset_iff.mp h).2

/-- A boundary determines the complete set of partial heads used by this
traversal. Total modality orbits need no additional heads. -/
def boundarySupport (Δ : Bounds) (boundary : List CompareTy) : Set CompareTy :=
  {h | ∃ a ∈ boundary, h ∈ support Δ a none}

theorem boundarySupport_finite (Δ : Bounds) (boundary : List CompareTy) :
    (boundarySupport Δ boundary).Finite := by
  induction boundary with
  | nil => simpa only [boundarySupport, List.not_mem_nil, false_and, exists_false,
      Set.setOf_false] using Set.finite_empty
  | cons a boundary ih =>
      have he : boundarySupport Δ (a :: boundary) = support Δ a none ∪ boundarySupport Δ boundary := by
        ext h
        simp only [boundarySupport, List.mem_cons, Set.mem_setOf_eq, Set.mem_union]
        constructor
        · rintro ⟨b, rfl | hb, hh⟩
          · exact Or.inl hh
          · exact Or.inr ⟨b,hb,hh⟩
        · rintro (hh | ⟨b,hb,hh⟩)
          · exact ⟨a,Or.inl rfl,hh⟩
          · exact ⟨b,Or.inr hb,hh⟩
      rw [he]
      exact (support_finite Δ a none).union ih

theorem support_subset_boundary {Δ boundary a} (ha : a ∈ boundary) :
    support Δ a none ⊆ boundarySupport Δ boundary := fun _ h => ⟨a,ha,h⟩

theorem carrier_boundary {Δ boundary a} (ha : a ∈ boundary) (hg : GuardedLattice Δ a) :
    Carrier Δ (boundarySupport Δ boundary) a :=
  carrier_of_support (suffix := none) hg (support_subset_boundary ha)

theorem support_total_subset_boundary {Δ boundary a suffix}
    (ha : a ∈ boundary) (hs : suffix.total Δ) :
    support Δ a suffix ⊆ boundarySupport Δ boundary := by
  rw [support_total hs]
  exact support_subset_boundary ha

end
end ModalityInference.ComparisonRawHeadRestriction
