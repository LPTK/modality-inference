import ModalityInference.Proofs.ComparisonTupleReflection

/-! Finite signed controls normalize defined modal expressions into pure lattice
polynomials. The heads may be structural types; their whole declared order is
preserved by algebraic equivalence. -/
namespace ModalityInference.ComparisonControls

open ComparisonAlgebra ComparisonPropagation ComparisonTupleReflection

inductive LatticeForm (basis : List CompareTy) : CompareTy → Prop where
  | atom {a} : a ∈ basis → LatticeForm basis a
  | join {a b} : LatticeForm basis a → LatticeForm basis b → LatticeForm basis (.join a b)
  | meet {a b} : LatticeForm basis a → LatticeForm basis b → LatticeForm basis (.meet a b)

private def interleave (basis heads modes : Nat → Bool) (i : Nat) : Bool :=
  if i % 3 = 0 then basis (i / 3)
  else if i % 3 = 1 then heads (i / 3)
  else modes (i / 3)

@[simp] private theorem interleave_basis (basis heads modes : Nat → Bool) (i : Nat) :
    interleave basis heads modes (3 * i) = basis i := by
  simp [interleave, Nat.mul_comm]

@[simp] private theorem interleave_heads (basis heads modes : Nat → Bool) (i : Nat) :
    interleave basis heads modes (3 * i + 1) = heads i := by
  have hd : (3 * i + 1) / 3 = i := by omega
  have hm : (3 * i + 1) % 3 = 1 := by omega
  simp [interleave, hd, hm]

@[simp] private theorem interleave_modes (basis heads modes : Nat → Bool) (i : Nat) :
    interleave basis heads modes (3 * i + 2) = modes i := by
  have hd : (3 * i + 2) / 3 = i := by omega
  have hm : (3 * i + 2) % 3 = 2 := by omega
  simp [interleave, hd, hm]

private theorem observer_formula {Δ : Bounds} {shape : ComparisonShape}
    (g : Generated b) (f : LatticeHom (Order Δ shape) Bool)
    (lower upper : Carrier Δ shape)
    (hh : ∀ a ∈ b.heads, InInterval (lower.atMode Mode.bottom) (upper.atMode Mode.top) a)
    (hd : g.term.DefinedUnder Δ) (coordinate : Coordinate) (σ : Nat → Bool)
    (headAtom modeAtom : Nat → Nat)
    (hhead : ∀ a ∈ b.heads, σ (headAtom (b.heads.idxOf a)) = booleanValue f a)
    (hm : ∀ t, InInterval (lower.atMode Mode.bottom) (upper.atMode Mode.top) t →
      ∀ m ∈ labels g, booleanValue f (.modal t m) =
        (coordinate.modalWith modeAtom (.const (booleanValue f t)) m).eval σ) :
    booleanValue f g.term = (g.formula headAtom modeAtom coordinate).eval σ := by
  induction g with
  | head a ha => exact (hhead a ha).symm
  | join a c iha ihc =>
    have hd := CompareTy.definedUnder_join_iff.mp hd
    rw [Generated.term, booleanValue_join, Generated.formula, BoolExpr.eval,
      iha hd.1 (fun t ht m hm' => hm t ht m (List.mem_append_left _ hm')),
      ihc hd.2 (fun t ht m hm' => hm t ht m (List.mem_append_right _ hm'))]
  | meet a c iha ihc =>
    have hd := CompareTy.definedUnder_meet_iff.mp hd
    rw [Generated.term, booleanValue_meet, Generated.formula, BoolExpr.eval,
      iha hd.1 (fun t ht m hm' => hm t ht m (List.mem_append_left _ hm')),
      ihc hd.2 (fun t ht m hm' => hm t ht m (List.mem_append_right _ hm'))]
  | modal a m hms ih =>
    have hd := CompareTy.definedUnder_modal_iff.mp hd
    rw [Generated.term, hm a.term (interval a lower upper hh hd.1) m (by simp [labels]),
      ih hd.1 (fun t ht n hn => hm t ht n (List.mem_cons_of_mem _ hn)), Generated.formula]
    cases coordinate <;> rfl

/-- Modal expressions over a finite common-shape basis have an algebraically
 equivalent pure lattice expression over its finite signed controls. Labels
 need only be defined under the declared bounds. -/
theorem Generated.lattice_normal {Δ : Bounds} {shape : ComparisonShape}
    (g : Generated b) (hh : ∀a∈b.heads, Representable Δ shape a)
    (hd : g.term.DefinedUnder Δ) :
    ∃ t, LatticeForm b.types t ∧ Representable Δ shape t ∧
      AlgebraSubtype Δ g.term t ∧ AlgebraSubtype Δ t g.term := by
  obtain ⟨clauses, t, _, ht, hformula⟩ := g.reconstructs
  have hform : LatticeForm b.types t :=
    reify_property ht (LatticeForm b.types) (fun _ => LatticeForm.atom)
      (fun _ _ => LatticeForm.join) (fun _ _ => LatticeForm.meet)
  obtain ⟨lower, upper, _, _, hlu, hheads, htypes, hpairs⟩ := b.carrier_interval
    CompareTy.var ModExpr.var (by simpa only [CompareTy.subst_id] using hh)
    (fun _ _ _ _ => rfl)
  simp only [CompareTy.subst_id] at hheads htypes hpairs
  obtain ⟨hg, hlg, hgu⟩ := interval g lower upper hheads hd
  have hti := InInterval.reify ht CompareTy.var ModExpr.var
    (by simpa only [CompareTy.subst_id] using htypes)
  simp only [CompareTy.subst_id] at hti
  obtain ⟨htr, hlt, htu⟩ := hti
  have he : ∀f : LatticeHom (Order Δ shape) Bool,
      booleanValue f g.term = booleanValue f t := by
    intro f
    cases hlo : observer f (lower.atMode Mode.bottom) with
    | true =>
      have hl := observer_mono f hlg hlo
      have hr := observer_mono f hlt hlo
      simpa only [booleanValue_represented f _ hg,
        booleanValue_represented f _ htr] using hl.trans hr.symm
    | false =>
      cases hhi : observer f (upper.atMode Mode.top) with
      | false =>
        have hl : observer f (represented hg) = false := by
          cases hx : observer f (represented hg)
          · rfl
          · have := observer_mono f hgu hx
            simp_all
        have hr : observer f (represented htr) = false := by
          cases hx : observer f (represented htr)
          · rfl
          · have := observer_mono f htu hx
            simp_all
        simpa only [booleanValue_represented f _ hg,
          booleanValue_represented f _ htr] using hl.trans hr.symm
      | true =>
        obtain ⟨c, η, _, hmodel⟩ := b.observer_model f lower upper hlu hlo hhi
          ModExpr.var (fun η => η) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
          (by simpa only [CompareTy.subst_id] using hpairs) (labels g)
          (by simpa only [ModExpr.subst_id] using labels_defined g hd)
        let σ := interleave (basisValue b.types (booleanValue f))
          (basisValue b.heads (booleanValue f)) (encodeModes η)
        have hhead : ∀i (hi : i < b.heads.length),
            σ (3 * i + 1) = booleanValue f b.heads[i] := by
          intro i hi
          simp [σ, basisValue, List.getElem?_eq_getElem hi]
        have hbases : ∀i (hi : i < b.types.length),
            σ (3 * i) = booleanValue f b.types[i] := by
          intro i hi
          simp [σ, basisValue, List.getElem?_eq_getElem hi]
        obtain ⟨htheory, hmodal⟩ := hmodel σ (fun i => 3*i)
          (fun i => 3*i+1) (fun i => 3*i+2)
          (by simpa only [CompareTy.subst_id] using hhead)
          (by simpa only [CompareTy.subst_id] using hbases)
          (by intro i; simp [σ])
        simp only [CompareTy.subst_id] at hmodal
        have hgvalue := observer_formula g f lower upper hheads hd c σ
          (fun i => 3*i+1) (fun i => 3*i+2) (by
            intro a ha
            have hi := List.idxOf_lt_length_of_mem ha
            have he : b.heads[b.heads.idxOf a] = a := by
              simpa only [List.idxOf, beq_iff_eq] using
                (List.findIdx_getElem (xs := b.heads) (p := (· == a)) (w := hi))
            simpa only [he] using hhead (b.heads.idxOf a) hi) hmodal
        have hsem := hformula (fun i => 3*i) (fun i => 3*i+1)
          (fun i => 3*i+2) c σ htheory
        have hσ : σ ∘ (fun i => 3*i) = basisValue b.types (booleanValue f) := by
          funext i
          simp [σ]
        rw [hσ, ← hgvalue] at hsem
        have htvalue := reify_booleanValue ht f CompareTy.var ModExpr.var
        simp only [CompareTy.subst_id] at htvalue
        exact Bool.eq_iff_iff.mpr (hsem.symm.trans htvalue.symm)
  refine ⟨t, hform, htr, ?_, ?_⟩
  · apply (subtype_iff_boolean_observers (represented hg) (represented htr)).mpr
    intro f
    have h := he f
    rw [booleanValue_represented f _ hg, booleanValue_represented f _ htr] at h
    exact le_of_eq h
  · apply (subtype_iff_boolean_observers (represented htr) (represented hg)).mpr
    intro f
    have h := he f
    rw [booleanValue_represented f _ hg, booleanValue_represented f _ htr] at h
    exact le_of_eq h.symm

end ModalityInference.ComparisonControls
