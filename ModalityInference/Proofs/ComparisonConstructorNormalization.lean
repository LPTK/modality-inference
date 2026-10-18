import ModalityInference.ComparisonConstructorNormalization
import ModalityInference.Proofs.ComparisonStructuralLattice

/-! The finite constructor traversal computes the Cartesian lattice lifting.
All equalities use the guarded structural equations, including the dual
function-domain lattice operations. -/
namespace ModalityInference.ComparisonConstructorNormalization
open ComparisonAlgebra ComparisonControls ComparisonStructuralLattice

theorem right_atom {op : CompareTy → CompareTy → CompareTy} {basis : List CompareTy}
    {a b : CompareTy} (hb : b∈basis) : right op basis a b = some (op a b) := by
  cases b <;> simp [right, hb]

theorem right_complete (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    {basis : List CompareTy} {a b : CompareTy}
    (ha : Representable Δ s a) (hb : LatticeForm basis b)
    (hs : ∀y∈basis, Representable Δ t y) :
    ∃c, right k.op basis a b = some c ∧ LatticeForm (basis.map (k.op a)) c ∧
      Representable Δ (k.shape s t) c ∧ Equiv Δ (k.op a b) c := by
  induction hb with
  | atom hb =>
    exact ⟨_, right_atom hb, .atom (List.mem_map.mpr ⟨_,hb,rfl⟩),
      k.op_representable ha (hs _ hb), .refl (k.op_representable ha (hs _ hb)).1⟩
  | @join b d hb hd ihb ihd =>
    by_cases hm : CompareTy.join b d ∈ basis
    · exact ⟨_, right_atom hm, .atom (List.mem_map.mpr ⟨_,hm,rfl⟩),
        k.op_representable ha (hs _ hm), .refl (k.op_representable ha (hs _ hm)).1⟩
    · obtain ⟨x, hx, hxf, hxr, hxe⟩ := ihb
      obtain ⟨y, hy, hyf, hyr, hye⟩ := ihd
      refine ⟨.join x y, ?_, .join hxf hyf, representable_typeOp true hxr hyr, ?_⟩
      · simp [right, hm, hx, hy]
      · refine (k.right_distrib true ha.1 ha.2.1
          ((represented (hb.representable hs)).compatible
            (represented (hd.representable hs)))).trans ?_
        exact Equiv.typeOp true hxe hye
          (hxe.1.shape_equivalent.trans (hxr.2.2.trans
            (hyr.2.2.symm.trans hye.1.shape_equivalent.symm)))
  | @meet b d hb hd ihb ihd =>
    by_cases hm : CompareTy.meet b d ∈ basis
    · exact ⟨_, right_atom hm, .atom (List.mem_map.mpr ⟨_,hm,rfl⟩),
        k.op_representable ha (hs _ hm), .refl (k.op_representable ha (hs _ hm)).1⟩
    · obtain ⟨x, hx, hxf, hxr, hxe⟩ := ihb
      obtain ⟨y, hy, hyf, hyr, hye⟩ := ihd
      refine ⟨.meet x y, ?_, .meet hxf hyf, representable_typeOp false hxr hyr, ?_⟩
      · simp [right, hm, hx, hy]
      · refine (k.right_distrib false ha.1 ha.2.1
          ((represented (hb.representable hs)).compatible
            (represented (hd.representable hs)))).trans ?_
        exact Equiv.typeOp false hxe hye
          (hxe.1.shape_equivalent.trans (hxr.2.2.trans
            (hyr.2.2.symm.trans hye.1.shape_equivalent.symm)))

theorem lift_atom {op : CompareTy → CompareTy → CompareTy} {sign : Bool → Bool}
    {left basis : List CompareTy} {a b : CompareTy} (ha : a∈left) :
    lift op sign left basis a b = right op basis a b := by
  cases a <;> simp [lift, ha]

theorem lift_complete (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    {left basis : List CompareTy} {a b : CompareTy}
    (ha : LatticeForm left a) (hb : LatticeForm basis b)
    (hs : ∀x∈left, Representable Δ s x)
    (ht : ∀y∈basis, Representable Δ t y) :
    ∃c, lift k.op k.leftSign left basis a b = some c ∧
      LatticeForm (left.flatMap fun x => basis.map (k.op x)) c ∧
      Representable Δ (k.shape s t) c ∧ Equiv Δ (k.op a b) c := by
  induction ha with
  | atom ha =>
    obtain ⟨c, hc, hcf, hcr, hce⟩ := right_complete k (hs _ ha) hb ht
    exact ⟨c, (lift_atom ha).trans hc,
      hcf.mono (fun _ h => List.mem_flatMap.mpr ⟨_,ha,h⟩), hcr, hce⟩
  | @join a d ha hd iha ihd =>
    by_cases hm : CompareTy.join a d ∈ left
    · obtain ⟨c, hc, hcf, hcr, hce⟩ := right_complete k (hs _ hm) hb ht
      exact ⟨c, (lift_atom hm).trans hc,
        hcf.mono (fun _ h => List.mem_flatMap.mpr ⟨_,hm,h⟩), hcr, hce⟩
    · obtain ⟨x, hx, hxf, hxr, hxe⟩ := iha
      obtain ⟨y, hy, hyf, hyr, hye⟩ := ihd
      refine ⟨typeOp (k.leftSign true) x y, ?_, lattice_typeOp _ hxf hyf,
        representable_typeOp _ hxr hyr, ?_⟩
      · simp [lift, hm, hx, hy]
      · refine (k.left_distrib true
          ((represented (ha.representable hs)).compatible
            (represented (hd.representable hs)))
          (hb.representable ht).1 (hb.representable ht).2.1).trans ?_
        exact Equiv.typeOp _ hxe hye
          (hxe.1.shape_equivalent.trans (hxr.2.2.trans
            (hyr.2.2.symm.trans hye.1.shape_equivalent.symm)))
  | @meet a d ha hd iha ihd =>
    by_cases hm : CompareTy.meet a d ∈ left
    · obtain ⟨c, hc, hcf, hcr, hce⟩ := right_complete k (hs _ hm) hb ht
      exact ⟨c, (lift_atom hm).trans hc,
        hcf.mono (fun _ h => List.mem_flatMap.mpr ⟨_,hm,h⟩), hcr, hce⟩
    · obtain ⟨x, hx, hxf, hxr, hxe⟩ := iha
      obtain ⟨y, hy, hyf, hyr, hye⟩ := ihd
      refine ⟨typeOp (k.leftSign false) x y, ?_, lattice_typeOp _ hxf hyf,
        representable_typeOp _ hxr hyr, ?_⟩
      · simp [lift, hm, hx, hy]
      · refine (k.left_distrib false
          ((represented (ha.representable hs)).compatible
            (represented (hd.representable hs)))
          (hb.representable ht).1 (hb.representable ht).2.1).trans ?_
        exact Equiv.typeOp _ hxe hye
          (hxe.1.shape_equivalent.trans (hxr.2.2.trans
            (hyr.2.2.symm.trans hye.1.shape_equivalent.symm)))

end ModalityInference.ComparisonConstructorNormalization
