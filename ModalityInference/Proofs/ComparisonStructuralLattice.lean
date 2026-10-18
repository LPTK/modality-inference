import ModalityInference.Proofs.ComparisonStructuralControls
import ModalityInference.Proofs.ComparisonStructuralProjection

/-! Structural constructors lift finite guarded lattice grammars. The function
constructor reverses the domain operations; no projection or decomposition of
declared type bounds is used. -/
namespace ModalityInference.ComparisonStructuralLattice

open ComparisonAlgebra ComparisonControls ComparisonDefinedCovers

def Equiv (Δ : Bounds) (a b : CompareTy) : Prop :=
  AlgebraSubtype Δ a b ∧ AlgebraSubtype Δ b a

theorem Equiv.trans {Δ : Bounds} {a b c : CompareTy} (h : Equiv Δ a b) (g : Equiv Δ b c) :
    Equiv Δ a c := ⟨h.1.trans g.1, g.2.trans h.2⟩

theorem Equiv.symm {Δ : Bounds} {a b : CompareTy} (h : Equiv Δ a b) : Equiv Δ b a :=
  ⟨h.2, h.1⟩

theorem Equiv.refl {Δ : Bounds} {a : CompareTy} (h : a.WellShaped Δ) : Equiv Δ a a :=
  ⟨.refl h, .refl h⟩

theorem Equiv.typeOp {Δ : Bounds} {a b c d : CompareTy} (p : Bool)
    (h : Equiv Δ a c) (g : Equiv Δ b d)
    (hs : ComparisonShape.Equivalent Δ a.shape b.shape) :
    Equiv Δ (typeOp p a b) (typeOp p c d) := by
  have hl : (.join a b : CompareTy).WellShaped Δ := ⟨h.1.wellShaped_left, g.1.wellShaped_left, hs⟩
  have hr : (.join c d : CompareTy).WellShaped Δ :=
    ⟨h.1.wellShaped_right, g.1.wellShaped_right, h.1.shape_equivalent.symm.trans (hs.trans g.1.shape_equivalent)⟩
  cases p
  · exact ⟨.meetGreatest ((AlgebraSubtype.shaped (.meetLeft hl)).trans h.1)
      ((AlgebraSubtype.shaped (.meetRight hl)).trans g.1),
      .meetGreatest ((AlgebraSubtype.shaped (.meetLeft hr)).trans h.2)
        ((AlgebraSubtype.shaped (.meetRight hr)).trans g.2)⟩
  · exact ⟨.joinLeast (h.1.trans (.shaped (.joinLeft hr))) (g.1.trans (.shaped (.joinRight hr))),
      .joinLeast (h.2.trans (.shaped (.joinLeft hl))) (g.2.trans (.shaped (.joinRight hl)))⟩

inductive Kind where
  | prod | sum | fn

def Kind.op : Kind → CompareTy → CompareTy → CompareTy
  | .prod => .prod
  | .sum => .sum
  | .fn => .fn

def Kind.shape : Kind → ComparisonShape → ComparisonShape → ComparisonShape
  | .prod => .prod
  | .sum => .sum
  | .fn => .fn

def Kind.leftSign : Kind → Bool → Bool
  | .fn, p => !p
  | _, p => p

theorem Kind.op_representable (k : Kind) {Δ : Bounds} {s t : ComparisonShape} {a b : CompareTy}
    (ha : Representable Δ s a) (hb : Representable Δ t b) :
    Representable Δ (k.shape s t) (k.op a b) := by
  cases k <;> refine ⟨⟨ha.1, hb.1⟩, ?_, ?_⟩
  all_goals first
    | exact CompareTy.definedUnder_prod_iff.mpr ⟨ha.2.1, hb.2.1⟩
    | exact CompareTy.definedUnder_sum_iff.mpr ⟨ha.2.1, hb.2.1⟩
    | exact CompareTy.definedUnder_fn_iff.mpr ⟨ha.2.1, hb.2.1⟩
    | intro ρ hρ; simp only [Kind.op, Kind.shape, CompareTy.shape, ComparisonShape.subst,
        ha.2.2 ρ hρ, hb.2.2 ρ hρ]

theorem Kind.congr (k : Kind) {Δ : Bounds} {a b c d : CompareTy}
    (ha : Equiv Δ a c) (hb : Equiv Δ b d) : Equiv Δ (k.op a b) (k.op c d) := by
  cases k
  · exact ⟨prod_congr ha.1 hb.1, prod_congr ha.2 hb.2⟩
  · exact ⟨sum_congr ha.1 hb.1, sum_congr ha.2 hb.2⟩
  · exact ⟨fn_congr ha.2 hb.1, fn_congr ha.1 hb.2⟩

theorem Kind.distrib (k : Kind) {Δ : Bounds} {a b c d : CompareTy} (p : Bool)
    (ha : Compatible Δ a c) (hb : Compatible Δ b d) :
    Equiv Δ (k.op (typeOp (k.leftSign p) a c) (typeOp p b d))
      (typeOp p (k.op a b) (k.op c d)) := by
  cases k
  · exact ⟨.equationRev (.prod p ha hb), .equation (.prod p ha hb)⟩
  · exact ⟨.equationRev (.sum p ha hb), .equation (.sum p ha hb)⟩
  · exact ⟨.equationRev (.fn p ha hb), .equation (.fn p ha hb)⟩

theorem Kind.left_distrib (k : Kind) {Δ : Bounds} {a b c : CompareTy} (p : Bool)
    (ha : Compatible Δ a c) (hb : b.WellShaped Δ) (hbd : b.DefinedUnder Δ) :
    Equiv Δ (k.op (typeOp p a c) b)
      (typeOp (k.leftSign p) (k.op a b) (k.op c b)) := by
  have hid := ComparisonStructuralProjection.typeOp_idem hb (k.leftSign p)
  have hl : Equiv Δ (k.op (typeOp p a c) b)
      (k.op (typeOp p a c) (typeOp (k.leftSign p) b b)) :=
    k.congr (.refl ((typeOp_wellShaped p Δ a c).mpr ⟨ha.1.1, ha.1.2.1, ha.1.2.2⟩)) hid
  apply hl.trans
  have hh := k.distrib (k.leftSign p) ha ⟨⟨hb, hb, .refl⟩, hbd, hbd⟩
  cases k <;> simpa only [Kind.leftSign, Bool.not_not] using hh

theorem Kind.right_distrib (k : Kind) {Δ : Bounds} {a b d : CompareTy} (p : Bool)
    (ha : a.WellShaped Δ) (had : a.DefinedUnder Δ) (hb : Compatible Δ b d) :
    Equiv Δ (k.op a (typeOp p b d))
      (typeOp p (k.op a b) (k.op a d)) := by
  have hid := ComparisonStructuralProjection.typeOp_idem ha (k.leftSign p)
  apply (k.congr hid (.refl ((typeOp_wellShaped p Δ b d).mpr
    ⟨hb.1.1, hb.1.2.1, hb.1.2.2⟩))).trans
  exact k.distrib p ⟨⟨ha, ha, .refl⟩, had, had⟩ hb

theorem representable_typeOp {Δ : Bounds} {s : ComparisonShape} {a b : CompareTy}
    (p : Bool) (ha : Representable Δ s a) (hb : Representable Δ s b) :
    Representable Δ s (typeOp p a b) := by
  cases p <;> refine ⟨⟨ha.1, hb.1, ha.2.2.trans hb.2.2.symm⟩, ?_, ha.2.2⟩
  · exact CompareTy.definedUnder_meet_iff.mpr ⟨ha.2.1, hb.2.1⟩
  · exact CompareTy.definedUnder_join_iff.mpr ⟨ha.2.1, hb.2.1⟩

theorem lattice_typeOp {basis : List CompareTy} {a b : CompareTy}
    (p : Bool) (ha : LatticeForm basis a) (hb : LatticeForm basis b) :
    LatticeForm basis (typeOp p a b) := by
  cases p
  · exact .meet ha hb
  · exact .join ha hb

theorem lattice_mono {left right : List CompareTy} {a : CompareTy}
    (h : ∀x ∈ left, x ∈ right) (ha : LatticeForm left a) : LatticeForm right a := by
  induction ha with
  | atom ha => exact .atom (h _ ha)
  | join _ _ iha ihb => exact .join iha ihb
  | meet _ _ iha ihb => exact .meet iha ihb

theorem lattice_representable {Δ : Bounds} {s : ComparisonShape}
    {basis : List CompareTy} {a : CompareTy}
    (hs : ∀x∈basis, Representable Δ s x) (ha : LatticeForm basis a) :
    Representable Δ s a := by
  induction ha with
  | atom ha => exact hs _ ha
  | join _ _ iha ihb => exact representable_typeOp true iha ihb
  | meet _ _ iha ihb => exact representable_typeOp false iha ihb

theorem Kind.lattice_right (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    {right : List CompareTy} {a b : CompareTy}
    (ha : Representable Δ s a) (hb : LatticeForm right b)
    (hs : ∀y∈right, Representable Δ t y) :
    ∃ c, LatticeForm (right.map (k.op a)) c ∧
      Representable Δ (k.shape s t) c ∧ Equiv Δ (k.op a b) c := by
  induction hb with
  | atom hb =>
    exact ⟨_, .atom (List.mem_map.mpr ⟨_, hb, rfl⟩), k.op_representable ha (hs _ hb),
      .refl (k.op_representable ha (hs _ hb)).1⟩
  | join hb hd ihb ihd =>
    obtain ⟨x, hx, hxr, hxe⟩ := ihb
    obtain ⟨y, hy, hyr, hye⟩ := ihd
    refine ⟨typeOp true x y, lattice_typeOp _ hx hy, representable_typeOp _ hxr hyr, ?_⟩
    refine (k.right_distrib true ha.1 ha.2.1
      ((represented (lattice_representable hs hb)).compatible
        (represented (lattice_representable hs hd)))).trans ?_
    exact Equiv.typeOp _ hxe hye
      (hxe.1.shape_equivalent.trans (hxr.2.2.trans
        (hyr.2.2.symm.trans hye.1.shape_equivalent.symm)))
  | meet hb hd ihb ihd =>
    obtain ⟨x, hx, hxr, hxe⟩ := ihb
    obtain ⟨y, hy, hyr, hye⟩ := ihd
    refine ⟨typeOp false x y, lattice_typeOp _ hx hy, representable_typeOp _ hxr hyr, ?_⟩
    refine (k.right_distrib false ha.1 ha.2.1
      ((represented (lattice_representable hs hb)).compatible
        (represented (lattice_representable hs hd)))).trans ?_
    exact Equiv.typeOp _ hxe hye
      (hxe.1.shape_equivalent.trans (hxr.2.2.trans
        (hyr.2.2.symm.trans hye.1.shape_equivalent.symm)))

/-- Structural constructors lift finite lattice grammars to the finite Cartesian
product of their bases. Function domains dualize the lattice operations. -/
theorem Kind.lattice (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    {left right : List CompareTy} {a b : CompareTy}
    (ha : LatticeForm left a) (hb : LatticeForm right b)
    (hs : ∀x∈left, Representable Δ s x)
    (ht : ∀y∈right, Representable Δ t y) :
    ∃ c, LatticeForm (left.flatMap fun x => right.map (k.op x)) c ∧
      Representable Δ (k.shape s t) c ∧ Equiv Δ (k.op a b) c := by
  induction ha with
  | atom ha =>
    obtain ⟨c, hc, hcr, hce⟩ := k.lattice_right (hs _ ha) hb ht
    exact ⟨c, lattice_mono (fun _ h => List.mem_flatMap.mpr ⟨_, ha, h⟩) hc, hcr, hce⟩
  | join ha hc iha ihc =>
    obtain ⟨x, hx, hxr, hxe⟩ := iha
    obtain ⟨y, hy, hyr, hye⟩ := ihc
    refine ⟨typeOp (k.leftSign true) x y, lattice_typeOp _ hx hy,
      representable_typeOp _ hxr hyr, ?_⟩
    refine (k.left_distrib true
      ((represented (lattice_representable hs ha)).compatible
        (represented (lattice_representable hs hc)))
      (lattice_representable ht hb).1 (lattice_representable ht hb).2.1).trans ?_
    exact Equiv.typeOp _ hxe hye
      (hxe.1.shape_equivalent.trans (hxr.2.2.trans
        (hyr.2.2.symm.trans hye.1.shape_equivalent.symm)))
  | meet ha hc iha ihc =>
    obtain ⟨x, hx, hxr, hxe⟩ := iha
    obtain ⟨y, hy, hyr, hye⟩ := ihc
    refine ⟨typeOp (k.leftSign false) x y, lattice_typeOp _ hx hy,
      representable_typeOp _ hxr hyr, ?_⟩
    refine (k.left_distrib false
      ((represented (lattice_representable hs ha)).compatible
        (represented (lattice_representable hs hc)))
      (lattice_representable ht hb).1 (lattice_representable ht hb).2.1).trans ?_
    exact Equiv.typeOp _ hxe hye
      (hxe.1.shape_equivalent.trans (hxr.2.2.trans
        (hyr.2.2.symm.trans hye.1.shape_equivalent.symm)))

end ModalityInference.ComparisonStructuralLattice

namespace ModalityInference.ComparisonControls.LatticeForm

theorem representable {Δ : Bounds} {shape : ComparisonShape}
    {basis : List CompareTy} {a : CompareTy} (h : LatticeForm basis a)
    (hs : ∀x∈basis, ComparisonAlgebra.Representable Δ shape x) :
    ComparisonAlgebra.Representable Δ shape a :=
  ComparisonStructuralLattice.lattice_representable hs h

theorem mono {left right : List CompareTy} {a : CompareTy}
    (ha : LatticeForm left a) (h : ∀x ∈ left, x ∈ right) : LatticeForm right a :=
  ComparisonStructuralLattice.lattice_mono h ha

theorem nonempty {basis : List CompareTy} {a : CompareTy} (h : LatticeForm basis a) :
    basis ≠ [] := by
  induction h with
  | atom h => exact List.ne_nil_of_mem h
  | join _ _ iha _ => exact iha
  | meet _ _ iha _ => exact iha

end ModalityInference.ComparisonControls.LatticeForm
