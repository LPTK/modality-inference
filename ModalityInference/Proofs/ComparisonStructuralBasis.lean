import ModalityInference.ComparisonStructuralBasis
import ModalityInference.Proofs.ComparisonStructuralControls
import ModalityInference.Proofs.ComparisonStructuralControlClosure
import ModalityInference.Proofs.ComparisonStructuralLattice

/-! A finite declared shape model indexes constructor bases. Fixed names are
retained at their entire solved shape, while constructor entries combine the
finite control bases of their children. Defined supported witnesses normalize
without decomposing the declared whole-type inequalities. -/
namespace ModalityInference.ComparisonStructuralBasis

open ComparisonAlgebra ComparisonControls ComparisonStructuralLattice

theorem extend_representable {Δ : Bounds} {s : ComparisonShape}
    (modes : List ModVar) {as : List CompareTy}
    (ha : ∀a∈as, Representable Δ s a) :
    ∀a∈extend modes as, Representable Δ s a := by
  cases as with
  | nil => simp [extend]
  | cons a rest =>
    let b : Basis := ⟨a, rest, modes⟩
    obtain ⟨_, _, _, _, _, _, ht, _⟩ := b.carrier_interval CompareTy.var ModExpr.var
      (by simpa only [CompareTy.subst_id] using ha) (fun _ _ _ _ => rfl)
    simp only [CompareTy.subst_id] at ht
    exact fun a ha => (ht a ha).1

theorem heads_representable {Δ : Bounds} (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape)
    (hs : ∀v, ComparisonShape.Equivalent Δ (.var v) (shapes v)) (s : ComparisonShape) :
    ∀a∈heads names modes shapes s, Representable Δ s a := by
  have hv : ∀s a, a∈fixedHeads names shapes s → Representable Δ s a := by
    intro s a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    have he : shapes v = s := by simpa using (List.mem_filter.mp hv).2
    exact ⟨trivial, (by intro η hη c hc; cases hc), he ▸ hs v⟩
  have hp : ∀ {s t : ComparisonShape} {left right : List CompareTy},
      (∀a∈left, Representable Δ s a) → (∀b∈right, Representable Δ t b) →
      (∀a∈pairs .prod left right, Representable Δ (.prod s t) a) ∧
      (∀a∈pairs .sum left right, Representable Δ (.sum s t) a) ∧
      (∀a∈pairs .fn left right, Representable Δ (.fn s t) a) := by
    intro s t left right hl hr
    have hpair (op : CompareTy → CompareTy → CompareTy) :
        ∀a∈pairs op left right, ∃b∈left, ∃c∈right, a=op b c := by
      intro a ha
      obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      exact ⟨b, hb, c, hc, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    all_goals
      intro a ha
      obtain ⟨b, hb, c, hc, rfl⟩ := hpair _ a ha
      have hb := hl b hb
      have hc := hr c hc
      refine ⟨⟨hb.1, hc.1⟩, ?_, ?_⟩
      · exact CompareTy.definedUnder_prod_iff.mpr ⟨hb.2.1, hc.2.1⟩
      · intro ρ hρ
        simp only [CompareTy.shape, ComparisonShape.subst, hb.2.2 ρ hρ, hc.2.2 ρ hρ]
  induction s with
  | var v => exact hv _
  | unit =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hv _ a ha
    · obtain rfl := List.mem_singleton.mp ha
      exact ⟨trivial, (by intro η hη c hc; cases hc), .refl⟩
  | credit =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hv _ a ha
    · obtain rfl := List.mem_singleton.mp ha
      exact ⟨trivial, (by intro η hη c hc; cases hc), .refl⟩
  | prod s t ihs iht =>
    exact List.forall_mem_append.mpr ⟨hv _, (hp (extend_representable modes ihs)
      (extend_representable modes iht)).1⟩
  | sum s t ihs iht =>
    exact List.forall_mem_append.mpr ⟨hv _, (hp (extend_representable modes ihs)
      (extend_representable modes iht)).2.1⟩
  | fn s t ihs iht =>
    exact List.forall_mem_append.mpr ⟨hv _, (hp (extend_representable modes ihs)
      (extend_representable modes iht)).2.2⟩

theorem basis_spec {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {s : ComparisonShape} {b : Basis}
    (h : basis names modes shapes s = some b) :
    b.heads = heads names modes shapes s ∧ b.modes = modes ∧
      b.types = extend modes (heads names modes shapes s) := by
  unfold basis at h
  cases hh : heads names modes shapes s with
  | nil => simp [hh] at h
  | cons a rest =>
    simp only [hh, Option.some.injEq] at h
    subst b
    simp [Basis.heads, extend]

theorem basis_exists {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {s : ComparisonShape}
    (h : heads names modes shapes s ≠ []) :
    ∃b, basis names modes shapes s = some b := by
  unfold basis
  cases hh : heads names modes shapes s with
  | nil => simp [hh] at h
  | cons a rest => exact ⟨_, rfl⟩

def Normal (Δ : Bounds) (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape) (s : ComparisonShape) (a : CompareTy) : Prop :=
  ∃b, basis names modes shapes s = some b ∧ ∃t, LatticeForm b.types t ∧
    Representable Δ s t ∧ Equiv Δ a t

theorem normal_of_form {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {s : ComparisonShape} {a t : CompareTy}
    (hform : LatticeForm (heads names modes shapes s) t)
    (ht : Representable Δ s t) (he : Equiv Δ a t) :
    Normal Δ names modes shapes s a := by
  obtain ⟨b, hb⟩ := basis_exists hform.nonempty
  refine ⟨b, hb, t, hform.mono ?_, ht, he⟩
  intro x hx
  have hx' : x∈b.heads := (basis_spec hb).1.symm ▸ hx
  apply List.mem_map.mpr
  exact ⟨.head x, List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨x, hx', rfl⟩)), rfl⟩

theorem normal_of_head {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {s : ComparisonShape} {a : CompareTy}
    (hs : ∀v, ComparisonShape.Equivalent Δ (.var v) (shapes v))
    (ha : a∈heads names modes shapes s) : Normal Δ names modes shapes s a := by
  have hr := heads_representable names modes shapes hs s a ha
  exact normal_of_form (.atom ha) hr (.refl hr.1)

theorem Normal.typeOp {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {s : ComparisonShape} {a c : CompareTy}
    (p : Bool) (ha : Normal Δ names modes shapes s a) (hc : Normal Δ names modes shapes s c) :
    Normal Δ names modes shapes s (typeOp p a c) := by
  obtain ⟨b, hb, x, hx, hxr, hxe⟩ := ha
  obtain ⟨b', hb', y, hy, hyr, hye⟩ := hc
  have he : b'=b := Option.some.inj (hb'.symm.trans hb)
  subst b'
  refine ⟨b, hb, ComparisonAlgebra.typeOp p x y, lattice_typeOp p hx hy, representable_typeOp p hxr hyr, ?_⟩
  exact Equiv.typeOp p hxe hye
    (hxe.1.shape_equivalent.trans (hxr.2.2.trans (hyr.2.2.symm.trans hye.1.shape_equivalent.symm)))

theorem Normal.modal {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {s : ComparisonShape} {a : CompareTy} {m : ModExpr}
    (hs : ∀v, ComparisonShape.Equivalent Δ (.var v) (shapes v))
    (ha : Normal Δ names modes shapes s a) (hm : DefinedMode Δ m)
    (hms : ∀v∈m.freeVariables, v∈modes) :
    Normal Δ names modes shapes s (.modal a m) := by
  obtain ⟨b, hb, x, hx, hxr, hxe⟩ := ha
  obtain ⟨g, hg⟩ := hx.generated (fun _ => b.types_generated)
  let gm : ComparisonControls.Generated b := .modal g m (fun v hv => (basis_spec hb).2.1 ▸ hms v hv)
  have hgm : gm.term = .modal x m := by simp [gm, ComparisonControls.Generated.term, hg]
  have hgd : gm.term.DefinedUnder Δ := by
    rw [hgm]
    exact CompareTy.definedUnder_modal_iff.mpr ⟨hxr.2.1, hm⟩
  have hheads : ∀t∈b.heads, Representable Δ s t := by
    rw [(basis_spec hb).1]
    exact heads_representable names modes shapes hs s
  obtain ⟨t, ht, htr, hforward, hbackward⟩ := gm.lattice_normal hheads hgd
  refine ⟨b, hb, t, ht, htr, ?_⟩
  have hsm : Submode Δ m m := .refl hm
  rw [hgm] at hforward hbackward
  exact ⟨(AlgebraSubtype.congr hxe.1 hsm).trans hforward,
    hbackward.trans (.congr hxe.2 hsm)⟩

theorem constructor_heads (k : Kind) (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape) (s t : ComparisonShape) :
    ∀a∈pairs k.op (extend modes (heads names modes shapes s))
      (extend modes (heads names modes shapes t)), a∈heads names modes shapes (k.shape s t) := by
  cases k <;> exact fun _ => List.mem_append_right _

theorem Normal.constructor {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {s t : ComparisonShape} {a c : CompareTy}
    (hs : ∀v, ComparisonShape.Equivalent Δ (.var v) (shapes v)) (k : Kind)
    (ha : Normal Δ names modes shapes s a) (hc : Normal Δ names modes shapes t c) :
    Normal Δ names modes shapes (k.shape s t) (k.op a c) := by
  obtain ⟨b, hb, x, hx, hxr, hxe⟩ := ha
  obtain ⟨b', hb', y, hy, hyr, hye⟩ := hc
  rw [(basis_spec hb).2.2] at hx
  rw [(basis_spec hb').2.2] at hy
  obtain ⟨z, hz, hzr, hze⟩ := k.lattice hx hy
    (extend_representable modes (heads_representable names modes shapes hs s))
    (extend_representable modes (heads_representable names modes shapes hs t))
  apply normal_of_form (hz.mono (constructor_heads k names modes shapes s t)) hzr
  exact (k.congr hxe hye).trans hze

/-- With a finite declared shape model, input-supported defined witnesses have
 finite constructor-and-control normal forms. Fixed names remain available at
 their entire solved shape, including compound shapes. -/
theorem normal_of_supported {Δ : Bounds} (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape) (hmodels : ComparisonShape.Models Δ shapes)
    (hshapes : ∀v, ComparisonShape.Equivalent Δ (.var v) (shapes v))
    {a : CompareTy} (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (hsupport : ComparisonInterpolation.Supports (·∈names) (·∈modes) a) :
    Normal Δ names modes shapes (a.shape.subst shapes) a := by
  induction a with
  | var v =>
    apply normal_of_head hshapes
    have hv : CompareTy.var v ∈ fixedHeads names shapes (shapes v) := by
      exact List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨hsupport, by simp⟩, rfl⟩
    cases hshape : shapes v <;> simp only [hshape] at hv
    all_goals simp only [CompareTy.shape, ComparisonShape.subst, hshape, heads]
    all_goals first | exact hv | exact List.mem_append_left _ hv
  | unit => exact normal_of_head hshapes (List.mem_append_right _ (by simp))
  | credit => exact normal_of_head hshapes (List.mem_append_right _ (by simp))
  | prod a c iha ihc =>
    exact Normal.constructor hshapes .prod
      (iha hs.1 (CompareTy.definedUnder_prod_iff.mp hd).1 hsupport.1)
      (ihc hs.2 (CompareTy.definedUnder_prod_iff.mp hd).2 hsupport.2)
  | sum a c iha ihc =>
    exact Normal.constructor hshapes .sum
      (iha hs.1 (CompareTy.definedUnder_sum_iff.mp hd).1 hsupport.1)
      (ihc hs.2 (CompareTy.definedUnder_sum_iff.mp hd).2 hsupport.2)
  | fn a c iha ihc =>
    exact Normal.constructor hshapes .fn
      (iha hs.1 (CompareTy.definedUnder_fn_iff.mp hd).1 hsupport.1)
      (ihc hs.2 (CompareTy.definedUnder_fn_iff.mp hd).2 hsupport.2)
  | join a c iha ihc =>
    have he : a.shape.subst shapes = c.shape.subst shapes := hs.2.2 shapes hmodels
    apply Normal.typeOp true (iha hs.1 (CompareTy.definedUnder_join_iff.mp hd).1 hsupport.1)
    rw [he]
    exact ihc hs.2.1 (CompareTy.definedUnder_join_iff.mp hd).2 hsupport.2
  | meet a c iha ihc =>
    have he : a.shape.subst shapes = c.shape.subst shapes := hs.2.2 shapes hmodels
    apply Normal.typeOp false (iha hs.1 (CompareTy.definedUnder_meet_iff.mp hd).1 hsupport.1)
    rw [he]
    exact ihc hs.2.1 (CompareTy.definedUnder_meet_iff.mp hd).2 hsupport.2
  | modal a m ih =>
    exact Normal.modal hshapes (ih hs (CompareTy.definedUnder_modal_iff.mp hd).1 hsupport.1)
      (CompareTy.definedUnder_modal_iff.mp hd).2
      (fun v hv => hsupport.2 v ((m.mem_freeVariables v).mp hv))

end ModalityInference.ComparisonStructuralBasis
