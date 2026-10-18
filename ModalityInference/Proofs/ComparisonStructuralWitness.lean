import ModalityInference.Proofs.ComparisonStructuralPrepared
import ModalityInference.Proofs.ComparisonPreparedCarrierNormalization

/-! Simultaneous finite-basis normalization preserves the guarded comparison
witness, its modality assignment, and its exact substitution domains. -/

namespace ModalityInference.ComparisonStructuralBasis

open ComparisonAlgebra ComparisonControls ComparisonStructuralLattice
open ComparisonInterpolation ComparisonWitnessRestriction ComparisonPreparation

structure Replacement (Δ : Bounds) (σ τ : CompareSubstitution) : Prop where
  images : ∀ v, Equiv Δ (σ.type v) (τ.type v)
  defined : ∀ v, (τ.type v).DefinedUnder Δ
  modes : ∀ v, τ.mode v = σ.mode v

namespace Replacement

variable {Δ : Bounds} {σ τ : CompareSubstitution} (h : Replacement Δ σ τ)

include h

theorem ty_equivalent (t : Ty) (hd : (σ.ty t).DefinedUnder Δ) :
    Equiv Δ (σ.ty t) (τ.ty t) := by
  induction t with
  | var v => exact h.images v
  | unit | credit => exact .refl trivial
  | prod a b iha ihb =>
    exact Kind.congr .prod (iha (CompareTy.definedUnder_prod_iff.mp hd).1)
      (ihb (CompareTy.definedUnder_prod_iff.mp hd).2)
  | sum a b iha ihb =>
    exact Kind.congr .sum (iha (CompareTy.definedUnder_sum_iff.mp hd).1)
      (ihb (CompareTy.definedUnder_sum_iff.mp hd).2)
  | fn a b iha ihb =>
    exact Kind.congr .fn (iha (CompareTy.definedUnder_fn_iff.mp hd).1)
      (ihb (CompareTy.definedUnder_fn_iff.mp hd).2)
  | modal a m ih =>
    obtain ⟨ha, hm⟩ := CompareTy.definedUnder_modal_iff.mp hd
    have hi := ih ha
    have he := m.subst_congr (fun v _ => h.modes v)
    change Equiv Δ (.modal (σ.ty a) (m.subst σ.mode)) (.modal (τ.ty a) (m.subst τ.mode))
    rw [he]
    exact ⟨.congr hi.1 (.refl hm), .congr hi.2 (.refl hm)⟩

theorem ty_defined (t : Ty) (hd : (σ.ty t).DefinedUnder Δ) :
    (τ.ty t).DefinedUnder Δ := by
  induction t with
  | var v => exact h.defined v
  | unit | credit => exact hd
  | prod a b iha ihb =>
    exact CompareTy.definedUnder_prod_iff.mpr
      ⟨iha (CompareTy.definedUnder_prod_iff.mp hd).1, ihb (CompareTy.definedUnder_prod_iff.mp hd).2⟩
  | sum a b iha ihb =>
    exact CompareTy.definedUnder_sum_iff.mpr
      ⟨iha (CompareTy.definedUnder_sum_iff.mp hd).1, ihb (CompareTy.definedUnder_sum_iff.mp hd).2⟩
  | fn a b iha ihb =>
    exact CompareTy.definedUnder_fn_iff.mpr
      ⟨iha (CompareTy.definedUnder_fn_iff.mp hd).1, ihb (CompareTy.definedUnder_fn_iff.mp hd).2⟩
  | modal a m ih =>
    obtain ⟨ha, hm⟩ := CompareTy.definedUnder_modal_iff.mp hd
    apply CompareTy.definedUnder_modal_iff.mpr
    exact ⟨ih ha, (m.subst_congr (fun v _ => h.modes v)).symm ▸ hm⟩

theorem sub {a b : Ty} (hab : AlgebraEntails Δ (.sub (σ.ty a) (σ.ty b))) :
    AlgebraEntails Δ (.sub (τ.ty a) (τ.ty b)) :=
  ⟨(h.ty_equivalent a hab.2.1).2.trans (hab.1.trans (h.ty_equivalent b hab.2.2).1),
    h.ty_defined a hab.2.1, h.ty_defined b hab.2.2⟩

theorem constraint (c : Constraint) (hc : AlgebraEntails Δ (σ.constraint c)) :
    AlgebraEntails Δ (τ.constraint c) := by
  cases c with
  | sub a b => exact h.sub hc
  | equiv a b =>
    have ha := h.ty_equivalent a hc.2.2.1
    have hb := h.ty_equivalent b hc.2.2.2
    exact ⟨ha.2.trans (hc.1.trans hb.1), hb.2.trans (hc.2.1.trans ha.1),
      h.ty_defined a hc.2.2.1, h.ty_defined b hc.2.2.2⟩
  | equal v a =>
    rw [σ.algebra_equal_iff] at hc
    rw [τ.algebra_equal_iff]
    exact ⟨h.sub (a := .var v) (b := a) hc.1, h.sub (a := a) (b := .var v) hc.2⟩
  | mode m n =>
    have hm := m.subst_congr (fun v _ => h.modes v)
    have hn := n.subst_congr (fun v _ => h.modes v)
    simpa only [CompareSubstitution.constraint, hm, hn] using hc
  | defined m =>
    have hm := m.subst_congr (fun v _ => h.modes v)
    simpa only [CompareSubstitution.constraint, hm] using hc

theorem bounds (cs : Bounds) (hc : AlgebraEntailsAll Δ (σ.bounds cs)) :
    AlgebraEntailsAll Δ (τ.bounds cs) := by
  intro out hout
  obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hout
  exact h.constraint c (hc _ (List.mem_map.mpr ⟨c, hc', rfl⟩))

theorem prepared {p : SchemePreparation.Prepared} (he : Δ = p.assumptions)
    (hw : PreparedWitnessUnder p σ)
    (hd : τ.DomainsAbove p.firstType p.firstMode) (hs : τ.WellShaped p.assumptions) :
    PreparedWitnessUnder p τ := by
  subst Δ
  refine ⟨⟨hd, hs, h.bounds _ hw.1.2.2.1,
    (h.ty_equivalent _ hw.2.2).2.trans hw.1.2.2.2⟩, ⟨h.defined, ?_⟩,
    h.ty_defined _ hw.2.2⟩
  intro v
  rw [h.modes v]
  exact hw.2.1.modes v

end Replacement

theorem extend_support {P : TypeVar → Prop} {Q : ModVar → Prop}
    {as : List CompareTy} (modes : List ModVar)
    (ha : ∀a∈as, Supports P Q a) (hm : ∀v∈modes, Q v) :
    ∀a∈extend modes as, Supports P Q a := by
  cases as with
  | nil => simp [extend]
  | cons a rest => exact Basis.supports ha hm

theorem heads_support (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape) (s : ComparisonShape) :
    ∀a∈heads names modes shapes s, Supports (·∈names) (·∈modes) a := by
  have hv : ∀s a, a∈fixedHeads names shapes s → Supports (·∈names) (·∈modes) a := by
    intro s a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact (List.mem_filter.mp hv).1
  have hp : ∀ {left right : List CompareTy} (op : CompareTy → CompareTy → CompareTy),
      (∀a∈left, Supports (·∈names) (·∈modes) a) →
      (∀b∈right, Supports (·∈names) (·∈modes) b) →
      (∀a b, Supports (·∈names) (·∈modes) a → Supports (·∈names) (·∈modes) b →
        Supports (·∈names) (·∈modes) (op a b)) →
      ∀a∈pairs op left right, Supports (·∈names) (·∈modes) a := by
    intro left right op hl hr hop a ha
    obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    exact hop b c (hl b hb) (hr c hc)
  induction s with
  | var v => exact hv _
  | unit | credit =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hv _ a ha
    · obtain rfl := List.mem_singleton.mp ha
      trivial
  | prod s t ihs iht | sum s t ihs iht | fn s t ihs iht =>
    exact List.forall_mem_append.mpr ⟨hv _, hp _
      (extend_support modes ihs (fun _ h => h))
      (extend_support modes iht (fun _ h => h)) (fun _ _ ha hb => ⟨ha, hb⟩)⟩

theorem basis_support {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {s : ComparisonShape} {b : Basis}
    (h : basis names modes shapes s = some b) :
    ∀a∈b.types, Supports (·∈names) (·∈modes) a := by
  apply b.supports
  · rw [(basis_spec h).1]
    exact heads_support names modes shapes s
  · intro v hv
    simpa only [(basis_spec h).2.1] using hv

theorem lattice_support {P : TypeVar → Prop} {Q : ModVar → Prop}
    {as : List CompareTy} {a : CompareTy} (h : LatticeForm as a)
    (hs : ∀b∈as, Supports P Q b) : Supports P Q a := by
  induction h with
  | atom h => exact hs _ h
  | join _ _ ih₁ ih₂ | meet _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

theorem fixed_head_mem (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape) {v : TypeVar} (hv : v∈names) :
    CompareTy.var v ∈ heads names modes shapes (shapes v) := by
  have hh : CompareTy.var v ∈ fixedHeads names shapes (shapes v) :=
    List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨hv, by simp⟩, rfl⟩
  cases he : shapes v <;> simp only [he, heads] at *
  all_goals first | exact hh | exact List.mem_append_left _ hh

theorem head_mem_types {b : Basis} {a : CompareTy} (h : a∈b.heads) : a∈b.types :=
  List.mem_map.mpr ⟨.head a, List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨a, h, rfl⟩)), rfl⟩

theorem variable_lattice {Δ : Bounds} (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape)
    (hs : ∀v, ComparisonShape.Equivalent Δ (.var v) (shapes v))
    {v : TypeVar} (hv : v∈names) :
    ∃b, basis names modes shapes (shapes v) = some b ∧
      LatticeForm b.types (.var v) ∧ Representable Δ (shapes v) (.var v) := by
  have hh := fixed_head_mem names modes shapes hv
  obtain ⟨b, hb⟩ := basis_exists (List.ne_nil_of_mem hh)
  exact ⟨b, hb, .atom (head_mem_types ((basis_spec hb).1.symm ▸ hh)),
    heads_representable names modes shapes hs _ _ hh⟩

theorem supported_type_of_key {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (h : Supported p σ) {n : Nat} (hn : n ∈ σ.types.map Prod.fst) :
    Supports (·∈inputTypes p) (·∈inputModes p) (σ.type (.flex n)) := by
  cases he : σ.types.lookup n with
  | none =>
    obtain ⟨entry, hm, rfl⟩ := List.mem_map.mp hn
    have hne := List.lookup_eq_none_iff.mp he entry hm
    simp at hne
  | some a =>
    obtain ⟨left, right, hx, _⟩ := List.lookup_eq_some_iff.mp he
    simpa only [CompareSubstitution.type, he, Option.getD_some] using
      h.1 (n,a) (by simp [hx])

/-- All observed images are replaced together by finite lattice forms. The
modality action, key lists, guarded source bounds, and original target judgment
are preserved. -/
theorem prepared_lattice_witness_on {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    {fuel : Nat} {shapes : ComparisonShapeSolver.Solved}
    (names : List TypeVar) (modes : List ModVar)
    (ht : ∀v, v∈names ↔ v∈inputTypes p) (hm : ∀v, v∈modes ↔ v∈inputModes p)
    (hs : ComparisonShapeSolver.prepare fuel p = .success (.solved shapes))
    (hw : PreparedWitnessUnder p σ) (hsp : Supported p σ) :
    ∃ τ, PreparedWitnessUnder p τ ∧
      τ.types.map Prod.fst = σ.types.map Prod.fst ∧ τ.modes = σ.modes ∧
      Supported p τ ∧ Replacement p.assumptions σ τ ∧
      ∀v∈inputTypes p, ∃b,
        basis names modes shapes.fixedShapes
          ((σ.type v).shape.subst shapes.fixedShapes) = some b ∧
        LatticeForm b.types (τ.type v) ∧
        Representable p.assumptions ((σ.type v).shape.subst shapes.fixedShapes) (τ.type v) := by
  classical
  have hchoose : ∀v, ∃a, Equiv p.assumptions (σ.type v) a ∧
      a.DefinedUnder p.assumptions ∧
      (v∈inputTypes p → ∃b,
        basis names modes shapes.fixedShapes
          ((σ.type v).shape.subst shapes.fixedShapes) = some b ∧
        LatticeForm b.types a ∧
        Representable p.assumptions ((σ.type v).shape.subst shapes.fixedShapes) a) ∧
      (v∉inputTypes p → a = σ.type v) := by
    intro v
    by_cases hv : v∈inputTypes p
    · obtain ⟨b, hb, a, ha, har, hae⟩ := prepared_image_normal_on names modes ht hm hs hw hsp hv
      exact ⟨a, hae, har.2.1, fun _ => ⟨b, hb, ha, har⟩, fun h => (h hv).elim⟩
    · exact ⟨σ.type v, .refl (hw.1.2.1.type v), hw.2.1.types v,
        fun h => (hv h).elim, fun _ => rfl⟩
  choose images hi using hchoose
  let τ := ComparisonPartialCarrier.reimage σ images
  have hreplace : Replacement p.assumptions σ τ := by
    refine ⟨?_, ?_, ?_⟩
    · intro v
      rcases ComparisonPartialCarrier.reimage_type_cases σ images v with he | he
      · exact he ▸ (hi v).1
      · change Equiv p.assumptions (σ.type v) ((ComparisonPartialCarrier.reimage σ images).type v)
        rw [he.1]
        exact .refl (hw.1.2.1.type v)
    · intro v
      rcases ComparisonPartialCarrier.reimage_type_cases σ images v with he | he
      · exact he ▸ (hi v).2.1
      · exact he.1 ▸ hw.2.1.types v
    · intro v
      cases v <;> rfl
  have hshaped : τ.WellShaped p.assumptions :=
    ComparisonPartialCarrier.reimage_wellShaped (fun v => (hi v).1.1.wellShaped_right)
  have hsupported : Supported p τ := by
    refine ⟨?_, hsp.2⟩
    intro entry he
    change entry∈(σ.types.map Prod.fst).map (fun n => (n, images (.flex n))) at he
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
    by_cases hv : TypeVar.flex n ∈ inputTypes p
    · obtain ⟨b, hb, hf, _⟩ := (hi (.flex n)).2.2.1 hv
      exact (lattice_support hf (basis_support hb)).mono
        (fun v h => (ht v).mp h) (fun v h => (hm v).mp h)
    · change Supports (·∈inputTypes p) (·∈inputModes p) (images (.flex n))
      rw [(hi (.flex n)).2.2.2 hv]
      exact supported_type_of_key hsp hn
  refine ⟨τ, hreplace.prepared rfl hw
    (ComparisonPartialCarrier.reimage_domainsAbove hw.1.1 images) hshaped,
    ComparisonPartialCarrier.reimage_keys σ images, rfl, hsupported, hreplace, ?_⟩
  intro v hv
  rcases ComparisonPartialCarrier.reimage_type_cases σ images v with he | he
  · change ∃b : Basis, _ ∧ LatticeForm b.types ((ComparisonPartialCarrier.reimage σ images).type v) ∧ _
    rw [he]
    exact (hi v).2.2.1 hv
  · change ∃b : Basis, _ ∧ LatticeForm b.types ((ComparisonPartialCarrier.reimage σ images).type v) ∧ _
    rw [he.1, he.2]
    apply variable_lattice _ _ _ _ ((ht v).mpr hv)
    intro w ρ hρ
    exact (ComparisonShapeSolver.unify_factor (ComparisonShapeSolver.prepare_solved_iff.mp hs).1 hρ w).symm


theorem prepared_lattice_witness {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    {fuel : Nat} {shapes : ComparisonShapeSolver.Solved}
    (hs : ComparisonShapeSolver.prepare fuel p = .success (.solved shapes))
    (hw : PreparedWitnessUnder p σ) (hsp : Supported p σ) :
    ∃ τ, PreparedWitnessUnder p τ ∧
      τ.types.map Prod.fst = σ.types.map Prod.fst ∧ τ.modes = σ.modes ∧
      Supported p τ ∧ Replacement p.assumptions σ τ ∧
      ∀v∈inputTypes p, ∃b,
        basis (inputTypes p).toList (inputModes p).toList shapes.fixedShapes
          ((σ.type v).shape.subst shapes.fixedShapes) = some b ∧
        LatticeForm b.types (τ.type v) ∧
        Representable p.assumptions ((σ.type v).shape.subst shapes.fixedShapes) (τ.type v) :=
  prepared_lattice_witness_on (inputTypes p).toList (inputModes p).toList
    (fun _ => Finset.mem_toList) (fun _ => Finset.mem_toList) hs hw hsp

end ModalityInference.ComparisonStructuralBasis
