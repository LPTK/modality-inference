import ModalityInference.Proofs.ComparisonSignedObservation
import ModalityInference.ComparisonAnnotations

/-! Actual selected layouts align instantiated public endpoint syntax with
their finite observer routes. Annotation guards follow from endpoint
definedness under the original assumptions; the observer label list preserves
the same shared modality substitution. -/

namespace ModalityInference.ComparisonSignedObservation
open ComparisonSignedEndpoints ComparisonStructuralLayout ComparisonControls ComparisonAlgebra
  ComparisonStructuralBasis ComparisonInterpolation

theorem build_represented {Δ names modes shapes layout a}
    (hmodel : ComparisonShape.Models Δ shapes)
    (hshapes : ∀v,ComparisonShape.Equivalent Δ (.var v) (shapes v))
    (hw : a.WellShaped Δ) (hd : a.DefinedUnder Δ) (hs : Supports (·∈names) (·∈modes) a)
    (hbuild : build names modes shapes (a.shape.subst shapes)=some layout) :
    layout.shape=a.shape.subst shapes ∧ Based names modes shapes layout ∧ Representable Δ layout.shape a := by
  obtain ⟨basis,hbasis,t,ht,htr,he⟩ := normal_of_supported names modes shapes hmodel hshapes hw hd hs
  obtain ⟨node,hn,hnshape,_,hb⟩ := build_complete names modes shapes _ hbasis
  have hnode : node=layout := Option.some.inj (hn.symm.trans hbuild)
  subst node
  exact ⟨hnshape,hb,hw,hd,hnshape ▸ he.1.shape_equivalent.trans htr.2.2⟩

theorem fixed_head {names modes shapes v} (hv : v∈names) :
    CompareTy.var v∈heads names modes shapes (shapes v) := by
  have h : CompareTy.var v∈fixedHeads names shapes (shapes v) :=
    List.mem_map.mpr ⟨v,List.mem_filter.mpr ⟨hv,by simp⟩,rfl⟩
  cases he : shapes v <;> simp only [heads]
  all_goals first | exact he ▸ h | exact List.mem_append_left _ (he ▸ h)

theorem build_constructor_result {names modes shapes k s t layout bl br}
    (hl : basis names modes shapes s=some bl) (hr : basis names modes shapes t=some br)
    (h : build names modes shapes (k.shape s t)=some layout) :
    ∃b left right, layout=.fork k b left right ∧
      build names modes shapes s=some left ∧ build names modes shapes t=some right := by
  rw [build_constructor] at h
  cases hb : basis names modes shapes (k.shape s t) <;> simp [hb,hl,hr] at h
  rename_i b
  cases hleft : build names modes shapes s <;> simp [hleft] at h
  rename_i left
  cases hright : build names modes shapes t <;> simp [hright] at h
  rename_i right
  subst layout
  exact ⟨b,left,right,rfl,rfl,rfl⟩

theorem endpoint_constructor {Δ labels keys σ names modes shapes k a b layout}
    (hmodel : ComparisonShape.Models Δ shapes)
    (hshapes : ∀v,ComparisonShape.Equivalent Δ (.var v) (shapes v))
    (haw : (σ.ty a).WellShaped Δ) (had : (σ.ty a).DefinedUnder Δ)
    (has : Supports (·∈names) (·∈modes) (σ.ty a))
    (hbw : (σ.ty b).WellShaped Δ) (hbd : (σ.ty b).DefinedUnder Δ)
    (hbs : Supports (·∈names) (·∈modes) (σ.ty b))
    (hla : ∀node,build names modes shapes ((σ.ty a).shape.subst shapes)=some node →
      Endpoint Δ labels keys σ node a)
    (hlb : ∀node,build names modes shapes ((σ.ty b).shape.subst shapes)=some node →
      Endpoint Δ labels keys σ node b)
    (hbuild : build names modes shapes
      (k.shape ((σ.ty a).shape.subst shapes) ((σ.ty b).shape.subst shapes))=some layout) :
    Endpoint Δ labels keys σ layout (publicOp k a b) := by
  obtain ⟨bl,hbl,_⟩ := normal_of_supported names modes shapes hmodel hshapes haw had has
  obtain ⟨br,hbr,_⟩ := normal_of_supported names modes shapes hmodel hshapes hbw hbd hbs
  obtain ⟨basis,left,right,rfl,hl,hr⟩ := build_constructor_result hbl hbr hbuild
  exact .node (hla left hl) (hlb right hr)

theorem build_endpoint {Δ labels keys σ names modes shapes layout a}
    (hmodel : ComparisonShape.Models Δ shapes)
    (hshapes : ∀v,ComparisonShape.Equivalent Δ (.var v) (shapes v))
    (hfixed : ∀v,(∀n∈keys,v≠.flex n) → σ.type v=.var v)
    (hw : (σ.ty a).WellShaped Δ) (hd : (σ.ty a).DefinedUnder Δ)
    (hs : Supports (·∈names) (·∈modes) (σ.ty a))
    (hlabels : ∀m∈ComparisonAnnotations.expressions a,∃g∈labels,g.expression=m.subst σ.mode)
    (hbuild : build names modes shapes ((σ.ty a).shape.subst shapes)=some layout) :
    Endpoint Δ labels keys σ layout a := by
  induction a generalizing layout with
  | var v =>
    obtain ⟨hshape,hbased,hrep⟩ := build_represented hmodel hshapes hw hd hs hbuild
    by_cases hsel : ∃n∈keys,v=.flex n
    · obtain ⟨n,hn,rfl⟩ := hsel
      exact .image hn hrep
    · have hu : ∀n∈keys,v≠.flex n := fun n hn he => hsel ⟨n,hn,he⟩
      have hf := hfixed v hu
      refine .fixed hu hf ?_
      rw [(basis_spec hbased.basis).1]
      have hv : v∈names := by simpa only [CompareSubstitution.ty,CompareTy.ofTy,CompareTy.subst,hf] using hs
      have he : layout.shape=shapes v := by
        simpa only [CompareSubstitution.ty,CompareTy.ofTy,CompareTy.subst,hf,CompareTy.shape,
          ComparisonShape.subst] using hshape
      rw [he]
      exact fixed_head hv
  | unit =>
    obtain ⟨hshape,hbased,_⟩ := build_represented hmodel hshapes hw hd hs hbuild
    apply Endpoint.unit
    rw [(basis_spec hbased.basis).1,hshape]
    exact List.mem_append_right _ (by simp)
  | credit =>
    obtain ⟨hshape,hbased,_⟩ := build_represented hmodel hshapes hw hd hs hbuild
    apply Endpoint.credit
    rw [(basis_spec hbased.basis).1,hshape]
    exact List.mem_append_right _ (by simp)
  | prod a b iha ihb =>
    have hd := CompareTy.definedUnder_prod_iff.mp hd
    exact endpoint_constructor (k := .prod) hmodel hshapes hw.1 hd.1 hs.1 hw.2 hd.2 hs.2
      (fun node hn => iha hw.1 hd.1 hs.1
        (fun m hm => hlabels m (List.mem_append_left _ hm)) hn)
      (fun node hn => ihb hw.2 hd.2 hs.2
        (fun m hm => hlabels m (List.mem_append_right _ hm)) hn) hbuild
  | sum a b iha ihb =>
    have hd := CompareTy.definedUnder_sum_iff.mp hd
    exact endpoint_constructor (k := .sum) hmodel hshapes hw.1 hd.1 hs.1 hw.2 hd.2 hs.2
      (fun node hn => iha hw.1 hd.1 hs.1
        (fun m hm => hlabels m (List.mem_append_left _ hm)) hn)
      (fun node hn => ihb hw.2 hd.2 hs.2
        (fun m hm => hlabels m (List.mem_append_right _ hm)) hn) hbuild
  | fn a b iha ihb =>
    have hd := CompareTy.definedUnder_fn_iff.mp hd
    exact endpoint_constructor (k := .fn) hmodel hshapes hw.1 hd.1 hs.1 hw.2 hd.2 hs.2
      (fun node hn => iha hw.1 hd.1 hs.1
        (fun m hm => hlabels m (List.mem_append_left _ hm)) hn)
      (fun node hn => ihb hw.2 hd.2 hs.2
        (fun m hm => hlabels m (List.mem_append_right _ hm)) hn) hbuild
  | modal a m ih =>
    exact .modal (ih hw (CompareTy.definedUnder_modal_iff.mp hd).1 hs.1
      (fun n hn => hlabels n (List.mem_cons_of_mem _ hn)) hbuild)
      (hlabels m List.mem_cons_self)

theorem annotation_defined {Δ : Bounds} {σ : CompareSubstitution} {a : Ty} (hd : (σ.ty a).DefinedUnder Δ) :
    ∀m∈ComparisonAnnotations.expressions a,Entails Δ (.defined (m.subst σ.mode)) := by
  induction a with
  | var _ | unit | credit => intro m hm;cases hm
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    have hpair := CompareTy.definedUnder_prod_iff.mp hd
    intro m hm
    rcases List.mem_append.mp hm with hm|hm
    · exact iha hpair.1 m hm
    · exact ihb hpair.2 m hm
  | modal a n ih =>
    have hpair := CompareTy.definedUnder_modal_iff.mp hd
    intro m hm
    rcases List.mem_cons.mp hm with rfl|hm
    · exact hpair.2
    · exact ih hpair.1 m hm

theorem annotation_support {σ : CompareSubstitution} {a : Ty} {names : List TypeVar} {modes : List ModVar}
    (hs : Supports (·∈names) (·∈modes) (σ.ty a)) :
    ∀m∈ComparisonAnnotations.expressions a,∀v∈(m.subst σ.mode).freeVariables,v∈modes := by
  induction a with
  | var _ | unit | credit => intro m hm;cases hm
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    intro m hm
    rcases List.mem_append.mp hm with hm|hm
    · exact iha hs.1 m hm
    · exact ihb hs.2 m hm
  | modal a n ih =>
    intro m hm
    rcases List.mem_cons.mp hm with rfl|hm
    · exact fun v hv => hs.2 v ((m.subst σ.mode).mem_freeVariables v |>.mp hv)
    · exact ih hs.1 m hm

def endpointLabels {Δ : Bounds} {σ : CompareSubstitution} {a : Ty} (hd : (σ.ty a).DefinedUnder Δ) : List (GuardedMode Δ) :=
  (ComparisonAnnotations.expressions a).attach.map fun m =>
    GuardedMode.ofDefined (Δ := Δ) (m.val.subst σ.mode) (by
      change ∀η,ModeModels Δ η → (m.val.subst σ.mode).WellFormed η
      exact annotation_defined (σ := σ) (a := a) hd m.val m.property)

theorem endpointLabels_cover {Δ : Bounds} {σ : CompareSubstitution} {a : Ty} (hd : (σ.ty a).DefinedUnder Δ)
    (m : ModExpr) (hm : m∈ComparisonAnnotations.expressions a) :
    ∃g∈endpointLabels hd,g.expression=m.subst σ.mode := by
  exact ⟨_,List.mem_map.mpr ⟨⟨m,hm⟩,List.mem_attach _ _,rfl⟩,rfl⟩

theorem endpointLabels_support {Δ : Bounds} {σ : CompareSubstitution} {a : Ty} {names : List TypeVar} {modes : List ModVar} (hd : (σ.ty a).DefinedUnder Δ)
    (hs : Supports (·∈names) (·∈modes) (σ.ty a)) :
    ∀g∈endpointLabels hd,∀v∈g.expression.freeVariables,v∈modes := by
  intro g hg
  obtain ⟨m,_,rfl⟩ := List.mem_map.mp hg
  exact annotation_support hs m.val m.property

def observingLabels {Δ : Bounds} {σ : CompareSubstitution} {left right : Ty}
    (modes : List ModVar) (hl : (σ.ty left).DefinedUnder Δ) (hr : (σ.ty right).DefinedUnder Δ) :
    List (GuardedMode Δ) :=
  ComparisonStructuralLayout.labels Δ modes ++ endpointLabels hl ++ endpointLabels hr

theorem observingLabels_left {Δ : Bounds} {σ : CompareSubstitution} {left right : Ty} {modes : List ModVar} (hl : (σ.ty left).DefinedUnder Δ)
    (hr : (σ.ty right).DefinedUnder Δ) :
    ∀m∈ComparisonAnnotations.expressions left,
      ∃g∈observingLabels modes hl hr,g.expression=m.subst σ.mode := by
  intro m hm
  obtain ⟨g,hg,he⟩ := endpointLabels_cover hl m hm
  exact ⟨g,List.mem_append_left _ (List.mem_append_right _ hg),he⟩

theorem observingLabels_right {Δ : Bounds} {σ : CompareSubstitution} {left right : Ty} {modes : List ModVar} (hl : (σ.ty left).DefinedUnder Δ)
    (hr : (σ.ty right).DefinedUnder Δ) :
    ∀m∈ComparisonAnnotations.expressions right,
      ∃g∈observingLabels modes hl hr,g.expression=m.subst σ.mode := by
  intro m hm
  obtain ⟨g,hg,he⟩ := endpointLabels_cover hr m hm
  exact ⟨g,List.mem_append_right _ hg,he⟩

theorem observingLabels_tests {Δ : Bounds} {σ : CompareSubstitution} {left right : Ty} {modes : List ModVar} (hl : (σ.ty left).DefinedUnder Δ)
    (hr : (σ.ty right).DefinedUnder Δ) :
    ∀m∈ComparisonStructuralAlignment.tests modes,
      ∃g∈observingLabels modes hl hr,g.expression=m := by
  intro m hm
  obtain ⟨g,hg,he⟩ := ComparisonStructuralLayout.labels_tests Δ modes m hm
  exact ⟨g,List.mem_append_left _ (List.mem_append_left _ hg),he⟩

theorem observingLabels_basis {Δ : Bounds} {σ : CompareSubstitution} {left right : Ty} {modes : List ModVar} (hl : (σ.ty left).DefinedUnder Δ)
    (hr : (σ.ty right).DefinedUnder Δ) (b : Basis) (hb : b.modes=modes) :
    ∀p∈b.modalPairs,∃g∈observingLabels modes hl hr,g.expression=p.2 := by
  intro p hp
  obtain ⟨g,hg,he⟩ := ComparisonStructuralLayout.labels_basis Δ b hb p hp
  exact ⟨g,List.mem_append_left _ (List.mem_append_left _ hg),he⟩

theorem observingLabels_support {Δ : Bounds} {σ : CompareSubstitution} {left right : Ty} {names : List TypeVar} {modes : List ModVar}
    (hl : (σ.ty left).DefinedUnder Δ) (hr : (σ.ty right).DefinedUnder Δ)
    (hls : Supports (·∈names) (·∈modes) (σ.ty left))
    (hrs : Supports (·∈names) (·∈modes) (σ.ty right)) :
    ∀g∈observingLabels modes hl hr,∀v∈g.expression.freeVariables,v∈modes := by
  intro g hg
  rcases List.mem_append.mp hg with hg|hg
  · rcases List.mem_append.mp hg with hg|hg
    · exact ComparisonStructuralLayout.labels_support Δ modes g hg
    · exact endpointLabels_support hl hls g hg
  · exact endpointLabels_support hr hrs g hg

theorem build_endpoints {Δ keys σ names modes shapes layout left right}
    (hmodel : ComparisonShape.Models Δ shapes)
    (hshapes : ∀v,ComparisonShape.Equivalent Δ (.var v) (shapes v))
    (hfixed : ∀v,(∀n∈keys,v≠.flex n) → σ.type v=.var v)
    (hlw : (σ.ty left).WellShaped Δ) (hld : (σ.ty left).DefinedUnder Δ)
    (hls : Supports (·∈names) (·∈modes) (σ.ty left))
    (hrw : (σ.ty right).WellShaped Δ) (hrd : (σ.ty right).DefinedUnder Δ)
    (hrs : Supports (·∈names) (·∈modes) (σ.ty right))
    (he : ComparisonShape.Equivalent Δ (σ.ty left).shape (σ.ty right).shape)
    (hbuild : build names modes shapes ((σ.ty left).shape.subst shapes)=some layout) :
    Endpoint Δ (observingLabels modes hld hrd) keys σ layout left ∧
      Endpoint Δ (observingLabels modes hld hrd) keys σ layout right := by
  have hright : build names modes shapes ((σ.ty right).shape.subst shapes)=some layout := by
    rw [←he shapes hmodel]
    exact hbuild
  exact ⟨build_endpoint hmodel hshapes hfixed hlw hld hls (observingLabels_left hld hrd) hbuild,
    build_endpoint hmodel hshapes hfixed hrw hrd hrs (observingLabels_right hld hrd) hright⟩

end ModalityInference.ComparisonSignedObservation
