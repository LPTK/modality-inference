import ModalityInference.Proofs.ComparisonObserverShadowModelExistence
import ModalityInference.Proofs.ComparisonObserverShadowQueryValues

/-! Raw support markers retain every type name and scalar name used by a
finite family of defined comparison queries. They impose no new assumptions. -/
namespace ModalityInference.ComparisonObserverShadowQuerySupport

open ComparisonObserverBoundary ComparisonRawHeadTrace
  ComparisonObserverShadowModel ComparisonObserverShadowAnchorRows

noncomputable section

def support (queries : List CompareTy) : List Ty := queries.flatMap fun a =>
  (types a).toList.map (fun v => (show Ty from .var v)) ++ (modes a).toList.map fun v => (show Ty from .modal .unit (.var v))

def rawInputs (raw : List Ty) (queries : List CompareTy) : List Ty := raw ++ support queries

def sites (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) : List Site :=
  RawInput.trace Δ (rawInputs raw queries)

theorem raw_mem {Δ : Bounds} {raw : List Ty} {queries : List CompareTy} {a : Ty}
    (ha : a ∈ raw) : (a,none) ∈ sites Δ raw queries :=
  RawInput.query_mem (List.mem_append_left _ ha)

theorem type_marker_mem {raw : List Ty} {queries : List CompareTy} {a : CompareTy}
    (ha : a ∈ queries) {v : TypeVar} (hv : v ∈ types a) :
    (show Ty from .var v) ∈ rawInputs raw queries :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨a,ha,
    List.mem_append_left _ (List.mem_map.mpr ⟨v,Finset.mem_toList.mpr hv,rfl⟩)⟩)

theorem mode_marker_mem {raw : List Ty} {queries : List CompareTy} {a : CompareTy}
    (ha : a ∈ queries) {v : ModVar} (hv : v ∈ modes a) :
    (show Ty from .modal .unit (.var v)) ∈ rawInputs raw queries :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨a,ha,
    List.mem_append_right _ (List.mem_map.mpr ⟨v,Finset.mem_toList.mpr hv,rfl⟩)⟩)

theorem head_mem_of_input {Δ : Bounds} {raw : List Ty} {queries : List CompareTy} {a : Ty}
    (ha : a ∈ rawInputs raw queries) : a ∈ rawHeads (sites Δ raw queries) :=
  List.mem_map.mpr ⟨(a,none),RawInput.query_mem ha,rfl⟩

theorem query_fresh {Δ : Bounds} {raw : List Ty} {queries : List CompareTy} {a : CompareTy}
    (ha : a ∈ queries) : ∀ v ∈ types a, v.index < freshBase (rawHeads (sites Δ raw queries)) := by
  intro v hv
  apply freshBase_fresh (head_mem_of_input (type_marker_mem ha hv))
  exact Finset.mem_singleton_self v

theorem query_modes {Δ : Bounds} {raw : List Ty} {queries : List CompareTy} {a : CompareTy}
    (ha : a ∈ queries) : modes a ⊆ (modeNames Δ (sites Δ raw queries)).toFinset := by
  intro v hv
  apply head_names (head_mem_of_input (mode_marker_mem ha hv))
  simp [TypeExpr.modVars,ModExpr.vars]

end
end ModalityInference.ComparisonObserverShadowQuerySupport
