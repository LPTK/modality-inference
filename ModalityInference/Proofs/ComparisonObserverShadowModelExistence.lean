import ModalityInference.Proofs.ComparisonObserverShadowModelReflection

/-! Every finite raw query family has a finite, full-rule sound interpretation
reflecting its original comparison order in the shape-inconsistent case. -/
namespace ModalityInference.ComparisonObserverShadowModel.RawInput

open ComparisonRelativeSyntax ComparisonRelativeCoordinates ComparisonRawHeadFiniteOrbits
  ComparisonFiniteControls ComparisonObserverShadowPresentation ComparisonObserverShadowActionRows
  ComparisonObserverShadowActions ComparisonRawHeadTrace

noncomputable section

def boundInputs (Δ : Bounds) : List Ty := Δ.flatMap fun c =>
  match c with
  | .sub a b => [a,b]
  | _ => []

theorem boundInputs_mem {Δ : Bounds} {a b : Ty} (h : Constraint.sub a b ∈ Δ) :
    a ∈ boundInputs Δ ∧ b ∈ boundInputs Δ :=
  ⟨List.mem_flatMap.mpr ⟨.sub a b,h,List.mem_cons_self⟩,
   List.mem_flatMap.mpr ⟨.sub a b,h,List.mem_cons_of_mem _ List.mem_cons_self⟩⟩

def trace (Δ : Bounds) (queries : List Ty) : List Site := ofInputs Δ (boundInputs Δ ++ queries)

theorem query_mem {Δ : Bounds} {queries : List Ty} {a : Ty} (ha : a ∈ queries) :
    (a,none) ∈ trace Δ queries :=
  input_subset (List.mem_append_right _ ha) (root_mem Δ a none)

theorem bounds_mem (Δ : Bounds) (queries : List Ty) {a b : Ty} (h : Constraint.sub a b ∈ Δ) :
    (a,none) ∈ trace Δ queries ∧ (b,none) ∈ trace Δ queries :=
  ⟨input_subset (List.mem_append_left _ (boundInputs_mem h).1) (root_mem Δ a none),
   input_subset (List.mem_append_left _ (boundInputs_mem h).2) (root_mem Δ b none)⟩

theorem trace_closed (Δ : Bounds) (queries : List Ty) :
    ∀ s ∈ trace Δ queries, calls Δ s.1 s.2 ⊆ trace Δ queries :=
  fun _ hs => ofInputs_closed hs

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (queries : List Ty)

def extraRows : List (RawRow hn (assign hn (boundary Δ (trace Δ queries))
    (modeNames Δ (trace Δ queries))
    (ComparisonObserverShadowAnchorRows.freshBase (rawHeads (trace Δ queries))))) :=
  List.append
    (ComparisonObserverShadowAnchorRows.rows hn (rawHeads (trace Δ queries)) (modeNames Δ (trace Δ queries)))
    (ComparisonObserverShadowConstructorRows.rows hn (boundary Δ (trace Δ queries))
      (modeNames Δ (trace Δ queries))
      (ComparisonObserverShadowAnchorRows.freshBase (rawHeads (trace Δ queries))))

theorem anchor_rows : ComparisonObserverShadowAnchorRows.rows hn (rawHeads (trace Δ queries))
    (modeNames Δ (trace Δ queries)) ⊆ extraRows hn queries := fun _ h => List.mem_append_left _ h

theorem constructor_rows : ComparisonObserverShadowConstructorRows.rows hn (boundary Δ (trace Δ queries))
    (modeNames Δ (trace Δ queries))
    (ComparisonObserverShadowAnchorRows.freshBase (rawHeads (trace Δ queries))) ⊆ extraRows hn queries :=
  fun _ h => List.mem_append_right _ h

def realization : Realization hn (boundary Δ (trace Δ queries)) (modeNames Δ (trace Δ queries))
    (ComparisonObserverShadowAnchorRows.freshBase (rawHeads (trace Δ queries))) (extraRows hn queries) :=
  Classical.choice (exists_realization hn _ _ _ (extraRows hn queries))

def table : Tables (realization hn queries) := tables (realization hn queries) (constructor_rows hn queries)

def model := interpretation (realization hn queries) (table hn queries)

theorem sound {a b : CompareTy} (h : AlgebraSubtype Δ a b) : (model hn queries).Related a b :=
  algebra_sound (realization hn queries) (table hn queries) (anchor_rows hn queries)
    (trace_closed Δ queries) (fun _ _ hb => bounds_mem Δ queries hb) h

theorem raw_iff {a b : Ty} (ha : a ∈ queries) (hb : b ∈ queries) :
    (model hn queries).Related (.ofTy a) (.ofTy b) ↔ AlgebraSubtype Δ (.ofTy a) (.ofTy b) :=
  raw_related_iff (realization hn queries) (table hn queries) (anchor_rows hn queries)
    (trace_closed Δ queries) (query_mem ha) (query_mem hb)

theorem finite_carrier : Finite (Coordinates (Control Δ (modeNames Δ (trace Δ queries)))
    (realization hn queries).interval.Completion) := (realization hn queries).orbit_space_finite

include hn

/-- The constructed interpreter has a finite Boolean carrier. Its evaluation
is sound for all comparison terms and exact on the supplied raw query family. -/
theorem finite_raw_model : ∃ n : Nat, ∃ value : CompareTy → Fin n → Bool,
    (∀ a b, AlgebraSubtype Δ a b → value a ≤ value b) ∧
    (∀ a ∈ queries, ∀ b ∈ queries,
      value (.ofTy a) ≤ value (.ofTy b) ↔ AlgebraSubtype Δ (.ofTy a) (.ofTy b)) := by
  let X := Control Δ (modeNames Δ (trace Δ queries)) × (realization hn queries).interval.Observation
  letI : Fintype (Control Δ (modeNames Δ (trace Δ queries))) := Fintype.ofFinite _
  letI : Fintype (realization hn queries).interval.Observation := Fintype.ofFinite _
  letI : Fintype X := by dsimp [X]; infer_instance
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let value (a : CompareTy) (i : Fin (Fintype.card X)) : Bool :=
    (model hn queries).denote a none (e.symm i).1 (e.symm i).2
  have hv (a b : CompareTy) : value a ≤ value b ↔ (model hn queries).Related a b := by
    constructor
    · intro h m o
      simpa only [value,Equiv.symm_apply_apply] using h (e (m,o))
    · intro h i
      exact h _ _
  refine ⟨Fintype.card X,value,?_,?_⟩
  · intro a b h
    exact (hv a b).mpr (sound hn queries h)
  · intro a ha b hb
    exact (hv _ _).trans (raw_iff hn queries ha hb)

theorem finite_raw_countermodel (a b : Ty) (h : ¬ AlgebraSubtype Δ (.ofTy a) (.ofTy b)) :
    ∃ n : Nat, ∃ value : CompareTy → Fin n → Bool,
      (∀ x y, AlgebraSubtype Δ x y → value x ≤ value y) ∧
      ¬ value (.ofTy a) ≤ value (.ofTy b) := by
  obtain ⟨n,value,hs,hr⟩ := finite_raw_model hn [a,b]
  exact ⟨n,value,hs,fun hv => h ((hr a (by simp) b (by simp)).mp hv)⟩

end
end ModalityInference.ComparisonObserverShadowModel.RawInput
