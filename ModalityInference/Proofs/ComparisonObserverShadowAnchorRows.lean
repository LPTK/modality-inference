import ModalityInference.Proofs.ComparisonObserverShadowActions

namespace ModalityInference.ComparisonObserverShadowActions.Realization

open ComparisonObserverShadowPresentation ComparisonObserverShadowActionRows
  ComparisonObserverRangeTransfer ComparisonRawHeadFiniteOrbits

theorem contains_extra {Δ : Bounds} {hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ}
    {B : Boundary Δ} {names : List ModVar} {base : Nat}
    {extra : List (RawRow hn (assign hn B names base))} {r : RawRow hn (assign hn B names base)}
    (hr : r ∈ extra) : r.pair ∈ diagramRows hn B names base extra :=
  List.mem_append_right _ (List.mem_map.mpr ⟨r,List.mem_append_right _ hr,rfl⟩)

theorem extra_bound {Δ : Bounds} {hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ}
    {B : Boundary Δ} {names : List ModVar} {base : Nat}
    {extra : List (RawRow hn (assign hn B names base))}
    (R : Realization hn B names base extra) {r : RawRow hn (assign hn B names base)} (hr : r ∈ extra) :
    ∀ i, ComparisonObserverMachine.value R.machine (.ofTy r.pair.1) i ≤
      ComparisonObserverMachine.value R.machine (.ofTy r.pair.2) i :=
  fun i => R.certified.bounds i _ _ (context_sub.mpr (contains_extra hr))

end ModalityInference.ComparisonObserverShadowActions.Realization

/-! Defined raw heads are pinned using two raw inequalities. Consistency of
their optional cuts supplies the other directions, and total actions then
preserve the resulting equality throughout the finite orbit. -/
namespace ModalityInference.ComparisonObserverShadowAnchorRows

open ComparisonObserverShadowPresentation ComparisonObserverShadowActionRows
  ComparisonObserverShadowActions ComparisonObserverHeadCuts ComparisonObserverShadowRows
  ComparisonRawHeadFiniteOrbits ComparisonObserverRangeProduct ComparisonAlgebra
  ComparisonObserverGluing ComparisonObserverRangeTransfer

noncomputable section
attribute [local instance] Classical.propDecidable

def indexBound : List TypeVar → Nat
  | [] => 0
  | v :: vs => max v.index (indexBound vs)

theorem index_le_bound {v : TypeVar} {vs : List TypeVar} (hv : v ∈ vs) : v.index ≤ indexBound vs := by
  induction vs with
  | nil => cases hv
  | cons w ws ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · exact le_max_left _ _
    · exact (ih hv).trans (le_max_right _ _)

def freshBase (heads : List Ty) : Nat :=
  indexBound (heads.flatMap fun a => a.typeVars.toList) + 1

theorem freshBase_fresh {heads : List Ty} {a : Ty} (ha : a ∈ heads) {v : TypeVar}
    (hv : v ∈ a.typeVars) : v.index < freshBase heads :=
  Nat.lt_succ_of_le (index_le_bound (List.mem_flatMap.mpr ⟨a,ha,Finset.mem_toList.mpr hv⟩))

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (heads : List Ty) (names : List ModVar)

def headIndex (i : Fin heads.length) : Fin (Boundary.ofRaw Δ heads).heads.length :=
  ⟨i,by simpa only [Boundary.ofRaw,List.length_map] using i.isLt⟩

theorem headIndex_value (i : Fin heads.length) :
    (Boundary.ofRaw Δ heads).heads[headIndex (Δ := Δ) heads i] = .ofTy heads[i] := by
  simp [Boundary.ofRaw,headIndex]

def point (i : Fin heads.length) : Point (Boundary.ofRaw Δ heads) names :=
  Point.base _ _ (headIndex heads i)

theorem point_equivalent (i : Fin heads.length) :
    AlgebraSubtype Δ (point (Δ := Δ) heads names i).term (.ofTy heads[i]) ∧
      AlgebraSubtype Δ (.ofTy heads[i]) (point (Δ := Δ) heads names i).term := by
  simpa only [headIndex_value] using
    (Point.base_equivalent (names := names) (headIndex (Δ := Δ) heads i))

def lower_present (i : Fin heads.length) (ha : heads[i].DefinedUnder Δ) :
    LowerInhabited (Δ := Δ) (shape := .unit) (point (Δ := Δ) heads names i).term :=
  ⟨represented (representable hn ((CompareTy.definedUnder_ofTy _ _).mpr ha)),
    (point_equivalent heads names i).2⟩

def upper_present (i : Fin heads.length) (ha : heads[i].DefinedUnder Δ) :
    UpperInhabited (Δ := Δ) (shape := .unit) (point (Δ := Δ) heads names i).term :=
  ⟨represented (representable hn ((CompareTy.definedUnder_ofTy _ _).mpr ha)),
    (point_equivalent heads names i).1⟩

theorem lower_value (i : Fin heads.length) (ha : heads[i].DefinedUnder Δ) :
    assign hn (Boundary.ofRaw Δ heads) names (freshBase heads)
      (shadowName (freshBase heads) (point (Δ := Δ) heads names i,false)) =
      ofType hn (.ofTy heads[i]) ((CompareTy.definedUnder_ofTy _ _).mpr ha) := by
  rw [lower_name hn _ names _ _ (lower_present hn heads names i ha)]
  let c := represented (representable hn ((CompareTy.definedUnder_ofTy _ _).mpr ha))
  have hd : LowerInhabited (Δ := Δ) (shape := .unit) c.type := ⟨c,.refl c.shaped⟩
  have he : lower (lower_present hn heads names i ha) = lower hd := le_antisymm
    (ComparisonObserverShadowRows.lower_mono _ hd (point_equivalent heads names i).1)
    (ComparisonObserverShadowRows.lower_mono hd _ (point_equivalent heads names i).2)
  exact he.trans (lower_defined c)

theorem upper_value (i : Fin heads.length) (ha : heads[i].DefinedUnder Δ) :
    assign hn (Boundary.ofRaw Δ heads) names (freshBase heads)
      (shadowName (freshBase heads) (point (Δ := Δ) heads names i,true)) =
      ofType hn (.ofTy heads[i]) ((CompareTy.definedUnder_ofTy _ _).mpr ha) := by
  rw [upper_name hn _ names _ _ (upper_present hn heads names i ha)]
  let c := represented (representable hn ((CompareTy.definedUnder_ofTy _ _).mpr ha))
  have hd : UpperInhabited (Δ := Δ) (shape := .unit) c.type := ⟨c,.refl c.shaped⟩
  have he : upper (upper_present hn heads names i ha) = upper hd := le_antisymm
    (ComparisonObserverShadowRows.upper_mono _ hd (point_equivalent heads names i).1)
    (ComparisonObserverShadowRows.upper_mono hd _ (point_equivalent heads names i).2)
  exact he.trans (upper_defined c)

def lowerRow (i : Fin heads.length) (ha : heads[i].DefinedUnder Δ) :
    RawRow hn (assign hn (Boundary.ofRaw Δ heads) names (freshBase heads)) :=
  anchor_le hn (source (Boundary.ofRaw Δ heads) names) (freshBase heads) heads[i] ha
    (fun _ hv => freshBase_fresh (List.getElem_mem i.isLt) hv)
    (shadowName (freshBase heads) (point (Δ := Δ) heads names i,false))
    (lower_value hn heads names i ha)

def upperRow (i : Fin heads.length) (ha : heads[i].DefinedUnder Δ) :
    RawRow hn (assign hn (Boundary.ofRaw Δ heads) names (freshBase heads)) :=
  le_anchor hn (source (Boundary.ofRaw Δ heads) names) (freshBase heads) heads[i] ha
    (fun _ hv => freshBase_fresh (List.getElem_mem i.isLt) hv)
    (shadowName (freshBase heads) (point (Δ := Δ) heads names i,true))
    (upper_value hn heads names i ha)

def rows : List (RawRow hn (assign hn (Boundary.ofRaw Δ heads) names (freshBase heads))) :=
  Finset.univ.toList.flatMap fun i : Fin heads.length =>
    if ha : heads[i].DefinedUnder Δ then [lowerRow hn heads names i ha,upperRow hn heads names i ha] else []

theorem lowerRow_mem (i : Fin heads.length) (ha : heads[i].DefinedUnder Δ) :
    lowerRow hn heads names i ha ∈ rows hn heads names := by
  apply List.mem_flatMap.mpr
  exact ⟨i,Finset.mem_toList.mpr (Finset.mem_univ i),by simp only [dif_pos ha,List.mem_cons_self]⟩

theorem upperRow_mem (i : Fin heads.length) (ha : heads[i].DefinedUnder Δ) :
    upperRow hn heads names i ha ∈ rows hn heads names := by
  apply List.mem_flatMap.mpr
  exact ⟨i,Finset.mem_toList.mpr (Finset.mem_univ i),by
    rw [dif_pos ha]
    exact List.mem_cons_of_mem _ List.mem_cons_self⟩

variable {hn heads names}
    {extra : List (RawRow hn (assign hn (Boundary.ofRaw Δ heads) names (freshBase heads)))}
    (R : Realization hn (Boundary.ofRaw Δ heads) names (freshBase heads) extra)
    (hrows : ∀ r ∈ rows hn heads names, r ∈ extra)

include hrows

theorem pinned (i : Fin heads.length) (ha : heads[i].DefinedUnder Δ) :
    let a := ComparisonObserverFiniteRange.eval R.range (.ofTy heads[i])
      ((CompareTy.definedUnder_ofTy _ _).mpr ha)
    R.interval.lower (point (Δ := Δ) heads names i) = some a ∧
      R.interval.upper (point (Δ := Δ) heads names i) = some a := by
  dsimp only
  let p := point (Δ := Δ) heads names i
  let lo := ComparisonObserverFiniteRange.atom R.certified.range (shadowName (freshBase heads) (p,false))
  let up := ComparisonObserverFiniteRange.atom R.certified.range (shadowName (freshBase heads) (p,true))
  have hl : R.interval.lower p = some lo :=
    (R.lower_eq p).trans (if_pos (lower_present hn heads names i ha))
  have hu : R.interval.upper p = some up :=
    (R.upper_eq p).trans (if_pos (upper_present hn heads names i ha))
  have hlu := R.interval.consistent p lo up hl hu
  have hal : ComparisonObserverFiniteRange.eval R.range (.ofTy heads[i])
      ((CompareTy.definedUnder_ofTy _ _).mpr ha) ≤ lo :=
    R.extra_bound (hrows _ (lowerRow_mem hn heads names i ha))
  have hua : up ≤ ComparisonObserverFiniteRange.eval R.range (.ofTy heads[i])
      ((CompareTy.definedUnder_ofTy _ _).mpr ha) :=
    R.extra_bound (hrows _ (upperRow_mem hn heads names i ha))
  exact ⟨hl.trans (congrArg some (le_antisymm (hlu.trans hua) hal)),
    hu.trans (congrArg some (le_antisymm hua (hal.trans hlu)))⟩

theorem pinned_action (m : ComparisonFiniteControls.Control Δ names)
    (i : Fin heads.length) (ha : heads[i].DefinedUnder Δ) :
    let a := ComparisonFiniteControlRange.action R.modal R.range m
      (ComparisonObserverFiniteRange.eval R.range (.ofTy heads[i])
        ((CompareTy.definedUnder_ofTy _ _).mpr ha))
    R.interval.lower (Point.act m (point (Δ := Δ) heads names i)) = some a ∧
      R.interval.upper (Point.act m (point (Δ := Δ) heads names i)) = some a := by
  dsimp only
  obtain ⟨lo,hl,hal⟩ := (R.action m).lower_shadow (pinned R hrows i ha).1
  obtain ⟨up,hu,hua⟩ := (R.action m).upper_shadow (pinned R hrows i ha).2
  have hlu := R.interval.consistent _ lo up hl hu
  exact ⟨hl.trans (congrArg some (le_antisymm (hlu.trans hua) hal)),
    hu.trans (congrArg some (le_antisymm hua (hal.trans hlu)))⟩

theorem orbit_pinned (i : Fin heads.length) (ha : heads[i].DefinedUnder Δ) :
    R.orbit (.inr (point (Δ := Δ) heads names i)) =
      R.orbit (.inl (ComparisonObserverFiniteRange.eval R.range (.ofTy heads[i])
        ((CompareTy.definedUnder_ofTy _ _).mpr ha))) :=
  ComparisonRelativeDiagramActions.diagramOrbit_anchor R.action R.defined_index R.boundary_index
    (pinned R hrows i ha).1 (pinned R hrows i ha).2

end
end ModalityInference.ComparisonObserverShadowAnchorRows
