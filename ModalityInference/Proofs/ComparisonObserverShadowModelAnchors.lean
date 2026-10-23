import ModalityInference.Proofs.ComparisonObserverShadowModel

/-! Defined raw trace sites agree with the finite defined algebra because
their two optional cuts are pinned by the recorded anchor rows. -/
namespace ModalityInference.ComparisonObserverShadowModel

open ComparisonRelativeSyntax ComparisonRawHeadFiniteOrbits ComparisonFiniteControls
  ComparisonObserverShadowPresentation ComparisonObserverShadowActionRows
  ComparisonObserverShadowActions ComparisonObserverFiniteRange ComparisonRawHeadTrace

noncomputable section

variable {Δ : Bounds} {hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ}
  {sites : List Site} {names : List ModVar}
  {extra : List (RawRow hn (assign hn (boundary Δ sites) names
    (ComparisonObserverShadowAnchorRows.freshBase (rawHeads sites))))}
  (R : Realization hn (boundary Δ sites) names
    (ComparisonObserverShadowAnchorRows.freshBase (rawHeads sites)) extra)

def siteTag : Site → ComparisonObserverFiniteRange.Value R.machine ⊕ Point (boundary Δ sites) names :=
  tag (unit R.range) Δ sites names

theorem siteTag_mem {s : Site} (hs : s ∈ sites) :
    siteTag R s = .inr (memberPoint Δ names hs) := tag_mem _ Δ names hs

theorem definedOrbit_eq (a : ComparisonObserverFiniteRange.Value R.machine) :
    definedOrbit R.interval R.modal R.range a = R.orbit (.inl a) := by
  ext m o
  rfl

theorem orbit_siteTag_defined
    (hrows : ComparisonObserverShadowAnchorRows.rows hn (rawHeads sites) names ⊆ extra)
    {s : Site} (hs : s ∈ sites) (hd : (applyPrefix s.2 s.1).DefinedUnder Δ) :
    R.orbit (siteTag R s) = definedOrbit R.interval R.modal R.range
      (eval R.range (.ofTy (applyPrefix s.2 s.1)) ((CompareTy.definedUnder_ofTy _ _).mpr hd)) := by
  rw [siteTag_mem R hs]
  let i : Fin (rawHeads sites).length := ⟨(index hs).val,
    by simpa only [rawHeads,List.length_map] using (index hs).isLt⟩
  have hi : (rawHeads sites)[i] = applyPrefix s.2 s.1 := by
    simpa [rawHeads,i] using congrArg (fun t : Site => applyPrefix t.2 t.1) (index_value hs)
  have hp : ComparisonObserverShadowAnchorRows.point (rawHeads sites) names i =
      memberPoint Δ names hs := rfl
  have he := ComparisonObserverShadowAnchorRows.orbit_pinned R hrows i (hi.symm ▸ hd)
  rw [hp] at he
  have heval {a b : Ty} (hab : a = b) (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
      eval R.range (.ofTy a) ((CompareTy.definedUnder_ofTy _ _).mpr ha) =
        eval R.range (.ofTy b) ((CompareTy.definedUnder_ofTy _ _).mpr hb) := by
    cases hab
    rfl
  have he' : R.orbit (.inr (memberPoint Δ names hs)) =
      R.orbit (.inl (eval R.range (.ofTy (applyPrefix s.2 s.1))
        ((CompareTy.definedUnder_ofTy _ _).mpr hd))) := by
    exact he.trans (congrArg (fun x => R.orbit (.inl x)) (heval hi (hi.symm ▸ hd) hd))
  exact he'.trans (definedOrbit_eq R _).symm

end
end ModalityInference.ComparisonObserverShadowModel
