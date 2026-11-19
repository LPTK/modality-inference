import ModalityInference.Proofs.ComparisonRawHeadTrace
import ModalityInference.Proofs.ComparisonRawHeadPrefixRows

/-! Every visited raw constructor supplies its exact finite table row. The
membership proofs may come from any trace closed under recursive calls. -/
namespace ModalityInference.ComparisonRawHeadTraceRows

open ComparisonRawHeadTrace ComparisonRawHeadFiniteOrbits ComparisonFiniteControls
  ComparisonStructuralLayout

noncomputable section

variable {Δ : Bounds} {sites : List Site} {names : List ModVar}

def headIndex {s : Site} (hs : s ∈ sites) : Fin (boundary Δ sites).heads.length :=
  ⟨(index hs).val,by simpa only [boundary,Boundary.ofRaw,rawHeads,List.length_map] using
    (index hs).isLt⟩

theorem headIndex_value {s : Site} (hs : s ∈ sites) :
    (boundary Δ sites).heads[headIndex (Δ := Δ) hs] = .ofTy (applyPrefix s.2 s.1) := by
  simpa [headIndex,boundary,Boundary.ofRaw,rawHeads] using
    congrArg (fun t : Site => CompareTy.ofTy (applyPrefix t.2 t.1)) (index_value hs)

theorem memberPoint_eq {s : Site} (hs : s ∈ sites) :
    memberPoint Δ names hs = Point.base (boundary Δ sites) names (headIndex hs) := rfl

theorem act_memberPoint {s : Site} (hs : s ∈ sites) (m : Control Δ names) :
    Point.act m (memberPoint Δ names hs) = ⟨headIndex hs,m⟩ := by
  simp only [memberPoint_eq,Point.base,Point.act,one_mul]

def noneRow (k : Constructor) {a b c : Ty}
    (ha : (a,none) ∈ sites) (hb : (b,none) ∈ sites) (hc : (c,none) ∈ sites)
    (he : CompareTy.ofTy c = k.op (.ofTy a) (.ofTy b)) :
    ComparisonRawHeadFiniteRows.HeadRow (boundary Δ sites) k where
  left := headIndex ha
  right := headIndex hb
  output := headIndex hc
  equation := by simpa only [headIndex_value,applyPrefix] using he

def someRow (k : Constructor) (pref : ModExpr) {a b c : Ty}
    (ha : (a,some pref) ∈ sites) (hb : (b,some pref) ∈ sites)
    (hc : (c,some pref) ∈ sites)
    (he : CompareTy.ofTy c = k.op (.ofTy a) (.ofTy b)) :
    ComparisonRawHeadPrefixRows.HeadRow (boundary Δ sites) k pref where
  left := headIndex ha
  right := headIndex hb
  output := headIndex hc
  equation := by
    refine ⟨.ofTy a,.ofTy b,?_,?_,?_⟩
    · simp only [headIndex_value,applyPrefix,CompareTy.ofTy]
    · simp only [headIndex_value,applyPrefix,CompareTy.ofTy]
    · simpa only [headIndex_value,applyPrefix,CompareTy.ofTy] using congrArg (fun t => CompareTy.modal t pref) he

theorem pair_none (k : Constructor) {a b c : Ty}
    (ha : (a,none) ∈ sites) (hb : (b,none) ∈ sites) (hc : (c,none) ∈ sites)
    (he : CompareTy.ofTy c = k.op (.ofTy a) (.ofTy b)) (m : Control Δ names) :
    ComparisonRawHeadFiniteRows.PairRow k m
      (Point.act m (memberPoint Δ names ha)) (Point.act m (memberPoint Δ names hb))
      (Point.act m (memberPoint Δ names hc)) := by
  refine ⟨noneRow k ha hb hc he,?_,?_,?_⟩
  all_goals exact act_memberPoint _ m

theorem pair_some (k : Constructor) (pref : ModExpr) {a b c : Ty}
    (ha : (a,some pref) ∈ sites) (hb : (b,some pref) ∈ sites)
    (hc : (c,some pref) ∈ sites)
    (he : CompareTy.ofTy c = k.op (.ofTy a) (.ofTy b)) (m : Control Δ names) :
    ComparisonRawHeadPrefixRows.Row k pref m
      (Point.act m (memberPoint Δ names ha)) (Point.act m (memberPoint Δ names hb))
      (Point.act m (memberPoint Δ names hc)) := by
  refine ⟨someRow k pref ha hb hc he,?_,?_,?_⟩
  all_goals exact act_memberPoint _ m

theorem prod_none {a b : Ty} (ha : (a,none) ∈ sites) (hb : (b,none) ∈ sites)
    (hc : (.prod a b,none) ∈ sites) (m : Control Δ names) :
    ComparisonRawHeadFiniteRows.PairRow .prod m
      (Point.act m (memberPoint Δ names ha)) (Point.act m (memberPoint Δ names hb))
      (Point.act m (memberPoint Δ names hc)) := pair_none .prod ha hb hc rfl m

theorem sum_none {a b : Ty} (ha : (a,none) ∈ sites) (hb : (b,none) ∈ sites)
    (hc : (.sum a b,none) ∈ sites) (m : Control Δ names) :
    ComparisonRawHeadFiniteRows.PairRow .sum m
      (Point.act m (memberPoint Δ names ha)) (Point.act m (memberPoint Δ names hb))
      (Point.act m (memberPoint Δ names hc)) := pair_none .sum ha hb hc rfl m

theorem fn_none {a b : Ty} (ha : (a,none) ∈ sites) (hb : (b,none) ∈ sites)
    (hc : (.fn a b,none) ∈ sites) (m : Control Δ names) :
    ComparisonRawHeadFiniteRows.FnRow m
      (memberPoint Δ names ha) (memberPoint Δ names hb)
      (Point.act m (memberPoint Δ names hc)) := by
  refine ⟨noneRow .fn ha hb hc rfl,rfl,rfl,?_⟩
  exact act_memberPoint _ m

theorem prod_some {a b : Ty} {pref : ModExpr}
    (ha : (a,some pref) ∈ sites) (hb : (b,some pref) ∈ sites)
    (hc : (.prod a b,some pref) ∈ sites) (m : Control Δ names) :
    ComparisonRawHeadPrefixRows.Row .prod pref m
      (Point.act m (memberPoint Δ names ha)) (Point.act m (memberPoint Δ names hb))
      (Point.act m (memberPoint Δ names hc)) := pair_some .prod pref ha hb hc rfl m

theorem sum_some {a b : Ty} {pref : ModExpr}
    (ha : (a,some pref) ∈ sites) (hb : (b,some pref) ∈ sites)
    (hc : (.sum a b,some pref) ∈ sites) (m : Control Δ names) :
    ComparisonRawHeadPrefixRows.Row .sum pref m
      (Point.act m (memberPoint Δ names ha)) (Point.act m (memberPoint Δ names hb))
      (Point.act m (memberPoint Δ names hc)) := pair_some .sum pref ha hb hc rfl m

end
end ModalityInference.ComparisonRawHeadTraceRows
