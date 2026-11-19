import ModalityInference.Proofs.ComparisonObserverShadowSource

/-! Modal and constructor inequalities on named shadow values are raw defined
bounds, so they can be imposed in the same finite realization as the optional
interval order. -/
namespace ModalityInference.ComparisonObserverShadowPresentation

open ComparisonObserverRangeTransfer ComparisonObserverRangeProduct
  ComparisonStructuralObservers ComparisonObserverGluing ComparisonObserverRepresentatives

noncomputable section

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ)

def rawOp : ComparisonStructuralLattice.Kind → Ty → Ty → Ty
  | .prod => .prod
  | .sum => .sum
  | .fn => .fn

theorem rawOp_defined (k : ComparisonStructuralLattice.Kind) {a b : Ty}
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) : (rawOp k a b).DefinedUnder Δ := by
  intro η hη c hc
  cases k <;> exact (List.mem_append.mp hc).elim (ha η hη c) (hb η hη c)

theorem rawModal_defined {a : Ty} (ha : a.DefinedUnder Δ) {m : ModExpr}
    (hm : Entails Δ (.defined m)) : (show Ty from .modal a m).DefinedUnder Δ := by
  intro η hη c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact ha η hη c hc
  · have he : c = .defined m := by simpa only [List.mem_singleton] using hc
    subst c
    exact hm η hη

theorem modal_named_value (m : ModExpr) (hm : Entails Δ (.defined m))
    (v : TypeVar) (g : Child Δ) :
    ComparisonObserverMachine.value (nodes hn assign) (.modal (.var v) m) g =
      (modal m hm (assign v) g).val := rfl

theorem op_named_value (k : ComparisonStructuralLattice.Kind)
    (v w : TypeVar) (g : Child Δ) :
    ComparisonObserverMachine.value (nodes hn assign) (.ofTy (rawOp k (.var v) (.var w))) g =
      (op hn k (assign v) (assign w) g).val := by
  cases k <;> simp only [rawOp,CompareTy.ofTy,ComparisonObserverMachine.value,nodes,
    ComparisonStructuralLayout.Constructor.kind,op_val,leftSign]

theorem modal_op_named_value (k : ComparisonStructuralLattice.Kind)
    (m : ModExpr) (hm : Entails Δ (.defined m)) (v w : TypeVar) (g : Child Δ) :
    ComparisonObserverMachine.value (nodes hn assign)
        (.ofTy (.modal (rawOp k (.var v) (.var w)) m)) g =
      (modal m hm (op hn k (assign v) (assign w)) g).val := by
  change g.transition.apply m _ = g.transition.apply m _
  exact congrArg (g.transition.apply m) (op_named_value hn assign k v w g)

structure RawRow where
  pair : Ty × Ty
  defined : pair.1.DefinedUnder Δ ∧ pair.2.DefinedUnder Δ
  sound : ∀ g, ComparisonObserverMachine.value (nodes hn assign) (.ofTy pair.1) g ≤
    ComparisonObserverMachine.value (nodes hn assign) (.ofTy pair.2) g

namespace RawRow

def modal_le (m : ModExpr) (hm : Entails Δ (.defined m)) (v w : TypeVar)
    (h : modal m hm (assign v) ≤ assign w) : RawRow hn assign where
  pair := (.modal (.var v) m,.var w)
  defined := ⟨rawModal_defined (raw_var_defined Δ v) hm,raw_var_defined Δ w⟩
  sound := h

def le_modal (m : ModExpr) (hm : Entails Δ (.defined m)) (v w : TypeVar)
    (h : assign v ≤ modal m hm (assign w)) : RawRow hn assign where
  pair := (.var v,.modal (.var w) m)
  defined := ⟨raw_var_defined Δ v,rawModal_defined (raw_var_defined Δ w) hm⟩
  sound := h

def op_le (k : ComparisonStructuralLattice.Kind) (m : ModExpr)
    (hm : Entails Δ (.defined m)) (u v w : TypeVar)
    (h : modal m hm (op hn k (assign u) (assign v)) ≤ assign w) : RawRow hn assign where
  pair := (.modal (rawOp k (.var u) (.var v)) m,.var w)
  defined := ⟨rawModal_defined (rawOp_defined k (raw_var_defined Δ u) (raw_var_defined Δ v)) hm,
    raw_var_defined Δ w⟩
  sound g := by
    rw [modal_op_named_value hn assign k m hm u v g]
    exact h g

def le_op (k : ComparisonStructuralLattice.Kind) (m : ModExpr)
    (hm : Entails Δ (.defined m)) (u v w : TypeVar)
    (h : assign u ≤ modal m hm (op hn k (assign v) (assign w))) : RawRow hn assign where
  pair := (.var u,.modal (rawOp k (.var v) (.var w)) m)
  defined := ⟨raw_var_defined Δ u,
    rawModal_defined (rawOp_defined k (raw_var_defined Δ v) (raw_var_defined Δ w)) hm⟩
  sound g := by
    rw [modal_op_named_value hn assign k m hm v w g]
    exact h g

def rows (rs : List (RawRow hn assign)) : List (Ty × Ty) := rs.map RawRow.pair

theorem rows_defined (rs : List (RawRow hn assign)) : ∀ p ∈ rows hn assign rs,
    p.1.DefinedUnder Δ ∧ p.2.DefinedUnder Δ := by
  intro p hp
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hp
  exact r.defined

theorem rows_sound (rs : List (RawRow hn assign)) : ∀ p ∈ rows hn assign rs, ∀ g,
    ComparisonObserverMachine.value (nodes hn assign) (.ofTy p.1) g ≤
      ComparisonObserverMachine.value (nodes hn assign) (.ofTy p.2) g := by
  intro p hp
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hp
  exact r.sound

end RawRow
end
end ModalityInference.ComparisonObserverShadowPresentation
