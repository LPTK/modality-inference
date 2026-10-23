import ModalityInference.Proofs.ComparisonObserverRangeProduct
import ModalityInference.Proofs.ComparisonObserverBoundary
import ModalityInference.Proofs.ComparisonBalancedProjection

/-! Assigning arbitrary attained observer values to new variables gives a
sound infinite observer machine. One finite machine then preserves its entire
finite boundary, including all negative comparisons simultaneously. -/
namespace ModalityInference.ComparisonObserverRangeTransfer

open ComparisonAlgebra ComparisonStructuralLayout ComparisonStructuralLattice
  ComparisonStructuralObservers ComparisonObserverGluing ComparisonObserverRepresentatives
  ComparisonObserverRangeProduct ComparisonObserverBoundary ComparisonBalancedProjection

noncomputable section
attribute [local instance] Classical.propDecidable

def nodes {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ) (g : Child Δ) : ComparisonObserverMachine.Node (Child Δ) where
  atom v := (assign v g).val
  unitValue := (data hn g).unitValue
  creditValue := (data hn g).creditValue
  action := g.transition.apply
  branch k := ⟨((data hn g).branch k.kind).left,((data hn g).branch k.kind).child⟩
  range x := decide (g.Range x)

theorem modal_valid {Δ Γ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ) (hmodels : ∀ η, ModeModels Δ η → ModeModels Γ η) :
    ComparisonObserverMachine.ModalValid Γ (nodes hn assign) where
  monotone g m hm := g.transition.monotone m (fun η hη => hm η (hmodels η hη))
  epsilon g := g.transition.epsilon
  compose g m n hm hn' := g.transition.compose m n
    (fun η hη => hm η (hmodels η hη)) (fun η hη => hn' η (hmodels η hη))
  join g m n hm hn' := g.transition.join m n
    (fun η hη => hm η (hmodels η hη)) (fun η hη => hn' η (hmodels η hη))
  meet g m n hm hn' := g.transition.meet m n
    (fun η hη => hm η (hmodels η hη)) (fun η hη => hn' η (hmodels η hη))
  submode g m n h := g.transition.submode m n (.valid fun η hη => h.denote (hmodels η hη))

theorem range_closed {Δ Γ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ) (hmodels : ∀ η, ModeModels Δ η → ModeModels Γ η) :
    ComparisonObserverMachine.RangeClosed Γ (nodes hn assign) := by
  constructor
  · intro g v
    exact decide_eq_true (assign v g).property
  · intro g
    exact decide_eq_true (data_range hn g (a := .unit)
      (by intro η h; simp [CompareTy.wellFormedBounds,ModeModels]))
  · intro g
    exact decide_eq_true (data_range hn g (a := .credit)
      (by intro η h; simp [CompareTy.wellFormedBounds,ModeModels]))
  · intro g k x hx
    have h := ComparisonObserverFiniteMachine.branch_range hn g k.kind (of_decide_eq_true hx)
    apply decide_eq_true
    cases k <;> simpa only [nodes,Constructor.kind,ComparisonObserverMachine.sign,
      Constructor.dual,Bool.and_false,Bool.and_true,Bool.false_eq_true,
      if_false,Branch.sign,leftSign,ite_self] using h
  · intro g m hm x hx
    exact decide_eq_true (ComparisonObserverFiniteMachine.range_action g
      (fun η hη => hm η (hmodels η hη)) (of_decide_eq_true hx))

theorem coherent {Δ Γ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ) (hmodels : ∀ η, ModeModels Δ η → ModeModels Γ η) :
    ComparisonObserverMachine.Coherent Γ (nodes hn assign) := by
  constructor
  · intro g k hk m hm x hx
    have hk' : k.kind = .prod ∨ k.kind = .sum := by
      rcases hk with rfl | rfl <;> simp [Constructor.kind]
    exact (data_coherent hn g).pair k.kind hk' m
      (fun η hη => hm η (hmodels η hη)) x (of_decide_eq_true hx)
  · intro g m n h x hx
    have hh := (data_coherent hn g).fn m n
      (.valid fun η hη => h.denote (hmodels η hη)) x (of_decide_eq_true hx)
    simpa only [nodes,Constructor.kind,ComparisonObserverMachine.sign,
      Constructor.dual,Bool.and_true,Branch.sign,leftSign] using hh

theorem certified {Δ Γ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ) (hmodels : ∀ η, ModeModels Δ η → ModeModels Γ η)
    (hb : ComparisonObserverMachine.BoundsHold Γ (nodes hn assign)) :
    ComparisonObserverMachine.Certified Γ (nodes hn assign) :=
  ⟨modal_valid hn assign hmodels,range_closed hn assign hmodels,coherent hn assign hmodels,hb⟩

theorem subtype_mono {Δ Γ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ) (hmodels : ∀ η, ModeModels Δ η → ModeModels Γ η)
    (hb : ComparisonObserverMachine.BoundsHold Γ (nodes hn assign))
    (hΓ : Γ.TypeBoundsDefined) {a b : CompareTy}
    (ha : a.DefinedUnder Γ) (hb' : b.DefinedUnder Γ) (hab : AlgebraSubtype Γ a b) :
    ∀ g, ComparisonObserverMachine.value (nodes hn assign) a g ≤
      ComparisonObserverMachine.value (nodes hn assign) b g :=
  ComparisonObserverMachine.subtype_mono (modal_valid hn assign hmodels)
    (range_closed hn assign hmodels) (coherent hn assign hmodels) hb hΓ ha hb' hab

theorem not_subtype {Δ Γ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ) (hmodels : ∀ η, ModeModels Δ η → ModeModels Γ η)
    (hb : ComparisonObserverMachine.BoundsHold Γ (nodes hn assign))
    (hΓ : Γ.TypeBoundsDefined) {a b : CompareTy}
    (ha : a.DefinedUnder Γ) (hb' : b.DefinedUnder Γ)
    (hab : ¬ ∀ g, ComparisonObserverMachine.value (nodes hn assign) a g ≤
      ComparisonObserverMachine.value (nodes hn assign) b g) : ¬ AlgebraSubtype Γ a b :=
  fun h => hab (subtype_mono hn assign hmodels hb hΓ ha hb' h)

/-- One finite machine realizes every boundary pattern of the semantic
assignment. In particular, different negative anchors need not share a
separating coordinate, but they all survive in this same finite machine. -/
theorem finite_boundary {Δ Γ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ)
    (hmodels : ∀ η, ModeModels Δ η → ModeModels Γ η)
    (hb : ComparisonObserverMachine.BoundsHold Γ (nodes hn assign))
    (hΓ : Γ.TypeBoundsDefined) (hshape : ¬ ∃ ρ, ComparisonShape.Models Γ ρ)
    (queries : List CompareTy) :
    ∃ count ≤ sizeBound Γ queries, ∃ machine : ComparisonObserverMachine.Machine count,
      ComparisonObserverMachine.Certified Γ machine ∧
      ∀ g : Child Δ, ∃ i : Fin count, ∀ a ∈ queries, a.DefinedUnder Γ →
        ComparisonObserverMachine.value machine a i =
          ComparisonObserverMachine.value (nodes hn assign) a g := by
  let hc := certified hn assign hmodels hb
  obtain ⟨count,hcount,machine,hmachine,hcover⟩ := input_bounded_machine hshape hΓ queries
  refine ⟨count,hcount,machine,hmachine,?_⟩
  intro g
  obtain ⟨i,hi⟩ := hcover (hc.observer hΓ g)
  refine ⟨i,?_⟩
  intro a ha had
  rw [hi a ha had,booleanValue_represented _ a (representable hshape had)]
  rfl

/-- These are already prepared algebra bounds. The original shape facts
remain literal markers and must not be expanded through `Bounds.assumptions`. -/
def context (Δ : Bounds) (rows : List (Ty × Ty)) : Bounds :=
  rows.map (fun p => Constraint.sub p.1 p.2) ++ shapeShadow Δ

theorem context_modes (Δ : Bounds) (rows : List (Ty × Ty)) (η : ModVar → Mode) :
    ModeModels (context Δ rows) η ↔ ModeModels Δ η := by
  constructor
  · intro h
    apply (modeModels_shadow Δ η).mp
    exact fun c hc => h c (List.mem_append_right _ hc)
  · intro h c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨p,_,rfl⟩ := List.mem_map.mp hc
      trivial
    · exact (modeModels_shadow Δ η).mpr h c hc

theorem context_sub {Δ rows a b} :
    Constraint.sub a b ∈ context Δ rows ↔ (a,b) ∈ rows := by
  simp only [context,List.mem_append,sub_not_mem_shadow,or_false,List.mem_map]
  constructor
  · rintro ⟨⟨x,y⟩,h,hxy⟩
    cases hxy
    exact h
  · exact fun h => ⟨(a,b),h,rfl⟩

theorem context_no_shapes {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (rows : List (Ty × Ty)) : ¬ ∃ ρ, ComparisonShape.Models (context Δ rows) ρ := by
  rintro ⟨ρ,hρ⟩
  apply hn
  refine ⟨ρ,(shapeModels_shadow Δ ρ).mp ?_⟩
  intro p hp
  apply hρ p
  simpa only [context,ComparisonShape.pairs,List.flatMap_append] using
    List.mem_append_right
      (ComparisonShape.pairs (rows.map (fun p => Constraint.sub p.1 p.2))) hp

theorem context_defined {Δ rows}
    (hd : ∀ p ∈ rows, p.1.DefinedUnder Δ ∧ p.2.DefinedUnder Δ) :
    (context Δ rows).TypeBoundsDefined := by
  intro a b hab
  obtain ⟨ha,hb⟩ := hd (a,b) (context_sub.mp hab)
  exact ⟨fun η hη => ha η ((context_modes Δ rows η).mp hη),
    fun η hη => hb η ((context_modes Δ rows η).mp hη)⟩

theorem context_bounds {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ) (rows : List (Ty × Ty))
    (hr : ∀ p ∈ rows, ∀ g, ComparisonObserverMachine.value (nodes hn assign) (.ofTy p.1) g ≤
      ComparisonObserverMachine.value (nodes hn assign) (.ofTy p.2) g) :
    ComparisonObserverMachine.BoundsHold (context Δ rows) (nodes hn assign) :=
  fun g a b hab => hr (a,b) (context_sub.mp hab) g

theorem finite_rows {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ) (rows : List (Ty × Ty))
    (hd : ∀ p ∈ rows, p.1.DefinedUnder Δ ∧ p.2.DefinedUnder Δ)
    (hr : ∀ p ∈ rows, ∀ g, ComparisonObserverMachine.value (nodes hn assign) (.ofTy p.1) g ≤
      ComparisonObserverMachine.value (nodes hn assign) (.ofTy p.2) g)
    (queries : List CompareTy) :
    ∃ count ≤ sizeBound (context Δ rows) queries,
      ∃ machine : ComparisonObserverMachine.Machine count,
      ComparisonObserverMachine.Certified (context Δ rows) machine ∧
      ∀ g : Child Δ, ∃ i : Fin count, ∀ a ∈ queries, a.DefinedUnder (context Δ rows) →
        ComparisonObserverMachine.value machine a i =
          ComparisonObserverMachine.value (nodes hn assign) a g :=
  finite_boundary hn assign (fun η => (context_modes Δ rows η).mpr)
    (context_bounds hn assign rows hr) (context_defined hd) (context_no_shapes hn rows) queries

end
end ModalityInference.ComparisonObserverRangeTransfer
