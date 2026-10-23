import ModalityInference.Proofs.ComparisonObserverFiniteMachine

/-! The product of the inhabited Boolean ranges of all genuine observers.
The product admits nonempty suprema and infima without adding a value to a
constant observer's range. Constructor coordinates retain their selected child. -/
namespace ModalityInference.ComparisonObserverRangeProduct

open ComparisonAlgebra ComparisonStructuralLattice ComparisonStructuralObservers
  ComparisonObserverGluing ComparisonObserverRepresentatives ComparisonObserverFiniteMachine

noncomputable section

private def unitCarrier (Δ : Bounds) : Carrier Δ .unit where
  type := .unit
  shaped := trivial
  defined := by simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
  shape_eq := .refl

abbrev Fiber {Δ} (g : Child Δ) := {b : Bool // g.Range b}

instance fiberNonempty {Δ} (g : Child Δ) : Nonempty (Fiber g) :=
  ⟨⟨observer g.observer (unitCarrier Δ),⟨unitCarrier Δ,rfl⟩⟩⟩

abbrev Value (Δ : Bounds) := ∀ g : Child Δ, Fiber g

def embed {Δ} (a : Carrier Δ .unit) : Value Δ :=
  fun g => ⟨observer g.observer a,⟨a,rfl⟩⟩

def modal {Δ} (m : ModExpr) (hm : Entails Δ (.defined m)) (x : Value Δ) : Value Δ :=
  fun g => ⟨g.transition.apply m (x g).val,range_action g hm (x g).property⟩

def op {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (k : Kind)
    (x y : Value Δ) : Value Δ := fun g =>
  let b := (data hn g).branch k
  if b.left then
    ⟨b.sign k (x b.child).val,branch_range hn g k (x b.child).property⟩
  else ⟨b.sign k (y b.child).val,branch_range hn g k (y b.child).property⟩

@[ext] theorem value_ext {Δ} {x y : Value Δ}
    (h : ∀ g, (x g).val = (y g).val) : x = y :=
  funext fun g => Subtype.ext (h g)

@[simp] theorem modal_val {Δ} (m : ModExpr) (hm : Entails Δ (.defined m))
    (x : Value Δ) (g : Child Δ) :
    (modal m hm x g).val = g.transition.apply m (x g).val := rfl

theorem op_val {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (k : Kind)
    (x y : Value Δ) (g : Child Δ) :
    (op hn k x y g).val =
      if ((data hn g).branch k).left then
        leftSign k (x ((data hn g).branch k).child).val
      else (y ((data hn g).branch k).child).val := by
  simp only [op]
  split <;> simp_all [Branch.sign]

theorem pair_absorb {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (k : Kind)
    (hk : k = .prod ∨ k = .sum) (m : ModExpr) (hm : Entails Δ (.defined m))
    (x y : Value Δ) :
    modal m hm (op hn k (modal m hm x) (modal m hm y)) =
      modal m hm (op hn k x y) := by
  apply value_ext
  intro g
  have hc := (data_coherent hn g).pair k hk m hm
  have hs (v : Bool) : leftSign k v = v := by
    rcases hk with rfl | rfl <;> rfl
  simp only [modal_val, op_val, hs]
  split
  · exact hc _ (x ((data hn g).branch k).child).property
  · exact hc _ (y ((data hn g).branch k).child).property

theorem fn_future {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (m n : ModExpr) (hm : Entails Δ (.defined m)) (hn' : Entails Δ (.defined n))
    (h : Submode Δ m (.compose n .top)) (x y : Value Δ) :
    modal m hm (op hn .fn x y) ≤ modal n hn' (op hn .fn x y) := by
  intro g
  have hc := (data_coherent hn g).fn m n h
  change g.transition.apply m (op hn .fn x y g).val ≤
    g.transition.apply n (op hn .fn x y g).val
  simp only [op]
  split
  · exact hc _ (x ((data hn g).branch .fn).child).property
  · exact hc _ (y ((data hn g).branch .fn).child).property

@[simp] theorem sup_val {Δ} (x y : Value Δ) (g : Child Δ) :
    ((x ⊔ y) g).val = ((x g).val || (y g).val) := by
  change (max (x g) (y g)).val = _
  simp only [max_def]
  split
  · rename_i h
    change (x g).val ≤ (y g).val at h
    cases hx : (x g).val <;> cases hy : (y g).val <;> simp_all [Bool.le_iff_imp]
  · rename_i h
    change ¬ (x g).val ≤ (y g).val at h
    cases hx : (x g).val <;> cases hy : (y g).val <;> simp_all [Bool.le_iff_imp]

@[simp] theorem inf_val {Δ} (x y : Value Δ) (g : Child Δ) :
    ((x ⊓ y) g).val = ((x g).val && (y g).val) := by
  change (min (x g) (y g)).val = _
  simp only [min_def]
  split
  · rename_i h
    change (x g).val ≤ (y g).val at h
    cases hx : (x g).val <;> cases hy : (y g).val <;> simp_all [Bool.le_iff_imp]
  · rename_i h
    change ¬ (x g).val ≤ (y g).val at h
    cases hx : (x g).val <;> cases hy : (y g).val <;> simp_all [Bool.le_iff_imp]

theorem modal_mono {Δ} (m : ModExpr) (hm : Entails Δ (.defined m)) :
    Monotone (modal m hm) := fun _ _ h g => g.transition.monotone m hm (h g)

theorem modal_submode {Δ} (m n : ModExpr)
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (h : Submode Δ m n) (x : Value Δ) : modal m hm x ≤ modal n hn x :=
  fun g => g.transition.submode m n h (x g).val

theorem modal_epsilon {Δ} (hε : Entails Δ (.defined .epsilon)) (x : Value Δ) :
    modal .epsilon hε x = x := by
  apply value_ext
  exact fun g => g.transition.epsilon _

theorem modal_compose {Δ} (m n : ModExpr)
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (hmn : Entails Δ (.defined (.compose m n))) (x : Value Δ) :
    modal (.compose m n) hmn x = modal n hn (modal m hm x) := by
  apply value_ext
  exact fun g => g.transition.compose m n hm hn _

theorem modal_sup {Δ} (m : ModExpr) (hm : Entails Δ (.defined m)) (x y : Value Δ) :
    modal m hm (x ⊔ y) = modal m hm x ⊔ modal m hm y := by
  apply value_ext
  intro g
  simp only [modal_val, sup_val]
  exact g.transition.modal_join hm _ _

theorem modal_inf {Δ} (m : ModExpr) (hm : Entails Δ (.defined m)) (x y : Value Δ) :
    modal m hm (x ⊓ y) = modal m hm x ⊓ modal m hm y := by
  apply value_ext
  intro g
  simp only [modal_val, inf_val]
  exact g.transition.modal_meet hm _ _

theorem pair_mono {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (k : Kind)
    (hk : k = .prod ∨ k = .sum) {x y u v : Value Δ} (hxu : x ≤ u) (hyv : y ≤ v) :
    op hn k x y ≤ op hn k u v := by
  intro g
  change (op hn k x y g).val ≤ (op hn k u v g).val
  have hs (b : Bool) : leftSign k b = b := by rcases hk with rfl | rfl <;> rfl
  simp only [op_val, hs]
  split
  · exact hxu _
  · exact hyv _

theorem fn_mono {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    {x y u v : Value Δ} (hux : u ≤ x) (hyv : y ≤ v) :
    op hn .fn x y ≤ op hn .fn u v := by
  intro g
  change (op hn .fn x y g).val ≤ (op hn .fn u v g).val
  simp only [op_val, leftSign]
  split
  · have h := hux ((data hn g).branch .fn).child
    change (u _).val ≤ (x _).val at h
    cases hx : (x ((data hn g).branch .fn).child).val <;>
      cases hu : (u ((data hn g).branch .fn).child).val <;> simp_all
  · exact hyv _

theorem embed_le_iff {Δ} (a b : Carrier Δ .unit) :
    embed a ≤ embed b ↔ AlgebraSubtype Δ a.type b.type := by
  constructor
  · intro h
    apply (subtype_iff_boolean_observers a b).mpr
    intro f
    exact h (Child.ofObserver f)
  · intro h g
    exact observer_mono g.observer h

theorem embed_sup {Δ} (a b : Carrier Δ .unit) :
    embed (a.join b) = embed a ⊔ embed b := by
  apply value_ext
  intro g
  rw [sup_val]
  exact observer_join g.observer a b

theorem embed_inf {Δ} (a b : Carrier Δ .unit) :
    embed (a.meet b) = embed a ⊓ embed b := by
  apply value_ext
  intro g
  rw [inf_val]
  exact observer_meet g.observer a b

theorem modal_embed {Δ} (m : ModExpr) (hm : Entails Δ (.defined m))
    (a : Carrier Δ .unit) : modal m hm (embed a) = embed (a.modal m hm) := by
  apply value_ext
  intro g
  have h := g.action m hm a.type ⟨a.shaped,a.defined,a.shape_eq⟩
  rw [booleanValue_carrier g.observer a] at h
  exact h.trans (booleanValue_carrier g.observer (a.modal m hm))

theorem op_embed {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (k : Kind)
    (a b : Carrier Δ .unit) (hab : (k.op a.type b.type).DefinedUnder Δ) :
    op hn k (embed a) (embed b) = embed (represented (representable hn hab)) := by
  apply value_ext
  intro g
  rw [op_val]
  have h := data_represents hn g _ hab
  rw [booleanValue_represented g.observer _ (representable hn hab)] at h
  change _ = observer g.observer (represented (representable hn hab)) at h
  change _ = observer g.observer (represented (representable hn hab))
  rw [← h]
  cases k <;> simp only [Kind.op, Data.value, Branch.value, embed,
    booleanValue_carrier, observer]

def ofType {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (a : CompareTy) (ha : a.DefinedUnder Δ) : Value Δ :=
  embed (represented (representable hn ha))

@[simp] theorem ofType_val {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (a : CompareTy) (ha : a.DefinedUnder Δ) (g : Child Δ) :
    (ofType hn a ha g).val = booleanValue g.observer a :=
  (booleanValue_represented g.observer a (representable hn ha)).symm

theorem ofType_le_iff {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (a b : CompareTy) (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    ofType hn a ha ≤ ofType hn b hb ↔ AlgebraSubtype Δ a b :=
  embed_le_iff _ _

theorem pair_sup {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (k : Kind)
    (hk : k = .prod ∨ k = .sum) (x y u v : Value Δ) :
    op hn k (x ⊔ u) (y ⊔ v) = op hn k x y ⊔ op hn k u v := by
  apply value_ext
  intro g
  have hs (b : Bool) : leftSign k b = b := by rcases hk with rfl | rfl <;> rfl
  simp only [sup_val, op_val, hs]
  split <;> simp_all

theorem pair_inf {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (k : Kind)
    (hk : k = .prod ∨ k = .sum) (x y u v : Value Δ) :
    op hn k (x ⊓ u) (y ⊓ v) = op hn k x y ⊓ op hn k u v := by
  apply value_ext
  intro g
  have hs (b : Bool) : leftSign k b = b := by rcases hk with rfl | rfl <;> rfl
  simp only [inf_val, op_val, hs]
  split <;> simp_all

theorem fn_sup {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (x y u v : Value Δ) :
    op hn .fn (x ⊓ u) (y ⊔ v) = op hn .fn x y ⊔ op hn .fn u v := by
  apply value_ext
  intro g
  simp only [sup_val, inf_val, op_val, leftSign]
  split <;> simp_all

theorem fn_inf {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (x y u v : Value Δ) :
    op hn .fn (x ⊔ u) (y ⊓ v) = op hn .fn x y ⊓ op hn .fn u v := by
  apply value_ext
  intro g
  simp only [sup_val, inf_val, op_val, leftSign]
  split <;> simp_all

theorem modal_join_mode {Δ} (m n : ModExpr)
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (hmn : Entails Δ (.defined (.join m n))) (x : Value Δ) :
    modal (.join m n) hmn x = modal m hm x ⊔ modal n hn x := by
  apply value_ext
  intro g
  simp only [modal_val, sup_val]
  exact g.transition.join m n hm hn _

theorem modal_meet_mode {Δ} (m n : ModExpr)
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (hmn : Entails Δ (.defined (.meet m n))) (x : Value Δ) :
    modal (.meet m n) hmn x = modal m hm x ⊓ modal n hn x := by
  apply value_ext
  intro g
  simp only [modal_val, inf_val]
  exact g.transition.meet m n hm hn _

theorem modal_clamp {Δ} (m : ModExpr) (hm : Entails Δ (.defined m))
    {b a u : Value Δ} (hba : b ≤ a) (hau : a ≤ u) :
    modal m hm a = (a ⊔ modal m hm b) ⊓ modal m hm u := by
  apply value_ext
  intro g
  simp only [modal_val, inf_val, sup_val]
  exact g.transition.clamp hm (hba g) (hau g)

theorem fn_step {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (m n : ModExpr) (hm : Entails Δ (.defined m)) (hn' : Entails Δ (.defined n))
    (h : Submode Δ m (.compose n .top)) {x y u v : Value Δ}
    (hux : u ≤ x) (hyv : y ≤ v) :
    modal m hm (op hn .fn x y) ≤ modal n hn' (op hn .fn u v) :=
  (modal_mono m hm (fn_mono hn hux hyv)).trans (fn_future hn m n hm hn' h u v)

end
end ModalityInference.ComparisonObserverRangeProduct
