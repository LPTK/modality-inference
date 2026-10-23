import ModalityInference.Proofs.ComparisonObserverHeadCuts
import ModalityInference.Proofs.ComparisonObserverRangeProduct

/-! Optional shadows live in the ranges of genuine observers. Each coordinate
is attained by a defined cut witness, which supplies the exact mixed-row
inequalities without choosing a finite term for the entire cut. -/
namespace ModalityInference.ComparisonObserverShadowRows

open ComparisonAlgebra ComparisonStructuralLattice ComparisonStructuralObservers
  ComparisonObserverGluing ComparisonObserverHeadCuts ComparisonObserverRangeProduct
  ComparisonObserverRepresentatives

noncomputable section

variable {Δ : Bounds}

private theorem lower_range {p : CompareTy} (hp : LowerInhabited (Δ := Δ) (shape := .unit) p)
    (g : Child Δ) : g.Range (lowerBit p g.observer) := by
  obtain ⟨a,_,ha⟩ := lower_attained hp g.observer
  exact ⟨a,ha.symm⟩

private theorem upper_range {p : CompareTy} (hp : UpperInhabited (Δ := Δ) (shape := .unit) p)
    (g : Child Δ) : g.Range (upperBit p g.observer) := by
  obtain ⟨a,_,ha⟩ := upper_attained hp g.observer
  exact ⟨a,ha.symm⟩

def lower {p : CompareTy} (hp : LowerInhabited (Δ := Δ) (shape := .unit) p) : ComparisonObserverRangeProduct.Value Δ :=
  fun g => ⟨lowerBit p g.observer,lower_range hp g⟩

def upper {p : CompareTy} (hp : UpperInhabited (Δ := Δ) (shape := .unit) p) : ComparisonObserverRangeProduct.Value Δ :=
  fun g => ⟨upperBit p g.observer,upper_range hp g⟩

@[simp] theorem lower_val {p : CompareTy} (hp : LowerInhabited (Δ := Δ) (shape := .unit) p)
    (g : Child Δ) : (lower hp g).val = lowerBit p g.observer := rfl

@[simp] theorem upper_val {p : CompareTy} (hp : UpperInhabited (Δ := Δ) (shape := .unit) p)
    (g : Child Δ) : (upper hp g).val = upperBit p g.observer := rfl

theorem consistent {p : CompareTy} (hp : LowerInhabited (Δ := Δ) (shape := .unit) p)
    (hu : UpperInhabited (Δ := Δ) (shape := .unit) p) : lower hp ≤ upper hu :=
  fun g => bits_consistent p g.observer

theorem lower_mono {p q : CompareTy} (hp : LowerInhabited (Δ := Δ) (shape := .unit) p)
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) q) (h : AlgebraSubtype Δ p q) :
    lower hp ≤ lower hq := fun g => lowerBit_mono h g.observer

theorem upper_mono {p q : CompareTy} (hp : UpperInhabited (Δ := Δ) (shape := .unit) p)
    (hq : UpperInhabited (Δ := Δ) (shape := .unit) q) (h : AlgebraSubtype Δ p q) :
    upper hp ≤ upper hq := fun g => upperBit_mono h g.observer

theorem saturation {p q : CompareTy} (hp : UpperInhabited (Δ := Δ) (shape := .unit) p)
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) q) (h : upper hp ≤ lower hq) :
    AlgebraSubtype Δ p q :=
  bits_saturation hp hq (fun f => h (Child.ofObserver f))

theorem lower_defined (a : Carrier Δ .unit) :
    lower (p := a.type) ⟨a,.refl a.shaped⟩ = embed a := by
  apply value_ext
  intro g
  exact lowerBit_defined a g.observer

theorem upper_defined (a : Carrier Δ .unit) :
    upper (p := a.type) ⟨a,.refl a.shaped⟩ = embed a := by
  apply value_ext
  intro g
  exact upperBit_defined a g.observer

theorem lower_modal {p : CompareTy} (hp : LowerInhabited (Δ := Δ) (shape := .unit) p)
    (m : ModExpr) (hm : Entails Δ (.defined m))
    (hr : LowerInhabited (Δ := Δ) (shape := .unit) (.modal p m)) :
    modal m hm (lower hp) ≤ lower hr := by
  intro g
  obtain ⟨a,ha,hv⟩ := lower_attained hp g.observer
  have hb : AlgebraSubtype Δ (a.modal m hm).type (.modal p m) := .congr ha (.refl hm)
  have he : g.transition.apply m (lowerBit p g.observer) = observer g.observer (a.modal m hm) := by
    rw [hv]
    exact congrArg (fun x => (x g).val) (modal_embed m hm a)
  change g.transition.apply m (lowerBit p g.observer) ≤ lowerBit (.modal p m) g.observer
  rw [he]
  exact eval_le_lower (a.modal m hm) hb g.observer

theorem upper_modal {p : CompareTy} (hp : UpperInhabited (Δ := Δ) (shape := .unit) p)
    (m : ModExpr) (hm : Entails Δ (.defined m))
    (hr : UpperInhabited (Δ := Δ) (shape := .unit) (.modal p m)) :
    upper hr ≤ modal m hm (upper hp) := by
  intro g
  obtain ⟨a,ha,hv⟩ := upper_attained hp g.observer
  have hb : AlgebraSubtype Δ (.modal p m) (a.modal m hm).type := .congr ha (.refl hm)
  have he : g.transition.apply m (upperBit p g.observer) = observer g.observer (a.modal m hm) := by
    rw [hv]
    exact congrArg (fun x => (x g).val) (modal_embed m hm a)
  change upperBit (.modal p m) g.observer ≤ g.transition.apply m (upperBit p g.observer)
  rw [he]
  exact upper_le_eval (a.modal m hm) hb g.observer

private theorem op_defined (k : Kind) (a b : Carrier Δ .unit) :
    (k.op a.type b.type).DefinedUnder Δ := by
  cases k <;> exact CompareTy.definedUnder_prod_iff.mpr ⟨a.defined,b.defined⟩

/-- A lower row remains sound against all defined rows. The premise is the
original comparison for actual defined operands, not a shadow approximation. -/
theorem lower_row (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (k : Kind)
    (m : ModExpr) (hm : Entails Δ (.defined m)) {p q r : CompareTy}
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) p)
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) q)
    (hr : LowerInhabited (Δ := Δ) (shape := .unit) r)
    (hrow : ∀ a b : Carrier Δ .unit, AlgebraSubtype Δ a.type p → AlgebraSubtype Δ b.type q →
      AlgebraSubtype Δ (.modal (k.op a.type b.type) m) r) :
    modal m hm (op hn k (lower hp) (lower hq)) ≤ lower hr := by
  intro g
  let branch := (data hn g).branch k
  obtain ⟨a,ha,hva⟩ := lower_attained hp branch.child.observer
  obtain ⟨b,hb,hvb⟩ := lower_attained hq branch.child.observer
  let c := represented (representable hn (op_defined k a b))
  have hv : (op hn k (lower hp) (lower hq) g).val = (embed c g).val := by
    calc
      _ = (op hn k (embed a) (embed b) g).val := by
        simp only [op_val,lower_val,embed]
        change (if branch.left then leftSign k (lowerBit p branch.child.observer)
          else lowerBit q branch.child.observer) = _
        rw [hva,hvb]
        rfl
      _ = _ := congrArg (fun x => (x g).val) (op_embed hn k a b (op_defined k a b))
  have he : (modal m hm (op hn k (lower hp) (lower hq)) g).val =
      (embed (c.modal m hm) g).val := by
    rw [modal_val,hv]
    exact congrArg (fun x => (x g).val) (modal_embed m hm c)
  change (modal m hm (op hn k (lower hp) (lower hq)) g).val ≤ lowerBit r g.observer
  rw [he]
  exact eval_le_lower (c.modal m hm) (hrow a b ha hb) g.observer

/-- The dual upper row has the reversed outer inequality. -/
theorem upper_row (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (k : Kind)
    (m : ModExpr) (hm : Entails Δ (.defined m)) {p q r : CompareTy}
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) p)
    (hq : UpperInhabited (Δ := Δ) (shape := .unit) q)
    (hr : UpperInhabited (Δ := Δ) (shape := .unit) r)
    (hrow : ∀ a b : Carrier Δ .unit, AlgebraSubtype Δ p a.type → AlgebraSubtype Δ q b.type →
      AlgebraSubtype Δ r (.modal (k.op a.type b.type) m)) :
    upper hr ≤ modal m hm (op hn k (upper hp) (upper hq)) := by
  intro g
  let branch := (data hn g).branch k
  obtain ⟨a,ha,hva⟩ := upper_attained hp branch.child.observer
  obtain ⟨b,hb,hvb⟩ := upper_attained hq branch.child.observer
  let c := represented (representable hn (op_defined k a b))
  have hv : (op hn k (upper hp) (upper hq) g).val = (embed c g).val := by
    calc
      _ = (op hn k (embed a) (embed b) g).val := by
        simp only [op_val,upper_val,embed]
        change (if branch.left then leftSign k (upperBit p branch.child.observer)
          else upperBit q branch.child.observer) = _
        rw [hva,hvb]
        rfl
      _ = _ := congrArg (fun x => (x g).val) (op_embed hn k a b (op_defined k a b))
  have he : (modal m hm (op hn k (upper hp) (upper hq)) g).val =
      (embed (c.modal m hm) g).val := by
    rw [modal_val,hv]
    exact congrArg (fun x => (x g).val) (modal_embed m hm c)
  change upperBit r g.observer ≤ (modal m hm (op hn k (upper hp) (upper hq)) g).val
  rw [he]
  exact upper_le_eval (c.modal m hm) (hrow a b ha hb) g.observer

private theorem pair_lower_bound (k : Kind) (hk : k = .prod ∨ k = .sum)
    (m : ModExpr) (hm : Entails Δ (.defined m)) {a b p q : CompareTy}
    (ha : AlgebraSubtype Δ a (.modal p m)) (hb : AlgebraSubtype Δ b (.modal q m)) :
    AlgebraSubtype Δ (.modal (k.op a b) m) (.modal (k.op p q) m) := by
  have hpa := ComparisonStructuralFamily.modal_idem (a := p) ha.wellShaped_right
    (GuardedMode.ofDefined m hm)
  have hqb := ComparisonStructuralFamily.modal_idem (a := q) hb.wellShaped_right
    (GuardedMode.ofDefined m hm)
  have h₁ := (ha.congr (Submode.refl hm)).trans hpa.1
  have h₂ := (hb.congr (Submode.refl hm)).trans hqb.1
  rcases hk with rfl | rfl
  · exact .prod h₁ h₂
  · exact .sum h₁ h₂

private theorem pair_upper_bound (k : Kind) (hk : k = .prod ∨ k = .sum)
    (m : ModExpr) (hm : Entails Δ (.defined m)) {a b p q : CompareTy}
    (ha : AlgebraSubtype Δ (.modal p m) a) (hb : AlgebraSubtype Δ (.modal q m) b) :
    AlgebraSubtype Δ (.modal (k.op p q) m) (.modal (k.op a b) m) := by
  have hpa := ComparisonStructuralFamily.modal_idem (a := p) ha.wellShaped_left
    (GuardedMode.ofDefined m hm)
  have hqb := ComparisonStructuralFamily.modal_idem (a := q) hb.wellShaped_left
    (GuardedMode.ofDefined m hm)
  have h₁ := hpa.2.trans (ha.congr (Submode.refl hm))
  have h₂ := hqb.2.trans (hb.congr (Submode.refl hm))
  rcases hk with rfl | rfl
  · exact .prod h₁ h₂
  · exact .sum h₁ h₂

theorem lower_pair_inhabited (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (k : Kind) (hk : k = .prod ∨ k = .sum) (m : ModExpr) (hm : Entails Δ (.defined m))
    {p q : CompareTy} (hp : LowerInhabited (Δ := Δ) (shape := .unit) (.modal p m))
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) (.modal q m)) :
    LowerInhabited (Δ := Δ) (shape := .unit) (.modal (k.op p q) m) := by
  obtain ⟨a,ha⟩ := hp
  obtain ⟨b,hb⟩ := hq
  exact ⟨(represented (representable hn (op_defined k a b))).modal m hm,
    pair_lower_bound k hk m hm ha hb⟩

theorem upper_pair_inhabited (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (k : Kind) (hk : k = .prod ∨ k = .sum) (m : ModExpr) (hm : Entails Δ (.defined m))
    {p q : CompareTy} (hp : UpperInhabited (Δ := Δ) (shape := .unit) (.modal p m))
    (hq : UpperInhabited (Δ := Δ) (shape := .unit) (.modal q m)) :
    UpperInhabited (Δ := Δ) (shape := .unit) (.modal (k.op p q) m) := by
  obtain ⟨a,ha⟩ := hp
  obtain ⟨b,hb⟩ := hq
  exact ⟨(represented (representable hn (op_defined k a b))).modal m hm,
    pair_upper_bound k hk m hm ha hb⟩

/-- Exact inherited product/sum row inequalities use the acted child shadows
and the defined operation `x,y ↦ (op x y)@m`. -/
theorem lower_pair (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (k : Kind) (hk : k = .prod ∨ k = .sum) (m : ModExpr) (hm : Entails Δ (.defined m))
    {p q : CompareTy} (hp : LowerInhabited (Δ := Δ) (shape := .unit) (.modal p m))
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) (.modal q m))
    (hr : LowerInhabited (Δ := Δ) (shape := .unit) (.modal (k.op p q) m)) :
    modal m hm (op hn k (lower hp) (lower hq)) ≤ lower hr :=
  lower_row hn k m hm hp hq hr (fun _ _ ha hb => pair_lower_bound k hk m hm ha hb)

theorem upper_pair (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (k : Kind) (hk : k = .prod ∨ k = .sum) (m : ModExpr) (hm : Entails Δ (.defined m))
    {p q : CompareTy} (hp : UpperInhabited (Δ := Δ) (shape := .unit) (.modal p m))
    (hq : UpperInhabited (Δ := Δ) (shape := .unit) (.modal q m))
    (hr : UpperInhabited (Δ := Δ) (shape := .unit) (.modal (k.op p q) m)) :
    upper hr ≤ modal m hm (op hn k (upper hp) (upper hq)) :=
  upper_row hn k m hm hp hq hr (fun _ _ ha hb => pair_upper_bound k hk m hm ha hb)

theorem lower_fn_inhabited (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (m : ModExpr) (hm : Entails Δ (.defined m)) {p q : CompareTy}
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) p)
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) q) :
    LowerInhabited (Δ := Δ) (shape := .unit) (.modal (.fn p q) m) := by
  obtain ⟨a,ha⟩ := hp
  obtain ⟨b,hb⟩ := hq
  exact ⟨(represented (representable hn (op_defined .fn a b))).modal m hm,
    (ComparisonDefinedCovers.fn_congr ha hb).congr (.refl hm)⟩

theorem upper_fn_inhabited (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (m : ModExpr) (hm : Entails Δ (.defined m)) {p q : CompareTy}
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) p)
    (hq : UpperInhabited (Δ := Δ) (shape := .unit) q) :
    UpperInhabited (Δ := Δ) (shape := .unit) (.modal (.fn p q) m) := by
  obtain ⟨a,ha⟩ := hp
  obtain ⟨b,hb⟩ := hq
  exact ⟨(represented (representable hn (op_defined .fn a b))).modal m hm,
    (ComparisonDefinedCovers.fn_congr ha hb).congr (.refl hm)⟩

/-- Function rows use unacted operands and exchange lower/upper domain cuts. -/
theorem lower_fn (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (m : ModExpr) (hm : Entails Δ (.defined m)) {p q : CompareTy}
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) p)
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) q)
    (hr : LowerInhabited (Δ := Δ) (shape := .unit) (.modal (.fn p q) m)) :
    modal m hm (op hn .fn (upper hp) (lower hq)) ≤ lower hr := by
  intro g
  let branch := (data hn g).branch .fn
  obtain ⟨a,ha,hva⟩ := upper_attained hp branch.child.observer
  obtain ⟨b,hb,hvb⟩ := lower_attained hq branch.child.observer
  let c := represented (representable hn (op_defined .fn a b))
  have hv : (op hn .fn (upper hp) (lower hq) g).val = (embed c g).val := by
    calc
      _ = (op hn .fn (embed a) (embed b) g).val := by
        simp only [op_val,upper_val,lower_val,embed]
        change (if branch.left then leftSign .fn (upperBit p branch.child.observer)
          else lowerBit q branch.child.observer) = _
        rw [hva,hvb]
        rfl
      _ = _ := congrArg (fun x => (x g).val) (op_embed hn .fn a b (op_defined .fn a b))
  have he : (modal m hm (op hn .fn (upper hp) (lower hq)) g).val =
      (embed (c.modal m hm) g).val := by
    rw [modal_val,hv]
    exact congrArg (fun x => (x g).val) (modal_embed m hm c)
  change (modal m hm (op hn .fn (upper hp) (lower hq)) g).val ≤
    lowerBit (.modal (.fn p q) m) g.observer
  rw [he]
  exact eval_le_lower (c.modal m hm) ((ComparisonDefinedCovers.fn_congr ha hb).congr (.refl hm)) g.observer

theorem upper_fn (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (m : ModExpr) (hm : Entails Δ (.defined m)) {p q : CompareTy}
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) p)
    (hq : UpperInhabited (Δ := Δ) (shape := .unit) q)
    (hr : UpperInhabited (Δ := Δ) (shape := .unit) (.modal (.fn p q) m)) :
    upper hr ≤ modal m hm (op hn .fn (lower hp) (upper hq)) := by
  intro g
  let branch := (data hn g).branch .fn
  obtain ⟨a,ha,hva⟩ := lower_attained hp branch.child.observer
  obtain ⟨b,hb,hvb⟩ := upper_attained hq branch.child.observer
  let c := represented (representable hn (op_defined .fn a b))
  have hv : (op hn .fn (lower hp) (upper hq) g).val = (embed c g).val := by
    calc
      _ = (op hn .fn (embed a) (embed b) g).val := by
        simp only [op_val,upper_val,lower_val,embed]
        change (if branch.left then leftSign .fn (lowerBit p branch.child.observer)
          else upperBit q branch.child.observer) = _
        rw [hva,hvb]
        rfl
      _ = _ := congrArg (fun x => (x g).val) (op_embed hn .fn a b (op_defined .fn a b))
  have he : (modal m hm (op hn .fn (lower hp) (upper hq)) g).val =
      (embed (c.modal m hm) g).val := by
    rw [modal_val,hv]
    exact congrArg (fun x => (x g).val) (modal_embed m hm c)
  change upperBit (.modal (.fn p q) m) g.observer ≤
    (modal m hm (op hn .fn (lower hp) (upper hq)) g).val
  rw [he]
  exact upper_le_eval (c.modal m hm) ((ComparisonDefinedCovers.fn_congr ha hb).congr (.refl hm)) g.observer

end
end ModalityInference.ComparisonObserverShadowRows
