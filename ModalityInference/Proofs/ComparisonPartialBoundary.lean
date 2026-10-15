import ModalityInference.Proofs.ComparisonBoundDefinedness

/-!
# Definedness at public comparison boundaries

A public type comparable with a defined internal type is itself defined when
the declared type bounds have defined endpoints. A signed path interpretation
separates undefined public annotations from the defined comparison algebra.
-/

namespace ModalityInference.ComparisonPartialBoundary

abbrev Point := Bool × Bool
abbrev Carrier := List Bool → Point

def middle : Carrier := fun _ => (false, true)
def extreme (e : Bool) : Carrier := fun _ => (e, e)
def dual (x : Carrier) : Carrier := fun p => (!(x p).2, !(x p).1)
def join (x y : Carrier) : Carrier := fun p => ((x p).1 || (y p).1, (x p).2 || (y p).2)
def meet (x y : Carrier) : Carrier := fun p => ((x p).1 && (y p).1, (x p).2 && (y p).2)
def branch (x y : Carrier) : Carrier
  | [] => (false, true)
  | false :: p => x p
  | true :: p => y p

def Le (x y : Carrier) : Prop :=
  ∀ p, ((x p).1 = true → (y p).1 = true) ∧ ((x p).2 = true → (y p).2 = true)

theorem le_refl (x : Carrier) : Le x x := by simp [Le]
theorem le_trans {x y z : Carrier} (hxy : Le x y) (hyz : Le y z) : Le x z := by
  intro p
  exact ⟨fun h => (hyz p).1 ((hxy p).1 h), fun h => (hyz p).2 ((hxy p).2 h)⟩
theorem le_antisymm {x y : Carrier} (hxy : Le x y) (hyx : Le y x) : x = y := by
  funext p
  have hx := hxy p
  have hy := hyx p
  cases he : x p with
  | mk a b =>
    cases hf : y p with
    | mk c d =>
      cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem dual_dual (x : Carrier) : dual (dual x) = x := by
  funext p
  simp [dual]
theorem dual_middle : dual middle = middle := by rfl
theorem dual_le {x y : Carrier} (h : Le x y) : Le (dual y) (dual x) := by
  intro p
  have hp := h p
  cases he : x p with
  | mk a b =>
    cases hf : y p with
    | mk c d =>
      cases a <;> cases b <;> cases c <;> cases d <;> simp_all [dual]

theorem branch_mono {a b c d : Carrier} (hac : Le a c) (hbd : Le b d) :
    Le (branch a b) (branch c d) := by
  intro p
  cases p with
  | nil => exact ⟨id, id⟩
  | cons h p => cases h <;> first | exact hac p | exact hbd p

theorem branch_middle : branch middle middle = middle := by
  funext p
  cases p with
  | nil => rfl
  | cons h p => cases h <;> rfl

theorem branch_dual (a b : Carrier) : dual (branch a b) = branch (dual a) (dual b) := by
  funext p
  cases p with
  | nil => rfl
  | cons h p => cases h <;> rfl

theorem join_left (x y : Carrier) : Le x (join x y) := by
  intro p
  exact ⟨fun h => by simp [join, h], fun h => by simp [join, h]⟩
theorem join_right (x y : Carrier) : Le y (join x y) := by
  intro p
  exact ⟨fun h => by simp [join, h], fun h => by simp [join, h]⟩
theorem join_least {x y z : Carrier} (hx : Le x z) (hy : Le y z) : Le (join x y) z := by
  intro p
  simpa [join, Bool.or_eq_true, or_imp] using And.intro
    (And.intro (hx p).1 (hy p).1) (And.intro (hx p).2 (hy p).2)
theorem meet_left (x y : Carrier) : Le (meet x y) x := by
  simp only [Le, meet, Bool.and_eq_true, and_imp]
  exact fun _ => ⟨fun h _ => h, fun h _ => h⟩
theorem meet_right (x y : Carrier) : Le (meet x y) y := by simp [Le, meet]
theorem meet_greatest {x y z : Carrier} (hx : Le x y) (hy : Le x z) : Le x (meet y z) := by
  intro p
  exact ⟨fun h => by simp [meet, (hx p).1 h, (hy p).1 h],
    fun h => by simp [meet, (hx p).2 h, (hy p).2 h]⟩

def scalar (η : ModVar → Mode) (e : Bool) (m : ModExpr) (x : Carrier) : Carrier :=
  if (m.eval (some ∘ η)).isSome then x else extreme e

theorem scalar_defined {η : ModVar → Mode} {e : Bool} {m : ModExpr} (x : Carrier)
    (h : m.WellFormed η) : scalar η e m x = x := by
  simp only [scalar, ModExpr.WellFormed] at *
  simp [h]

theorem scalar_compose (η : ModVar → Mode) (e : Bool) (m n : ModExpr) (x : Carrier) :
    scalar η e (.compose m n) x = scalar η e n (scalar η e m x) := by
  cases hm : m.eval (some ∘ η) <;> cases hn : n.eval (some ∘ η) <;>
    simp [scalar, ModExpr.eval, hm, hn]

theorem scalar_mono {Δ : Bounds} {η : ModVar → Mode} {e : Bool} {m n : ModExpr}
    {x y : Carrier} (hη : ModeModels Δ η) (hmn : Submode Δ m n) (hxy : Le x y) :
    Le (scalar η e m x) (scalar η e n y) := by
  rw [scalar_defined _ (hmn.defined.1 η hη), scalar_defined _ (hmn.defined.2 η hη)]
  exact hxy

def interpret (η : ModVar → Mode) (e : Bool) : CompareTy → Carrier
  | .var _ | .unit | .credit => middle
  | .prod a b | .sum a b => branch (interpret η e a) (interpret η e b)
  | .fn a b => branch (dual (interpret η e a)) (interpret η e b)
  | .modal a m => scalar η e m (interpret η e a)
  | .join a b => join (interpret η e a) (interpret η e b)
  | .meet a b => meet (interpret η e a) (interpret η e b)

theorem interpret_defined {Δ : Bounds} {η : ModVar → Mode} (e : Bool)
    (hη : ModeModels Δ η) {a : CompareTy} (h : a.DefinedUnder Δ) :
    interpret η e a = middle := by
  induction a with
  | var | unit | credit => rfl
  | prod a b iha ihb =>
    have hh := CompareTy.definedUnder_prod_iff.mp h
    rw [interpret, iha hh.1, ihb hh.2, branch_middle]
  | sum a b iha ihb =>
    have hh := CompareTy.definedUnder_sum_iff.mp h
    rw [interpret, iha hh.1, ihb hh.2, branch_middle]
  | fn a b iha ihb =>
    have hh := CompareTy.definedUnder_fn_iff.mp h
    rw [interpret, iha hh.1, ihb hh.2, dual_middle, branch_middle]
  | modal a m ih =>
    have hh := CompareTy.definedUnder_modal_iff.mp h
    rw [interpret, scalar_defined _ (hh.2 η hη), ih hh.1]
  | join a b iha ihb =>
    have hh := CompareTy.definedUnder_join_iff.mp h
    rw [interpret, iha hh.1, ihb hh.2]
    rfl
  | meet a b iha ihb =>
    have hh := CompareTy.definedUnder_meet_iff.mp h
    rw [interpret, iha hh.1, ihb hh.2]
    rfl


theorem scalar_branch_mono (η : ModVar → Mode) (e : Bool) (m : ModExpr)
    {a b c d : Carrier} (hac : Le (scalar η e m a) (scalar η e m c))
    (hbd : Le (scalar η e m b) (scalar η e m d)) :
    Le (scalar η e m (branch a b)) (scalar η e m (branch c d)) := by
  cases hm : (m.eval (some ∘ η)).isSome <;>
    simp only [scalar, hm, Bool.false_eq_true, if_false, if_true] at hac hbd ⊢
  · exact le_refl _
  · exact branch_mono hac hbd

theorem scalar_fn_mono {Δ : Bounds} {η : ModVar → Mode} (e : Bool)
    (hη : ModeModels Δ η) {m n : ModExpr} {a b c d : Carrier}
    (hca : Le c a) (hbd : Le b d) (hm : Submode Δ m (.compose n .top)) :
    Le (scalar η e m (branch (dual a) b)) (scalar η e n (branch (dual c) d)) := by
  rw [scalar_defined _ (hm.defined.1 η hη),
    scalar_defined _ ((Entails.defined_compose_iff.mp hm.defined.2).1 η hη)]
  exact branch_mono (dual_le hca) hbd

theorem shaped_sound {Δ : Bounds} {η : ModVar → Mode} (e : Bool)
    (hη : ModeModels Δ η) (hΔ : Δ.TypeBoundsDefined) {a b : CompareTy}
    (h : ShapedSubtype Δ a b) : Le (interpret η e a) (interpret η e b) := by
  induction h with
  | refl => exact le_refl _
  | trans _ _ ih₁ ih₂ => exact le_trans ih₁ ih₂
  | bound hb =>
    have hd := hΔ _ _ hb
    rw [interpret_defined e hη ((CompareTy.definedUnder_ofTy _ _).mpr hd.1),
      interpret_defined e hη ((CompareTy.definedUnder_ofTy _ _).mpr hd.2)]
    exact le_refl _
  | identity | identityRev => exact le_refl _
  | compose | composeRev =>
    simp only [interpret, scalar_compose]
    exact le_refl _
  | congr _ hm ih => exact scalar_mono hη hm ih
  | prod _ _ ih₁ ih₂ | sum _ _ ih₁ ih₂ => exact scalar_branch_mono _ _ _ ih₁ ih₂
  | fn _ _ hm ih₁ ih₂ => exact scalar_fn_mono e hη ih₁ ih₂ hm
  | joinLeft => exact join_left _ _
  | joinRight => exact join_right _ _
  | joinLeast _ _ ih₁ ih₂ => exact join_least ih₁ ih₂
  | meetLeft => exact meet_left _ _
  | meetRight => exact meet_right _ _
  | meetGreatest _ _ ih₁ ih₂ => exact meet_greatest ih₁ ih₂


@[simp] theorem join_middle : join middle middle = middle := rfl
@[simp] theorem meet_middle : meet middle middle = middle := rfl

theorem equation_sound {Δ : Bounds} {η : ModVar → Mode} (e : Bool)
    (hη : ModeModels Δ η) {a b : CompareTy} (h : ComparisonAlgebra.Equation Δ a b) :
    interpret η e a = interpret η e b := by
  cases h with
  | distrib p hab hac =>
    cases p <;> simp [ComparisonAlgebra.typeOp, interpret,
      interpret_defined e hη hab.2.1, interpret_defined e hη hab.2.2,
      interpret_defined e hη hac.2.2]
  | modal p hab hm =>
    cases p <;> simp [ComparisonAlgebra.typeOp, interpret,
      interpret_defined e hη hab.2.1, interpret_defined e hη hab.2.2,
      scalar_defined _ (hm η hη)]
  | scalar p hs ha hm hn =>
    rename_i a m n
    have ht : (ComparisonAlgebra.modeOp p m n).WellFormed η := by
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hm η hη)
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hn η hη)
      cases p <;> simp [ComparisonAlgebra.modeOp, ModExpr.WellFormed, ModExpr.eval, ha, hb]
    cases p <;> simp [interpret, ComparisonAlgebra.typeOp, interpret_defined e hη ha,
      scalar_defined _ ht, scalar_defined _ (hm η hη), scalar_defined _ (hn η hη)]
  | prod p hac hbd | sum p hac hbd | fn p hac hbd =>
    cases p <;> simp [ComparisonAlgebra.typeOp, interpret,
      interpret_defined e hη hac.2.1, interpret_defined e hη hac.2.2,
      interpret_defined e hη hbd.2.1, interpret_defined e hη hbd.2.2,
      branch_middle, dual_middle]

theorem algebra_sound {Δ : Bounds} {η : ModVar → Mode} (e : Bool)
    (hη : ModeModels Δ η) (hΔ : Δ.TypeBoundsDefined) {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) : Le (interpret η e a) (interpret η e b) := by
  induction h with
  | shaped h => exact shaped_sound e hη hΔ h
  | trans _ _ ih₁ ih₂ => exact le_trans ih₁ ih₂
  | equation h => rw [equation_sound e hη h]; exact le_refl _
  | equationRev h => rw [equation_sound e hη h]; exact le_refl _
  | congr _ hm ih => exact scalar_mono hη hm ih
  | prod _ _ ih₁ ih₂ | sum _ _ ih₁ ih₂ => exact scalar_branch_mono _ _ _ ih₁ ih₂
  | fn _ _ hm ih₁ ih₂ => exact scalar_fn_mono e hη ih₁ ih₂ hm
  | joinLeast _ _ ih₁ ih₂ => exact join_least ih₁ ih₂
  | meetGreatest _ _ ih₁ ih₂ => exact meet_greatest ih₁ ih₂
  | clamp hab hat hm | clampRev hab hat hm =>
    simp only [interpret, interpret_defined e hη hab.2.1, interpret_defined e hη hab.2.2,
      interpret_defined e hη hat.2.2, scalar_defined _ (hm η hη), join_middle, meet_middle]
    exact le_refl _


theorem branch_eq_middle {a b : Carrier} (h : branch a b = middle) : a = middle ∧ b = middle := by
  constructor
  · funext p
    exact congrFun h (false :: p)
  · funext p
    exact congrFun h (true :: p)

theorem extreme_ne_middle (e : Bool) : extreme e ≠ middle := by
  intro h
  have hh := congrFun h []
  cases e <;> simp [extreme, middle] at hh

theorem interpret_public_dual (η : ModVar → Mode) (e : Bool) (a : Ty) :
    interpret η (!e) (.ofTy a) = dual (interpret η e (.ofTy a)) := by
  induction a with
  | var | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb =>
    simp only [CompareTy.ofTy, interpret, iha, ihb, branch_dual]
  | fn a b iha ihb =>
    simp only [CompareTy.ofTy, interpret, iha, ihb, branch_dual]
  | modal a m ih =>
    simp only [CompareTy.ofTy, interpret, scalar]
    split
    · exact ih
    · rfl

theorem interpret_public_middle_models (η : ModVar → Mode) (e : Bool) (a : Ty)
    (h : interpret η e (.ofTy a) = middle) : ModeModels a.wellFormedBounds η := by
  induction a with
  | var | unit | credit => simp [TypeExpr.wellFormedBounds, ModeModels]
  | prod a b iha ihb | sum a b iha ihb =>
    obtain ⟨ha, hb⟩ := branch_eq_middle h
    simpa only [TypeExpr.wellFormedBounds, ModeModels, List.mem_append, or_imp, forall_and]
      using And.intro (iha ha) (ihb hb)
  | fn a b iha ihb =>
    obtain ⟨ha, hb⟩ := branch_eq_middle h
    have ha' : interpret η e (.ofTy a) = middle := by
      have hh := congrArg dual ha
      simpa only [dual_dual, dual_middle] using hh
    simpa only [TypeExpr.wellFormedBounds, ModeModels, List.mem_append, or_imp, forall_and]
      using And.intro (iha ha') (ihb hb)
  | modal a m ih =>
    change scalar η e m (interpret η e (.ofTy a)) = middle at h
    unfold scalar at h
    split at h
    · next hm =>
      have hh := ih h
      simp only [TypeExpr.wellFormedBounds, ModeModels, List.mem_append, or_imp, forall_and,
        List.mem_singleton, forall_eq]
      exact ⟨hh, hm⟩
    · exact False.elim (extreme_ne_middle e h)

/-- A public lower boundary cannot acquire definedness through internal lattice
intermediates. -/
theorem public_defined_of_below {Δ : Bounds} {a : Ty} {b : CompareTy}
    (hΔ : Δ.TypeBoundsDefined) (hb : b.DefinedUnder Δ)
    (h : AlgebraSubtype Δ (.ofTy a) b) : a.DefinedUnder Δ := by
  intro η hη
  have hfalse := algebra_sound false hη hΔ h
  have htrue := algebra_sound true hη hΔ h
  rw [interpret_defined false hη hb] at hfalse
  have hd : interpret η true (.ofTy a) = dual (interpret η false (.ofTy a)) :=
    interpret_public_dual η false a
  rw [interpret_defined true hη hb, hd] at htrue
  have hback := dual_le htrue
  rw [dual_middle, dual_dual] at hback
  exact interpret_public_middle_models η false a (le_antisymm hfalse hback)

/-- A public upper boundary cannot acquire definedness through internal lattice
intermediates. -/
theorem public_defined_of_above {Δ : Bounds} {a : Ty} {b : CompareTy}
    (hΔ : Δ.TypeBoundsDefined) (hb : b.DefinedUnder Δ)
    (h : AlgebraSubtype Δ b (.ofTy a)) : a.DefinedUnder Δ := by
  intro η hη
  have hfalse := algebra_sound false hη hΔ h
  have htrue := algebra_sound true hη hΔ h
  rw [interpret_defined false hη hb] at hfalse
  have hd : interpret η true (.ofTy a) = dual (interpret η false (.ofTy a)) :=
    interpret_public_dual η false a
  rw [interpret_defined true hη hb, hd] at htrue
  have hback := dual_le htrue
  rw [dual_middle, dual_dual] at hback
  exact interpret_public_middle_models η false a (le_antisymm hback hfalse)


theorem public_defined_of_below_assumptions {bounds : Bounds} {a : Ty} {b : CompareTy}
    (hb : b.DefinedUnder bounds.assumptions)
    (h : AlgebraSubtype bounds.assumptions (.ofTy a) b) : a.DefinedUnder bounds.assumptions :=
  public_defined_of_below (Bounds.assumptions_typeBoundsDefined bounds) hb h

theorem public_defined_of_above_assumptions {bounds : Bounds} {a : Ty} {b : CompareTy}
    (hb : b.DefinedUnder bounds.assumptions)
    (h : AlgebraSubtype bounds.assumptions b (.ofTy a)) : a.DefinedUnder bounds.assumptions :=
  public_defined_of_above (Bounds.assumptions_typeBoundsDefined bounds) hb h

theorem prepared_public_defined_of_below (source target : Scheme) {a : Ty} {b : CompareTy}
    (hb : b.DefinedUnder (SchemePreparation.prepare [] source target).assumptions)
    (h : AlgebraSubtype (SchemePreparation.prepare [] source target).assumptions (.ofTy a) b) :
    a.DefinedUnder (SchemePreparation.prepare [] source target).assumptions :=
  public_defined_of_below (SchemePreparation.prepared_typeBoundsDefined source target) hb h

theorem prepared_public_defined_of_above (source target : Scheme) {a : Ty} {b : CompareTy}
    (hb : b.DefinedUnder (SchemePreparation.prepare [] source target).assumptions)
    (h : AlgebraSubtype (SchemePreparation.prepare [] source target).assumptions b (.ofTy a)) :
    a.DefinedUnder (SchemePreparation.prepare [] source target).assumptions :=
  public_defined_of_above (SchemePreparation.prepared_typeBoundsDefined source target) hb h

end ModalityInference.ComparisonPartialBoundary
