import ModalityInference.Proofs.ComparisonDefinedPropagationWitness
import ModalityInference.Proofs.ComparisonReductionTermination
import ModalityInference.Proofs.ComparisonRootProjection
import ModalityInference.Proofs.ComparisonSkeletonLeafCoordinates

/-! Forward structural reduction preserves one defined assignment of opaque
type coordinates and shared modalities under residual declared bounds. -/

namespace ModalityInference.ComparisonReduction

open ComparisonStructuralProjection

/-- The classifier recognizes every annotation traversed in this type. -/
def AnnotationsTotal (known : List ModExpr) (t : Ty) : Prop :=
  ∀ m ∈ ComparisonAnnotations.expressions t, ComparisonBody.isTotal known m = true

theorem AnnotationsTotal.hasPartial {known : List ModExpr} {t : Ty}
    (h : AnnotationsTotal known t) :
    ComparisonAnnotations.hasPartial (ComparisonBody.isTotal known) t = false := by
  simpa only [AnnotationsTotal, ComparisonAnnotations.hasPartial, List.any_eq_false,
    Bool.not_eq_true', Bool.not_eq_false] using h

theorem AnnotationsTotal.outer {known : List ModExpr} {t : Ty}
    (h : AnnotationsTotal known t) :
    AnnotationsTotal known t.outer.1 ∧ ComparisonBody.isTotal known t.outer.2 = true := by
  induction t <;> simp_all [AnnotationsTotal, ComparisonAnnotations.expressions,
    TypeExpr.outer, ComparisonBody.isTotal, ModExpr.epsilon]

theorem defined_outer {Δ : Bounds} {σ : CompareSubstitution} {t : Ty}
    (h : (σ.ty t).DefinedUnder Δ) :
    (σ.ty t.outer.1).DefinedUnder Δ ∧ Entails Δ (.defined (t.outer.2.subst σ.mode)) := by
  induction t <;> simp_all [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst,
    TypeExpr.outer, CompareTy.definedUnder_modal_iff, ModExpr.subst,
    Entails.defined_compose_iff, ModExpr.epsilon]
  all_goals exact fun _ _ => rfl

/-- Type-coordinate images retain an opaque constructor root. -/
def OpaqueAction (σ : CompareSubstitution) : Prop :=
  ∀ v, rootTag (σ.type v).shape = 0

theorem OpaqueAction.rootTag {σ : CompareSubstitution} (h : OpaqueAction σ) (t : Ty) :
    rootTag (σ.ty t).shape = rootTag (ComparisonShape.ofTy t) := by
  induction t <;> simp_all [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst,
    CompareTy.shape, ComparisonShape.ofTy, ComparisonStructuralProjection.rootTag, OpaqueAction]

theorem PairHolds.rootTag_eq {Δ : Bounds} {σ : CompareSubstitution} {a b : Ty}
    (hR : Residual Δ) (ho : OpaqueAction σ) (h : PairHolds Δ σ (a, b)) :
    rootTag (ComparisonShape.ofTy a.outer.1) = rootTag (ComparisonShape.ofTy b.outer.1) := by
  simpa only [TypeExpr.outer_comparisonShape, ho.rootTag] using
    rootTag_equivalent hR h.shape_equivalent

theorem PairHolds.outer {Δ : Bounds} {σ : CompareSubstitution} {a b : Ty}
    (hs : σ.WellShaped Δ) (ha : (σ.ty a).DefinedUnder Δ) (hb : (σ.ty b).DefinedUnder Δ)
    (h : PairHolds Δ σ (a, b)) :
    AlgebraSubtype Δ (.modal (σ.ty a.outer.1) (a.outer.2.subst σ.mode))
      (.modal (σ.ty b.outer.1) (b.outer.2.subst σ.mode)) :=
  (outer_algebra hs a (.refl (defined_outer ha).2)).2.trans
    (h.trans (outer_algebra hs b (.refl (defined_outer hb).2)).1)

theorem modal_root_mode {Δ : Bounds} {a b : CompareTy} {m n : ModExpr}
    (hR : Residual Δ) (h : AlgebraSubtype Δ (.modal a m) (.modal b n))
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (ha : rootExpr a = .epsilon) (hb : rootExpr b = .epsilon)
    (hopaque : rootTag a.shape ≠ 0) (hfn : rootTag a.shape ≠ 5) :
    Submode Δ m n := by
  apply Submode.valid
  intro η hη
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hm η hη)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hn η hη)
  refine ⟨x, y, hx, hy, ?_⟩
  simpa only [rootOrder, hfn, ↓reduceIte, rootValue, rootExpr, ha, hb,
    ModExpr.complete, ModExpr.epsilon, Mode.identity_compose,
    ModExpr.complete_of_eval hx, ModExpr.complete_of_eval hy] using
    algebra_rootValue hR h hopaque rfl hη

theorem modal_root_future {Δ : Bounds} {a b : CompareTy} {m n : ModExpr}
    (hR : Residual Δ) (h : AlgebraSubtype Δ (.modal a m) (.modal b n))
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (ha : rootExpr a = .epsilon) (hb : rootExpr b = .epsilon)
    (hfn : rootTag a.shape = 5) : Submode Δ m (.compose n .top) := by
  apply Submode.valid
  intro η hη
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hm η hη)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hn η hη)
  refine ⟨x, y.compose Mode.top, hx, by simp [ModExpr.eval, hy, ModExpr.top], ?_⟩
  have hr : (x.compose Mode.top).le (y.compose Mode.top) = true := by
    simpa only [rootOrder, ↓reduceIte, rootValue, rootExpr, ha, hb,
      ModExpr.complete, ModExpr.epsilon, Mode.identity_compose,
      ModExpr.complete_of_eval hx, ModExpr.complete_of_eval hy] using
      algebra_rootValue hR h (by decide : 5 ≠ 0) hfn hη
  exact Mode.le_trans (by simp [Mode.le_iff, Mode.compose, Mode.top]) hr

def DefinedPair (Δ : Bounds) (σ : CompareSubstitution) (known : List ModExpr)
    (pair : Ty × Ty) : Prop :=
  PairHolds Δ σ pair ∧ (σ.ty pair.1).DefinedUnder Δ ∧ (σ.ty pair.2).DefinedUnder Δ ∧
    AnnotationsTotal known pair.1 ∧ AnnotationsTotal known pair.2

structure OrdinaryHolds (Δ : Bounds) (σ : CompareSubstitution) (s : State) : Prop where
  pending : ∀ pair ∈ s.pending, DefinedPair Δ σ s.totalModes pair
  inequalities : ∀ pair ∈ s.inequalities, PairHolds Δ σ pair
  modes : AlgebraEntailsAll Δ (σ.bounds s.modes)
  bare : s.bareVariables = []
  shared : s.shared = false

theorem OrdinaryHolds.drop {Δ : Bounds} {σ : CompareSubstitution} {s : State}
    (h : OrdinaryHolds Δ σ s) {pair : Ty × Ty} {rest : List (Ty × Ty)}
    (hp : s.pending = pair :: rest) : OrdinaryHolds Δ σ {s with pending := rest} where
  pending p hm := h.pending p (hp ▸ List.mem_cons_of_mem _ hm)
  inequalities := h.inequalities
  modes := h.modes
  bare := h.bare
  shared := h.shared

theorem OrdinaryHolds.extend {Δ : Bounds} {σ : CompareSubstitution} {s : State}
    (h : OrdinaryHolds Δ σ s) (pending inequalities : List (Ty × Ty)) (modes : Bounds)
    (hp : ∀ pair ∈ pending, DefinedPair Δ σ s.totalModes pair)
    (hi : ∀ pair ∈ inequalities, PairHolds Δ σ pair)
    (hm : AlgebraEntailsAll Δ (σ.bounds modes)) :
    OrdinaryHolds Δ σ { s with
      pending := pending ++ s.pending
      inequalities := inequalities ++ s.inequalities
      modes := modes ++ s.modes } where
  pending pair hmem := (List.mem_append.mp hmem).elim (hp pair) (h.pending pair)
  inequalities pair hmem := (List.mem_append.mp hmem).elim (hi pair) (h.inequalities pair)
  modes := by
    simpa only [CompareSubstitution.bounds, List.map_append, AlgebraEntailsAll,
      List.mem_append, or_imp, forall_and] using And.intro hm h.modes
  bare := h.bare
  shared := h.shared

theorem bareVariable_nil (t : Ty) : bareVariable [] t = none := by
  cases h : bareVariable [] t with
  | none => rfl
  | some n => exact False.elim (List.not_mem_nil (bareVariable_mem h))

theorem step_not_rejected_ordinary {Δ : Bounds} {σ : CompareSubstitution} {s : State}
    (hR : Residual Δ) (ho : OpaqueAction σ) (h : OrdinaryHolds Δ σ s)
    (reason : String) : step s ≠ .rejected reason := by
  intro hr
  unfold step at hr
  split at hr
  · contradiction
  next left right rest hp =>
    have ht := (h.pending (left, right) (hp ▸ List.mem_cons_self)).1.rootTag_eq hR ho
    simp only at hr
    repeat' first | contradiction | (split at hr <;> try simp only at hr)
    have hleft := left.outer_not_modal
    have hright := right.outer_not_modal
    cases hl : left.outer.1 <;> cases hr : right.outer.1 <;>
      simp_all [ComparisonShape.ofTy, ComparisonStructuralProjection.rootTag]
    all_goals grind

theorem DefinedPair.outer {Δ : Bounds} {σ : CompareSubstitution} {known : List ModExpr}
    {a b : Ty} (hs : σ.WellShaped Δ) (h : DefinedPair Δ σ known (a, b)) :
    DefinedPair Δ σ known (.modal a.outer.1 a.outer.2, .modal b.outer.1 b.outer.2) := by
  refine ⟨h.1.outer hs h.2.1 h.2.2.1, ?_, ?_, ?_, ?_⟩
  · exact CompareTy.definedUnder_modal_iff.mpr (defined_outer h.2.1)
  · exact CompareTy.definedUnder_modal_iff.mpr (defined_outer h.2.2.1)
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h.2.2.2.1.outer.2
    · exact h.2.2.2.1.outer.1 m hm
  · intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h.2.2.2.2.outer.2
    · exact h.2.2.2.2.outer.1 m hm

theorem DefinedPair.prod {Δ : Bounds} {σ : CompareSubstitution} {known : List ModExpr}
    {a b c d : Ty} {m n : ModExpr} (hR : Residual Δ)
    (h : DefinedPair Δ σ known (.modal (.prod a b) m, .modal (.prod c d) n)) :
    DefinedPair Δ σ known (.modal a m, .modal c n) ∧
    DefinedPair Δ σ known (.modal b m, .modal d n) ∧
    Submode Δ (m.subst σ.mode) (n.subst σ.mode) := by
  simp only [DefinedPair, PairHolds, CompareSubstitution.ty, CompareTy.ofTy,
    CompareTy.subst, CompareTy.definedUnder_modal_iff, CompareTy.definedUnder_prod_iff,
    AnnotationsTotal, ComparisonAnnotations.expressions, List.forall_mem_cons,
    List.mem_append, or_imp, forall_and] at h ⊢
  rcases h with ⟨ht, ⟨⟨ha, hb⟩, hm⟩, ⟨⟨hc, hd⟩, hn⟩, ⟨htm, hta, htb⟩, htn, htc, htd⟩
  have hi := product_inversion hR ht
  exact ⟨⟨hi.1, ⟨ha, hm⟩, ⟨hc, hn⟩, ⟨htm, hta⟩, htn, htc⟩,
    ⟨hi.2, ⟨hb, hm⟩, ⟨hd, hn⟩, ⟨htm, htb⟩, htn, htd⟩,
    modal_root_mode hR ht hm hn rfl rfl (by simp [CompareTy.shape, rootTag]) (by simp [CompareTy.shape, rootTag])⟩

theorem DefinedPair.sum {Δ : Bounds} {σ : CompareSubstitution} {known : List ModExpr}
    {a b c d : Ty} {m n : ModExpr} (hR : Residual Δ)
    (h : DefinedPair Δ σ known (.modal (.sum a b) m, .modal (.sum c d) n)) :
    DefinedPair Δ σ known (.modal a m, .modal c n) ∧
    DefinedPair Δ σ known (.modal b m, .modal d n) ∧
    Submode Δ (m.subst σ.mode) (n.subst σ.mode) := by
  simp only [DefinedPair, PairHolds, CompareSubstitution.ty, CompareTy.ofTy,
    CompareTy.subst, CompareTy.definedUnder_modal_iff, CompareTy.definedUnder_sum_iff,
    AnnotationsTotal, ComparisonAnnotations.expressions, List.forall_mem_cons,
    List.mem_append, or_imp, forall_and] at h ⊢
  rcases h with ⟨ht, ⟨⟨ha, hb⟩, hm⟩, ⟨⟨hc, hd⟩, hn⟩, ⟨htm, hta, htb⟩, htn, htc, htd⟩
  have hi := sum_inversion hR ht
  exact ⟨⟨hi.1, ⟨ha, hm⟩, ⟨hc, hn⟩, ⟨htm, hta⟩, htn, htc⟩,
    ⟨hi.2, ⟨hb, hm⟩, ⟨hd, hn⟩, ⟨htm, htb⟩, htn, htd⟩,
    modal_root_mode hR ht hm hn rfl rfl (by simp [CompareTy.shape, rootTag]) (by simp [CompareTy.shape, rootTag])⟩

theorem DefinedPair.fn {Δ : Bounds} {σ : CompareSubstitution} {known : List ModExpr}
    {a b c d : Ty} {m n : ModExpr} (hR : Residual Δ)
    (h : DefinedPair Δ σ known (.modal (.fn a b) m, .modal (.fn c d) n)) :
    DefinedPair Δ σ known (c, a) ∧ DefinedPair Δ σ known (b, d) ∧
    Submode Δ (m.subst σ.mode) (.compose (n.subst σ.mode) .top) := by
  simp only [DefinedPair, PairHolds, CompareSubstitution.ty, CompareTy.ofTy,
    CompareTy.subst, CompareTy.definedUnder_modal_iff, CompareTy.definedUnder_fn_iff,
    AnnotationsTotal, ComparisonAnnotations.expressions, List.forall_mem_cons,
    List.mem_append, or_imp, forall_and] at h ⊢
  rcases h with ⟨ht, ⟨⟨ha, hb⟩, hm⟩, ⟨⟨hc, hd⟩, hn⟩, ⟨htm, hta, htb⟩, htn, htc, htd⟩
  have hi := function_inversion hR ht
  exact ⟨⟨hi.1, hc, ha, htc, hta⟩, ⟨hi.2, hb, hd, htb, htd⟩,
    modal_root_future hR ht hm hn rfl rfl rfl⟩

theorem step_forward {Δ : Bounds} {σ : CompareSubstitution} {s next : State}
    (hR : Residual Δ) (hs : σ.WellShaped Δ)
    (h : OrdinaryHolds Δ σ s) (hstep : step s = .success next) :
    OrdinaryHolds Δ σ next := by
  unfold step at hstep
  split at hstep
  · cases hstep
    exact h
  next left right rest hp =>
    have hp0 := h.pending (left, right) (hp ▸ List.mem_cons_self)
    have houter := hp0.outer hs
    have hd := h.drop hp
    simp only [h.bare, h.shared] at hd
    simp only at hstep
    simp only [h.bare, bareVariable_nil, h.shared, Bool.false_eq_true, ↓reduceIte,
      hp0.2.2.2.1.hasPartial, hp0.2.2.2.2.hasPartial, Bool.false_or] at hstep
    split at hstep
    · cases hstep
      exact hd
    split at hstep
    · cases hstep
      exact hd
    split at hstep
    all_goals try contradiction
    all_goals cases hstep
    · apply hd.extend [] [(left, right)] [.defined left.outer.2, .defined right.outer.2]
      · simp
      · simpa only [List.forall_mem_singleton] using hp0.1
      · simpa [CompareSubstitution.bounds, AlgebraEntailsAll, CompareSubstitution.constraint,
          AlgebraEntails] using And.intro (defined_outer hp0.2.1).2 (defined_outer hp0.2.2.1).2
    · have hsub := hp0.1.outer hs hp0.2.1 hp0.2.2.1
      simp only [‹left.outer.1 = .unit›, ‹right.outer.1 = .unit›,
        CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst] at hsub
      have hm := modal_root_mode hR hsub (defined_outer hp0.2.1).2
        (defined_outer hp0.2.2.1).2 rfl rfl (by decide) (by decide)
      apply hd.extend [] [] [.mode left.outer.2 right.outer.2]
      · simp
      · simp
      · simpa [CompareSubstitution.bounds, AlgebraEntailsAll,
          CompareSubstitution.constraint, AlgebraEntails] using hm
    · have hsub := hp0.1.outer hs hp0.2.1 hp0.2.2.1
      simp only [‹left.outer.1 = .credit›, ‹right.outer.1 = .credit›,
        CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst] at hsub
      have hm := modal_root_mode hR hsub (defined_outer hp0.2.1).2
        (defined_outer hp0.2.2.1).2 rfl rfl (by decide) (by decide)
      apply hd.extend [] [] [.mode left.outer.2 right.outer.2]
      · simp
      · simp
      · simpa [CompareSubstitution.bounds, AlgebraEntailsAll,
          CompareSubstitution.constraint, AlgebraEntails] using hm
    · simp only [‹left.outer.1 = .prod _ _›, ‹right.outer.1 = .prod _ _›] at houter
      have hh := DefinedPair.prod hR houter
      apply hd.extend [_ , _] [] [.mode left.outer.2 right.outer.2]
      · simp only [List.forall_mem_cons]
        exact ⟨hh.1, hh.2.1, by simp⟩
      · simp
      · simpa [CompareSubstitution.bounds, AlgebraEntailsAll,
          CompareSubstitution.constraint, AlgebraEntails] using hh.2.2
    · simp only [‹left.outer.1 = .sum _ _›, ‹right.outer.1 = .sum _ _›] at houter
      have hh := DefinedPair.sum hR houter
      apply hd.extend [_ , _] [] [.mode left.outer.2 right.outer.2]
      · simp only [List.forall_mem_cons]
        exact ⟨hh.1, hh.2.1, by simp⟩
      · simp
      · simpa [CompareSubstitution.bounds, AlgebraEntailsAll,
          CompareSubstitution.constraint, AlgebraEntails] using hh.2.2
    · simp only [‹left.outer.1 = .fn _ _›, ‹right.outer.1 = .fn _ _›] at houter
      have hh := DefinedPair.fn hR houter
      apply hd.extend [_ , _] [] [.mode left.outer.2 (.compose right.outer.2 .top)]
      · simp only [List.forall_mem_cons]
        exact ⟨hh.1, hh.2.1, by simp⟩
      · simp
      · simpa [CompareSubstitution.bounds, AlgebraEntailsAll,
          CompareSubstitution.constraint, AlgebraEntails, ModExpr.subst, ModExpr.top] using hh.2.2


theorem run_forward {Δ : Bounds} {σ : CompareSubstitution} {s next : State} {fuel : Nat}
    (hR : Residual Δ) (hs : σ.WellShaped Δ) (h : OrdinaryHolds Δ σ s)
    (hrun : run fuel s = .success next) : OrdinaryHolds Δ σ next := by
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at hrun
    split at hrun
    · cases hrun
      exact h
    · cases hstep : step s <;> simp only [hstep] at hrun <;> try contradiction
      exact ih (step_forward hR hs h hstep) hrun

theorem run_not_rejected_ordinary {Δ : Bounds} {σ : CompareSubstitution} {s : State}
    (hR : Residual Δ) (hs : σ.WellShaped Δ) (ho : OpaqueAction σ)
    (h : OrdinaryHolds Δ σ s) (fuel : Nat) (reason : String) :
    run fuel s ≠ .rejected reason := by
  intro hr
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at hr
    split at hr
    · contradiction
    · cases hstep : step s <;> simp only [hstep] at hr <;> try contradiction
      · exact ih (step_forward hR hs h hstep) hr
      · exact step_not_rejected_ordinary hR ho h _ hstep

theorem run_complete_ordinary {Δ : Bounds} {σ : CompareSubstitution} {s : State}
    (hR : Residual Δ) (hs : σ.WellShaped Δ) (ho : OpaqueAction σ)
    (h : OrdinaryHolds Δ σ s) :
    ∃ n next, (∀ fuel ≥ n, run fuel s = .success next) ∧ OrdinaryHolds Δ σ next := by
  obtain ⟨n, result, hresult, hr⟩ := run_fuel_terminates s
  cases result with
  | exhausted => exact False.elim (hresult rfl)
  | rejected reason => exact False.elim (run_not_rejected_ordinary hR hs ho h n reason (hr n le_rfl))
  | success next => exact ⟨n, next, hr, run_forward hR hs h (hr n le_rfl)⟩

/-- The initial state of ordinary reduction after a fixed template allocation. -/
def ordinaryInitial (p : SchemePreparation.Prepared) (templates : ComparisonSkeleton.Templates)
    (known : List ModExpr) : State :=
  { initial (templates.substitution.bounds p.sourceBounds)
      (templates.substitution.ty p.sourceType) p.targetType with
    assumptions := p.assumptions
    bareVariables := []
    totalModes := known
    shared := false }

/-- Both executable reduction passes finish with the same defined witness. -/
theorem prepare_complete_ordinary {Δ : Bounds} {σ : CompareSubstitution}
    {p : SchemePreparation.Prepared} {templates : ComparisonSkeleton.Templates}
    {known : List ModExpr} (hR : Residual Δ) (hs : σ.WellShaped Δ) (ho : OpaqueAction σ)
    (h : OrdinaryHolds Δ σ (ordinaryInitial p templates known)) :
    ∃ n next, (∀ fuel ≥ n, prepare fuel p templates [] known false = .success next) ∧
      OrdinaryHolds Δ σ next := by
  obtain ⟨n, reduced, hr, hh⟩ := run_complete_ordinary hR hs ho h
  let next : State := { reduced with pending := [], bareVariables := [], bareBounds := [], partialTypes := [] }
  refine ⟨n + 1, next, ?_, ?_⟩
  · intro fuel hf
    have hr' := hr fuel (by omega)
    dsimp only [ordinaryInitial] at hr'
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold prepare
      dsimp only
      rw [hr']
      simp only [bind, RunResult.bind, ComparisonPartial.reduceBare,
        List.map_nil, List.flatMap_nil, run, List.isEmpty_nil, ↓reduceIte]
      rfl
  · exact ⟨by simp [next], hh.inequalities, hh.modes, rfl, hh.shared⟩

end ModalityInference.ComparisonReduction
