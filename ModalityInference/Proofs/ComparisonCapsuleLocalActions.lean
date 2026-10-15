import ModalityInference.Proofs.ComparisonCapsuleParameterization

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonBody ComparisonCapsuleIntervals

/-- Only certified annotations occurring in the source context require total
instantiated actions. Modality images in frozen contexts remain unrestricted. -/
def SourceActionsTotal (Δ : Bounds) (total : ModExpr → Bool)
    (images : ModVar → ModExpr) (source : Ty) : Prop :=
  ∀ m ∈ ComparisonAnnotations.expressions source,
    total m = true → Entails Δ (.defined (m.subst images))

theorem requests_action_subst_total {Δ : Bounds} (p : Prepared) (total : ModExpr → Bool)
    (images : ModVar → ModExpr)
    (fuel : Nat) (lower : Bool) (source target : Ty) (sm tm : ModExpr)
    (hsource : SourceActionsTotal Δ total images source)
    (hsm : Entails Δ (.defined (sm.subst images)))
    {r : Request} (hr : r ∈ requests p total fuel lower source target sm tm) :
    Entails Δ (.defined (r.action.subst images)) := by
  induction fuel generalizing lower source target sm tm with
  | zero => simp [requests] at hr
  | succ fuel ih =>
    cases source with
    | modal a m =>
      simp only [requests] at hr
      split at hr
      · next hm =>
          exact ih lower a target (.compose m sm) tm
            (fun n hn => hsource n (List.mem_cons_of_mem _ hn))
            (Entails.defined_compose_iff.mpr ⟨hsource m List.mem_cons_self hm, hsm⟩) hr
      · simp at hr
    | var v =>
      cases v with
      | flex n =>
        simp only [requests] at hr
        split at hr
        · cases List.mem_singleton.mp hr; exact hsm
        · simp at hr
      | rigid n =>
        cases target <;> simp only [requests] at hr
        all_goals try simp at hr
        exact ih _ _ _ _ _ hsource hsm hr
    | unit | credit =>
      cases target <;> simp only [requests] at hr
      all_goals try simp at hr
      exact ih _ _ _ _ _ hsource hsm hr
    | prod a b | sum a b | fn a b =>
      have ha : SourceActionsTotal Δ total images a :=
        fun m hm => hsource m (List.mem_append_left _ hm)
      have hb : SourceActionsTotal Δ total images b :=
        fun m hm => hsource m (List.mem_append_right _ hm)
      cases target <;> simp only [requests] at hr
      all_goals try simp at hr
      case modal c m => exact ih _ _ _ _ _ hsource hsm hr
      all_goals
        rcases hr with hr | hr
        · exact ih _ _ _ _ _ ha (by first | exact hsm | exact fun _ _ => rfl) hr
        · exact ih _ _ _ _ _ hb (by first | exact hsm | exact fun _ _ => rfl) hr

theorem collect_action_subst_total {Δ : Bounds} (p : Prepared) (total : ModExpr → Bool)
    (images : ModVar → ModExpr) (hsource : SourceActionsTotal Δ total images p.sourceType)
    {r : Request} (hr : r ∈ collect p total) :
    Entails Δ (.defined (r.action.subst images)) :=
  requests_action_subst_total p total images _ false p.sourceType p.targetType
    .epsilon .epsilon hsource (fun _ _ => rfl) hr

theorem frozenTypeSupport_congr (body : Ty) (total other : ModExpr → Bool)
    (h : ∀ m ∈ ComparisonAnnotations.expressions body, total m = other m) :
    frozenTypeSupport total body = frozenTypeSupport other body := by
  induction body with
  | var | unit | credit => rfl
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    change frozenTypeSupport total a ∪ frozenTypeSupport total b =
      frozenTypeSupport other a ∪ frozenTypeSupport other b
    rw [ia (fun m hm => h m (List.mem_append_left _ hm)),
      ib (fun m hm => h m (List.mem_append_right _ hm))]
  | modal a m ia =>
    simp only [frozenTypeSupport, h m List.mem_cons_self]
    split
    · exact ia (fun n hn => h n (List.mem_cons_of_mem _ hn))
    · rfl

end ModalityInference.ComparisonCapsuleContext

namespace ModalityInference.ComparisonPartialCarrier

open ComparisonCapsuleContext

/-- Whole-body reconstruction needs totality only at the source annotations
through which it changes an image. All frozen modality syntax is retained. -/
theorem body_replacement_local {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {types replacement : TypeVar → CompareTy} {modes : ModVar → ModExpr}
    (total : ModExpr → Bool) {body : Ty}
    (htotal : SourceActionsTotal Δ total modes body)
    {endpoint : CompareTy} (hc : Carrier Δ endpoint)
    (h : AlgebraSubtype Δ (publicImage types modes body) endpoint)
    (hp : ∀ v ∈ body.typeVars, PreservesBounds Δ (types v) (replacement v))
    (hf : ∀ v ∈ frozenTypes total body, replacement v = types v) :
    AlgebraSubtype Δ (publicImage replacement modes body) endpoint := by
  let localTotal : ModExpr → Bool := fun m => total m && decide (m ∈ ComparisonAnnotations.expressions body)
  have he : frozenTypeSupport localTotal body = frozenTypeSupport total body :=
    frozenTypeSupport_congr body _ _ (fun m hm => by simp only [localTotal, hm, decide_true, Bool.and_true])
  have hl : ∀ m, localTotal m = true → Entails Δ (.defined (m.subst modes)) := by
    intro m hm
    have hh : total m = true ∧ m ∈ ComparisonAnnotations.expressions body := by
      simpa only [localTotal, Bool.and_eq_true, decide_eq_true_eq] using hm
    exact htotal m hh.2 hh.1
  exact body_replacement hΔ localTotal hl hc h hp (by simpa only [frozenTypes, he] using hf)

end ModalityInference.ComparisonPartialCarrier
