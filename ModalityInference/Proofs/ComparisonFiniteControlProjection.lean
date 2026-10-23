import ModalityInference.Proofs.ComparisonFiniteControls
import ModalityInference.Proofs.ComparisonModeRestriction

/-! Labels outside the fixed name boundary are projected before entering the
finite control monoid. The projection preserves the original scalar rules. -/
namespace ModalityInference.ComparisonFiniteControlProjection

open ComparisonFiniteControls ComparisonModeRestriction

noncomputable section

variable {Δ : Bounds} {names : List ModVar} (hnames : Δ.modVars ⊆ names.toFinset)

def project (m : ModExpr) (hm : Entails Δ (.defined m)) : Control Δ names :=
  encode (m.subst (restrict names.toFinset)) ((restrict_fixed Δ names.toFinset hnames).defined hm)
    (restrict_support names.toFinset m)

theorem project_eval (m : ModExpr) (hm : Entails Δ (.defined m)) (η : Model Δ) :
    (m.subst (restrict names.toFinset)).eval (some ∘ η.val) =
      some ((project hnames m hm).val η) := encode_eval _ _ _ η

@[simp] theorem project_epsilon (hm : Entails Δ (.defined .epsilon)) :
    project hnames .epsilon hm = 1 := rfl

@[simp] theorem project_top (hm : Entails Δ (.defined .top)) :
    project hnames .top hm = top := rfl

theorem project_compose (m n : ModExpr) (hm : Entails Δ (.defined m))
    (hn : Entails Δ (.defined n)) (hmn : Entails Δ (.defined (.compose m n))) :
    project hnames (.compose m n) hmn = project hnames m hm * project hnames n hn := by
  apply control_ext
  intro η
  exact Option.some.inj ((project_eval hnames _ hmn η).symm.trans
    (by simp [ModExpr.subst,ModExpr.eval,project_eval hnames m hm η,project_eval hnames n hn η,mul_val]))

theorem project_submode {m n : ModExpr} (h : Submode Δ m n) :
    project hnames m h.defined.1 ≤ project hnames n h.defined.2 :=
  (encode_le_iff _ _ _ _ _ _).mpr ((restrict_fixed Δ names.toFinset hnames).submode h)

theorem project_future {m n : ModExpr} (hm : Entails Δ (.defined m))
    (hn : Entails Δ (.defined n)) (h : Submode Δ m (.compose n .top)) :
    FutureLe (project hnames m hm) (project hnames n hn) := by
  simpa only [FutureLe,project_compose hnames n .top hn (fun _ _ => rfl),project_top]
    using project_submode hnames h

theorem restrict_of_supported (m : ModExpr) (hs : m.vars ⊆ names.toFinset) :
    m.subst (restrict names.toFinset) = m :=
  (ModExpr.subst_congr m (τ := ModExpr.var)
    (fun v hv => by simp only [restrict,if_pos (hs hv)])).trans (ModExpr.subst_id m)

theorem project_supported (m : ModExpr) (hm : Entails Δ (.defined m))
    (hs : m.vars ⊆ names.toFinset) : project hnames m hm = encode m hm hs := by
  apply control_ext
  intro η
  exact Option.some.inj ((project_eval hnames m hm η).symm.trans
    ((congrArg (fun t => t.eval (some ∘ η.val)) (restrict_of_supported m hs)).trans
      (encode_eval m hm hs η)))

theorem project_expression (m : Control Δ names) :
    project hnames (expression m) (expression_defined m) = m :=
  (project_supported hnames _ _ (expression_support m)).trans (encode_expression m)

end
end ModalityInference.ComparisonFiniteControlProjection
