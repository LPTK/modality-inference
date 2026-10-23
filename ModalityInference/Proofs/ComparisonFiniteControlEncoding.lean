import ModalityInference.ComparisonFiniteControlEncoding
import ModalityInference.Proofs.ComparisonControlForms
import ModalityInference.Proofs.ComparisonFiniteControlProjection
import ModalityInference.Proofs.ScalarDecision

/-! The executable control indices present the semantic ordered control monoid
exactly. Lookup's fallback is excluded for every supported defined label. -/
namespace ModalityInference.ComparisonFiniteControlEncoding

noncomputable section

theorem equivalent_correct (Δ : Bounds) (m n : ModExpr) :
    equivalent Δ m n = true ↔ Submode Δ m n ∧ Submode Δ n m := by
  simp only [equivalent,Bool.and_eq_true,ScalarDecision.submode_correct]

private theorem filtered_complete {Δ : Bounds} {xs : List ModExpr}
    (ht : ∀ m ∈ xs, Entails Δ (.defined m)) {m : ModExpr} (hm : m ∈ xs) :
    ∃ r ∈ xs.pwFilter (fun a b => equivalent Δ a b = false), equivalent Δ m r = true := by
  induction xs with
  | nil => cases hm
  | cons a xs ih =>
    have htail := ih (fun r hr => ht r (List.mem_cons_of_mem _ hr))
    by_cases hk : ∀ b ∈ xs.pwFilter (fun a b => equivalent Δ a b = false), equivalent Δ a b = false
    · rw [List.pwFilter_cons_of_pos hk]
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨m,List.mem_cons_self,(equivalent_correct Δ m m).mpr
          ⟨Submode.refl (ht m List.mem_cons_self),Submode.refl (ht m List.mem_cons_self)⟩⟩
      · obtain ⟨r,hr,he⟩ := htail hm
        exact ⟨r,List.mem_cons_of_mem _ hr,he⟩
    · rw [List.pwFilter_cons_of_neg hk]
      rcases List.mem_cons.mp hm with rfl | hm
      · push_neg at hk
        obtain ⟨r,hr,he⟩ := hk
        exact ⟨r,hr,by simpa using he⟩
      · exact htail hm

theorem labels_subset (Δ : Bounds) (names : List ModVar) :
    labels Δ names ⊆ ComparisonControlForms.representatives names :=
  List.pwFilter_subset _

theorem labels_complete {Δ : Bounds} {names : List ModVar} {m : ModExpr}
    (hm : Entails Δ (.defined m)) (hs : m.vars ⊆ names.toFinset) :
    ∃ r ∈ labels Δ names, equivalent Δ m r = true := by
  obtain ⟨r,hr,hmr,hrm⟩ := ComparisonControlForms.representatives_complete hm hs
  obtain ⟨s,hmem,he⟩ := filtered_complete
    (fun _ h => ComparisonControlForms.representatives_total h) hr
  obtain ⟨hrs,hsr⟩ := (equivalent_correct Δ r s).mp he
  exact ⟨s,hmem,(equivalent_correct Δ m s).mpr ⟨hmr.trans hrs,hsr.trans hrm⟩⟩

theorem expression_mem {Δ : Bounds} {names : List ModVar} (c : Code Δ names) :
    expression c ∈ labels Δ names := List.getElem_mem c.index.isLt

theorem expression_defined {Δ : Bounds} {names : List ModVar} (c : Code Δ names) :
    Entails Δ (.defined (expression c)) :=
  ComparisonControlForms.representatives_total (labels_subset Δ names (expression_mem c))

theorem expression_support {Δ : Bounds} {names : List ModVar} (c : Code Δ names) :
    (expression c).vars ⊆ names.toFinset :=
  ComparisonControlForms.representatives_support (labels_subset Δ names (expression_mem c))

theorem lookup_equivalent {Δ : Bounds} {names : List ModVar} {m : ModExpr}
    (hm : Entails Δ (.defined m)) (hs : m.vars ⊆ names.toFinset) :
    equivalent Δ m (expression (lookup Δ names m)) = true := by
  have hi := List.findIdx_lt_length.mpr (labels_complete hm hs)
  simpa only [lookup,dif_pos hi,expression] using (List.findIdx_getElem (w := hi))

def decode {Δ : Bounds} {names : List ModVar} (c : Code Δ names) :
    ComparisonFiniteControls.Control Δ names :=
  ComparisonFiniteControls.encode (expression c) (expression_defined c) (expression_support c)

theorem order_iff {Δ : Bounds} {names : List ModVar} (a b : Code Δ names) :
    a ≤ b ↔ decode a ≤ decode b := by
  exact (ScalarDecision.submode_correct Δ _ _).trans
    (ComparisonFiniteControls.encode_le_iff _ _ _ _ _ _).symm

theorem decode_injective {Δ : Bounds} {names : List ModVar} :
    Function.Injective (decode (Δ := Δ) (names := names)) := by
  intro a b he
  have hab : equivalent Δ (expression a) (expression b) = true :=
    (equivalent_correct Δ _ _).mpr
      ⟨(ComparisonFiniteControls.encode_le_iff _ _ _ _ _ _).mp he.le,
       (ComparisonFiniteControls.encode_le_iff _ _ _ _ _ _).mp he.ge⟩
  have hp := List.pairwise_iff_getElem.mp (List.pairwise_pwFilter
    (R := fun m n => equivalent Δ m n = false) (ComparisonControlForms.representatives names))
  rcases lt_trichotomy a.index.val b.index.val with hlt | heq | hlt
  · have hx := hp _ _ a.index.isLt b.index.isLt hlt
    change equivalent Δ (expression a) (expression b) = false at hx
    simp [hab] at hx
  · exact congrArg Code.mk (Fin.ext heq)
  · have hx := hp _ _ b.index.isLt a.index.isLt hlt
    change equivalent Δ (expression b) (expression a) = false at hx
    have hy : equivalent Δ (expression b) (expression a) = true := by
      simpa only [equivalent,Bool.and_comm] using hab
    simp [hy] at hx

theorem decode_lookup {Δ : Bounds} {names : List ModVar} {m : ModExpr}
    (hm : Entails Δ (.defined m)) (hs : m.vars ⊆ names.toFinset) :
    decode (lookup Δ names m) = ComparisonFiniteControls.encode m hm hs := by
  obtain ⟨hmr,hrm⟩ := (equivalent_correct Δ _ _).mp (lookup_equivalent hm hs)
  exact le_antisymm ((ComparisonFiniteControls.encode_le_iff _ _ _ _ _ _).mpr hrm)
    ((ComparisonFiniteControls.encode_le_iff _ _ _ _ _ _).mpr hmr)

theorem decode_surjective {Δ : Bounds} {names : List ModVar} :
    Function.Surjective (decode (Δ := Δ) (names := names)) := by
  intro m
  exact ⟨lookup Δ names (ComparisonFiniteControls.expression m),
    (decode_lookup (ComparisonFiniteControls.expression_defined m)
      (ComparisonFiniteControls.expression_support m)).trans (ComparisonFiniteControls.encode_expression m)⟩

theorem lookup_expression {Δ : Bounds} {names : List ModVar} (c : Code Δ names) :
    lookup Δ names (expression c) = c :=
  decode_injective (decode_lookup (expression_defined c) (expression_support c))

theorem decode_eval {Δ : Bounds} {names : List ModVar} (c : Code Δ names)
    (η : ComparisonFiniteControls.Model Δ) :
    (expression c).eval (some ∘ η.val) = some ((decode c).val η) :=
  ComparisonFiniteControls.encode_eval _ _ _ η

theorem decode_one {Δ : Bounds} {names : List ModVar} :
    decode (1 : Code Δ names) = 1 :=
  decode_lookup (m := .epsilon) (fun _ _ => rfl) (by simp [ModExpr.epsilon,ModExpr.vars])

theorem decode_top (Δ : Bounds) (names : List ModVar) :
    decode (top Δ names) = ComparisonFiniteControls.top :=
  decode_lookup (m := .top) (fun _ _ => rfl) (by simp [ModExpr.top,ModExpr.vars])

theorem decode_mul {Δ : Bounds} {names : List ModVar} (a b : Code Δ names) :
    decode (a * b) = decode a * decode b := by
  change decode (lookup Δ names _) = _
  rw [decode_lookup (Entails.defined_compose_iff.mpr ⟨expression_defined a,expression_defined b⟩)
    (Finset.union_subset (expression_support a) (expression_support b))]
  apply ComparisonFiniteControls.control_ext
  intro η
  exact Option.some.inj ((ComparisonFiniteControls.encode_eval _ _ _ η).symm.trans
    (by simp [ModExpr.eval,decode_eval,ComparisonFiniteControls.mul_val]))

instance {Δ : Bounds} {names : List ModVar} : PartialOrder (Code Δ names) where
  le a b := order a b = true
  le_refl a := (order_iff a a).mpr le_rfl
  le_trans a b c h k := (order_iff a c).mpr ((order_iff a b).mp h |>.trans ((order_iff b c).mp k))
  le_antisymm a b h k := decode_injective (le_antisymm ((order_iff a b).mp h) ((order_iff b a).mp k))

instance {Δ : Bounds} {names : List ModVar} : CommMonoid (Code Δ names) where
  mul_assoc a b c := decode_injective (by simp only [decode_mul,mul_assoc])
  one_mul a := decode_injective (by simp only [decode_mul,decode_one,one_mul])
  mul_one a := decode_injective (by simp only [decode_mul,decode_one,mul_one])
  mul_comm a b := decode_injective (by simp only [decode_mul,mul_comm])

def equiv (Δ : Bounds) (names : List ModVar) : Code Δ names ≃ ComparisonFiniteControls.Control Δ names where
  toFun := decode
  invFun m := lookup Δ names (ComparisonFiniteControls.expression m)
  left_inv c := decode_injective
    ((decode_lookup (ComparisonFiniteControls.expression_defined (decode c))
      (ComparisonFiniteControls.expression_support (decode c))).trans
        (ComparisonFiniteControls.encode_expression (decode c)))
  right_inv m := (decode_lookup (ComparisonFiniteControls.expression_defined m)
    (ComparisonFiniteControls.expression_support m)).trans (ComparisonFiniteControls.encode_expression m)

def orderIso (Δ : Bounds) (names : List ModVar) : Code Δ names ≃o ComparisonFiniteControls.Control Δ names where
  toEquiv := equiv Δ names
  map_rel_iff' := (order_iff _ _).symm

def mulEquiv (Δ : Bounds) (names : List ModVar) : Code Δ names ≃* ComparisonFiniteControls.Control Δ names where
  toEquiv := equiv Δ names
  map_mul' := decode_mul

@[simp] theorem orderIso_apply {Δ : Bounds} {names : List ModVar} (c : Code Δ names) :
    orderIso Δ names c = decode c := rfl

@[simp] theorem mulEquiv_apply {Δ : Bounds} {names : List ModVar} (c : Code Δ names) :
    mulEquiv Δ names c = decode c := rfl

theorem decode_project {Δ : Bounds} {names : List ModVar}
    (hnames : Δ.modVars ⊆ names.toFinset) (m : ModExpr) (hm : Entails Δ (.defined m)) :
    decode (project Δ names m) = ComparisonFiniteControlProjection.project hnames m hm :=
  decode_lookup ((ComparisonModeRestriction.restrict_fixed Δ names.toFinset hnames).defined hm)
    (ComparisonModeRestriction.restrict_support names.toFinset m)

theorem project_expression {Δ : Bounds} {names : List ModVar}
    (hnames : Δ.modVars ⊆ names.toFinset) (c : Code Δ names) :
    project Δ names (expression c) = c := by
  apply decode_injective
  exact (decode_project hnames _ (expression_defined c)).trans
    (ComparisonFiniteControlProjection.project_supported _ _
      (expression_defined c) (expression_support c))

theorem project_submode {Δ : Bounds} {names : List ModVar}
    (hnames : Δ.modVars ⊆ names.toFinset) {m n : ModExpr} (h : Submode Δ m n) :
    project Δ names m ≤ project Δ names n := by
  rw [order_iff,decode_project hnames m h.defined.1,decode_project hnames n h.defined.2]
  exact ComparisonFiniteControlProjection.project_submode hnames h

end
end ModalityInference.ComparisonFiniteControlEncoding
