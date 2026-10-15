import ModalityInference.ComparisonPartial
import ModalityInference.Proofs.ComparisonInterpolation
import ModalityInference.Proofs.ComparisonTypes
import ModalityInference.Proofs.ModeWitness
import ModalityInference.Proofs.SubstitutionSupport

namespace ModalityInference.ComparisonPartial

theorem absentFromBounds_correct (name : Nat) (bounds : Bounds) :
    absentFromBounds name bounds = true ↔
      ∀ c ∈ bounds, TypeVar.flex name ∉ c.typeVars := by
  simp [absentFromBounds]

theorem mem_eligible {p : SchemePreparation.Prepared} {name : Nat} :
    name ∈ eligible p ↔
      name ∈ List.range' p.firstType (p.nextType - p.firstType) ∧
      (∀ c ∈ p.sourceBounds, TypeVar.flex name ∉ c.typeVars) ∧
      bareOccurrences name false p.sourceType = true := by
  simp [eligible, absentFromBounds_correct, and_assoc]

theorem eligible_avoids_bounds {p : SchemePreparation.Prepared} {name : Nat}
    (h : name ∈ eligible p) {c : Constraint} (hc : c ∈ p.sourceBounds) :
    TypeVar.flex name ∉ c.typeVars := (mem_eligible.mp h).2.1 c hc

theorem mem_lower {name : Nat} {bounds : List BareBound} {t : Ty} :
    t ∈ lower name bounds ↔
      ∃ b ∈ bounds, b.name = name ∧ b.isLower = true ∧ b.endpoint = t := by
  simp only [lower, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, h⟩
    split at h
    · next he =>
      simp only [Bool.and_eq_true, beq_iff_eq] at he
      exact ⟨b, hb, he.1, he.2, Option.some.inj h⟩
    · contradiction
  · rintro ⟨b, hb, hn, hl, ht⟩
    exact ⟨b, hb, by simp [hn, hl, ht]⟩

theorem mem_upper {name : Nat} {bounds : List BareBound} {t : Ty} :
    t ∈ upper name bounds ↔
      ∃ b ∈ bounds, b.name = name ∧ b.isLower = false ∧ b.endpoint = t := by
  simp only [upper, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, h⟩
    split at h
    · next he =>
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at he
      exact ⟨b, hb, he.1, he.2, Option.some.inj h⟩
    · contradiction
  · rintro ⟨b, hb, hn, hl, ht⟩
    exact ⟨b, hb, by simp [hn, hl, ht]⟩

def Interval (Δ : Bounds) (name : Nat) (bounds : List BareBound) (t : CompareTy) : Prop :=
  (∀ a ∈ lower name bounds, CompareSubtype Δ (CompareTy.ofTy a) t) ∧
    ∀ b ∈ upper name bounds, CompareSubtype Δ t (CompareTy.ofTy b)

def Crossed (Δ : Bounds) (goals : List (Ty × Ty)) : Prop :=
  ∀ p ∈ goals, CompareSubtype Δ (CompareTy.ofTy p.1) (CompareTy.ofTy p.2)

theorem crossed_correct (Δ : Bounds) (name : Nat) (bounds : List BareBound) :
    Crossed Δ (crossed name bounds) ↔
      ComparisonInterpolation.Crossed Δ ((lower name bounds).map CompareTy.ofTy)
        ((upper name bounds).map CompareTy.ofTy) := by
  simp only [Crossed, crossed, ComparisonInterpolation.Crossed,
    List.forall_mem_flatMap, List.forall_mem_map]

/-- Partial annotations are opaque endpoint syntax here: no endpoint or body
definedness premise is used by finite interval reconstruction. -/
theorem image_correct (Δ : Bounds) (name : Nat) (bounds : List BareBound) :
    Interval Δ name bounds (image name bounds) ↔ Crossed Δ (crossed name bounds) := by
  rw [crossed_correct, ← ComparisonInterpolation.witness_interval_iff]
  simp [Interval, image, ComparisonInterpolation.Interval]

theorem exists_interval_iff (Δ : Bounds) (name : Nat) (bounds : List BareBound) :
    (∃ t, Interval Δ name bounds t) ↔ Crossed Δ (crossed name bounds) := by
  rw [crossed_correct, ← ComparisonInterpolation.exists_interval_iff]
  simp [Interval, ComparisonInterpolation.Interval]

@[simp] theorem reduceBare_domain (indices : List Nat) (bounds : List BareBound) :
    (reduceBare indices bounds).images.map Prod.fst = indices := by
  simp [reduceBare, List.map_map, Function.comp_def]

theorem reduceBare_lookup {indices : List Nat} {bounds : List BareBound} {name : Nat}
    (h : name ∈ indices) :
    (reduceBare indices bounds).images.lookup name = some (image name bounds) :=
  lookup_map_self indices (fun name => image name bounds) h

theorem reduceBare_goals (Δ : Bounds) (indices : List Nat) (bounds : List BareBound) :
    Crossed Δ (reduceBare indices bounds).goals ↔
      ∀ name ∈ indices, Crossed Δ (crossed name bounds) := by
  simp only [Crossed, reduceBare, List.forall_mem_flatMap]

theorem reduceBare_correct (Δ : Bounds) (indices : List Nat) (bounds : List BareBound) :
    Crossed Δ (reduceBare indices bounds).goals ↔
      ∀ name ∈ indices, Interval Δ name bounds (image name bounds) := by
  simp only [reduceBare_goals, image_correct]

theorem reduceBare_complete (Δ : Bounds) (indices : List Nat) (bounds : List BareBound) :
    Crossed Δ (reduceBare indices bounds).goals ↔
      ∀ name ∈ indices, ∃ t, Interval Δ name bounds t := by
  simp only [reduceBare_goals, exists_interval_iff]

theorem mem_remaining {indices : List Nat} {bounds : List BareBound} {bound : BareBound} :
    bound ∈ (reduceBare indices bounds).remaining ↔ bound ∈ bounds ∧ bound.name ∉ indices := by
  simp [reduceBare]

theorem image_support {P : TypeVar → Prop} {Q : ModVar → Prop}
    {name : Nat} {bounds : List BareBound}
    (h : ∀ b ∈ bounds, ComparisonInterpolation.Supports P Q (CompareTy.ofTy b.endpoint)) :
    ComparisonInterpolation.Supports P Q (image name bounds) := by
  apply ComparisonInterpolation.witness_support
  · intro t ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    obtain ⟨b, hb, _, _, rfl⟩ := mem_lower.mp ha
    exact h b hb
  · intro t ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    obtain ⟨b, hb, _, _, rfl⟩ := mem_upper.mp ha
    exact h b hb

theorem reduceBare_lookup_none {indices : List Nat} {bounds : List BareBound} {name : Nat}
    (h : name ∉ indices) : (reduceBare indices bounds).images.lookup name = none := by
  apply List.lookup_eq_none_iff.mpr
  intro p hp
  apply bne_iff_ne.mpr
  intro he
  apply h
  rw [← reduceBare_domain indices bounds]
  exact List.mem_map.mpr ⟨p, hp, he.symm⟩

theorem reduceBare_type_fixed {indices : List Nat} {bounds : List BareBound} {name : Nat}
    (h : name ∉ indices) :
    (reduceBare indices bounds).substitution.type (.flex name) = .var (.flex name) := by
  simp [BareReduction.substitution, CompareSubstitution.type, reduceBare_lookup_none h]

@[simp] theorem reduceBare_mode (indices : List Nat) (bounds : List BareBound) (v : ModVar) :
    (reduceBare indices bounds).substitution.mode v = .var v := by cases v <;> rfl

theorem reduceBare_ty_fixed {indices : List Nat} {bounds : List BareBound} (t : Ty)
    (h : ∀ name ∈ indices, TypeVar.flex name ∉ t.typeVars) :
    (reduceBare indices bounds).substitution.ty t = CompareTy.ofTy t := by
  have hm : (reduceBare indices bounds).substitution.mode = ModExpr.var :=
    funext (reduceBare_mode indices bounds)
  induction t with
  | var v =>
    cases v with
    | rigid _ => rfl
    | flex name => exact reduceBare_type_fixed (fun hn => h name hn (by simp [TypeExpr.typeVars]))
  | unit => rfl
  | credit => rfl
  | prod a b ihA ihB =>
    have ha := ihA (fun n hn hv => h n hn (by simp [TypeExpr.typeVars, hv]))
    have hb := ihB (fun n hn hv => h n hn (by simp [TypeExpr.typeVars, hv]))
    exact congrArg₂ CompareTy.prod ha hb
  | sum a b ihA ihB =>
    have ha := ihA (fun n hn hv => h n hn (by simp [TypeExpr.typeVars, hv]))
    have hb := ihB (fun n hn hv => h n hn (by simp [TypeExpr.typeVars, hv]))
    exact congrArg₂ CompareTy.sum ha hb
  | fn a b ihA ihB =>
    have ha := ihA (fun n hn hv => h n hn (by simp [TypeExpr.typeVars, hv]))
    have hb := ihB (fun n hn hv => h n hn (by simp [TypeExpr.typeVars, hv]))
    exact congrArg₂ CompareTy.fn ha hb
  | modal a m ih =>
    have ha := ih h
    change CompareTy.modal ((reduceBare indices bounds).substitution.ty a)
      (m.subst (reduceBare indices bounds).substitution.mode) = .modal (CompareTy.ofTy a) m
    rw [ha, hm, ModExpr.subst_id]

theorem reduceBare_constraint_fixed {indices : List Nat} {bounds : List BareBound}
    (c : Constraint) (h : ∀ name ∈ indices, TypeVar.flex name ∉ c.typeVars) :
    (reduceBare indices bounds).substitution.constraint c = CompareConstraint.ofConstraint c := by
  have hm : (reduceBare indices bounds).substitution.mode = ModExpr.var :=
    funext (reduceBare_mode indices bounds)
  cases c with
  | sub a b =>
    have ha := reduceBare_ty_fixed (bounds := bounds) a (fun n hn hv => h n hn (by simp [Constraint.typeVars, hv]))
    have hb := reduceBare_ty_fixed (bounds := bounds) b (fun n hn hv => h n hn (by simp [Constraint.typeVars, hv]))
    simp [CompareSubstitution.constraint, CompareConstraint.ofConstraint, ha, hb]
  | equiv a b =>
    have ha := reduceBare_ty_fixed (bounds := bounds) a (fun n hn hv => h n hn (by simp [Constraint.typeVars, hv]))
    have hb := reduceBare_ty_fixed (bounds := bounds) b (fun n hn hv => h n hn (by simp [Constraint.typeVars, hv]))
    simp [CompareSubstitution.constraint, CompareConstraint.ofConstraint, ha, hb]
  | mode a b => simp [CompareSubstitution.constraint, CompareConstraint.ofConstraint, hm]
  | defined a => simp [CompareSubstitution.constraint, CompareConstraint.ofConstraint, hm]
  | equal v a =>
    have ha := reduceBare_ty_fixed (bounds := bounds) a (fun n hn hv => h n hn (by simp [Constraint.typeVars, hv]))
    cases v with
    | rigid _ => simp [CompareSubstitution.constraint, CompareConstraint.ofConstraint, ha]
    | flex n =>
      have hn : n ∉ indices := fun hn => h n hn (by simp [Constraint.typeVars])
      simp only [CompareSubstitution.constraint, CompareConstraint.ofConstraint,
        BareReduction.substitution, reduceBare_lookup_none hn]
      exact congrArg (CompareConstraint.equal (.flex n)) ha

/-- Every source constraint and its written guards are unchanged by the bare
body-only images; the hypothesis ranges over the full source bounds. -/
theorem reduceBare_bounds_fixed {indices : List Nat} {bounds : List BareBound}
    (sourceBounds : Bounds)
    (h : ∀ name ∈ indices, ∀ c ∈ sourceBounds, TypeVar.flex name ∉ c.typeVars) :
    (reduceBare indices bounds).substitution.bounds sourceBounds =
      sourceBounds.map CompareConstraint.ofConstraint := by
  apply List.map_congr_left
  intro c hc
  exact reduceBare_constraint_fixed c (fun n hn => h n hn c hc)

theorem eligible_bounds_fixed (p : SchemePreparation.Prepared) (bounds : List BareBound) :
    (reduceBare (eligible p) bounds).substitution.bounds p.sourceBounds =
      p.sourceBounds.map CompareConstraint.ofConstraint :=
  reduceBare_bounds_fixed p.sourceBounds (fun _ hn _ hc => eligible_avoids_bounds hn hc)

end ModalityInference.ComparisonPartial
