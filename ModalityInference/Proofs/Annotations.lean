import ModalityInference.Annotations
import ModalityInference.Proofs.Erasure

/-! Annotation transport preserves evaluation, references, and liveness. -/
namespace ModalityInference

@[simp] theorem Term.erase_mapAnnotation (t : Term A) (f : A → B) :
    (t.mapAnnotation f).erase = t.erase := by
  induction t <;> simp_all [Term.erase, Term.mapAnnotation]

theorem trimEnvironment_mapAnnotation (γ : Environment) (used : Finset Nat)
    (f : Capture → Capture) :
    (trimEnvironment γ used).map (Value.mapAnnotation f) =
      trimEnvironment (γ.map (Value.mapAnnotation f)) used := by
  apply List.ext_getElem?
  intro i
  cases h : γ[i]? <;> by_cases hi : i ∈ used <;>
    simp [trimEnvironment, List.getElem?_map, List.getElem?_mapIdx, h, hi, Value.mapAnnotation]

theorem Eval.mapAnnotation {s γ t v} (h : Eval s γ t v) (f : Capture → Capture) :
    Eval s (γ.map (Value.mapAnnotation f)) (t.mapAnnotation f) (v.mapAnnotation f) := by
  induction h
  all_goals simp only [Term.mapAnnotation, Value.mapAnnotation, List.map_cons, List.map_nil] at *
  all_goals try solve_by_elim (config := { maxDepth := 8 }) [Eval.unit, Eval.app,
    Eval.pair, Eval.stackPair, Eval.inl, Eval.inr, Eval.defn, Eval.split,
    Eval.caseLeft, Eval.caseRight, Eval.reuse, Eval.region]
  case var _ _ _ _ h => exact .var (by simp [List.getElem?_map, h])
  case lam =>
    simpa only [Term.freeVars_mapAnnotation, trimEnvironment_mapAnnotation] using
      (Eval.lam (s := _) (γ := _) (captured := f _) (body := Term.mapAnnotation f _))

theorem Value.mapAnnotation_erasure (v : Value) (f : Capture → Capture) :
    ValueErasure v (v.mapAnnotation f) := by
  induction v using Value.rec
    (motive_2 := fun γ => List.Forall₂ ValueErasure γ (γ.map (Value.mapAnnotation f)))
  all_goals simp only [Value.mapAnnotation, List.map_cons, List.map_nil]
  all_goals try solve_by_elim (config := {maxDepth := 6}) [ValueErasure.unit,
    ValueErasure.credit, ValueErasure.pair, ValueErasure.inl, ValueErasure.inr,
    List.Forall₂.nil, List.Forall₂.cons]
  case closure _ _ _ ih => exact .closure ih (Term.erase_mapAnnotation _ _).symm

theorem References.closure_iff {γ Γ t l} :
    References (.closure γ Γ t) l ↔ EnvironmentReferences γ l :=
  ⟨fun h => by cases h with | closure hv hr => exact ⟨_, hv, hr⟩,
   fun ⟨_, hv, hr⟩ => .closure hv hr⟩

theorem ValueErasure.references {v w} (h : ValueErasure v w) :
    ∀ l, References v l ↔ References w l := by
  induction h using ValueErasure.rec
    (motive_2 := fun γ δ _ => ∀ l, EnvironmentReferences γ l ↔ EnvironmentReferences δ l)
  case unit | credit | nil => simp
  case cons _ _ iha ihl l =>
    simpa only [EnvironmentReferences, List.mem_cons, exists_prop, or_and_right,
      exists_or, exists_eq_left] using or_congr (iha l) (ihl l)
  case closure _ _ ih => simpa only [References.closure_iff] using ih
  all_goals intro l
  all_goals constructor <;> intro hl <;> cases hl
  all_goals aesop (add 50% constructors References)

@[simp] theorem Value.references_mapAnnotation (v : Value) (f : Capture → Capture) (l) :
    References (v.mapAnnotation f) l ↔ References v l :=
  ((v.mapAnnotation_erasure f).references l).symm

@[simp] theorem Value.valid_mapAnnotation (v : Value) (f : Capture → Capture) (w : World) :
    w.ValidValue (v.mapAnnotation f) ↔ w.ValidValue v := by
  simp only [World.ValidValue, Value.references_mapAnnotation]

@[simp] theorem environmentReferences_mapAnnotation (γ : Environment) (f : Capture → Capture) (l) :
    EnvironmentReferences (γ.map (Value.mapAnnotation f)) l ↔ EnvironmentReferences γ l := by
  simp [EnvironmentReferences]

@[simp] theorem World.compatible_mapAnnotation (w : World) (s : Supplies)
    (γ : Environment) (f : Capture → Capture) :
    w.Compatible s (γ.map (Value.mapAnnotation f)) ↔ w.Compatible s γ := by
  simp only [World.Compatible, environmentReferences_mapAnnotation]

theorem Eval.substTypes {s γ t v} (h : Eval s γ t v) (σ : Substitution) :
    Eval s (γ.map (fun v => v.substTypes σ)) (t.substTypes σ) (v.substTypes σ) :=
  h.mapAnnotation _

theorem Value.substCapturedTypes_erasure (v : Value) (σ : Substitution) :
    ValueErasure v (v.substCapturedTypes σ) := by
  induction v using Value.rec
    (motive_2 := fun γ => ∀ f : Nat → Substitution,
      List.Forall₂ ValueErasure γ
        ((γ.map Value.substCapturedTypes).mapIdx fun i subst => subst (f i))) generalizing σ
  all_goals simp only [Value.substCapturedTypes, List.map_cons, List.map_nil,
    List.mapIdx_cons, List.mapIdx_nil]
  all_goals try solve_by_elim (config := {maxDepth := 6}) [ValueErasure.unit,
    ValueErasure.credit, ValueErasure.pair, ValueErasure.inl, ValueErasure.inr,
    List.Forall₂.nil, List.Forall₂.cons]
  case closure _ _ _ ih => exact .closure (ih _) (Term.erase_mapAnnotation _ _).symm

@[simp] theorem Value.references_substCapturedTypes (v : Value) (σ : Substitution) (l) :
    References (v.substCapturedTypes σ) l ↔ References v l :=
  ((v.substCapturedTypes_erasure σ).references l).symm

@[simp] theorem Value.valid_substCapturedTypes (v : Value) (σ : Substitution) (w : World) :
    w.ValidValue (v.substCapturedTypes σ) ↔ w.ValidValue v := by
  simp only [World.ValidValue, Value.references_substCapturedTypes]

theorem SchemeValue.subst_erasure (p : SchemeValue) (σ : Substitution) :
    ValueErasure p.value (p.subst σ).value := p.value.substCapturedTypes_erasure _

/-- Evaluation is insensitive to this change of metadata. The result is related
by erasure; no unproved equality with a chosen result annotation is asserted. -/
theorem Eval.substCapturedTypes_erasure {s γ t v} (h : Eval s γ t v) (σ : Substitution) :
    ∃ u, Eval s (γ.map (fun v => v.substCapturedTypes σ)) (t.substTypes σ) u ∧
      ValueErasure v u := by
  apply h.annotation_erasure ?_ (Term.erase_mapAnnotation _ _).symm
  clear h
  induction γ with
  | nil => exact .nil
  | cons v γ ih => exact .cons (v.substCapturedTypes_erasure σ) ih

end ModalityInference
