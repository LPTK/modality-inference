import ModalityInference.Proofs.InstanceDefinedness

/-! Defined scheme instances preserve all images used by the body and bounds.
Unused quantified images can be replaced by identities without changing either
instantiated judgment or the exact substitution domain. -/
namespace ModalityInference

private theorem lookup_map_key (xs : List (Nat × α)) (f : Nat → α → β) (n : Nat) :
    (xs.map (fun p => (p.1, f p.1 p.2))).lookup n = (xs.lookup n).map (f n) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨k, a⟩
    cases he : n == k with
    | false => simp [List.lookup_cons, he, ih]
    | true =>
      have h : n = k := by simpa using he
      subst k
      simp

def Scheme.definedInstance (s : Scheme) (σ : Substitution) : Substitution where
  types := σ.types.map fun (n, a) =>
    (n, if TypeVar.flex n ∈ s.body.typeVars ∪ s.bounds.typeVars then a else .var (.flex n))
  modes := σ.modes.map fun (n, m) =>
    (n, if ModVar.flex n ∈ s.body.modVars ∪ s.bounds.modVars then m else .var (.flex n))

@[simp] theorem Scheme.definedInstance_type_keys (s : Scheme) (σ : Substitution) :
    (s.definedInstance σ).types.map Prod.fst = σ.types.map Prod.fst := by
  simp [definedInstance, List.map_map, Function.comp_def]

@[simp] theorem Scheme.definedInstance_mode_keys (s : Scheme) (σ : Substitution) :
    (s.definedInstance σ).modes.map Prod.fst = σ.modes.map Prod.fst := by
  simp [definedInstance, List.map_map, Function.comp_def]

theorem Scheme.definedInstance_type (s : Scheme) (σ : Substitution) (v : TypeVar) :
    (s.definedInstance σ).type v =
      if v ∈ s.body.typeVars ∪ s.bounds.typeVars then σ.type v else .var v := by
  cases v with
  | rigid n => simp [Substitution.type]
  | flex n =>
    have he := lookup_map_key σ.types
      (fun k a => if TypeVar.flex k ∈ s.body.typeVars ∪ s.bounds.typeVars
        then a else .var (.flex k)) n
    change (s.definedInstance σ).types.lookup n = _ at he
    simp only [Substitution.type]
    rw [he]
    cases σ.types.lookup n <;> split <;> simp_all

theorem Scheme.definedInstance_mode (s : Scheme) (σ : Substitution) (v : ModVar) :
    (s.definedInstance σ).mode v =
      if v ∈ s.body.modVars ∪ s.bounds.modVars then σ.mode v else .var v := by
  cases v with
  | rigid n => simp [Substitution.mode]
  | flex n =>
    have he := lookup_map_key σ.modes
      (fun k m => if ModVar.flex k ∈ s.body.modVars ∪ s.bounds.modVars
        then m else .var (.flex k)) n
    change (s.definedInstance σ).modes.lookup n = _ at he
    simp only [Substitution.mode]
    rw [he]
    cases σ.modes.lookup n <;> split <;> simp_all

@[simp] theorem Scheme.definedInstance_body (s : Scheme) (σ : Substitution) :
    (s.definedInstance σ).ty s.body = σ.ty s.body := by
  apply TypeExpr.subst_congr
  · intro v hv; simp [s.definedInstance_type σ, hv]
  · intro v hv; simp [s.definedInstance_mode σ, hv]

private theorem Scheme.definedInstance_constraint (s : Scheme) (σ : Substitution)
    (c : Constraint) (hc : c ∈ s.bounds) :
    (s.definedInstance σ).constraint c = σ.constraint c := by
  have ht : ∀v∈c.typeVars, (s.definedInstance σ).type v = σ.type v := by
    intro v hv
    rw [s.definedInstance_type σ, if_pos]
    exact Finset.mem_union_right _ ((s.bounds.mem_typeVars_iff v).mpr ⟨c, hc, hv⟩)
  have hm : ∀v∈c.modVars, (s.definedInstance σ).mode v = σ.mode v := by
    intro v hv
    rw [s.definedInstance_mode σ, if_pos]
    exact Finset.mem_union_right _ ((s.bounds.mem_modVars_iff v).mpr ⟨c, hc, hv⟩)
  have hh := c.subst_congr ht hm
  cases c <;> try exact hh
  case equal v a =>
    have he : (s.definedInstance σ).ty a = σ.ty a :=
      a.subst_congr (fun w hw => ht w (by simp [Constraint.typeVars, hw])) hm
    cases v with
    | rigid n => simp [Substitution.constraint, he]
    | flex n =>
      have hv : TypeVar.flex n ∈ s.body.typeVars ∪ s.bounds.typeVars :=
        Finset.mem_union_right _ ((s.bounds.mem_typeVars_iff (.flex n)).mpr
          ⟨.equal (.flex n) a, hc, by simp [Constraint.typeVars]⟩)
      have hk := lookup_map_key σ.types
        (fun k t => if TypeVar.flex k ∈ s.body.typeVars ∪ s.bounds.typeVars
          then t else .var (.flex k)) n
      change (s.definedInstance σ).types.lookup n = _ at hk
      simp only [hv, if_true] at hk
      simp only [Substitution.constraint, hk, he]
      cases σ.types.lookup n <;> rfl

@[simp] theorem Scheme.definedInstance_bounds (s : Scheme) (σ : Substitution) :
    (s.definedInstance σ).bounds s.bounds = σ.bounds s.bounds := by
  apply List.map_congr_left
  exact s.definedInstance_constraint σ

/-- The used-image guards are enough to obtain a fully defined substitution;
no totality is required of images for unused parameters in the supplied action. -/
theorem Scheme.definedInstance_wellFormed {s : Scheme} {σ : Substitution} {Δ : Bounds}
    (hb : EntailsAll Δ (σ.bounds s.bounds)) (hd : (σ.ty s.body).DefinedUnder Δ) :
    (s.definedInstance σ).WellFormedUnder Δ := by
  have hs := Scheme.instance_support_defined hb hd
  constructor
  · intro v
    rw [s.definedInstance_type σ]
    split
    · next hv => exact hs.1 v hv
    · simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]
  · intro v
    rw [s.definedInstance_mode σ]
    split
    · next hv => exact hs.2 v hv
    · exact fun _ _ => rfl

theorem Instantiates.definedInstance {s : Scheme} {σ : Substitution}
    (h : Instantiates s σ) : Instantiates s (s.definedInstance σ) := by
  simpa only [Instantiates, Scheme.definedInstance_type_keys,
    Scheme.definedInstance_mode_keys] using h

/-- Every guarded body instance has a fully defined witness with exactly the
same type, bounds, and quantified domain. -/
theorem Instantiates.exists_wellFormed {s : Scheme} {σ : Substitution} {Δ : Bounds}
    (hi : Instantiates s σ) (hb : EntailsAll Δ (σ.bounds s.bounds))
    (hd : (σ.ty s.body).DefinedUnder Δ) :
    ∃ τ, Instantiates s τ ∧ τ.WellFormedUnder Δ ∧
      τ.ty s.body = σ.ty s.body ∧ τ.bounds s.bounds = σ.bounds s.bounds :=
  ⟨s.definedInstance σ, hi.definedInstance, Scheme.definedInstance_wellFormed hb hd,
    s.definedInstance_body σ, s.definedInstance_bounds σ⟩

/-- The normalized witness satisfies the full instance discipline. -/
theorem Instantiates.definedInstance_under {s : Scheme} {σ : Substitution} {Δ : Bounds}
    (hi : Instantiates s σ) (hb : EntailsAll Δ (σ.bounds s.bounds))
    (hd : (σ.ty s.body).DefinedUnder Δ) :
    InstantiatesUnder Δ s (s.definedInstance σ) where
  domain := hi.definedInstance
  images := Scheme.definedInstance_wellFormed hb hd
  body := by simpa only [s.definedInstance_body σ] using hd

/-- Guarded instantiation admits an admissible witness without changing the
instantiated body or any declared constraint. -/
theorem Instantiates.exists_under {s : Scheme} {σ : Substitution} {Δ : Bounds}
    (hi : Instantiates s σ) (hb : EntailsAll Δ (σ.bounds s.bounds))
    (hd : (σ.ty s.body).DefinedUnder Δ) :
    ∃ τ, InstantiatesUnder Δ s τ ∧
      τ.ty s.body = σ.ty s.body ∧ τ.bounds s.bounds = σ.bounds s.bounds :=
  ⟨s.definedInstance σ, hi.definedInstance_under hb hd,
    s.definedInstance_body σ, s.definedInstance_bounds σ⟩

end ModalityInference
