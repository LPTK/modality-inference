import ModalityInference.Proofs.GenerationInstantiation
import ModalityInference.Proofs.SolverExtension
import ModalityInference.Proofs.GroundSkolemization

/-! Transport scheme instances through capture-avoiding substitution. -/
namespace ModalityInference

def Scheme.substitutedInstance (s : Scheme) (σ θ : Substitution) : Substitution :=
  let (nt, nm) := s.fresheningIndices σ
  { types := (s.subst σ).typeParams.map fun k =>
      (k, σ.ty (θ.type (.flex ((s.typeParams[k - nt]?).getD 0))))
    modes := (s.subst σ).modParams.map fun k =>
      (k, (θ.mode (.flex ((s.modParams[k - nm]?).getD 0))).subst σ.mode) }

theorem Scheme.substitutedInstance_type_at (s : Scheme) (σ θ : Substitution) {i p : Nat}
    (hi : s.typeParams[i]? = some p) :
    (s.substitutedInstance σ θ).type (.flex ((s.fresheningIndices σ).1 + i)) =
      σ.ty (θ.type (.flex p)) := by
  have hk : (s.fresheningIndices σ).1 + i ∈ (s.subst σ).typeParams :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1, rfl⟩
  simp only [Scheme.substitutedInstance, Substitution.type, List.lookup_graph _ hk,
    Option.getD_some, Nat.add_sub_cancel_left, hi]

theorem Scheme.substitutedInstance_mode_at (s : Scheme) (σ θ : Substitution) {i p : Nat}
    (hi : s.modParams[i]? = some p) :
    (s.substitutedInstance σ θ).mode (.flex ((s.fresheningIndices σ).2 + i)) =
      (θ.mode (.flex p)).subst σ.mode := by
  have hk : (s.fresheningIndices σ).2 + i ∈ (s.subst σ).modParams :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1, rfl⟩
  simp only [Scheme.substitutedInstance, Substitution.mode, List.lookup_graph _ hk,
    Option.getD_some, Nat.add_sub_cancel_left, hi]

theorem Scheme.freshening_bounded (s : Scheme) (σ : Substitution) :
    s.Bounded (s.fresheningIndices σ).1 (s.fresheningIndices σ).2 ∧
      σ.Bounded (s.fresheningIndices σ).1 (s.fresheningIndices σ).2 := by
  have ht : ∀ v ∈ s.typeParams.map TypeVar.flex ++ s.body.typeVariables ++ s.bounds.typeVariables ++
      σ.types.flatMap (fun p => .flex p.1 :: p.2.typeVariables),
      v.index < (s.fresheningIndices σ).1 := (freshFold_bounds TypeVar.index _ 0).2
  have hm : ∀ v ∈ s.modParams.map ModVar.flex ++ s.body.modeVariables ++ s.bounds.modeVariables ++
      σ.types.flatMap (fun p => p.2.modeVariables) ++
      σ.modes.flatMap (fun p => .flex p.1 :: p.2.freeVariables),
      v.index < (s.fresheningIndices σ).2 := (freshFold_bounds ModVar.index _ 0).2
  simp only [List.mem_append, List.mem_flatMap, List.mem_cons, TypeExpr.mem_typeVariables,
    TypeExpr.mem_modeVariables, Bounds.mem_typeVariables, Bounds.mem_modeVariables,
    ModExpr.mem_freeVariables, or_imp, forall_and] at ht hm
  exact ⟨⟨(s.body.bounded_iff _ _).mpr ⟨ht.1.1.2, hm.1.1.1.2⟩,
    (s.bounds.bounded_iff _ _).mpr ⟨ht.1.2, hm.1.1.2⟩⟩,
    ⟨fun n a ha => ⟨ht.2 _ ⟨(n, a), ha, Or.inl rfl⟩,
      (a.bounded_iff _ _).mpr ⟨fun v hv => ht.2 v ⟨(n, a), ha, Or.inr hv⟩,
        fun v hv => hm.1.2 v ⟨(n, a), ha, hv⟩⟩⟩,
     fun n m hm' => ⟨hm.2 _ ⟨(n, m), hm', Or.inl rfl⟩,
      (m.bounded_iff _).mpr fun v hv => hm.2 v ⟨(n, m), hm', Or.inr hv⟩⟩⟩⟩

theorem Scheme.substitutedInstance_type_lt (s : Scheme) (σ θ : Substitution) {v : TypeVar}
    (hv : v.index < (s.fresheningIndices σ).1) :
    (s.substitutedInstance σ θ).type v = .var v := by
  cases v with
  | rigid _ => rfl
  | flex n =>
    apply Substitution.type_fresh
    simp only [Scheme.substitutedInstance, List.map_map, Function.comp_def, Scheme.subst,
      List.mem_map, List.mem_range, not_exists, not_and]
    exact fun x _ he => (Nat.not_lt.mpr (he ▸ Nat.le_add_right (s.fresheningIndices σ).1 x)) hv

theorem Scheme.substitutedInstance_mode_lt (s : Scheme) (σ θ : Substitution) {v : ModVar}
    (hv : v.index < (s.fresheningIndices σ).2) :
    (s.substitutedInstance σ θ).mode v = .var v := by
  cases v with
  | rigid _ => rfl
  | flex n =>
    apply Substitution.mode_fresh
    simp only [Scheme.substitutedInstance, List.map_map, Function.comp_def, Scheme.subst,
      List.mem_map, List.mem_range, not_exists, not_and]
    exact fun x _ he => (Nat.not_lt.mpr (he ▸ Nat.le_add_right (s.fresheningIndices σ).2 x)) hv

theorem Scheme.substitutedInstance_ty_fixed (s : Scheme) (σ θ : Substitution) {a : Ty}
    (ha : a.Bounded (s.fresheningIndices σ).1 (s.fresheningIndices σ).2) :
    (s.substitutedInstance σ θ).ty a = a :=
  (a.subst_congr
    (fun v hv => s.substitutedInstance_type_lt σ θ (((a.bounded_iff _ _).mp ha).1 v hv))
    (fun v hv => s.substitutedInstance_mode_lt σ θ (((a.bounded_iff _ _).mp ha).2 v hv))).trans a.subst_id

theorem Scheme.substitutedInstance_mode_fixed (s : Scheme) (σ θ : Substitution) {m : ModExpr}
    (hm : m.Bounded (s.fresheningIndices σ).2) :
    m.subst (s.substitutedInstance σ θ).mode = m :=
  (m.subst_congr
    (fun v hv => s.substitutedInstance_mode_lt σ θ ((m.bounded_iff _).mp hm v hv))).trans m.subst_id

theorem Substitution.Bounded.type_ge {σ : Substitution} {nt nm n}
    (h : σ.Bounded nt nm) (hn : nt ≤ n) : σ.type (.flex n) = .var (.flex n) :=
  σ.type_fresh fun hk =>
    let ⟨⟨k, a⟩, ha, he⟩ := List.mem_map.mp hk
    (Nat.not_lt.mpr hn) (he ▸ (h.types k a ha).1)

theorem Substitution.Bounded.mode_ge {σ : Substitution} {nt nm n}
    (h : σ.Bounded nt nm) (hn : nm ≤ n) : σ.mode (.flex n) = .var (.flex n) :=
  σ.mode_fresh fun hk =>
    let ⟨⟨k, m⟩, hm, he⟩ := List.mem_map.mp hk
    (Nat.not_lt.mpr hn) (he ▸ (h.modes k m hm).1)

theorem Instantiates.substitutedInstance_type {s : Scheme} {θ : Substitution}
    (h : Instantiates s θ) (σ : Substitution) {v : TypeVar}
    (hv : v.index < (s.fresheningIndices σ).1) :
    (s.substitutedInstance σ θ).ty (σ.ty ((s.binderRenaming σ).type v)) =
      σ.ty (θ.type v) := by
  cases v with
  | rigid n => rfl
  | flex n =>
    cases he : (s.binderRenaming σ).types.lookup n with
    | none =>
      have hn := lookup_fresh_none (xs := s.typeParams)
        (f := fun i => TypeExpr.var (.flex ((s.fresheningIndices σ).1 + i))) he
      rw [θ.type_fresh (fun hk => hn (h.1.mem_iff.mp hk)),
        show (s.binderRenaming σ).type (.flex n) = .var (.flex n) by
          simp only [Substitution.type, he, Option.getD_none]]
      exact s.substitutedInstance_ty_fixed σ θ ((s.freshening_bounded σ).2.type _ hv)
    | some a =>
      obtain ⟨i, hi, rfl⟩ := lookup_fresh_some (xs := s.typeParams)
        (f := fun i => TypeExpr.var (.flex ((s.fresheningIndices σ).1 + i))) he
      rw [show (s.binderRenaming σ).type (.flex n) =
        .var (.flex ((s.fresheningIndices σ).1 + i)) by simp only [Substitution.type, he, Option.getD_some]]
      change (s.substitutedInstance σ θ).ty (σ.type (.flex ((s.fresheningIndices σ).1 + i))) = _
      exact (congrArg (s.substitutedInstance σ θ).ty
        ((s.freshening_bounded σ).2.type_ge (Nat.le_add_right _ i))).trans
          (s.substitutedInstance_type_at σ θ hi)

theorem Instantiates.substitutedInstance_mode {s : Scheme} {θ : Substitution}
    (h : Instantiates s θ) (σ : Substitution) {v : ModVar}
    (hv : v.index < (s.fresheningIndices σ).2) :
    (((s.binderRenaming σ).mode v).subst σ.mode).subst (s.substitutedInstance σ θ).mode =
      (θ.mode v).subst σ.mode := by
  cases v with
  | rigid n => rfl
  | flex n =>
    cases he : (s.binderRenaming σ).modes.lookup n with
    | none =>
      have hn := lookup_fresh_none (xs := s.modParams)
        (f := fun i => ModExpr.var (.flex ((s.fresheningIndices σ).2 + i))) he
      rw [θ.mode_fresh (fun hk => hn (h.2.mem_iff.mp hk)),
        show (s.binderRenaming σ).mode (.flex n) = .var (.flex n) by
          simp only [Substitution.mode, he, Option.getD_none]]
      exact s.substitutedInstance_mode_fixed σ θ ((s.freshening_bounded σ).2.mode _ hv)
    | some m =>
      obtain ⟨i, hi, rfl⟩ := lookup_fresh_some (xs := s.modParams)
        (f := fun i => ModExpr.var (.flex ((s.fresheningIndices σ).2 + i))) he
      rw [show (s.binderRenaming σ).mode (.flex n) =
        .var (.flex ((s.fresheningIndices σ).2 + i)) by simp only [Substitution.mode, he, Option.getD_some]]
      change (σ.mode (.flex ((s.fresheningIndices σ).2 + i))).subst (s.substitutedInstance σ θ).mode = _
      exact (congrArg (fun m => m.subst (s.substitutedInstance σ θ).mode)
        ((s.freshening_bounded σ).2.mode_ge (Nat.le_add_right _ i))).trans
          (s.substitutedInstance_mode_at σ θ hi)

theorem Substitution.constraint_entails_congr_on {σ τ : Substitution} (c : Constraint) (Δ : Bounds)
    (ht : ∀ v ∈ c.typeVars, σ.type v = τ.type v)
    (hm : ∀ v ∈ c.modVars, σ.mode v = τ.mode v) :
    Entails Δ (σ.constraint c) ↔ Entails Δ (τ.constraint c) := by
  cases c <;> simp only [Constraint.typeVars, Constraint.modVars, Finset.mem_union,
    Finset.mem_insert, or_imp, forall_and, forall_eq] at ht hm
  case equal v a =>
    rw [σ.equal_entails Δ v a, τ.equal_entails Δ v a, ht.1,
      show σ.ty a = τ.ty a from a.subst_congr ht.2 hm]
  case sub a b | equiv a b =>
    simp only [Substitution.constraint, Constraint.subst,
      a.subst_congr ht.1 hm.1, b.subst_congr ht.2 hm.2]
  case mode a b =>
    simp only [Substitution.constraint, Constraint.subst, a.subst_congr hm.1, b.subst_congr hm.2]
  case defined m =>
    simp only [Substitution.constraint, Constraint.subst, m.subst_congr hm]

/-- Every original instance has a corresponding instance after capture-avoiding
scheme substitution, with exactly the same type and equivalent bound entailment.
No distinct-parameter or total-modality-image premise is required. -/
theorem Instantiates.substitute {s : Scheme} {θ : Substitution}
    (h : Instantiates s θ) (σ : Substitution) :
    ∃ θ', Instantiates (s.subst σ) θ' ∧
      θ'.ty (s.subst σ).body = σ.ty (θ.ty s.body) ∧
      ∀ Δ, EntailsAll Δ (θ'.bounds (s.subst σ).bounds) ↔
        EntailsAll Δ (σ.bounds (θ.bounds s.bounds)) := by
  refine ⟨s.substitutedInstance σ θ, ?_, ?_, ?_⟩
  · simp [Instantiates, Scheme.substitutedInstance, List.map_map, Function.comp_def]
  · rw [Scheme.subst_body_action, Substitution.ty_compose, Substitution.ty_compose]
    apply s.body.subst_congr
    · exact fun v hv => by
        simpa only [Scheme.substitutionAction, Substitution.type_compose] using
          h.substitutedInstance_type σ (((s.body.bounded_iff _ _).mp (s.freshening_bounded σ).1.1).1 v hv)
    · exact fun v hv => by
        simpa only [Scheme.substitutionAction, Substitution.mode_compose] using
          h.substitutedInstance_mode σ (((s.body.bounded_iff _ _).mp (s.freshening_bounded σ).1.1).2 v hv)
  · simp only [Scheme.subst_bounds_action, EntailsAll, Substitution.bounds,
      List.forall_mem_map, Substitution.constraint_compose]
    refine fun Δ => forall_congr' fun c => forall_congr' fun hc => ?_
    apply Substitution.constraint_entails_congr_on
    · exact fun v hv => by
        simpa only [Scheme.substitutionAction, Substitution.type_compose] using
          h.substitutedInstance_type σ
            (((c.bounded_iff _ _).mp ((s.freshening_bounded σ).1.2 c hc)).1 v hv)
    · exact fun v hv => by
        simpa only [Scheme.substitutionAction, Substitution.mode_compose] using
          h.substitutedInstance_mode σ
            (((c.bounded_iff _ _).mp ((s.freshening_bounded σ).1.2 c hc)).2 v hv)

theorem Typing.var_substitute {Γ : Context} {i s θ Δ σ}
    (hi : Γ[i]? = some (some s)) (hθ : Instantiates s θ)
    (hb : EntailsAll Δ (σ.bounds (θ.bounds s.bounds)))
    (hd : (σ.ty (θ.ty s.body)).DefinedUnder Δ) :
    Typing Δ (Γ.subst σ) (.var i) (σ.ty (θ.ty s.body)) := by
  obtain ⟨θ', hθ', ha, hb'⟩ := hθ.substitute σ
  rw [← ha] at hd ⊢
  exact .var (by simp [Context.subst, List.getElem?_map, hi]) hθ' ((hb' Δ).mpr hb)
    ((TypeExpr.definedUnder_iff_entails_wellFormed _ _).mp hd)

end ModalityInference
