import ModalityInference.Proofs.InstanceDefinedness
import ModalityInference.Proofs.SkolemSubstitution

/-! Syntactic instantiation of declarative scheme comparisons. -/
namespace ModalityInference

def Scheme.instanceTypeMap (s : Scheme) (θ : Substitution) (nt : Nat) : TypeVar → Ty
  | .flex n => .var (.flex n)
  | .rigid k => if nt ≤ k then
      (s.typeParams[k - nt]?).elim (.var (.rigid k)) (fun p =>
        if .flex p ∈ s.body.typeVars ∪ s.bounds.typeVars then θ.type (.flex p) else .unit)
    else .var (.rigid k)

def Scheme.instanceModeMap (s : Scheme) (θ : Substitution) (nm : Nat) : ModVar → ModExpr
  | .flex n => .var (.flex n)
  | .rigid k => if nm ≤ k then
      (s.modParams[k - nm]?).elim (.var (.rigid k)) (fun p =>
        if .flex p ∈ s.body.modVars ∪ s.bounds.modVars then θ.mode (.flex p) else .epsilon)
    else .var (.rigid k)

theorem Scheme.instanceTypeMap_lt (s : Scheme) (θ : Substitution) (nt : Nat)
    {v : TypeVar} (hv : v.index < nt) : s.instanceTypeMap θ nt v = .var v := by
  cases v <;> simp_all [instanceTypeMap, TypeVar.index, Nat.not_le_of_gt]

theorem Scheme.instanceModeMap_lt (s : Scheme) (θ : Substitution) (nm : Nat)
    {v : ModVar} (hv : v.index < nm) : s.instanceModeMap θ nm v = .var v := by
  cases v <;> simp_all [instanceModeMap, ModVar.index, Nat.not_le_of_gt]

theorem Scheme.instanceTypeMap_defined {s : Scheme} {θ : Substitution} {Δ : Bounds}
    (hb : EntailsAll Δ (θ.bounds s.bounds)) (hd : (θ.ty s.body).DefinedUnder Δ)
    (nt : Nat) (v : TypeVar) : (s.instanceTypeMap θ nt v).DefinedUnder Δ := by
  cases v <;> simp only [instanceTypeMap]
  case rigid k =>
    split
    · cases s.typeParams[k - nt]? with
      | none => simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]
      | some p =>
        dsimp only [Option.elim]
        split
        · exact (s.instance_support_defined hb hd).1 _ ‹_›
        · simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]
    · simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]
  case flex n => simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]

theorem Scheme.instanceModeMap_defined {s : Scheme} {θ : Substitution} {Δ : Bounds}
    (hb : EntailsAll Δ (θ.bounds s.bounds)) (hd : (θ.ty s.body).DefinedUnder Δ)
    (nm : Nat) (v : ModVar) (η : ModVar → Mode) (hη : ModeModels Δ η) :
    (s.instanceModeMap θ nm v).WellFormed η := by
  cases v <;> simp only [instanceModeMap]
  case rigid k =>
    split
    · cases s.modParams[k - nm]? with
      | none => rfl
      | some p =>
        dsimp only [Option.elim]
        split
        · exact (s.instance_support_defined hb hd).2 _ ‹_› η hη
        · rfl
    · rfl
  case flex n => rfl

theorem Instantiates.skolemized_type_map {s : Scheme} {θ : Substitution}
    (hi : Instantiates s θ) {nt nm : Nat} {v : TypeVar}
    (hf : v.index < nt) (hv : v ∈ s.body.typeVars ∪ s.bounds.typeVars) :
    ((s.freshSubstitution nt nm true).type v).subst
      (s.instanceTypeMap θ nt) (s.instanceModeMap θ nm) = θ.type v := by
  cases v
  case flex n =>
    cases he : (s.freshSubstitution nt nm true).types.lookup n
    case some a =>
      obtain ⟨i, hi, rfl⟩ := lookup_fresh_some (xs := s.typeParams)
        (f := fun i => (.var (.rigid (nt + i)) : Ty)) he
      simp_all [Substitution.type, TypeExpr.subst, Scheme.instanceTypeMap]
    case none =>
      have hn := lookup_fresh_none (xs := s.typeParams)
        (f := fun i => (.var (.rigid (nt + i)) : Ty)) he
      simpa [Substitution.type, he, TypeExpr.subst, Scheme.instanceTypeMap] using
        (θ.type_fresh (fun hmem => hn (hi.1.mem_iff.mp hmem))).symm
  case rigid n =>
    exact s.instanceTypeMap_lt θ nt hf

theorem Instantiates.skolemized_mode_map {s : Scheme} {θ : Substitution}
    (hi : Instantiates s θ) {nt nm : Nat} {v : ModVar}
    (hf : v.index < nm) (hv : v ∈ s.body.modVars ∪ s.bounds.modVars) :
    ((s.freshSubstitution nt nm true).mode v).subst (s.instanceModeMap θ nm) =
      θ.mode v := by
  cases v
  case flex n =>
    cases he : (s.freshSubstitution nt nm true).modes.lookup n
    case some a =>
      obtain ⟨i, hi, rfl⟩ := lookup_fresh_some (xs := s.modParams)
        (f := fun i => (.var (.rigid (nm + i)) : ModExpr)) he
      simp_all [Substitution.mode, ModExpr.subst, Scheme.instanceModeMap]
    case none =>
      have hn := lookup_fresh_none (xs := s.modParams)
        (f := fun i => (.var (.rigid (nm + i)) : ModExpr)) he
      simpa [Substitution.mode, he, ModExpr.subst, Scheme.instanceModeMap] using
        (θ.mode_fresh (fun hmem => hn (hi.2.mem_iff.mp hmem))).symm
  case rigid n => exact s.instanceModeMap_lt θ nm hf

theorem Instantiates.skolemMap {Δ target θ} {source : Scheme} (hi : Instantiates target θ)
    (hb : EntailsAll Δ (θ.bounds target.bounds)) (hd : (θ.ty target.body).DefinedUnder Δ) :
    let (nt, nm) := source.subsumptionIndices Δ target
    let κ := target.freshSubstitution nt nm true
    ∃ ts ms, JudgmentMap (Δ ++ (κ.bounds target.bounds).assumptions) Δ ts ms ∧
      (κ.ty target.body).subst ts ms = θ.ty target.body ∧
      (∀ v ∈ source.body.typeVars ∪ source.bounds.typeVars, ts v = .var v) ∧
      (∀ v ∈ source.body.modVars ∪ source.bounds.modVars, ms v = .var v) := by
  let nt := (source.subsumptionIndices Δ target).1
  let nm := (source.subsumptionIndices Δ target).2
  let κ := target.freshSubstitution nt nm true
  let ts := target.instanceTypeMap θ nt
  let ms := target.instanceModeMap θ nm
  change ∃ ts ms, JudgmentMap (Δ ++ (κ.bounds target.bounds).assumptions) Δ ts ms ∧
    (κ.ty target.body).subst ts ms = θ.ty target.body ∧
    (∀ v ∈ source.body.typeVars ∪ source.bounds.typeVars, ts v = .var v) ∧
    (∀ v ∈ source.body.modVars ∪ source.bounds.modVars, ms v = .var v)
  have ht : ∀ v ∈ target.body.typeVars ∪ target.bounds.typeVars,
      (κ.type v).subst ts ms = θ.type v := fun v hv =>
    hi.skolemized_type_map ((Scheme.lt_freshTypeIndex hv).trans_le
      ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _))) hv
  have hm : ∀ v ∈ target.body.modVars ∪ target.bounds.modVars,
      (κ.mode v).subst ms = θ.mode v := fun v hv =>
    hi.skolemized_mode_map ((Scheme.lt_freshModeIndex hv).trans_le
      ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _))) hv
  refine ⟨ts, ms, ?_, ?_, ?_, ?_⟩
  case refine_1 =>
    refine JudgmentMap.append_of_fixed
      (fun v hv => target.instanceTypeMap_lt θ nt
        (source.subsumptionIndices_type_fresh target ((Bounds.mem_typeVariables Δ v).mpr hv)))
      (fun v hv => target.instanceModeMap_lt θ nm
        (source.subsumptionIndices_mode_fresh target ((Bounds.mem_modeVariables Δ v).mpr hv)))
      (target.instanceTypeMap_defined hb hd nt)
      (fun v η hη => target.instanceModeMap_defined hb hd nm v η hη)
      (EntailsAll.subst_function_assumptions ?_)
    simp only [Substitution.bounds, EntailsAll, List.forall_mem_map]
    intro c hc
    rw [κ.constraint_subst, Constraint.subst_subst,
      c.subst_congr
        (fun v hv => ht v (Finset.mem_union_right _
          ((target.bounds.mem_typeVars_iff v).mpr ⟨c, hc, hv⟩)))
        (fun v hv => hm v (Finset.mem_union_right _
          ((target.bounds.mem_modVars_iff v).mpr ⟨c, hc, hv⟩)))]
    exact (θ.constraint_subst_entails c Δ).mp
      (hb _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
  case refine_2 =>
    simpa only [Substitution.ty, TypeExpr.subst_subst] using
      target.body.subst_congr
        (fun v hv => ht v (Finset.mem_union_left _ hv))
        (fun v hv => hm v (Finset.mem_union_left _ hv))
  case refine_3 =>
    exact fun v hv => target.instanceTypeMap_lt θ nt ((Scheme.lt_freshTypeIndex hv).trans_le
      ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _)))
  case refine_4 =>
    exact fun v hv => target.instanceModeMap_lt θ nm ((Scheme.lt_freshModeIndex hv).trans_le
      ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _)))

theorem Subsumes.instantiate {Δ source target θ} (h : Subsumes Δ source target)
    (hi : Instantiates target θ) (hb : EntailsAll Δ (θ.bounds target.bounds))
    (hd : (θ.ty target.body).DefinedUnder Δ) :
    ∃ σ, Instantiates source σ ∧ EntailsAll Δ (σ.bounds source.bounds) ∧
      Subtype Δ (σ.ty source.body) (θ.ty target.body) := by
  obtain ⟨σ, hσ, hcs, hab⟩ := h
  obtain ⟨ts, ms, hm, ht, hst, hsm⟩ := hi.skolemMap (source := source) hb hd
  refine ⟨σ.mapFunctions ts ms, hσ.mapFunctions ts ms,
    hm.bounds_entails σ source.bounds
      (fun v hv => hst v (Finset.mem_union_right _ hv))
      (fun v hv => hsm v (Finset.mem_union_right _ hv)) hcs, ?_⟩
  simpa only [σ.mapFunctions_ty ts ms source.body
    (fun v hv => hst v (Finset.mem_union_left _ hv))
    (fun v hv => hsm v (Finset.mem_union_left _ hv)), ht] using hm.subtype hab

end ModalityInference
