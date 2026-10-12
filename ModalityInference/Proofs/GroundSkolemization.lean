import ModalityInference.Proofs.GroundSubstitution
import ModalityInference.Proofs.SubsumptionScope

/-! Realize target skolems while preserving the ambient bounds and all free
identifiers of the source scheme. Repeated parameter names require no new premise. -/
namespace ModalityInference

private theorem lookup_fresh_none {xs : List Nat} {f : Nat → A} {n : Nat}
    (h : (xs.zipIdx.map (fun (p, i) => (p, f i))).lookup n = none) : n ∉ xs := by
  intro hn
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hn
  simpa using List.lookup_eq_none_iff.mp h (n, f i)
    (List.mem_map.mpr ⟨(n, i), List.mk_mem_zipIdx_iff_getElem?.mpr hi, rfl⟩)

private theorem lookup_fresh_some {xs : List Nat} {f : Nat → A} {n : Nat} {a : A}
    (h : (xs.zipIdx.map (fun (p, i) => (p, f i))).lookup n = some a) :
    ∃ i, xs[i]? = some n ∧ a = f i := by
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp h
  obtain ⟨⟨p, i⟩, hi, hpi⟩ := List.mem_map.mp
    (show (n, a) ∈ xs.zipIdx.map (fun (p, i) => (p, f i)) by simp [he])
  exact ⟨i, (show p = n from congrArg Prod.fst hpi) ▸ List.mk_mem_zipIdx_iff_getElem?.mp hi,
    (congrArg Prod.snd hpi).symm⟩

def Scheme.skolemAssignment (s : Scheme) (nt nm : Nat)
    (ambient values : GroundAssignment) : GroundAssignment :=
  ⟨fun v => match v with
    | .flex _ => ambient.types v
    | .rigid k => if nt ≤ k then
        (s.typeParams[k - nt]?).elim (ambient.types v) (fun n => values.types (.flex n))
      else ambient.types v,
   fun v => match v with
    | .flex _ => ambient.modes v
    | .rigid k => if nm ≤ k then
        (s.modParams[k - nm]?).elim (ambient.modes v) (fun n => values.modes (.flex n))
      else ambient.modes v⟩

theorem Scheme.skolemAssignment_types_lt (s : Scheme) (nt nm : Nat)
    (ρ η : GroundAssignment) (v : TypeVar) (h : v.index < nt) :
    (s.skolemAssignment nt nm ρ η).types v = ρ.types v := by
  cases v <;> simp_all [Scheme.skolemAssignment, TypeVar.index, Nat.not_le_of_gt]

theorem Scheme.skolemAssignment_modes_lt (s : Scheme) (nt nm : Nat)
    (ρ η : GroundAssignment) (v : ModVar) (h : v.index < nm) :
    (s.skolemAssignment nt nm ρ η).modes v = ρ.modes v := by
  cases v <;> simp_all [Scheme.skolemAssignment, ModVar.index, Nat.not_le_of_gt]

theorem Scheme.skolemAssignment_type_at (s : Scheme) (nt nm : Nat)
    (ρ η : GroundAssignment) {i p : Nat} (h : s.typeParams[i]? = some p) :
    (s.skolemAssignment nt nm ρ η).types (.rigid (nt + i)) = η.types (.flex p) := by
  simp [Scheme.skolemAssignment, h]

theorem Scheme.skolemAssignment_mode_at (s : Scheme) (nt nm : Nat)
    (ρ η : GroundAssignment) {i p : Nat} (h : s.modParams[i]? = some p) :
    (s.skolemAssignment nt nm ρ η).modes (.rigid (nm + i)) = η.modes (.flex p) := by
  simp [Scheme.skolemAssignment, h]

theorem GroundInstantiates.skolemized_type {s : Scheme} {ρ η : GroundAssignment}
    (h : GroundInstantiates ρ s η) {nt nm : Nat} {v : TypeVar} (hf : v.index < nt) :
    ((s.freshSubstitution nt nm true).type v).realize (s.skolemAssignment nt nm ρ η) =
      some (η.types v) := by
  cases v
  case flex n =>
    cases he : (s.freshSubstitution nt nm true).types.lookup n
    case some a =>
      obtain ⟨i, hi, rfl⟩ := lookup_fresh_some (xs := s.typeParams)
        (f := fun i => (.var (.rigid (nt + i)) : Ty)) he
      simp [Substitution.type, he, TypeExpr.realize, s.skolemAssignment_type_at nt nm ρ η hi]
    case none =>
      have hn := lookup_fresh_none (xs := s.typeParams)
        (f := fun i => (.var (.rigid (nt + i)) : Ty)) he
      simpa [Substitution.type, he, TypeExpr.realize, Scheme.skolemAssignment] using
        congrArg some (h.1 (.flex n) (by simpa using hn)).symm
  case rigid n =>
    simpa [Substitution.type, TypeExpr.realize, s.skolemAssignment_types_lt nt nm ρ η _ hf] using
      congrArg some (h.1 (.rigid n) (by simp)).symm

theorem GroundInstantiates.skolemized_mode {s : Scheme} {ρ η : GroundAssignment}
    (h : GroundInstantiates ρ s η) {nt nm : Nat} {v : ModVar} (hf : v.index < nm) :
    ((s.freshSubstitution nt nm true).mode v).eval (some ∘ (s.skolemAssignment nt nm ρ η).modes) =
      some (η.modes v) := by
  cases v
  case flex n =>
    cases he : (s.freshSubstitution nt nm true).modes.lookup n
    case some a =>
      obtain ⟨i, hi, rfl⟩ := lookup_fresh_some (xs := s.modParams)
        (f := fun i => (.var (.rigid (nm + i)) : ModExpr)) he
      simp [Substitution.mode, he, ModExpr.eval, s.skolemAssignment_mode_at nt nm ρ η hi]
    case none =>
      have hn := lookup_fresh_none (xs := s.modParams)
        (f := fun i => (.var (.rigid (nm + i)) : ModExpr)) he
      simpa [Substitution.mode, he, ModExpr.eval, Scheme.skolemAssignment] using
        congrArg some (h.2.1 (.flex n) (by simpa using hn)).symm
  case rigid n =>
    simpa [Substitution.mode, ModExpr.eval, s.skolemAssignment_modes_lt nt nm ρ η _ hf] using
      congrArg some (h.2.1 (.rigid n) (by simp)).symm

theorem GroundInstantiates.skolemize {ρ η : GroundAssignment} {s t : Scheme} {Δ : Bounds}
    (h : GroundInstantiates ρ t η) (hΔ : GroundModels ρ Δ) :
    let (nt, nm) := s.subsumptionIndices Δ t
    let σ := t.freshSubstitution nt nm true
    ∃ θ, GroundModels θ (Δ ++ σ.bounds t.bounds) ∧
      (σ.ty t.body).realize θ = t.body.realize η ∧
      (∀ v ∈ s.freeTypes, ρ.types v = θ.types v) ∧
      (∀ v ∈ s.freeModes, ρ.modes v = θ.modes v) := by
  let nt := (s.subsumptionIndices Δ t).1
  let nm := (s.subsumptionIndices Δ t).2
  let θ := t.skolemAssignment nt nm ρ η
  let σ := t.freshSubstitution nt nm true
  change ∃ θ, GroundModels θ (Δ ++ σ.bounds t.bounds) ∧
    (σ.ty t.body).realize θ = t.body.realize η ∧
    (∀ v ∈ s.freeTypes, ρ.types v = θ.types v) ∧
    (∀ v ∈ s.freeModes, ρ.modes v = θ.modes v)
  have ht : ∀ v ∈ t.body.typeVars ∪ t.bounds.typeVars,
      (σ.type v).realize θ = some (η.types v) := fun v hv =>
    h.skolemized_type (nt := nt) (nm := nm) ((Scheme.lt_freshTypeIndex hv).trans_le
      ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _)))
  have hm : ∀ v ∈ t.body.modVars ∪ t.bounds.modVars,
      (σ.mode v).eval (some ∘ θ.modes) = some (η.modes v) := fun v hv =>
    h.skolemized_mode (nt := nt) (nm := nm) ((Scheme.lt_freshModeIndex hv).trans_le
      ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _)))
  refine ⟨θ, ?_, ?_, ?_, ?_⟩
  case refine_1 =>
    have hb : GroundModels θ (σ.bounds t.bounds) :=
      (GroundModels.subst_congr t.bounds
        (fun v hv => ht v (Finset.mem_union.mpr (.inr hv)))
        (fun v hv => hm v (Finset.mem_union.mpr (.inr hv)))).mpr h.2.2
    have hd : GroundModels θ Δ := (GroundModels.congr Δ
      (fun v hv => t.skolemAssignment_types_lt nt nm ρ η v
        (s.subsumptionIndices_type_fresh t ((Bounds.mem_typeVariables Δ v).mpr hv)))
      (fun v hv => t.skolemAssignment_modes_lt nt nm ρ η v
        (s.subsumptionIndices_mode_fresh t ((Bounds.mem_modeVariables Δ v).mpr hv)))).mpr hΔ
    exact fun c hc => (List.mem_append.mp hc).elim (hd c) (hb c)
  case refine_2 =>
    exact t.body.realize_subst_congr
      (fun v hv => ht v (Finset.mem_union.mpr (.inl hv)))
      (fun v hv => hm v (Finset.mem_union.mpr (.inl hv)))
  case refine_3 =>
    exact fun v hv => (t.skolemAssignment_types_lt nt nm ρ η v
      ((Scheme.lt_freshTypeIndex (Finset.mem_union.mpr ((s.mem_freeTypes_iff v).mp hv).1)).trans_le
        ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _)))).symm
  case refine_4 =>
    exact fun v hv => (t.skolemAssignment_modes_lt nt nm ρ η v
      ((Scheme.lt_freshModeIndex (Finset.mem_union.mpr ((s.mem_freeModes_iff v).mp hv).1)).trans_le
        ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _)))).symm

end ModalityInference
