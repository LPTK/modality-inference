import ModalityInference.Proofs.GroundFresh
import ModalityInference.Proofs.GroundSkolemization
import ModalityInference.Proofs.GenerationSupplies

/-! Ground instances extend the generator's assignment at its fresh identifiers,
preserving all identifiers allocated before the instantiation. -/
namespace ModalityInference

theorem SolverGround.AgreesBelow.mono {ρ η : GroundAssignment} {nt nm nt' nm'}
    (h : SolverGround.AgreesBelow η ρ nt nm) (ht : nt' ≤ nt) (hm : nm' ≤ nm) :
    SolverGround.AgreesBelow η ρ nt' nm' :=
  ⟨fun v hv => h.1 v (hv.trans_le ht), fun v hv => h.2 v (hv.trans_le hm)⟩

theorem SolverGround.AgreesBelow.trans {ρ η ζ : GroundAssignment} {nt nm}
    (h : SolverGround.AgreesBelow ζ η nt nm) (h' : SolverGround.AgreesBelow η ρ nt nm) :
    SolverGround.AgreesBelow ζ ρ nt nm :=
  ⟨fun v hv => (h.1 v hv).trans (h'.1 v hv), fun v hv => (h.2 v hv).trans (h'.2 v hv)⟩

theorem InferenceState.freshType_model (s : InferenceState) (ρ : GroundAssignment)
    (a : GroundTy) : ∃ η, (s.freshType).1.realize η = some a ∧
      SolverGround.AgreesBelow η ρ s.nextType s.nextMode := by
  refine ⟨ρ.setType (.flex s.nextType) a, ?_, ?_, fun _ _ => rfl⟩
  · simp [InferenceState.freshType, TypeExpr.realize, GroundAssignment.setType]
  · intro v hv
    have hn : v ≠ .flex s.nextType := by intro h; subst v; exact Nat.lt_irrefl _ hv
    simp [GroundAssignment.setType, hn]

def GroundAssignment.setMode (ρ : GroundAssignment) (v : ModVar) (m : Mode) : GroundAssignment :=
  {ρ with modes := fun w => if w = v then m else ρ.modes w}

theorem InferenceState.freshMode_model (s : InferenceState) (ρ : GroundAssignment)
    (m : Mode) : ∃ η, (s.freshMode).1.eval (some ∘ η.modes) = some m ∧
      SolverGround.AgreesBelow η ρ s.nextType s.nextMode := by
  refine ⟨ρ.setMode (.flex s.nextMode) m, ?_, (fun _ _ => rfl), ?_⟩
  · simp [InferenceState.freshMode, ModExpr.eval, GroundAssignment.setMode]
  · intro v hv
    have hn : v ≠ .flex s.nextMode := by intro h; subst v; exact Nat.lt_irrefl _ hv
    simp [GroundAssignment.setMode, hn]

def Scheme.freshAssignment (s : Scheme) (nt nm : Nat)
    (ambient values : GroundAssignment) : GroundAssignment :=
  ⟨fun v => match v with
    | .rigid _ => ambient.types v
    | .flex k => if nt ≤ k then
        (s.typeParams[k - nt]?).elim (ambient.types v) (fun n => values.types (.flex n))
      else ambient.types v,
   fun v => match v with
    | .rigid _ => ambient.modes v
    | .flex k => if nm ≤ k then
        (s.modParams[k - nm]?).elim (ambient.modes v) (fun n => values.modes (.flex n))
      else ambient.modes v⟩

theorem Scheme.freshAssignment_agreesBelow (s : Scheme) (nt nm : Nat)
    (ρ η : GroundAssignment) : SolverGround.AgreesBelow (s.freshAssignment nt nm ρ η) ρ nt nm := by
  constructor <;> intro v hv <;> cases v <;>
    simp_all [Scheme.freshAssignment, TypeVar.index, ModVar.index, Nat.not_le_of_gt]

theorem Scheme.freshAssignment_type_at (s : Scheme) (nt nm : Nat)
    (ρ η : GroundAssignment) {i p : Nat} (h : s.typeParams[i]? = some p) :
    (s.freshAssignment nt nm ρ η).types (.flex (nt + i)) = η.types (.flex p) := by
  simp [Scheme.freshAssignment, h]

theorem Scheme.freshAssignment_mode_at (s : Scheme) (nt nm : Nat)
    (ρ η : GroundAssignment) {i p : Nat} (h : s.modParams[i]? = some p) :
    (s.freshAssignment nt nm ρ η).modes (.flex (nm + i)) = η.modes (.flex p) := by
  simp [Scheme.freshAssignment, h]

theorem GroundInstantiates.freshened_type {s : Scheme} {ρ η : GroundAssignment}
    (h : GroundInstantiates ρ s η) {nt nm : Nat} {v : TypeVar} (hf : v.index < nt) :
    ((s.freshSubstitution nt nm).type v).realize (s.freshAssignment nt nm ρ η) =
      some (η.types v) := by
  cases v
  case flex n =>
    cases he : (s.freshSubstitution nt nm).types.lookup n
    case some a =>
      obtain ⟨i, hi, rfl⟩ := lookup_fresh_some (xs := s.typeParams)
        (f := fun i => (.var (.flex (nt + i)) : Ty)) he
      simp [Substitution.type, he, TypeExpr.realize, s.freshAssignment_type_at nt nm ρ η hi]
    case none =>
      have hn := lookup_fresh_none (xs := s.typeParams)
        (f := fun i => (.var (.flex (nt + i)) : Ty)) he
      simpa [Substitution.type, he, TypeExpr.realize,
        (s.freshAssignment_agreesBelow nt nm ρ η).1 _ hf] using
        congrArg some (h.1 (.flex n) (by simpa using hn)).symm
  case rigid n =>
    simpa [Substitution.type, TypeExpr.realize, Scheme.freshAssignment] using
      congrArg some (h.1 (.rigid n) (by simp)).symm

theorem GroundInstantiates.freshened_mode {s : Scheme} {ρ η : GroundAssignment}
    (h : GroundInstantiates ρ s η) {nt nm : Nat} {v : ModVar} (hf : v.index < nm) :
    ((s.freshSubstitution nt nm).mode v).eval (some ∘ (s.freshAssignment nt nm ρ η).modes) =
      some (η.modes v) := by
  cases v
  case flex n =>
    cases he : (s.freshSubstitution nt nm).modes.lookup n
    case some a =>
      obtain ⟨i, hi, rfl⟩ := lookup_fresh_some (xs := s.modParams)
        (f := fun i => (.var (.flex (nm + i)) : ModExpr)) he
      simp [Substitution.mode, he, ModExpr.eval, s.freshAssignment_mode_at nt nm ρ η hi]
    case none =>
      have hn := lookup_fresh_none (xs := s.modParams)
        (f := fun i => (.var (.flex (nm + i)) : ModExpr)) he
      simpa [Substitution.mode, he, ModExpr.eval,
        (s.freshAssignment_agreesBelow nt nm ρ η).2 _ hf] using
        congrArg some (h.2.1 (.flex n) (by simpa using hn)).symm
  case rigid n =>
    simpa [Substitution.mode, ModExpr.eval, Scheme.freshAssignment] using
      congrArg some (h.2.1 (.rigid n) (by simp)).symm

theorem GroundInstantiates.freshen {s : Scheme} {ρ η : GroundAssignment}
    (h : GroundInstantiates ρ s η) {nt nm : Nat} (hb : s.Bounded nt nm) :
    let ζ := s.freshAssignment nt nm ρ η
    (s.instantiate nt nm).2.realize ζ = s.body.realize η ∧
      GroundModels ζ (s.instantiate nt nm).1 := by
  have ht : ∀ v ∈ s.body.typeVars ∪ s.bounds.typeVars,
      ((s.freshSubstitution nt nm).type v).realize (s.freshAssignment nt nm ρ η) =
        some (η.types v) := by
    intro v hv
    exact h.freshened_type ((Finset.mem_union.mp hv).elim
      (((s.body.bounded_iff nt nm).mp hb.1).1 v)
      (((s.bounds.bounded_iff nt nm).mp hb.2).1 v))
  have hm : ∀ v ∈ s.body.modVars ∪ s.bounds.modVars,
      ((s.freshSubstitution nt nm).mode v).eval
        (some ∘ (s.freshAssignment nt nm ρ η).modes) = some (η.modes v) := by
    intro v hv
    exact h.freshened_mode ((Finset.mem_union.mp hv).elim
      (((s.body.bounded_iff nt nm).mp hb.1).2 v)
      (((s.bounds.bounded_iff nt nm).mp hb.2).2 v))
  exact ⟨s.body.realize_subst_congr
    (fun v hv => ht v (Finset.mem_union.mpr (.inl hv)))
    (fun v hv => hm v (Finset.mem_union.mpr (.inl hv))),
    (GroundModels.subst_congr s.bounds
      (fun v hv => ht v (Finset.mem_union.mpr (.inr hv)))
      (fun v hv => hm v (Finset.mem_union.mpr (.inr hv)))).mpr h.2.2⟩

theorem InferenceState.instantiate_model {s : InferenceState} {scheme : Scheme}
    {ρ η : GroundAssignment} {t : GroundTy}
    (hs : s.constraints.Bounded s.nextType s.nextMode)
    (hm : GroundModels ρ s.constraints)
    (hb : scheme.Bounded s.nextType s.nextMode)
    (hi : GroundInstantiates ρ scheme η) (ht : scheme.body.realize η = some t) :
    ∃ ζ, (s.instantiate scheme).1.realize ζ = some t ∧
      GroundModels ζ (s.instantiate scheme).2.constraints ∧
      SolverGround.AgreesBelow ζ ρ s.nextType s.nextMode := by
  let ζ := scheme.freshAssignment s.nextType s.nextMode ρ η
  have hf := hi.freshen hb
  have ha := scheme.freshAssignment_agreesBelow s.nextType s.nextMode ρ η
  refine ⟨ζ, hf.1.trans ht, ?_, ha⟩
  have hg : GroundModels ζ (scheme.instantiate s.nextType s.nextMode).2.wellFormedBounds :=
    ((scheme.instantiate s.nextType s.nextMode).2.wellFormedBounds_ground ζ).mpr
      (((scheme.instantiate s.nextType s.nextMode).2.wellFormedBounds_spec ζ).mpr
        (by rw [hf.1, ht]; rfl))
  intro c hc
  simp only [InferenceState.instantiate, List.mem_append] at hc
  exact hc.elim (fun h => h.elim (ha.models hs hm c) (hf.2 c)) (hg c)

end ModalityInference
