import ModalityInference.Proofs.Normalization
import ModalityInference.Proofs.GroundSubstitution
import ModalityInference.Proofs.SubsumptionScope
import ModalityInference.Proofs.SubstitutionSupport

/-! Finite closed substitutions realizing ground models of flexible constraints. -/
namespace ModalityInference

theorem ModExpr.eval_closed (m : ModExpr) (hm : m.vars = ∅)
    (ρ η : ModVar → Option Mode) : m.eval ρ = m.eval η :=
  m.eval_congr (by simp [hm])

theorem TypeExpr.realize_closed_subtype {a : Ty} {ρ t}
    (ht : a.typeVars = ∅) (hm : a.modVars = ∅) (ha : a.realize ρ = some t) :
    Subtype [] a t.reify ∧ Subtype [] t.reify a := by
  induction a generalizing t
  case var => simp [typeVars] at ht
  case unit | credit =>
    cases ha
    exact ⟨.identityRev, .identity⟩
  case prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [typeVars, modVars, Finset.union_eq_empty] at ht hm
    simp only [realize, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ha
    obtain ⟨x, hx, y, hy, rfl⟩ := ha
    have ha := iha ht.1 hm.1 hx
    have hb := ihb ht.2 hm.2 hy
    first
    | exact ⟨(Subtype.prod_congr ha.1 hb.1).trans .identityRev,
        Subtype.identity.trans (.prod_congr ha.2 hb.2)⟩
    | exact ⟨(Subtype.sum_congr ha.1 hb.1).trans .identityRev,
        Subtype.identity.trans (.sum_congr ha.2 hb.2)⟩
    | exact ⟨(Subtype.fn_congr ha.2 hb.1).trans .identityRev,
        Subtype.identity.trans (.fn_congr ha.1 hb.2)⟩
  case modal a m ih =>
    simp only [typeVars, modVars, Finset.union_eq_empty] at ht hm
    simp only [realize, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ha
    obtain ⟨x, hx, n, hn, rfl⟩ := ha
    have ha := ih ht hm.1 hx
    have he : ∀ η, m.eval (some ∘ η) = some n :=
      fun η => (m.eval_closed hm.2 _ _).trans hn
    exact ⟨(Subtype.congr ha.1 (.valid fun η _ =>
        ⟨n, n, he η, rfl, Mode.le_refl n⟩)).trans (x.reify_modal_right n []),
      (x.reify_modal_left n []).trans (.congr ha.2 (.valid fun η _ =>
        ⟨n, n, rfl, he η, Mode.le_refl n⟩))⟩

theorem TypeExpr.definedUnder_of_closed_realize {a : Ty} {ρ t Δ}
    (hm : a.modVars = ∅) (ha : a.realize ρ = some t) : a.DefinedUnder Δ := by
  intro η _
  apply (a.wellFormedBounds_spec {ρ with modes := η}).mpr
  rw [a.realize_congr (ρ := {ρ with modes := η}) (η := ρ)
    (fun _ _ => rfl) (by simp [hm]), ha]
  rfl

theorem GroundSatisfies.entails_closed {ρ c} (h : GroundSatisfies ρ c)
    (ht : c.typeVars = ∅) (hm : c.modVars = ∅) : Entails [] c := by
  cases c
  case equal => simp [Constraint.typeVars] at ht
  case sub a b | equiv a b =>
    simp only [Constraint.typeVars, Constraint.modVars, Finset.union_eq_empty] at ht hm
    obtain ⟨x, y, hx, hy, hs⟩ := h
    have ha := TypeExpr.realize_closed_subtype ht.1 hm.1 hx
    have hb := TypeExpr.realize_closed_subtype ht.2 hm.2 hy
    first
    | exact ⟨ha.1.trans (hs.trans hb.2),
        TypeExpr.definedUnder_of_closed_realize hm.1 hx,
        TypeExpr.definedUnder_of_closed_realize hm.2 hy⟩
    | exact ⟨ha.1.trans (hs.1.trans hb.2), hb.1.trans (hs.2.trans ha.2),
        TypeExpr.definedUnder_of_closed_realize hm.1 hx,
        TypeExpr.definedUnder_of_closed_realize hm.2 hy⟩
  case mode a b =>
    simp only [Constraint.modVars, Finset.union_eq_empty] at hm
    apply Submode.valid
    intro η _
    simpa only [GroundSatisfies, ModExpr.Below,
      a.eval_closed hm.1 (some ∘ η) (some ∘ ρ.modes),
      b.eval_closed hm.2 (some ∘ η) (some ∘ ρ.modes)] using h
  case defined a =>
    intro η _
    simpa only [ModExpr.WellFormed, a.eval_closed hm (some ∘ η) (some ∘ ρ.modes)] using h

@[simp] theorem GroundTy.reify_typeVars (a : GroundTy) : a.reify.typeVars = ∅ := by
  induction a <;> simp_all [reify, TypeExpr.typeVars]

@[simp] theorem GroundTy.reify_modVars (a : GroundTy) : a.reify.modVars = ∅ := by
  induction a <;> simp_all [reify, TypeExpr.modVars, ModExpr.vars]

theorem ModExpr.subst_closed {m : ModExpr} {σ : ModVar → ModExpr}
    (hm : ∀ v ∈ m.vars, (σ v).vars = ∅) : (m.subst σ).vars = ∅ := by
  induction m <;> simp_all [vars, subst, or_imp, forall_and]

theorem TypeExpr.subst_closed {a : Ty} {σ : TypeVar → Ty} {μ : ModVar → ModExpr}
    (ht : ∀ v ∈ a.typeVars, (σ v).typeVars = ∅ ∧ (σ v).modVars = ∅)
    (hm : ∀ v ∈ a.modVars, (μ v).vars = ∅) :
    (a.subst σ μ).typeVars = ∅ ∧ (a.subst σ μ).modVars = ∅ := by
  induction a <;> simp_all [typeVars, modVars, subst, or_imp, forall_and]
  exact ModExpr.subst_closed hm.2

theorem Substitution.constraint_closed {σ : Substitution} {c : Constraint}
    (ht : ∀ v ∈ c.typeVars, (σ.type v).typeVars = ∅ ∧ (σ.type v).modVars = ∅)
    (hm : ∀ v ∈ c.modVars, (σ.mode v).vars = ∅) :
    (σ.constraint c).typeVars = ∅ ∧ (σ.constraint c).modVars = ∅ := by
  cases c
  case sub a b | equiv a b =>
    have ha := TypeExpr.subst_closed (fun v hv => ht v (Finset.mem_union_left _ hv))
      (fun v hv => hm v (Finset.mem_union_left _ hv))
    have hb := TypeExpr.subst_closed (fun v hv => ht v (Finset.mem_union_right _ hv))
      (fun v hv => hm v (Finset.mem_union_right _ hv))
    simp_all [constraint, Constraint.subst, Constraint.typeVars, Constraint.modVars]
  case mode a b | defined a =>
    simp only [Constraint.modVars, Finset.mem_union, or_imp, forall_and] at hm
    simp_all [constraint, Constraint.subst, Constraint.typeVars, Constraint.modVars,
      ModExpr.subst_closed]
  case equal v a =>
    have hv := ht v (by simp [Constraint.typeVars])
    have ha := TypeExpr.subst_closed (fun w hw => ht w (Finset.mem_insert_of_mem hw)) hm
    cases v with
    | rigid n => simp [type, TypeExpr.typeVars] at hv
    | flex n =>
      cases he : σ.types.lookup n
      · simp [type, he, TypeExpr.typeVars] at hv
      · simpa [constraint, ty, type, he, Constraint.typeVars, Constraint.modVars, ha] using hv

/-- Only finitely many flexible identifiers are replaced; rigid identifiers keep
the ordinary substitution semantics. -/
def GroundAssignment.finiteSubstitution (ρ : GroundAssignment) (nt nm : Nat) : Substitution :=
  ⟨(List.range nt).map (fun n => (n, (ρ.types (.flex n)).reify)),
    (List.range nm).map (fun n => (n, ModExpr.const (ρ.modes (.flex n))))⟩

private theorem lookup_map_self {α β : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (f : α → β) {v} (hv : v ∈ xs) :
    (xs.map (fun w => (w, f w))).lookup v = some (f v) := by
  induction xs with
  | nil => contradiction
  | cons w xs ih =>
    by_cases h : v = w
    · subst w; simp
    · have he : (v == w) = false := by simpa using h
      simpa only [List.map_cons, List.lookup_cons, he] using
        ih ((List.mem_cons.mp hv).resolve_left h)

theorem GroundAssignment.finiteSubstitution_type (ρ : GroundAssignment) {nt nm n}
    (hn : n < nt) : (ρ.finiteSubstitution nt nm).type (.flex n) = (ρ.types (.flex n)).reify := by
  simp only [finiteSubstitution, Substitution.type,
    lookup_map_self _ _ (List.mem_range.mpr hn), Option.getD_some]

theorem GroundAssignment.finiteSubstitution_mode (ρ : GroundAssignment) {nt nm n}
    (hn : n < nm) : (ρ.finiteSubstitution nt nm).mode (.flex n) = .const (ρ.modes (.flex n)) := by
  simp only [finiteSubstitution, Substitution.mode,
    lookup_map_self _ _ (List.mem_range.mpr hn), Option.getD_some]

theorem GroundModels.boundsSatisfiable {ρ cs} (h : GroundModels ρ cs)
    (ht : ∀ v ∈ cs.typeVars, ∃ n, v = .flex n)
    (hm : ∀ v ∈ cs.modVars, ∃ n, v = .flex n) : BoundsSatisfiable cs := by
  let σ := ρ.finiteSubstitution cs.freshTypeIndex cs.freshModeIndex
  have hσt : ∀ v ∈ cs.typeVars, σ.type v = (ρ.types v).reify := by
    intro v hv
    obtain ⟨n, rfl⟩ := ht v hv
    exact ρ.finiteSubstitution_type (cs.lt_freshTypeIndex ((cs.mem_typeVariables _).mpr hv))
  have hσm : ∀ v ∈ cs.modVars, σ.mode v = .const (ρ.modes v) := by
    intro v hv
    obtain ⟨n, rfl⟩ := hm v hv
    exact ρ.finiteSubstitution_mode (cs.lt_freshModeIndex ((cs.mem_modeVariables _).mpr hv))
  have hg : GroundModels ρ (σ.bounds cs) := (GroundModels.subst_congr cs
    (fun v hv => by rw [hσt v hv]; exact GroundTy.realize_reify _ _)
    (fun v hv => by rw [hσm v hv]; rfl)).mpr h
  have hc : ∀ c ∈ σ.bounds cs, c.typeVars = ∅ ∧ c.modVars = ∅ := by
    intro c hmem
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmem
    apply Substitution.constraint_closed
    · intro v hv
      rw [hσt v ((cs.mem_typeVars_iff v).mpr ⟨d, hd, hv⟩)]
      simp
    · intro v hv
      rw [hσm v ((cs.mem_modVars_iff v).mpr ⟨d, hd, hv⟩)]
      rfl
  refine ⟨σ, ?_, ?_, fun c hh => (hg c hh).entails_closed (hc c hh).1 (hc c hh).2⟩
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro v hv
    obtain ⟨c, hh, hv⟩ := ((σ.bounds cs).mem_typeVars_iff v).mp
      (((σ.bounds cs).mem_typeVariables v).mp hv)
    simp [(hc c hh).1] at hv
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro v hv
    obtain ⟨c, hh, hv⟩ := ((σ.bounds cs).mem_modVars_iff v).mp
      (((σ.bounds cs).mem_modeVariables v).mp hv)
    simp [(hc c hh).2] at hv

end ModalityInference
