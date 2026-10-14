import ModalityInference.Proofs.TypeOrientation
import ModalityInference.Proofs.SubstitutionSupport

/-! Termination of the finite-shape precheck by variable elimination and size. -/
namespace ModalityInference
namespace ShapePairs

def vars : List (Ty × Ty) → Finset TypeVar
  | [] => ∅
  | (a, b) :: rest => a.typeVars ∪ b.typeVars ∪ vars rest

def nodes : List (Ty × Ty) → Nat
  | [] => 0
  | (a, b) :: rest => a.shapeSize + b.shapeSize + nodes rest

def rank (ps : List (Ty × Ty)) : Nat × Nat := ((vars ps).card, nodes ps)

abbrev Lt (ps qs : List (Ty × Ty)) : Prop := Prod.Lex (· < ·) (· < ·) (rank ps) (rank qs)

theorem mem_vars (ps : List (Ty × Ty)) (v : TypeVar) :
    v ∈ vars ps ↔ ∃ a b, (a, b) ∈ ps ∧ v ∈ a.typeVars ∪ b.typeVars := by
  induction ps with
  | nil => simp [vars]
  | cons pair rest ih =>
    rcases pair with ⟨a, b⟩
    simp only [vars, Finset.mem_union, ih, List.mem_cons, Prod.mk.injEq]
    aesop

theorem lt_tail (a b : Ty) (ps : List (Ty × Ty)) : Lt ps ((a, b) :: ps) := by
  have hcard : (vars ps).card ≤ (vars ((a, b) :: ps)).card :=
    Finset.card_le_card (Finset.subset_union_right)
  apply Prod.lex_def.mpr
  rcases lt_or_eq_of_le hcard with hc | hc
  · exact .inl hc
  · refine .inr ⟨hc, ?_⟩
    change nodes ps < a.shapeSize + b.shapeSize + nodes ps
    have ha := a.shapeSize_pos
    omega

theorem subst_vars_subset (ps : List (Ty × Ty)) (ts : TypeVar → Ty) (S : Finset TypeVar)
    (h : ∀ v ∈ vars ps, (ts v).typeVars ⊆ S) :
    vars (ps.map fun (a, b) => (a.subst ts ModExpr.var, b.subst ts ModExpr.var)) ⊆ S := by
  intro v hv
  obtain ⟨a, b, hab, hv⟩ := (mem_vars _ _).mp hv
  obtain ⟨⟨x, y⟩, hxy, he⟩ := List.mem_map.mp hab
  cases he
  simp only [Finset.mem_union, TypeExpr.mem_typeVars_subst] at hv
  exact hv.elim
    (fun ⟨w, hw, hv⟩ => h w ((mem_vars _ _).mpr ⟨x, y, hxy, Finset.mem_union_left _ hw⟩) hv)
    (fun ⟨w, hw, hv⟩ => h w ((mem_vars _ _).mpr ⟨x, y, hxy, Finset.mem_union_right _ hw⟩) hv)

def replace (v : TypeVar) (t : Ty) (w : TypeVar) : Ty := if w == v then t else .var w

theorem lt_replace (v : TypeVar) (t : Ty) (ps : List (Ty × Ty)) (hv : v ∉ t.typeVars) :
    Lt (ps.map fun (a, b) =>
      (a.subst (replace v t) ModExpr.var, b.subst (replace v t) ModExpr.var)) ((.var v, t) :: ps) := by
  let S := vars ((.var v, t) :: ps)
  have hsub : vars (ps.map fun (a, b) =>
      (a.subst (replace v t) ModExpr.var, b.subst (replace v t) ModExpr.var)) ⊆ S.erase v := by
    apply subst_vars_subset
    intro w hw
    by_cases he : w = v
    · subst w
      simp only [replace, beq_self_eq_true, ↓reduceIte]
      exact fun z hz => Finset.mem_erase.mpr ⟨fun he => hv (he ▸ hz),
        Finset.mem_union_left _ (Finset.mem_union_right _ hz)⟩
    · simpa [replace, he, TypeExpr.typeVars, S, vars] using And.intro he (Or.inr hw)
  exact Prod.lex_def.mpr (.inl ((Finset.card_le_card hsub).trans_lt
    (Finset.card_erase_lt_of_mem (by simp [S, vars, TypeExpr.typeVars]))))

theorem rank_swap (a b : Ty) (ps : List (Ty × Ty)) :
    rank ((a, b) :: ps) = rank ((b, a) :: ps) := by
  simp [rank, vars, nodes, Finset.union_comm, Nat.add_comm]

theorem lt_replace_right (v : TypeVar) (t : Ty) (ps : List (Ty × Ty)) (hv : v ∉ t.typeVars) :
    Lt (ps.map fun (a, b) =>
      (a.subst (replace v t) ModExpr.var, b.subst (replace v t) ModExpr.var)) ((t, .var v) :: ps) := by
  simpa only [Lt, ← rank_swap t (.var v) ps] using lt_replace v t ps hv

theorem lt_decompose {a b c d x y : Ty} (ps : List (Ty × Ty))
    (hx : x.typeVars = a.typeVars ∪ b.typeVars) (hy : y.typeVars = c.typeVars ∪ d.typeVars)
    (hxs : x.shapeSize = a.shapeSize + b.shapeSize + 1)
    (hys : y.shapeSize = c.shapeSize + d.shapeSize + 1) :
    Lt ((a, c) :: (b, d) :: ps) ((x, y) :: ps) := by
  apply Prod.lex_def.mpr
  right
  constructor
  · change (a.typeVars ∪ c.typeVars ∪ (b.typeVars ∪ d.typeVars ∪ vars ps)).card =
      (x.typeVars ∪ y.typeVars ∪ vars ps).card
    rw [hx, hy]
    congr 1
    ac_rfl
  · change a.shapeSize + c.shapeSize + (b.shapeSize + d.shapeSize + nodes ps) <
      x.shapeSize + y.shapeSize + nodes ps
    omega

theorem wellFounded : WellFounded Lt :=
  InvImage.wf rank (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)

end ShapePairs

theorem checkShapePairs_eventually (ps : List (Ty × Ty)) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, checkShapePairs fuel ps = result := by
  induction ps using ShapePairs.wellFounded.induction with
  | h ps ih =>
    cases ps with
    | nil => exact ⟨1, .success (), by simp, fun fuel hf => by cases fuel <;> simp_all [checkShapePairs]⟩
    | cons pair ps =>
      rcases pair with ⟨a, b⟩
      have advance (qs : List (Ty × Ty)) (hlt : ShapePairs.Lt qs ((a, b) :: ps))
          (he : ∀ fuel, checkShapePairs (fuel + 1) ((a, b) :: ps) = checkShapePairs fuel qs) :
          ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, checkShapePairs fuel ((a, b) :: ps) = result := by
        obtain ⟨n, result, hn, hresult⟩ := ih qs hlt
        refine ⟨n + 1, result, hn, fun fuel hf => ?_⟩
        cases fuel with
        | zero => omega
        | succ fuel => exact (he fuel).trans (hresult fuel (by omega))
      by_cases he : a = b
      · exact advance ps (ShapePairs.lt_tail a b ps) (fun fuel => by simp [checkShapePairs, he])
      have hne : (a == b) = false := by simp [he]
      have reject (reason : String)
          (hr : ∀ fuel, checkShapePairs (fuel + 1) ((a, b) :: ps) = .rejected reason) :
          ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, checkShapePairs fuel ((a, b) :: ps) = result := by
        refine ⟨1, .rejected reason, by simp, fun fuel hf => ?_⟩
        cases fuel with
        | zero => omega
        | succ fuel => exact hr fuel
      by_cases ha : ∃ v, a = .var v
      · obtain ⟨v, rfl⟩ := ha
        by_cases hoc : v ∈ b.typeVars
        · exact reject "occurs check failed through type-bound cycle"
            (fun fuel => by simp [checkShapePairs, hne, hoc])
        · refine advance _ (ShapePairs.lt_replace v b ps hoc) ?_
          intro fuel
          unfold ShapePairs.replace
          simp [checkShapePairs, hne, hoc]
      by_cases hb : ∃ v, b = .var v
      · obtain ⟨v, rfl⟩ := hb
        by_cases hoc : v ∈ a.typeVars
        · apply reject "occurs check failed through type-bound cycle"
          intro fuel
          cases a <;> simp_all [checkShapePairs]
        · refine advance _ (ShapePairs.lt_replace_right v a ps hoc) ?_
          intro fuel
          unfold ShapePairs.replace
          cases a <;> simp_all [checkShapePairs]
      cases a <;> cases b
      all_goals first
        | exact False.elim (ha ⟨_, rfl⟩)
        | exact False.elim (hb ⟨_, rfl⟩)
        | exact False.elim (he rfl)
        | solve |
            apply reject "incompatible finite type shapes"
            intro fuel
            simp [checkShapePairs, hne]
        | refine advance _ (ShapePairs.lt_decompose ps rfl rfl rfl rfl) ?_
      all_goals intro fuel; simp [checkShapePairs, hne]

theorem checkShapes_eventually (cs : Bounds) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, checkShapes fuel cs = result :=
  checkShapePairs_eventually _

end ModalityInference
