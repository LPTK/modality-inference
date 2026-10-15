import ModalityInference.ComparisonAbsorption
import ModalityInference.Proofs.ComparisonPartial
import ModalityInference.Proofs.ComparisonPartialModes

namespace ModalityInference.ComparisonAbsorption

theorem instantiate_congr (t : Ty) {ts us : TypeVar → CompareTy} {ms ns : ModVar → ModExpr}
    (ht : ∀ v ∈ t.typeVars, ts v = us v) (hm : ∀ v ∈ t.modVars, ms v = ns v) :
    instantiate ts ms t = instantiate us ns t := by
  induction t <;> simp_all [instantiate, CompareTy.ofTy, CompareTy.subst,
    TypeExpr.typeVars, TypeExpr.modVars, or_imp, forall_and]
  exact ModExpr.subst_congr _ hm.2

theorem instantiate_wellShaped {Δ : Bounds} (t : Ty) (ts : TypeVar → CompareTy)
    (ms : ModVar → ModExpr) (ht : ∀ v, (ts v).WellShaped Δ) :
    (instantiate ts ms t).WellShaped Δ := by
  induction t <;> simp_all [instantiate, CompareTy.ofTy, CompareTy.subst, CompareTy.WellShaped]

theorem disjoint_correct (owners : Owners) (t : Ty) :
    disjoint owners t = true ↔
      (∀ v ∈ t.typeVars, typeFree owners v = true) ∧
        ∀ v ∈ t.modVars, modeFree owners v = true := by
  simp [disjoint, List.all_eq_true]

theorem modeDisjoint_correct (owners : Owners) (m : ModExpr) :
    modeDisjoint owners m = true ↔ ∀ v ∈ m.vars, modeFree owners v = true := by
  simp [modeDisjoint, List.all_eq_true]

theorem mode_subst_congr {owners : Owners} {m : ModExpr} {ms ns : ModVar → ModExpr}
    (h : modeDisjoint owners m = true)
    (hf : ∀ v, modeFree owners v = true → ms v = ns v) : m.subst ms = m.subst ns :=
  ModExpr.subst_congr m (fun v hv => hf v ((modeDisjoint_correct owners m).mp h v hv))

private theorem sum_congr {Δ a b c d} (ha : ShapedSubtype Δ a c)
    (hb : ShapedSubtype Δ b d) : ShapedSubtype Δ (.sum a b) (.sum c d) :=
  (ShapedSubtype.identityRev (a := .sum a b) ⟨ha.wellShaped_left, hb.wellShaped_left⟩).trans
    ((ShapedSubtype.sum
      ((ShapedSubtype.identity ha.wellShaped_left).trans (ha.trans (.identityRev ha.wellShaped_right)))
      ((ShapedSubtype.identity hb.wellShaped_left).trans (hb.trans (.identityRev hb.wellShaped_right)))).trans
      (.identity ⟨ha.wellShaped_right, hb.wellShaped_right⟩))

/-- The certificate transports arbitrary internal images, including partial
joins and meets. No definedness premise is imposed on an image. -/
theorem rewrite_equivalent {Δ : Bounds} {owners : Owners} {total : ModExpr → Bool}
    {ts us : TypeVar → CompareTy} {ms ns : ModVar → ModExpr}
    (hus : ∀ v, (us v).WellShaped Δ)
    (ht : ∀ v, typeFree owners v = true → ts v = us v)
    (hm : ∀ v, modeFree owners v = true → ms v = ns v)
    (hc : ∀ x m, owners.lookup x = some m →
      ShapedSubtype Δ (.modal (ts (.flex x)) (ms (.flex m))) (us (.flex x)) ∧
        ShapedSubtype Δ (us (.flex x)) (.modal (ts (.flex x)) (ms (.flex m))))
    (htotal : ∀ m, total m = true → Submode Δ (m.subst ms) (m.subst ms))
    (t u : Ty) (h : rewrite total owners t = some u) :
    ShapedSubtype Δ (instantiate ts ms t) (instantiate us ns u) ∧
      ShapedSubtype Δ (instantiate us ns u) (instantiate ts ms t) := by
  induction t generalizing u with
  | var v =>
    simp only [rewrite] at h
    split at h
    · next hd =>
      cases Option.some.inj h
      have he := ht v (((disjoint_correct _ _).mp hd).1 v (by simp [TypeExpr.typeVars]))
      simp only [instantiate, CompareTy.ofTy, CompareTy.subst, he]
      exact ⟨.refl (hus v), .refl (hus v)⟩
    · contradiction
  | unit =>
    simp only [rewrite] at h
    split at h
    · cases Option.some.inj h; exact ⟨.refl trivial, .refl trivial⟩
    · contradiction
  | credit =>
    simp only [rewrite] at h
    split at h
    · cases Option.some.inj h; exact ⟨.refl trivial, .refl trivial⟩
    · contradiction
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    rw [rewrite.eq_def] at h
    split at h
    · next hd =>
      cases Option.some.inj h
      have he := instantiate_congr _
        (fun v hv => ht v (((disjoint_correct _ _).mp hd).1 v hv))
        (fun v hv => hm v (((disjoint_correct _ _).mp hd).2 v hv))
      rw [he]
      exact ⟨.refl (instantiate_wellShaped _ us ns hus), .refl (instantiate_wellShaped _ us ns hus)⟩
    · cases ha : rewrite total owners a <;> simp only [ha, Option.bind_eq_bind, Option.bind] at h
      · contradiction
      · next a' =>
        cases hb : rewrite total owners b <;> simp only [hb] at h
        · contradiction
        · next b' =>
          cases Option.some.inj h
          first
          | exact ⟨.prod_congr (iha _ ha).1 (ihb _ hb).1, .prod_congr (iha _ ha).2 (ihb _ hb).2⟩
          | exact ⟨sum_congr (iha _ ha).1 (ihb _ hb).1, sum_congr (iha _ ha).2 (ihb _ hb).2⟩
          | exact ⟨.fn_congr (iha _ ha).2 (ihb _ hb).1, .fn_congr (iha _ ha).1 (ihb _ hb).2⟩
  | modal a m ih =>
    rw [rewrite.eq_def] at h
    split at h
    · next hd =>
      cases Option.some.inj h
      have he := instantiate_congr _
        (fun v hv => ht v (((disjoint_correct _ _).mp hd).1 v hv))
        (fun v hv => hm v (((disjoint_correct _ _).mp hd).2 v hv))
      rw [he]
      exact ⟨.refl (instantiate_wellShaped _ us ns hus), .refl (instantiate_wellShaped _ us ns hus)⟩
    · split at h
      · next x n he =>
        cases he
        split at h
        · next hl =>
          cases Option.some.inj h
          exact hc x n (beq_iff_eq.mp hl)
        · contradiction
      · next _ _ he => cases he
      · next _ _ he => cases he
      · next _ _ he => cases he
      · next a' m' _ he =>
        cases he
        split at h
        · next hm' =>
          simp only [Bool.and_eq_true] at hm'
          obtain ⟨hfree, htotal'⟩ := hm'
          cases ha : rewrite total owners a <;> simp only [ha, Option.map] at h
          · contradiction
          · next a' =>
            cases Option.some.inj h
            have he := mode_subst_congr hfree hm
            have hh := htotal m htotal'
            simp only [instantiate, CompareTy.ofTy, CompareTy.subst, ← he]
            exact ⟨.congr (ih _ ha).1 hh, .congr (ih _ ha).2 hh⟩
        · contradiction
      · contradiction

theorem typeFree_lookup {owners : Owners} {x : Nat} (h : typeFree owners (.flex x) = true) :
    owners.lookup x = none := by
  have hx : x ∉ owners.map Prod.fst := by simpa [typeFree] using h
  apply List.lookup_eq_none_iff.mpr
  intro pair hp
  apply bne_iff_ne.mpr
  intro he
  exact hx (List.mem_map.mpr ⟨pair, hp, he.symm⟩)

theorem lookup_mode_mem {owners : Owners} {x m : Nat} (h : owners.lookup x = some m) :
    m ∈ modes owners := by
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp h
  have hm : (x, m) ∈ owners := by rw [he]; simp
  simp only [modes, List.mem_dedup, List.mem_map]
  exact ⟨(x, m), hm, rfl⟩

theorem neutral_free {owners : Owners} (ms : ModVar → ModExpr) (v : ModVar)
    (h : modeFree owners v = true) : neutral owners ms v = ms v := by
  cases v <;> simp_all [neutral, modeFree]

theorem neutral_selected {owners : Owners} (ms : ModVar → ModExpr) {x m : Nat}
    (h : owners.lookup x = some m) : neutral owners ms (.flex m) = .epsilon := by
  simp [neutral, lookup_mode_mem h]

theorem absorb_free {owners : Owners} (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (v : TypeVar) (h : typeFree owners v = true) : absorb owners ts ms v = ts v := by
  cases v with
  | rigid _ => rfl
  | flex x => simp [absorb, typeFree_lookup h]

theorem absorb_wellShaped {Δ : Bounds} (owners : Owners) (ts : TypeVar → CompareTy)
    (ms : ModVar → ModExpr) (ht : ∀ v, (ts v).WellShaped Δ) :
    ∀ v, (absorb owners ts ms v).WellShaped Δ := by
  intro v
  cases v with
  | rigid n => exact ht (.rigid n)
  | flex x =>
    cases he : owners.lookup x <;> simpa [absorb, he, CompareTy.WellShaped] using ht (.flex x)

/-- Any witness for the stripped body reconstructs with identity mode images.
Its internal type images need only be well-shaped, not defined. -/
theorem reconstruct {Δ : Bounds} {owners : Owners} {total : ModExpr → Bool}
    (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (hshape : ∀ v, (ts v).WellShaped Δ)
    (htotal : ∀ m, total m = true →
      Submode Δ (m.subst (neutral owners ms)) (m.subst (neutral owners ms)))
    {t u : Ty} (h : rewrite total owners t = some u) :
    ShapedSubtype Δ (instantiate ts (neutral owners ms) t) (instantiate ts ms u) ∧
      ShapedSubtype Δ (instantiate ts ms u) (instantiate ts (neutral owners ms) t) := by
  apply rewrite_equivalent hshape (fun _ _ => rfl) (neutral_free ms) _ htotal t u h
  intro x m hm
  rw [neutral_selected ms hm]
  exact ⟨.identity (hshape _), .identityRev (hshape _)⟩

/-- Conversely, every original instance in the certified fragment factors
through the stripped body by absorbing its uniform capsule into each owner. -/
theorem absorb_complete {Δ : Bounds} {owners : Owners} {total : ModExpr → Bool}
    (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (hshape : ∀ v, (ts v).WellShaped Δ)
    (htotal : ∀ m, total m = true → Submode Δ (m.subst ms) (m.subst ms))
    {t u : Ty} (h : rewrite total owners t = some u) :
    ShapedSubtype Δ (instantiate ts ms t) (instantiate (absorb owners ts ms) ms u) ∧
      ShapedSubtype Δ (instantiate (absorb owners ts ms) ms u) (instantiate ts ms t) := by
  apply rewrite_equivalent (absorb_wellShaped owners ts ms hshape)
    (fun v hv => (absorb_free ts ms v hv).symm) (fun _ _ => rfl) _ htotal t u h
  intro x m hm
  simp only [absorb, hm]
  exact ⟨.refl (hshape _), .refl (hshape _)⟩

@[simp] theorem rewrite_empty (total : ModExpr → Bool) (t : Ty) :
    rewrite total [] t = some t := by
  have hd : disjoint [] t = true := by
    apply (disjoint_correct [] t).mpr
    constructor <;> intro v _ <;> cases v <;> rfl
  rw [rewrite.eq_def, if_pos hd]

theorem plan_spec (p : SchemePreparation.Prepared) (total : ModExpr → Bool) :
    scopeCheck p (plan p total).owners = true ∧
      rewrite (transparent p total) (plan p total).owners p.sourceType =
        some (plan p total).body := by
  unfold plan
  dsimp only
  split
  · next hs =>
    cases h : rewrite (transparent p total) (candidates p total) p.sourceType with
    | none => exact ⟨rfl, rewrite_empty _ _⟩
    | some t => exact ⟨hs, h⟩
  · exact ⟨rfl, rewrite_empty _ _⟩

theorem scopeCheck_spec (p : SchemePreparation.Prepared) (owners : Owners) :
    scopeCheck p owners = true ↔
      ∀ pair ∈ owners,
        (p.firstType ≤ pair.1 ∧ pair.1 < p.nextType) ∧
        (p.firstMode ≤ pair.2 ∧ pair.2 < p.nextMode) ∧
        (∀ c ∈ p.sourceBounds, TypeVar.flex pair.1 ∉ c.typeVars) ∧
        (∀ c ∈ p.sourceBounds, ModVar.flex pair.2 ∉ c.modVars) := by
  simp [scopeCheck, sourceType, sourceMode, List.all_eq_true,
    ComparisonPartial.absentFromBounds_correct, ComparisonPartialModes.absentFromBounds_correct, and_assoc]

theorem plan_type_avoids_bounds {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    {x : Nat} (hx : x ∈ (plan p total).owners.map Prod.fst)
    {c : Constraint} (hc : c ∈ p.sourceBounds) : TypeVar.flex x ∉ c.typeVars := by
  obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hx
  exact ((scopeCheck_spec _ _).mp (plan_spec p total).1 pair hp).2.2.1 c hc

theorem plan_mode_avoids_bounds {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    {m : Nat} (hm : m ∈ (plan p total).modes)
    {c : Constraint} (hc : c ∈ p.sourceBounds) : ModVar.flex m ∉ c.modVars := by
  simp only [Result.modes, modes, List.mem_dedup, List.mem_map] at hm
  obtain ⟨pair, hp, rfl⟩ := hm
  exact ((scopeCheck_spec _ _).mp (plan_spec p total).1 pair hp).2.2.2 c hc

@[simp] theorem action_type (r : Result) (v : TypeVar) : r.action.type v = .var v := by
  cases v <;> rfl

theorem action_mode (r : Result) (v : ModVar) :
    r.action.mode v = neutral r.owners ModExpr.var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    by_cases hn : n ∈ r.modes
    · have hl := lookup_map_self r.modes (fun _ => ModExpr.epsilon) hn
      simp only [Result.action, Substitution.mode, hl, Option.getD_some]
      change n ∈ modes r.owners at hn
      simp [neutral, hn]
    · have hfree : n ∉ r.action.modes.map Prod.fst := by
        simpa [Result.action, List.map_map, Function.comp_def] using hn
      rw [Substitution.mode_fresh _ hfree]
      change n ∉ modes r.owners at hn
      simp [neutral, hn]

theorem action_mode_fixed (r : Result) {v : ModVar}
    (h : modeFree r.owners v = true) : r.action.mode v = .var v := by
  rw [action_mode]
  exact neutral_free ModExpr.var v h

theorem action_expr_fixed (r : Result) (m : ModExpr)
    (h : ∀ v ∈ m.vars, modeFree r.owners v = true) : m.subst r.action.mode = m := by
  have he : m.subst r.action.mode = m.subst ModExpr.var :=
    ModExpr.subst_congr m (fun v hv => action_mode_fixed r (h v hv))
  simpa using he

theorem action_ty_fixed (r : Result) (t : Ty)
    (h : ∀ v ∈ t.modVars, modeFree r.owners v = true) : r.action.ty t = t := by
  have he : t.subst r.action.type r.action.mode = t.subst TypeExpr.var ModExpr.var :=
    TypeExpr.subst_congr t (fun v _ => action_type r v)
      (fun v hv => action_mode_fixed r (h v hv))
  simpa using he

theorem action_constraint_fixed (r : Result) (c : Constraint)
    (h : ∀ v ∈ c.modVars, modeFree r.owners v = true) : r.action.constraint c = c := by
  cases c with
  | sub a b =>
    exact congrArg₂ Constraint.sub
      (action_ty_fixed r a (fun v hv => h v (by simp [Constraint.modVars, hv])))
      (action_ty_fixed r b (fun v hv => h v (by simp [Constraint.modVars, hv])))
  | equiv a b =>
    exact congrArg₂ Constraint.equiv
      (action_ty_fixed r a (fun v hv => h v (by simp [Constraint.modVars, hv])))
      (action_ty_fixed r b (fun v hv => h v (by simp [Constraint.modVars, hv])))
  | mode a b =>
    exact congrArg₂ Constraint.mode
      (action_expr_fixed r a (fun v hv => h v (by simp [Constraint.modVars, hv])))
      (action_expr_fixed r b (fun v hv => h v (by simp [Constraint.modVars, hv])))
  | defined m => exact congrArg Constraint.defined (action_expr_fixed r m h)
  | equal v a => cases v <;> exact congrArg (Constraint.equal _) (action_ty_fixed r a h)

/-- The prepass preserves every written source constraint and guard literally. -/
theorem plan_bounds_fixed (p : SchemePreparation.Prepared) (total : ModExpr → Bool) :
    (plan p total).action.bounds p.sourceBounds = p.sourceBounds := by
  calc
    _ = p.sourceBounds.map id := List.map_congr_left (fun c hc =>
      action_constraint_fixed (plan p total) c (by
        intro v hv
        cases v with
        | rigid _ => rfl
        | flex m =>
          have hn : m ∉ (plan p total).modes := fun hm => plan_mode_avoids_bounds hm hc hv
          simpa [modeFree, Result.modes] using hn))
    _ = p.sourceBounds := List.map_id p.sourceBounds

theorem plan_reconstruct {Δ : Bounds} (p : SchemePreparation.Prepared)
    (total : ModExpr → Bool) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (hshape : ∀ v, (ts v).WellShaped Δ)
    (htotal : ∀ m, transparent p total m = true →
      Submode Δ (m.subst (neutral (plan p total).owners ms))
        (m.subst (neutral (plan p total).owners ms))) :
    ShapedSubtype Δ (instantiate ts (neutral (plan p total).owners ms) p.sourceType)
      (instantiate ts ms (plan p total).body) ∧
    ShapedSubtype Δ (instantiate ts ms (plan p total).body)
      (instantiate ts (neutral (plan p total).owners ms) p.sourceType) :=
  reconstruct ts ms hshape htotal (plan_spec p total).2

theorem plan_absorb_complete {Δ : Bounds} (p : SchemePreparation.Prepared)
    (total : ModExpr → Bool) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (hshape : ∀ v, (ts v).WellShaped Δ)
    (htotal : ∀ m, transparent p total m = true → Submode Δ (m.subst ms) (m.subst ms)) :
    ShapedSubtype Δ (instantiate ts ms p.sourceType)
      (instantiate (absorb (plan p total).owners ts ms) ms (plan p total).body) ∧
    ShapedSubtype Δ (instantiate (absorb (plan p total).owners ts ms) ms (plan p total).body)
      (instantiate ts ms p.sourceType) :=
  absorb_complete ts ms hshape htotal (plan_spec p total).2

namespace Examples

def capsule (x m : Nat) : Ty := .modal (.var (.flex x)) (.var (.flex m))

def prepared (t : Ty) (nextType : Nat := 1) : SchemePreparation.Prepared :=
  { sourceRenaming := {}, targetRenaming := {}, assumptions := [], sourceBounds := []
    sourceType := t, targetType := .unit, firstType := 0, firstMode := 0
    nextType, nextMode := 1 }

theorem repeated_product_plan :
    plan (prepared (.prod (capsule 0 0) (capsule 0 0))) (fun _ => false) =
      ⟨[(0, 0)], .prod (.var (.flex 0)) (.var (.flex 0))⟩ := by decide

theorem multiple_owners_plan :
    plan (prepared (.prod (capsule 0 0) (capsule 1 0)) 2) (fun _ => false) =
      ⟨[(0, 0), (1, 0)], .prod (.var (.flex 0)) (.var (.flex 1))⟩ := by decide

theorem function_variance_plan :
    (plan (prepared (.fn (capsule 0 0) (capsule 0 0))) (fun _ => false)).body =
      .fn (.var (.flex 0)) (.var (.flex 0)) := by decide

theorem partial_barrier_preserved :
    (plan (prepared (.modal (capsule 0 0) ComparisonPartialModes.Examples.partialMode))
      (fun _ => false)).owners = [] := by decide

theorem nonuniform_type_preserved :
    (plan (prepared (.prod (capsule 0 0) (.var (.flex 0)))) (fun _ => false)).owners = [] := by
  decide

theorem concrete_anchor_preserved :
    (plan (prepared (.prod (capsule 0 0) (.modal .unit (.var (.flex 0)))))
      (fun _ => false)).owners = [] := by decide

theorem source_bound_guard_preserved :
    (plan { prepared (capsule 0 0) with sourceBounds := [.defined (.var (.flex 0))] }
      (fun _ => false)).owners = [] := by decide

/-- The endpoints may contain arbitrary partial annotations. The only premise
is the required compatibility of their shapes. -/
theorem repeated_product_interpolation {Δ : Bounds} (a b : CompareTy)
    (hshape : (CompareTy.meet a b).WellShaped Δ) :
    ShapedSubtype Δ
      (.prod (.modal (.meet a b) .epsilon) (.modal (.meet a b) .epsilon)) (.prod a b) :=
  .prod_congr ((ShapedSubtype.identity hshape).trans (.meetLeft hshape))
    ((ShapedSubtype.identity hshape).trans (.meetRight hshape))

end Examples

end ModalityInference.ComparisonAbsorption
