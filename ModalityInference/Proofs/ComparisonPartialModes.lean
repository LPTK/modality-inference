import ModalityInference.ComparisonPartialModes
import ModalityInference.Proofs.ComparisonShapes
import ModalityInference.Proofs.ReductionEntailment
import ModalityInference.Proofs.SubstitutionSupport

namespace ModalityInference.ComparisonPartialModes

/-- No annotation-definedness premise is needed for these outer rewrites. -/
theorem normalizeOuterFuel_correct (Δ : Bounds) (fuel : Nat) (t : Ty) :
    Subtype Δ t (normalizeOuterFuel fuel t) ∧
      Subtype Δ (normalizeOuterFuel fuel t) t := by
  induction fuel generalizing t with
  | zero => exact ⟨.refl, .refl⟩
  | succ fuel ih =>
    cases t with
    | var | unit | credit | prod | sum | fn => exact ⟨.refl, .refl⟩
    | modal a m =>
      cases m <;> simp only [normalizeOuterFuel]
      case compose m n =>
        exact ⟨Subtype.composeRev.trans (ih _).1, (ih _).2.trans .compose⟩
      all_goals
        split
        · next h =>
          have he := beq_iff_eq.mp h
          rw [he]
          exact ⟨Subtype.identity.trans (ih _).1, (ih _).2.trans .identityRev⟩
        · exact ⟨.refl, .refl⟩

theorem normalizeOuter_correct (Δ : Bounds) (t : Ty) :
    Subtype Δ t (normalizeOuter t) ∧ Subtype Δ (normalizeOuter t) t :=
  normalizeOuterFuel_correct Δ _ t

theorem act_wellShaped {Δ : Bounds} (ms : List ModExpr) {a : CompareTy}
    (ha : a.WellShaped Δ) : (act ms a).WellShaped Δ := by
  induction ms with
  | nil => exact ha
  | cons m ms ih => exact ih

theorem recompose_correct (Δ : Bounds) (ms : List ModExpr) (a : CompareTy)
    (ha : a.WellShaped Δ) :
    ShapedSubtype Δ (act ms a) (.modal a (recompose ms)) ∧
      ShapedSubtype Δ (.modal a (recompose ms)) (act ms a) := by
  match ms with
  | [] => exact ⟨.identityRev ha, .identity ha⟩
  | [m] => exact ⟨.refl ha, .refl ha⟩
  | m :: n :: ms =>
    have ih := recompose_correct Δ (.compose n m :: ms) a ha
    exact ⟨(ShapedSubtype.compose (act_wellShaped ms ha)).trans ih.1,
      ih.2.trans (.composeRev (act_wellShaped ms ha))⟩
termination_by ms.length

/-- Traversing a suffix uses only reflexivity of its explicitly total labels;
the stopped stem and the underlying type may remain partial. -/
theorem splitFuel_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m)
    (fuel : Nat) (ms : List ModExpr) (a : CompareTy) (ha : a.WellShaped Δ) :
    let frame := splitFuel total fuel ms
    ShapedSubtype Δ (act ms a) (act frame.suffix (act frame.stem a)) ∧
      ShapedSubtype Δ (act frame.suffix (act frame.stem a)) (act ms a) := by
  induction fuel generalizing ms with
  | zero => exact ⟨.refl (act_wellShaped ms ha), .refl (act_wellShaped ms ha)⟩
  | succ fuel ih =>
    cases ms with
    | nil => exact ⟨.refl ha, .refl ha⟩
    | cons m ms =>
      cases m <;> simp only [splitFuel]
      case compose m n =>
        exact ⟨(ShapedSubtype.composeRev (act_wellShaped ms ha)).trans (ih (n :: m :: ms)).1,
          (ih (n :: m :: ms)).2.trans (.compose (act_wellShaped ms ha))⟩
      all_goals
        split
        · next h =>
          have he := beq_iff_eq.mp h
          rw [he]
          exact ⟨(ShapedSubtype.identity (act_wellShaped ms ha)).trans (ih _).1,
            (ih _).2.trans (.identityRev (act_wellShaped ms ha))⟩
        · split
          · next h => exact ⟨.congr (ih _).1 (htotal _ h), .congr (ih _).2 (htotal _ h)⟩
          · exact ⟨.refl (act_wellShaped ms ha), .refl (act_wellShaped ms ha)⟩

theorem split_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m)
    (ms : List ModExpr) (a : CompareTy) (ha : a.WellShaped Δ) :
    let frame := split total ms
    ShapedSubtype Δ (act ms a) (act frame.suffix (act frame.stem a)) ∧
      ShapedSubtype Δ (act frame.suffix (act frame.stem a)) (act ms a) :=
  splitFuel_correct total htotal _ ms a ha

theorem splitFuel_total (total : ModExpr → Bool) (fuel : Nat) (ms : List ModExpr) :
    ∀ m ∈ (splitFuel total fuel ms).suffix, total m = true := by
  induction fuel generalizing ms with
  | zero => simp [splitFuel]
  | succ fuel ih =>
    cases ms with
    | nil => simp [splitFuel]
    | cons m ms =>
      cases m <;> simp only [splitFuel]
      case compose m n => exact ih _
      all_goals
        split
        · exact ih _
        · split
          · next h => simpa using And.intro h (ih ms)
          · simp

theorem split_total (total : ModExpr → Bool) (ms : List ModExpr) :
    ∀ m ∈ (split total ms).suffix, total m = true :=
  splitFuel_total total _ ms

theorem plan_spec {total : ModExpr → Bool} {name fresh : Nat}
    {requests : List Request} {b : Binding}
    (h : plan total name fresh requests = some b) :
    b.name = name ∧ b.fresh = fresh ∧
      b.requests = requests.filter (fun r => r.name == name) ∧
      b.requests ≠ [] ∧
      ∀ r ∈ b.requests, (split total [r.target]).stem = b.stem := by
  unfold plan at h
  dsimp only at h
  split at h
  · contradiction
  · next r rs hg =>
    split at h
    · next hs =>
      cases Option.some.inj h
      simp only [List.all_eq_true, beq_iff_eq] at hs
      refine ⟨rfl, rfl, rfl, ?_, ?_⟩
      · simpa only [hg] using List.cons_ne_nil r rs
      · intro s hmem
        change s ∈ requests.filter (fun r => r.name == name) at hmem
        rw [hg] at hmem
        rcases List.mem_cons.mp hmem with he | he
        · subst s
          rfl
        · exact hs s he
    · contradiction

def Request.Holds (Δ : Bounds) (r : Request) (image : ModExpr) (a : CompareTy) : Prop :=
  if r.isLower then ShapedSubtype Δ (.modal a r.target) (.modal a image)
  else ShapedSubtype Δ (.modal a image) (.modal a r.target)

/-- A common partial stem reduces comparison exactly to a guarded comparison
of the remaining suffixes. This theorem requires no totality of the stem. -/
theorem request_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m)
    (stem : List ModExpr) (fresh : Nat) (r : Request) (a : CompareTy)
    (ha : a.WellShaped Δ) (hstem : (split total [r.target]).stem = stem)
    (hb : Entails Δ (r.bound total fresh)) :
    r.Holds Δ (recompose (.var (.flex fresh) :: stem)) a := by
  have hs := split_correct total htotal [r.target] a ha
  dsimp only at hs
  rw [hstem] at hs
  have hi := recompose_correct Δ (.var (.flex fresh) :: stem) a ha
  have ht := recompose_correct Δ (split total [r.target]).suffix
    (act stem a) (act_wellShaped stem ha)
  cases he : r.isLower
  · simp only [Request.Holds, he, Bool.false_eq_true, ↓reduceIte]
    simp only [Request.bound, he, Bool.false_eq_true, ↓reduceIte, Entails] at hb
    exact hi.2.trans ((ShapedSubtype.congr (.refl (act_wellShaped stem ha)) hb).trans
      (ht.2.trans hs.2))
  · simp only [Request.Holds, he, ↓reduceIte]
    simp only [Request.bound, he, ↓reduceIte, Entails] at hb
    exact hs.1.trans (ht.1.trans
      ((ShapedSubtype.congr (.refl (act_wellShaped stem ha)) hb).trans hi.1))

theorem plan_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m)
    {name fresh : Nat} {requests : List Request} {b : Binding}
    (h : plan total name fresh requests = some b)
    (hb : EntailsAll Δ (b.bounds total)) (a : CompareTy) (ha : a.WellShaped Δ)
    {r : Request} (hr : r ∈ b.requests) : r.Holds Δ b.expression a :=
  request_correct total htotal b.stem b.fresh r a ha ((plan_spec h).2.2.2.2 r hr)
    (hb _ (List.mem_map.mpr ⟨r, hr, rfl⟩))

theorem mem_adapt_bindings {total : ModExpr → Bool} {indices : List Nat}
    {requests : List Request} {firstFresh : Nat} {b : Binding} :
    b ∈ (adapt total indices requests firstFresh).bindings ↔
      ∃ name offset, (name, offset) ∈ indices.zipIdx ∧
        plan total name (firstFresh + offset) requests = some b := by
  simp only [adapt, List.mem_filterMap, Prod.exists]

theorem adapt_domain_subset {total : ModExpr → Bool} {indices : List Nat}
    {requests : List Request} {firstFresh name : Nat}
    (h : name ∈ (adapt total indices requests firstFresh).images.map Prod.fst) :
    name ∈ indices := by
  have he : (adapt total indices requests firstFresh).images.map Prod.fst =
      (adapt total indices requests firstFresh).bindings.map Binding.name := by
    simp only [adapt, List.map_map, Function.comp_def]
  rw [he] at h
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
  obtain ⟨n, offset, hn, hp⟩ := mem_adapt_bindings.mp hb
  rw [(plan_spec hp).1]
  exact List.fst_mem_of_mem_zipIdx hn

theorem adapt_binding_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m)
    {indices : List Nat} {requests : List Request} {firstFresh : Nat}
    (hb : EntailsAll Δ (adapt total indices requests firstFresh).bounds)
    {b : Binding} (hmem : b ∈ (adapt total indices requests firstFresh).bindings)
    (a : CompareTy) (ha : a.WellShaped Δ) {r : Request} (hr : r ∈ b.requests) :
    r.Holds Δ b.expression a := by
  obtain ⟨name, offset, _, hp⟩ := mem_adapt_bindings.mp hmem
  apply plan_correct total htotal hp _ a ha hr
  intro c hc
  exact hb c (List.mem_flatMap.mpr ⟨b, hmem, hc⟩)

theorem mem_adapt_pending {total : ModExpr → Bool} {indices : List Nat}
    {requests : List Request} {firstFresh : Nat} {r : Request} :
    r ∈ (adapt total indices requests firstFresh).pending ↔ r ∈ requests ∧
      r.name ∉ (adapt total indices requests firstFresh).bindings.map Binding.name := by
  simp [adapt]

theorem adapt_covered {total : ModExpr → Bool} {indices : List Nat}
    {requests : List Request} {firstFresh : Nat} {r : Request}
    (hr : r ∈ requests) (hp : r ∉ (adapt total indices requests firstFresh).pending) :
    ∃ b ∈ (adapt total indices requests firstFresh).bindings, r ∈ b.requests := by
  have hn : r.name ∈ (adapt total indices requests firstFresh).bindings.map Binding.name := by
    by_contra hn
    exact hp (mem_adapt_pending.mpr ⟨hr, hn⟩)
  obtain ⟨b, hb, he⟩ := List.mem_map.mp hn
  obtain ⟨name, offset, _, hp⟩ := mem_adapt_bindings.mp hb
  refine ⟨b, hb, ?_⟩
  rw [(plan_spec hp).2.2.1]
  exact List.mem_filter.mpr ⟨hr, beq_iff_eq.mpr (he.symm.trans (plan_spec hp).1)⟩

theorem absentFromBounds_correct (name : Nat) (bounds : Bounds) :
    absentFromBounds name bounds = true ↔
      ∀ c ∈ bounds, ModVar.flex name ∉ c.modVars := by
  simp [absentFromBounds]

theorem mem_eligible {p : SchemePreparation.Prepared} {name : Nat} :
    name ∈ eligible p ↔
      name ∈ List.range' p.firstMode (p.nextMode - p.firstMode) ∧
      ∀ c ∈ p.sourceBounds, ModVar.flex name ∉ c.modVars := by
  simp [eligible, absentFromBounds_correct]

theorem eligible_avoids_bounds {p : SchemePreparation.Prepared} {name : Nat}
    (h : name ∈ eligible p) {c : Constraint} (hc : c ∈ p.sourceBounds) :
    ModVar.flex name ∉ c.modVars := (mem_eligible.mp h).2 c hc

theorem adapt_mode_fixed {total : ModExpr → Bool} {indices : List Nat}
    {requests : List Request} {firstFresh name : Nat} (h : name ∉ indices) :
    (adapt total indices requests firstFresh).substitution.mode (.flex name) =
      .var (.flex name) :=
  Substitution.mode_fresh _ (fun hn => h (adapt_domain_subset hn))

theorem adapt_expr_fixed {total : ModExpr → Bool} {indices : List Nat}
    {requests : List Request} {firstFresh : Nat} (m : ModExpr)
    (h : ∀ name ∈ indices, ModVar.flex name ∉ m.vars) :
    m.subst (adapt total indices requests firstFresh).substitution.mode = m := by
  suffices he : m.subst (adapt total indices requests firstFresh).substitution.mode =
      m.subst ModExpr.var by simpa using he
  apply ModExpr.subst_congr
  intro v hv
  cases v with
  | rigid _ => rfl
  | flex name =>
    exact adapt_mode_fixed (fun hn => h name hn (by simpa using hv))

theorem adapt_ty_fixed {total : ModExpr → Bool} {indices : List Nat}
    {requests : List Request} {firstFresh : Nat} (t : Ty)
    (h : ∀ name ∈ indices, ModVar.flex name ∉ t.modVars) :
    (adapt total indices requests firstFresh).substitution.ty t = t := by
  suffices he : t.subst (adapt total indices requests firstFresh).substitution.type
      (adapt total indices requests firstFresh).substitution.mode =
      t.subst TypeExpr.var ModExpr.var by simpa using he
  apply TypeExpr.subst_congr
  · intro v _
    cases v <;> rfl
  · intro v hv
    cases v with
    | rigid _ => rfl
    | flex name => exact adapt_mode_fixed (fun hn => h name hn hv)

theorem adapt_constraint_fixed {total : ModExpr → Bool} {indices : List Nat}
    {requests : List Request} {firstFresh : Nat} (c : Constraint)
    (h : ∀ name ∈ indices, ModVar.flex name ∉ c.modVars) :
    (adapt total indices requests firstFresh).substitution.constraint c = c := by
  cases c with
  | sub a b =>
    have ha := adapt_ty_fixed (total := total) (requests := requests) (firstFresh := firstFresh)
      a (fun n hn hv => h n hn (by simp [Constraint.modVars, hv]))
    have hb := adapt_ty_fixed (total := total) (requests := requests) (firstFresh := firstFresh)
      b (fun n hn hv => h n hn (by simp [Constraint.modVars, hv]))
    exact congrArg₂ Constraint.sub ha hb
  | equiv a b =>
    have ha := adapt_ty_fixed (total := total) (requests := requests) (firstFresh := firstFresh)
      a (fun n hn hv => h n hn (by simp [Constraint.modVars, hv]))
    have hb := adapt_ty_fixed (total := total) (requests := requests) (firstFresh := firstFresh)
      b (fun n hn hv => h n hn (by simp [Constraint.modVars, hv]))
    exact congrArg₂ Constraint.equiv ha hb
  | mode a b =>
    have ha := adapt_expr_fixed (total := total) (requests := requests) (firstFresh := firstFresh)
      a (fun n hn hv => h n hn (by simp [Constraint.modVars, hv]))
    have hb := adapt_expr_fixed (total := total) (requests := requests) (firstFresh := firstFresh)
      b (fun n hn hv => h n hn (by simp [Constraint.modVars, hv]))
    exact congrArg₂ Constraint.mode ha hb
  | defined m => exact congrArg Constraint.defined (adapt_expr_fixed m h)
  | equal v a =>
    have ha := adapt_ty_fixed (total := total) (requests := requests) (firstFresh := firstFresh) a h
    cases v <;> exact congrArg (Constraint.equal _) ha

/-- The substitution leaves the full source bound list literally unchanged,
including every original written guard. -/
theorem adapt_bounds_fixed {total : ModExpr → Bool} {indices : List Nat}
    {requests : List Request} {firstFresh : Nat} (sourceBounds : Bounds)
    (h : ∀ name ∈ indices, ∀ c ∈ sourceBounds, ModVar.flex name ∉ c.modVars) :
    (adapt total indices requests firstFresh).substitution.bounds sourceBounds = sourceBounds := by
  calc
    _ = sourceBounds.map id := List.map_congr_left (fun c hc =>
      adapt_constraint_fixed c (fun n hn => h n hn c hc))
    _ = sourceBounds := List.map_id sourceBounds

theorem eligible_bounds_fixed (total : ModExpr → Bool) (p : SchemePreparation.Prepared)
    (requests : List Request) (firstFresh : Nat) :
    (adapt total (eligible p) requests firstFresh).substitution.bounds p.sourceBounds =
      p.sourceBounds :=
  adapt_bounds_fixed p.sourceBounds (fun _ hn _ hc => eligible_avoids_bounds hn hc)

def SpineSupports (P : ModVar → Prop) (ms : List ModExpr) : Prop :=
  ∀ m ∈ ms, ∀ v ∈ m.vars, P v

theorem foldCompose_support {P : ModVar → Prop} (ms : List ModExpr)
    (hms : SpineSupports P ms) (m : ModExpr) (hm : ∀ v ∈ m.vars, P v) :
    ∀ v ∈ (ms.foldl (fun outer inner => ModExpr.compose inner outer) m).vars, P v := by
  induction ms generalizing m with
  | nil => exact hm
  | cons n ms ih =>
    apply ih (fun x hx => hms x (List.mem_cons_of_mem n hx)) (.compose n m)
    intro v hv
    rcases Finset.mem_union.mp hv with hn | hn
    · exact hms n (List.mem_cons_self) v hn
    · exact hm v hn

theorem recompose_support {P : ModVar → Prop} (ms : List ModExpr)
    (hms : SpineSupports P ms) : ∀ v ∈ (recompose ms).vars, P v := by
  cases ms with
  | nil => simp [recompose, ModExpr.epsilon, ModExpr.vars]
  | cons m ms =>
    exact foldCompose_support ms (fun x hx => hms x (List.mem_cons_of_mem m hx)) m
      (hms m List.mem_cons_self)

theorem splitFuel_support {P : ModVar → Prop} (total : ModExpr → Bool) (fuel : Nat)
    (ms : List ModExpr) (hms : SpineSupports P ms) :
    SpineSupports P (splitFuel total fuel ms).stem ∧
      SpineSupports P (splitFuel total fuel ms).suffix := by
  induction fuel generalizing ms with
  | zero => exact ⟨hms, by simp [SpineSupports, splitFuel]⟩
  | succ fuel ih =>
    cases ms with
    | nil => simp [SpineSupports, splitFuel]
    | cons m ms =>
      have hm := hms m List.mem_cons_self
      have ht : SpineSupports P ms := fun x hx => hms x (List.mem_cons_of_mem m hx)
      cases m <;> simp only [splitFuel]
      case compose m n =>
        apply ih
        intro x hx v hv
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hm v (Finset.mem_union_right _ hv)
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hm v (Finset.mem_union_left _ hv)
          · exact ht x hx v hv
      all_goals
        split
        · exact ih ms ht
        · split
          · refine ⟨(ih ms ht).1, ?_⟩
            intro x hx v hv
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hm v hv
            · exact (ih ms ht).2 x hx v hv
          · exact ⟨hms, by simp [SpineSupports]⟩

theorem split_support {P : ModVar → Prop} (total : ModExpr → Bool)
    (ms : List ModExpr) (hms : SpineSupports P ms) :
    SpineSupports P (split total ms).stem ∧ SpineSupports P (split total ms).suffix :=
  splitFuel_support total _ ms hms

theorem plan_support {P : ModVar → Prop} {total : ModExpr → Bool} {name fresh : Nat}
    {requests : List Request} {b : Binding}
    (h : plan total name fresh requests = some b) (hf : P (.flex fresh))
    (hr : ∀ r ∈ requests, ∀ v ∈ r.target.vars, P v) :
    ∀ v ∈ b.expression.vars, P v := by
  obtain ⟨hn, he, hg, hne, hs⟩ := plan_spec h
  obtain ⟨r, hmem⟩ := List.exists_mem_of_ne_nil _ hne
  have hreq : r ∈ requests := (List.mem_filter.mp (hg ▸ hmem)).1
  have hstem := (split_support total [r.target]
    (by simpa [SpineSupports] using hr r hreq)).1
  rw [hs r hmem] at hstem
  apply recompose_support
  intro m hm v hv
  rcases List.mem_cons.mp hm with rfl | hm
  · have hv' : v = .flex b.fresh := Finset.mem_singleton.mp hv
    simpa [hv', he] using hf
  · exact hstem m hm v hv

theorem adapt_lookup_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m)
    {indices : List Nat} {requests : List Request} {firstFresh : Nat}
    (hb : EntailsAll Δ (adapt total indices requests firstFresh).bounds)
    {r : Request} (hr : r ∈ requests) {image : ModExpr}
    (hl : (adapt total indices requests firstFresh).images.lookup r.name = some image)
    (a : CompareTy) (ha : a.WellShaped Δ) : r.Holds Δ image a := by
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp hl
  have hm : (r.name, image) ∈ (adapt total indices requests firstFresh).images := by
    rw [he]
    simp
  change (r.name, image) ∈ (adapt total indices requests firstFresh).bindings.map
    (fun b => (b.name, b.expression)) at hm
  obtain ⟨b, hbmem, hentry⟩ := List.mem_map.mp hm
  have hname : b.name = r.name := congrArg Prod.fst hentry
  have himage : b.expression = image := congrArg Prod.snd hentry
  obtain ⟨name, offset, _, hp⟩ := mem_adapt_bindings.mp hbmem
  have hrb : r ∈ b.requests := by
    rw [(plan_spec hp).2.2.1]
    exact List.mem_filter.mpr ⟨hr, beq_iff_eq.mpr (hname.symm.trans (plan_spec hp).1)⟩
  simpa only [himage] using adapt_binding_correct total htotal hb hbmem a ha hrb

theorem adapt_fresh_range {total : ModExpr → Bool} {indices : List Nat}
    {requests : List Request} {firstFresh : Nat} {b : Binding}
    (hb : b ∈ (adapt total indices requests firstFresh).bindings) :
    firstFresh ≤ b.fresh ∧ b.fresh < (adapt total indices requests firstFresh).nextMode := by
  obtain ⟨name, offset, hi, hp⟩ := mem_adapt_bindings.mp hb
  have ho := List.snd_lt_of_mem_zipIdx hi
  simp only [Nat.add_zero] at ho
  rw [(plan_spec hp).2.1]
  change firstFresh ≤ firstFresh + offset ∧ firstFresh + offset < firstFresh + indices.length
  omega

theorem adapt_support {P : ModVar → Prop} {total : ModExpr → Bool} {indices : List Nat}
    {requests : List Request} {firstFresh : Nat}
    (hf : ∀ n, firstFresh ≤ n → n < firstFresh + indices.length → P (.flex n))
    (hr : ∀ r ∈ requests, ∀ v ∈ r.target.vars, P v)
    {entry : Nat × ModExpr} (he : entry ∈ (adapt total indices requests firstFresh).images) :
    ∀ v ∈ entry.2.vars, P v := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
  obtain ⟨name, offset, _, hp⟩ := mem_adapt_bindings.mp hb
  have hrange := adapt_fresh_range hb
  have hpf : P (.flex b.fresh) := hf b.fresh hrange.1 hrange.2
  rw [(plan_spec hp).2.1] at hpf
  exact plan_support hp hpf hr

namespace Examples

def partialMode : ModExpr := .leftResidual .top .bottom

def constantsTotal : ModExpr → Bool
  | .const _ => true
  | _ => false

theorem constantsTotal_sound (Δ : Bounds) :
    ∀ m, constantsTotal m = true → Submode Δ m m := by
  intro m hm
  cases m <;> simp only [constantsTotal, Bool.false_eq_true] at hm
  case const m =>
    exact .valid fun _ _ => ⟨m, m, rfl, rfl, Mode.le_refl m⟩

theorem partialMode_undefined (η : ModVar → Mode) :
    partialMode.eval (some ∘ η) = none := rfl

theorem normalize_composed_partial :
    normalizeOuter (.modal (.modal .unit partialMode) .epsilon) =
      normalizeOuter (.modal .unit (.compose partialMode .epsilon)) := by decide

def sharedRequests : List Request :=
  [⟨0, .compose partialMode (.const Mode.global), false⟩,
   ⟨0, .compose partialMode (.const Mode.many), false⟩]

theorem shared_prefix_plan :
    plan constantsTotal 0 1 sharedRequests =
      some ⟨0, 1, [partialMode], sharedRequests⟩ := by decide

theorem shared_prefix_bounds :
    (adapt constantsTotal [0] sharedRequests 1).bounds =
      [.mode (.var (.flex 1)) (.const Mode.global),
       .mode (.var (.flex 1)) (.const Mode.many)] := by decide

theorem shared_prefix_no_pending :
    (adapt constantsTotal [0] sharedRequests 1).pending = [] := by decide

/-- An exact body image may contain an undefined annotation. Source bounds
remain empty, so this uses only the ordinary body reflexivity rule. -/
theorem arbitrary_partial_mode_instantiation (m : ModExpr) :
    Subsumes [] { modParams := [0], body := .modal .unit (.var (.flex 0)) }
      (Scheme.mono (.modal .unit m)) := by
  change ∃ σ : Substitution,
    Instantiates { modParams := [0], body := .modal .unit (.var (.flex 0)) } σ ∧
      EntailsAll [] (σ.bounds []) ∧
      Subtype [] (σ.ty (.modal .unit (.var (.flex 0))))
        (({} : Substitution).ty (.modal .unit m))
  refine ⟨{ modes := [(0, m)] }, ⟨.refl _, .refl _⟩, ?_, ?_⟩
  · simp [EntailsAll, Substitution.bounds]
  · have hm : ({} : Substitution).mode = ModExpr.var := by funext v; cases v <;> rfl
    simpa [Substitution.ty, TypeExpr.subst, Substitution.mode, hm] using
      (Subtype.refl (Δ := []) (a := .modal .unit m))

/-- This joint example fixes the type image exactly. It does not infer a
subtype relation underneath an undefined outer modality. -/
theorem exact_type_mode_instantiation (a : Ty) (m : ModExpr) :
    Subsumes [] { typeParams := [0], modParams := [0], body := .modal (.var (.flex 0)) (.var (.flex 0)) }
      (Scheme.mono (.modal a m)) := by
  change ∃ σ : Substitution,
    Instantiates { typeParams := [0], modParams := [0], body := .modal (.var (.flex 0)) (.var (.flex 0)) } σ ∧
      EntailsAll [] (σ.bounds []) ∧
      Subtype [] (σ.ty (.modal (.var (.flex 0)) (.var (.flex 0))))
        (({} : Substitution).ty (.modal a m))
  refine ⟨{ types := [(0, a)], modes := [(0, m)] }, ⟨.refl _, .refl _⟩, ?_, ?_⟩
  · simp [EntailsAll, Substitution.bounds]
  · have ht : ({} : Substitution).type = TypeExpr.var := by funext v; cases v <;> rfl
    have hm : ({} : Substitution).mode = ModExpr.var := by funext v; cases v <;> rfl
    simpa [Substitution.ty, TypeExpr.subst, Substitution.type, Substitution.mode, ht, hm] using
      (Subtype.refl (Δ := []) (a := .modal a m))

end Examples

end ModalityInference.ComparisonPartialModes
