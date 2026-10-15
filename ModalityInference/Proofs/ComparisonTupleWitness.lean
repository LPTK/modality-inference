import ModalityInference.ComparisonTupleWitness
import ModalityInference.Proofs.ComparisonTupleCNF

/-! Correctness of the executable shared-coordinate type constructor. -/
namespace ModalityInference.ComparisonTupleWitness

open ComparisonControls ComparisonTupleReification ComparisonOpaqueObserver SymbolicModes

/-- Erasing membership proofs leaves the executable expression unchanged. -/
def erase : Formula b α → Expression α
  | .head a _ => .head a
  | .scalar a => .scalar a
  | .join a c => .join (erase a) (erase c)
  | .meet a c => .meet (erase a) (erase c)

theorem erase_map (e : Formula b α) (f : α → β) :
    erase (ComparisonTupleCNF.mapFormula f e) = (erase e).map f := by
  induction e <;> simp_all [erase, Expression.map, ComparisonTupleCNF.mapFormula]

private theorem literal_erase {b : Basis} {scalars : Nat → BoolExpr} {value : Literal}
    (hp : value.1 < b.heads.length → value.2 = true) :
    literal b scalars value = some (erase (ComparisonTupleCNF.literal b scalars value)) := by
  by_cases hi : value.1 < b.heads.length
  · simp [literal, ComparisonTupleCNF.literal, hi, hp hi, erase]
  · simp [literal, ComparisonTupleCNF.literal, hi, erase]

private theorem clause_erase {b : Basis} {scalars : Nat → BoolExpr} {c : Clause}
    (hp : ∀value∈c, value.1 < b.heads.length → value.2 = true) :
    clause b scalars c = some (erase (ComparisonTupleCNF.clause b scalars c)) := by
  induction c with
  | nil => rfl
  | cons value rest ih =>
    have hr := ih (fun v hv => hp v (List.mem_cons_of_mem _ hv))
    unfold clause at hr ⊢
    cases hm : rest.mapM (literal b scalars) with
    | none => simp [hm] at hr
    | some terms =>
      simp only [hm, bind, pure, Option.bind_some, Option.some.injEq] at hr
      simp [List.mapM_cons, literal_erase (hp value List.mem_cons_self), hm,
        ComparisonTupleCNF.clause, erase]
      exact hr

theorem cnf_erase {b : Basis} {scalars : Nat → BoolExpr} {cs : CNF}
    (hp : ComparisonTupleCNF.HeadPositive b.heads.length cs) :
    cnf b scalars cs = some (erase (ComparisonTupleCNF.cnf b scalars cs)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hr := ih (fun d hd => hp d (List.mem_cons_of_mem _ hd))
    unfold cnf at hr ⊢
    cases hm : cs.mapM (clause b scalars) with
    | none => simp [hm] at hr
    | some terms =>
      simp only [hm, bind, pure, Option.bind_some, Option.some.injEq] at hr
      simp [List.mapM_cons, clause_erase (hp c List.mem_cons_self), hm,
        ComparisonTupleCNF.cnf, erase]
      exact hr

private def heads (isJoin : Bool) (a : ComparisonControls.Generated b) :
    (xs : List CompareTy) → (∀x∈xs, x∈b.heads) → ComparisonControls.Generated b
  | [], _ => a
  | x :: xs, hx => heads isJoin
      (if isJoin then .join a (.head x (hx x List.mem_cons_self))
        else .meet a (.head x (hx x List.mem_cons_self))) xs
      (fun x h => hx x (List.mem_cons_of_mem _ h))

private def high (b : Basis) : ComparisonControls.Generated b :=
  heads true (.head b.head List.mem_cons_self) b.rest (fun _ h => List.mem_cons_of_mem _ h)

private def low (b : Basis) : ComparisonControls.Generated b :=
  heads false (.head b.head List.mem_cons_self) b.rest (fun _ h => List.mem_cons_of_mem _ h)

private theorem heads_term (j : Bool) (a : ComparisonControls.Generated b) (xs : List CompareTy) (hx) :
    (heads j a xs hx).term = xs.foldl (if j then CompareTy.join else CompareTy.meet) a.term := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => cases j <;> simpa [heads] using ih _ _

private theorem heads_total (j : Bool) (a : ComparisonControls.Generated b) (xs : List CompareTy) (hx)
    (ha : ComparisonTupleReification.Total a) : ComparisonTupleReification.Total (heads j a xs hx) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih => apply ih; cases j <;> exact ⟨ha, trivial⟩

private theorem heads_observe (j : Bool) (a : ComparisonControls.Generated b) (xs : List CompareTy)
    (hx) (coordinate : Coordinate) (h : CompareTy → Bool) (η : ModVar → Mode) :
    observe coordinate h η (heads j a xs hx) =
      if j then observe coordinate h η a || xs.any h
      else observe coordinate h η a && xs.all h := by
  induction xs generalizing a with
  | nil => cases j <;> simp [heads]
  | cons x xs ih => cases j <;> simp [heads, ih, observe, Bool.or_assoc, Bool.and_assoc]

@[simp] private theorem high_term (b : Basis) : (high b).term = upper b := by
  simp [high, heads_term, upper, ComparisonControls.Generated.term]
@[simp] private theorem low_term (b : Basis) : (low b).term = lower b := by
  simp [low, heads_term, lower, ComparisonControls.Generated.term]
@[simp] private theorem high_total (b : Basis) : ComparisonTupleReification.Total (high b) := heads_total _ _ _ _ trivial
@[simp] private theorem low_total (b : Basis) : ComparisonTupleReification.Total (low b) := heads_total _ _ _ _ trivial
@[simp] private theorem high_observe (c : Coordinate) (h : CompareTy → Bool) (η : ModVar → Mode) :
    observe c h η (high b) = b.heads.any h := by
  simp [high, heads_observe, observe, Basis.heads]
@[simp] private theorem low_observe (c : Coordinate) (h : CompareTy → Bool) (η : ModVar → Mode) :
    observe c h η (low b) = b.heads.all h := by
  simp [low, heads_observe, observe, Basis.heads]

private def scalarMode (axis : Axis) (e : BoolExpr) : ModExpr := (reify axis e).getD .epsilon

private theorem scalarMode_spec {b : Basis} {axis : Axis} {e : BoolExpr}
    (h : ComparisonTupleReification.Supported b axis e) :
    reify axis e = some (scalarMode axis e) ∧
      (∀v∈(scalarMode axis e).freeVariables, v∈b.modes) ∧
      ∀η, (scalarMode axis e).eval (some ∘ η) = some (axis.embed (e.eval (encodeModes η))) := by
  obtain ⟨m, hm⟩ := (reify_supported axis e).mpr (fun i hi => (h i hi).1)
  have he : scalarMode axis e = m := by simp [scalarMode, hm]
  refine ⟨he ▸ hm, ?_, fun η => he ▸ reify_eval hm η⟩
  intro v hv
  rw [he] at hv
  obtain ⟨i, hi, rfl⟩ := reify_variables hm v ((ModExpr.mem_freeVariables _ _).mp hv)
  exact (h i hi).2

private theorem constant_supported (b : Basis) (m : Mode) :
    ∀v∈(ModExpr.const m).freeVariables, v∈b.modes := by simp [ModExpr.freeVariables]

private theorem neg_supported {b : Basis} {axis : Axis} {e : BoolExpr}
    (h : ComparisonTupleReification.Supported b axis e) :
    ComparisonTupleReification.Supported b axis (.imp e (.const false)) := by
  simpa [ComparisonTupleReification.Supported, BoolExpr.atoms] using h

private def lowerGenerated (axis : Axis) (e : Formula b BoolExpr)
    (hs : e.All (ComparisonTupleReification.Supported b axis)) : ComparisonControls.Generated b :=
  match e with
  | .head a ha => .head a ha
  | .scalar e => .modal (high b) (scalarMode axis e) (scalarMode_spec hs).2.1
  | .join a c => .join (lowerGenerated axis a hs.1) (lowerGenerated axis c hs.2)
  | .meet a c => .meet (lowerGenerated axis a hs.1) (lowerGenerated axis c hs.2)

private theorem lowerGenerated_term (axis : Axis) (e : Formula b BoolExpr)
    (hs : e.All (ComparisonTupleReification.Supported b axis)) :
    lowerRaw b axis (erase e) = some (lowerGenerated axis e hs).term := by
  induction e with
  | head => rfl
  | scalar e => simp [erase, lowerRaw, lowerGenerated, (scalarMode_spec hs).1, ComparisonControls.Generated.term]
  | join a c iha ihc | meet a c iha ihc =>
    simp [erase, lowerRaw, lowerGenerated, iha hs.1, ihc hs.2, ComparisonControls.Generated.term]

private theorem lowerGenerated_total (axis : Axis) (e : Formula b BoolExpr)
    (hs : e.All (ComparisonTupleReification.Supported b axis)) : ComparisonTupleReification.Total (lowerGenerated axis e hs) := by
  induction e with
  | head => trivial
  | scalar e =>
    exact ⟨high_total b, fun η => by simp [ModExpr.WellFormed, (scalarMode_spec hs).2.2 η]⟩
  | join a c iha ihc | meet a c iha ihc => exact ⟨iha hs.1, ihc hs.2⟩

private theorem lowerGenerated_observe (e : Formula b BoolExpr) (axis : Axis)
    (haxis : axis = .locality ∨ axis = .affinity)
    (hs : e.All (ComparisonTupleReification.Supported b axis)) :
    ∀ h η coordinate,
      observe coordinate h η (lowerGenerated axis e hs) =
        if (axis = .locality ∧ coordinate = .locality) ∨
           (axis = .affinity ∧ coordinate = .affinity) then
          b.heads.any h && e.eval (fun c => c.eval (encodeModes η)) h
        else e.eval (fun _ => b.heads.any h) h := by
  induction e with
  | head a ha =>
    intro h η coordinate
    have hhi : h a = true → b.heads.any h = true := fun hh => List.any_eq_true.mpr ⟨a, ha, hh⟩
    simp only [lowerGenerated, observe, Formula.eval]
    split
    · cases he : h a <;> simp_all
    · rfl
  | scalar e =>
    intro h η coordinate
    have hc := ModExpr.complete_of_eval ((scalarMode_spec hs).2.2 η)
    rcases haxis with rfl | rfl <;> cases coordinate <;>
      simp [lowerGenerated, observe, Formula.eval, hc, applyMode, Axis.embed]
  | join a c iha ihc | meet a c iha ihc =>
    intro h η coordinate
    simp only [lowerGenerated, observe, Formula.eval, iha hs.1, ihc hs.2]
    split <;> simp_all [Bool.and_or_distrib_left, Bool.and_assoc, Bool.and_left_comm]

private theorem all_of_forall (e : Formula b α) (p : α → Prop) (h : ∀x, p x) : e.All p := by
  induction e <;> simp_all [Formula.All]

private def lowerGadgetGenerated (axis : Axis) (e : Formula b BoolExpr)
    (hs : e.All (ComparisonTupleReification.Supported b axis)) : ComparisonControls.Generated b :=
  .join (lowerGenerated axis e hs) (.modal (high b) (.const (axis.embed false)) (constant_supported _ _))

private theorem lowerGadgetGenerated_term (axis : Axis) (e : Formula b BoolExpr)
    (hs : e.All (ComparisonTupleReification.Supported b axis)) :
    lowerGadget b axis (erase e) = some (lowerGadgetGenerated axis e hs).term := by
  simp [lowerGadget, lowerGenerated_term axis e hs, lowerGadgetGenerated,
    ComparisonControls.Generated.term]

private theorem lowerGadgetGenerated_total (axis : Axis) (e : Formula b BoolExpr)
    (hs : e.All (ComparisonTupleReification.Supported b axis)) :
    ComparisonTupleReification.Total (lowerGadgetGenerated axis e hs) :=
  ⟨lowerGenerated_total axis e hs, high_total b, fun _ => rfl⟩

private theorem lowerGadgetGenerated_observe (e : Formula b BoolExpr) (axis : Axis)
    (haxis : axis = .locality ∨ axis = .affinity)
    (hs : e.All (ComparisonTupleReification.Supported b axis))
    (h : CompareTy → Bool) (η : ModVar → Mode) (coordinate : Coordinate) :
    observe coordinate h η (lowerGadgetGenerated axis e hs) =
      if (axis = .locality ∧ coordinate = .locality) ∨
         (axis = .affinity ∧ coordinate = .affinity) then
        b.heads.any h && e.eval (fun c => c.eval (encodeModes η)) h
      else b.heads.any h := by
  have he := lowerGenerated_observe e axis haxis hs
  have hb : e.eval (fun _ => b.heads.any h) h = true → b.heads.any h = true :=
    e.eval_upper _ _ _ (fun a ha hv => List.any_eq_true.mpr ⟨a, ha, hv⟩)
      (all_of_forall e _ (fun _ => id))
  rcases haxis with rfl | rfl <;> cases coordinate <;>
    simp only [lowerGadgetGenerated, observe, high_observe, ModExpr.complete, applyMode,
      Axis.embed, he, reduceCtorEq, and_true, and_false, false_or, or_false,
      if_true, if_false, Bool.and_false, Bool.or_false]
  all_goals
    cases h₁ : e.eval (fun _ => b.heads.any h) h <;>
      cases h₂ : b.heads.any h <;> simp_all

private def upperGenerated (e : Formula b BoolExpr)
    (hs : e.All (ComparisonTupleReification.Supported b .uniqueness)) : ComparisonControls.Generated b :=
  match e with
  | .head a ha => .modal (.head a ha) (.const Mode.bottom) (constant_supported _ _)
  | .scalar e => .modal
      (.modal (low b) (scalarMode .uniqueness (.imp e (.const false)))
        (scalarMode_spec (neg_supported hs)).2.1)
      (.const Mode.bottom) (constant_supported _ _)
  | .join a c => .join (upperGenerated a hs.1) (upperGenerated c hs.2)
  | .meet a c => .meet (upperGenerated a hs.1) (upperGenerated c hs.2)

private theorem upperGenerated_term (e : Formula b BoolExpr)
    (hs : e.All (ComparisonTupleReification.Supported b .uniqueness)) :
    upperRaw b (erase e) = some (upperGenerated e hs).term := by
  induction e with
  | head => rfl
  | scalar e =>
    simp [erase, upperRaw, upperGenerated, (scalarMode_spec (neg_supported hs)).1,
      ComparisonControls.Generated.term]
  | join a c iha ihc | meet a c iha ihc =>
    simp [erase, upperRaw, upperGenerated, iha hs.1, ihc hs.2, ComparisonControls.Generated.term]

private theorem upperGenerated_total (e : Formula b BoolExpr)
    (hs : e.All (ComparisonTupleReification.Supported b .uniqueness)) :
    ComparisonTupleReification.Total (upperGenerated e hs) := by
  induction e with
  | head => exact ⟨trivial, fun _ => rfl⟩
  | scalar e =>
    exact ⟨⟨low_total b, fun η => by
      simp [ModExpr.WellFormed, (scalarMode_spec (neg_supported hs)).2.2 η]⟩, fun _ => rfl⟩
  | join a c iha ihc | meet a c iha ihc => exact ⟨iha hs.1, ihc hs.2⟩

private theorem upperGenerated_observe (e : Formula b BoolExpr)
    (hs : e.All (ComparisonTupleReification.Supported b .uniqueness)) :
    ∀h η coordinate,
      observe coordinate h η (upperGenerated e hs) = match coordinate with
        | .unaffected => e.eval (fun _ => b.heads.all h) h
        | .locality | .affinity => false
        | .uniqueness => b.heads.all h || e.eval (fun c => c.eval (encodeModes η)) h := by
  induction e with
  | head a ha =>
    intro h η coordinate
    have hlo : b.heads.all h = true → h a = true := fun hh => List.all_eq_true.mp hh a ha
    cases coordinate <;> simp only [upperGenerated, observe, Formula.eval, ModExpr.complete,
      applyMode, Mode.bottom, Bool.and_false, Bool.not_true, Bool.or_false]
    cases h₁ : b.heads.all h <;> cases h₂ : h a <;> simp_all
  | scalar e =>
    intro h η coordinate
    have hc := ModExpr.complete_of_eval ((scalarMode_spec (neg_supported hs)).2.2 η)
    cases coordinate <;> simp [upperGenerated, observe, Formula.eval, hc, applyMode,
      Axis.embed, ModExpr.complete, Mode.bottom, BoolExpr.eval]
  | join a c iha ihc | meet a c iha ihc =>
    intro h η coordinate
    cases coordinate <;> simp [upperGenerated, observe, Formula.eval, iha hs.1, ihc hs.2,
      Bool.or_assoc, Bool.or_left_comm, Bool.or_and_distrib_left]

private def upperGadgetGenerated (e : Formula b BoolExpr)
    (hs : e.All (ComparisonTupleReification.Supported b .uniqueness)) : ComparisonControls.Generated b :=
  .meet (upperGenerated e hs) (.modal (low b) (.const ⟨false, false, false⟩) (constant_supported _ _))

private theorem upperGadgetGenerated_term (e : Formula b BoolExpr)
    (hs : e.All (ComparisonTupleReification.Supported b .uniqueness)) :
    upperGadget b (erase e) = some (upperGadgetGenerated e hs).term := by
  simp [upperGadget, upperGenerated_term e hs, upperGadgetGenerated, ComparisonControls.Generated.term]

private theorem upperGadgetGenerated_total (e : Formula b BoolExpr)
    (hs : e.All (ComparisonTupleReification.Supported b .uniqueness)) :
    ComparisonTupleReification.Total (upperGadgetGenerated e hs) :=
  ⟨upperGenerated_total e hs, low_total b, fun _ => rfl⟩

private theorem upperGadgetGenerated_observe (e : Formula b BoolExpr)
    (hs : e.All (ComparisonTupleReification.Supported b .uniqueness))
    (h : CompareTy → Bool) (η : ModVar → Mode) (coordinate : Coordinate) :
    observe coordinate h η (upperGadgetGenerated e hs) = match coordinate with
      | .unaffected => b.heads.all h
      | .locality | .affinity => false
      | .uniqueness => b.heads.all h || e.eval (fun c => c.eval (encodeModes η)) h := by
  have hb : b.heads.all h = true → e.eval (fun _ => b.heads.all h) h = true :=
    e.eval_lower _ _ _ (fun a ha hv => List.all_eq_true.mp hv a ha)
      (all_of_forall e _ (fun _ => id))
  cases coordinate <;>
    simp only [upperGadgetGenerated, observe, low_observe, ModExpr.complete, applyMode,
      upperGenerated_observe, Bool.and_false, Bool.not_false, Bool.or_true, Bool.and_true]
  cases h₁ : e.eval (fun _ => b.heads.all h) h <;> cases h₂ : b.heads.all h <;> simp_all

private def nominalGenerated : Formula b Bool → ComparisonControls.Generated b
  | .head a ha => .head a ha
  | .scalar v => if v then high b else low b
  | .join a c => .join (nominalGenerated a) (nominalGenerated c)
  | .meet a c => .meet (nominalGenerated a) (nominalGenerated c)

private theorem nominalGenerated_term (e : Formula b Bool) :
    nominal b (erase e) = (nominalGenerated e).term := by
  induction e with
  | head => rfl
  | scalar v => cases v <;> simp [nominal, erase, nominalGenerated]
  | join a c iha ihc | meet a c iha ihc =>
    simp [nominal, erase, nominalGenerated, ComparisonControls.Generated.term, iha, ihc]

private theorem nominalGenerated_total (e : Formula b Bool) :
    ComparisonTupleReification.Total (nominalGenerated e) := by
  induction e with
  | head => trivial
  | scalar v => cases v <;> simp [nominalGenerated]
  | join a c iha ihc | meet a c iha ihc => exact ⟨iha, ihc⟩

private theorem nominalGenerated_raw (e : Formula b Bool) (h : CompareTy → Bool)
    (η : ModVar → Mode) (coordinate : Coordinate) :
    observe coordinate h η (nominalGenerated e) =
      e.eval (fun v => if v then b.heads.any h else b.heads.all h) h := by
  induction e with
  | head => rfl
  | scalar v => cases v <;> simp [nominalGenerated, Formula.eval]
  | join a c iha ihc | meet a c iha ihc => simp [nominalGenerated, observe, Formula.eval, iha, ihc]

private theorem formula_constant (e : Formula b α) (scalar : α → Bool)
    (h : CompareTy → Bool) (v : Bool) (hh : ∀a∈b.heads, h a = v) (hs : ∀c, scalar c = v) :
    e.eval scalar h = v := by
  induction e <;> simp_all [Formula.eval]

private theorem heads_bounds (b : Basis) (h : CompareTy → Bool) :
    b.heads.all h = true → b.heads.any h = true := by
  intro hh
  exact List.any_eq_true.mpr ⟨b.head, List.mem_cons_self,
    List.all_eq_true.mp hh b.head List.mem_cons_self⟩

private theorem nominalGenerated_observe (p : Formula b Bool)
    (hp0 : p.eval id (fun _ => false) = false) (hp1 : p.eval id (fun _ => true) = true)
    (h : CompareTy → Bool) (η : ModVar → Mode) (coordinate : Coordinate) :
    observe coordinate h η (nominalGenerated p) = p.eval id h := by
  rw [nominalGenerated_raw]
  cases ha : b.heads.all h
  · cases ho : b.heads.any h
    · have hz : ∀a∈b.heads, h a = false := by simpa [List.any_eq_false] using ho
      rw [p.eval_congr_heads id hz, hp0]
      exact formula_constant p _ h false hz (by intro v; cases v <;> rfl)
    · have hs : (fun v : Bool => if v then true else false) = id := by
        funext v; cases v <;> rfl
      rw [hs]
  · have ho := heads_bounds b h ha
    have hz : ∀a∈b.heads, h a = true := List.all_eq_true.mp ha
    rw [p.eval_congr_heads id hz, hp1]
    exact formula_constant p _ h true hz (by intro v; cases v <;> simp [ho])

private theorem nominal_bounds {b : Basis} (p : Formula b Bool)
    (hp0 : p.eval id (fun _ => false) = false)
    (hp1 : p.eval id (fun _ => true) = true) (h : CompareTy → Bool) :
    (b.heads.all h = true → p.eval id h = true) ∧
      (p.eval id h = true → b.heads.any h = true) := by
  constructor
  · intro hh
    rw [p.eval_congr_heads id (fun a ha => List.all_eq_true.mp hh a ha)]
    exact hp1
  · intro hh
    cases ho : b.heads.any h
    · have hz : ∀a∈b.heads, h a = false := by simpa [List.any_eq_false] using ho
      rw [p.eval_congr_heads id hz, hp0] at hh
      contradiction
    · rfl

private def tupleGenerated (p : Formula b Bool) (l f u : Formula b BoolExpr)
    (hl : l.All (ComparisonTupleReification.Supported b .locality))
    (hf : f.All (ComparisonTupleReification.Supported b .affinity))
    (hu : u.All (ComparisonTupleReification.Supported b .uniqueness)) : ComparisonControls.Generated b :=
  .join (.meet (.meet (nominalGenerated p) (lowerGadgetGenerated .locality l hl))
    (lowerGadgetGenerated .affinity f hf)) (upperGadgetGenerated u hu)

private theorem tupleGenerated_total (p : Formula b Bool) (l f u : Formula b BoolExpr)
    (hl : l.All (ComparisonTupleReification.Supported b .locality))
    (hf : f.All (ComparisonTupleReification.Supported b .affinity))
    (hu : u.All (ComparisonTupleReification.Supported b .uniqueness)) :
    ComparisonTupleReification.Total (tupleGenerated p l f u hl hf hu) :=
  ⟨⟨⟨nominalGenerated_total p, lowerGadgetGenerated_total .locality l hl⟩,
    lowerGadgetGenerated_total .affinity f hf⟩, upperGadgetGenerated_total u hu⟩

private theorem tuple_bits (lo hi p l f u : Bool)
    (hlow : lo = true → p = true) (hhigh : p = true → hi = true)
    (hlp : l = true → p = true) (hfp : f = true → p = true)
    (hpu : p = true → u = true) :
    (((p && hi && hi) || lo) = p) ∧
      ((p && (hi && l) && hi) = l) ∧
      ((p && hi && (hi && f)) = f) ∧
      (((p && hi && hi) || (lo || u)) = u) := by
  cases lo <;> cases hi <;> cases p <;> cases l <;> cases f <;> cases u <;> simp_all

private theorem tupleGenerated_observe (p : Formula b Bool) (l f u : Formula b BoolExpr)
    (hp0 : p.eval id (fun _ => false) = false) (hp1 : p.eval id (fun _ => true) = true)
    (hl : l.All (ComparisonTupleReification.Supported b .locality))
    (hf : f.All (ComparisonTupleReification.Supported b .affinity))
    (hu : u.All (ComparisonTupleReification.Supported b .uniqueness))
    (h : CompareTy → Bool) (η : ModVar → Mode)
    (hlp : l.eval (fun c => c.eval (encodeModes η)) h = true → p.eval id h = true)
    (hfp : f.eval (fun c => c.eval (encodeModes η)) h = true → p.eval id h = true)
    (hpu : p.eval id h = true → u.eval (fun c => c.eval (encodeModes η)) h = true) :
    (observe .unaffected h η (tupleGenerated p l f u hl hf hu) = p.eval id h) ∧
      (observe .locality h η (tupleGenerated p l f u hl hf hu) =
        l.eval (fun c => c.eval (encodeModes η)) h) ∧
      (observe .affinity h η (tupleGenerated p l f u hl hf hu) =
        f.eval (fun c => c.eval (encodeModes η)) h) ∧
      (observe .uniqueness h η (tupleGenerated p l f u hl hf hu) =
        u.eval (fun c => c.eval (encodeModes η)) h) := by
  have hb := nominal_bounds p hp0 hp1 h
  simp only [tupleGenerated, observe, nominalGenerated_observe p hp0 hp1,
    lowerGadgetGenerated_observe l .locality (.inl rfl),
    lowerGadgetGenerated_observe f .affinity (.inr rfl), upperGadgetGenerated_observe,
    reduceCtorEq, and_true, and_false, or_false, false_or, if_true, if_false, Bool.or_false]
  exact tuple_bits _ _ _ _ _ _ hb.1 hb.2 hlp hfp hpu

/-- Precisely the support needed by the executable scalar reifier. -/
def CoordinateSupported (b : Basis) (axis : Axis) (scalars : Nat → BoolExpr) (cs : CNF) : Prop :=
  ∀i∈CNFPropagation.atoms cs, b.heads.length ≤ i →
    ComparisonTupleReification.Supported b axis (scalars i)

private theorem reconstructWith_generated {b : Basis} {scalars : Nat → BoolExpr} {p l f u : CNF}
    (hp : ComparisonTupleCNF.HeadPositive b.heads.length p)
    (hl : ComparisonTupleCNF.HeadPositive b.heads.length l)
    (hf : ComparisonTupleCNF.HeadPositive b.heads.length f)
    (hu : ComparisonTupleCNF.HeadPositive b.heads.length u)
    (sl : CoordinateSupported b .locality scalars l)
    (sf : CoordinateSupported b .affinity scalars f)
    (su : CoordinateSupported b .uniqueness scalars u) :
    reconstructWith b scalars p l f u = some
      (tupleGenerated (ComparisonTupleCNF.nominal b p) (ComparisonTupleCNF.cnf b scalars l)
        (ComparisonTupleCNF.cnf b scalars f) (ComparisonTupleCNF.cnf b scalars u)
        (ComparisonTupleCNF.cnf_supported sl) (ComparisonTupleCNF.cnf_supported sf)
        (ComparisonTupleCNF.cnf_supported su)).term := by
  simp only [reconstructWith, cnf_erase hp, cnf_erase hl, cnf_erase hf, cnf_erase hu,
    bind, Option.bind_some]
  rw [lowerGadgetGenerated_term .locality _ (ComparisonTupleCNF.cnf_supported sl),
    lowerGadgetGenerated_term .affinity _ (ComparisonTupleCNF.cnf_supported sf),
    upperGadgetGenerated_term _ (ComparisonTupleCNF.cnf_supported su)]
  simp only [Option.bind_some, pure]
  rw [← erase_map, nominalGenerated_term]
  rfl

private theorem nominal_common {b : Basis} {scalars : Nat → BoolExpr} {p : CNF}
    (hp : ComparisonTupleCNF.HeadPositive b.heads.length p)
    (hs : ComparisonPropagation.Supported (List.range b.heads.length) p)
    (h : CompareTy → Bool) (values : Nat → Bool) :
    (ComparisonTupleCNF.nominal b p).eval id h = true ↔
      CNFHolds (ComparisonTupleCNF.world b h scalars values) p := by
  rw [ComparisonTupleCNF.nominal_correct hp]
  apply CNFPropagation.holds_congr
  intro i hi
  have hit : i < b.heads.length := List.mem_range.mp (hs i hi)
  simp [ComparisonTupleCNF.world, hit]

/-- The actual constructor terminates with a single generated type. At every
head interpretation and shared mode valuation satisfying the three order
constraints, that same type realizes all four supplied coordinate clauses. -/
theorem reconstructWith_complete {b : Basis} {scalars : Nat → BoolExpr} {p l f u : CNF}
    (hp : ComparisonPropagation.Positive p)
    (hs : ComparisonPropagation.Supported (List.range b.heads.length) p)
    (hz : ¬CNFHolds (fun _ => false) p) (ho : CNFHolds (fun _ => true) p)
    (hl : ComparisonTupleCNF.HeadPositive b.heads.length l)
    (hf : ComparisonTupleCNF.HeadPositive b.heads.length f)
    (hu : ComparisonTupleCNF.HeadPositive b.heads.length u)
    (sl : CoordinateSupported b .locality scalars l)
    (sf : CoordinateSupported b .affinity scalars f)
    (su : CoordinateSupported b .uniqueness scalars u) :
    ∃ g : ComparisonControls.Generated b,
      reconstructWith b scalars p l f u = some g.term ∧ ComparisonTupleReification.Total g ∧
      ∀ h η,
        let w := ComparisonTupleCNF.world b h scalars (encodeModes η)
        (CNFHolds w l → CNFHolds w p) →
        (CNFHolds w f → CNFHolds w p) →
        (CNFHolds w p → CNFHolds w u) →
        (observe .unaffected h η g = true ↔ CNFHolds w p) ∧
        (observe .locality h η g = true ↔ CNFHolds w l) ∧
        (observe .affinity h η g = true ↔ CNFHolds w f) ∧
        (observe .uniqueness h η g = true ↔ CNFHolds w u) := by
  have hpp := ComparisonTupleCNF.positive_headPositive (b := b) hp
  let pp := ComparisonTupleCNF.nominal b p
  let ll := ComparisonTupleCNF.cnf b scalars l
  let ff := ComparisonTupleCNF.cnf b scalars f
  let uu := ComparisonTupleCNF.cnf b scalars u
  have hsl := ComparisonTupleCNF.cnf_supported sl
  have hsf := ComparisonTupleCNF.cnf_supported sf
  have hsu := ComparisonTupleCNF.cnf_supported su
  refine ⟨tupleGenerated pp ll ff uu hsl hsf hsu,
    reconstructWith_generated hpp hl hf hu sl sf su, tupleGenerated_total _ _ _ _ _ _ _, ?_⟩
  intro h η
  dsimp only
  intro hlp hfp hpu
  have he := nominal_common (scalars := scalars) hpp hs h (encodeModes η)
  have heL := ComparisonTupleCNF.cnf_correct (scalars := scalars) hl h (encodeModes η)
  have heF := ComparisonTupleCNF.cnf_correct (scalars := scalars) hf h (encodeModes η)
  have heU := ComparisonTupleCNF.cnf_correct (scalars := scalars) hu h (encodeModes η)
  have hn := ComparisonTupleCNF.nominal_normalized hp hs hz ho
  obtain ⟨e₀, e₁, e₂, e₃⟩ := tupleGenerated_observe pp ll ff uu hn.1 hn.2 hsl hsf hsu h η
    (fun hv => he.mpr (hlp (heL.mp hv))) (fun hv => he.mpr (hfp (heF.mp hv)))
    (fun hv => heU.mpr (hpu (he.mp hv)))
  exact ⟨e₀ ▸ he, e₁ ▸ heL, e₂ ▸ heF, e₃ ▸ heU⟩

/-- Construction preserves the supplied heads' shape, guards, and identifier
support. Every newly introduced modality label is total. -/
theorem reconstructWith_properties {b : Basis} {scalars : Nat → BoolExpr} {p l f u : CNF}
    (hp : ComparisonTupleCNF.HeadPositive b.heads.length p)
    (hl : ComparisonTupleCNF.HeadPositive b.heads.length l)
    (hf : ComparisonTupleCNF.HeadPositive b.heads.length f)
    (hu : ComparisonTupleCNF.HeadPositive b.heads.length u)
    (sl : CoordinateSupported b .locality scalars l)
    (sf : CoordinateSupported b .affinity scalars f)
    (su : CoordinateSupported b .uniqueness scalars u)
    {t : CompareTy} (ht : reconstructWith b scalars p l f u = some t)
    {Δ : Bounds} {shape : ComparisonShape} {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hh : ∀a∈b.heads, a.WellShaped Δ ∧ ComparisonShape.Equivalent Δ a.shape shape)
    (hd : ∀a∈b.heads, a.DefinedUnder Δ)
    (hP : ∀a∈b.heads, ComparisonInterpolation.Supports P Q a)
    (hQ : ∀v∈b.modes, Q v) :
    t.WellShaped Δ ∧ ComparisonShape.Equivalent Δ t.shape shape ∧
      t.DefinedUnder Δ ∧ ComparisonInterpolation.Supports P Q t := by
  have he := reconstructWith_generated hp hl hf hu sl sf su
  rw [ht] at he
  cases Option.some.inj he
  exact ⟨(shaped _ hh).1, (shaped _ hh).2,
    (tupleGenerated_total _ _ _ _ _ _ _).definedUnder hd,
    ComparisonTupleReification.supports _ P Q hP hQ⟩

end ModalityInference.ComparisonTupleWitness
