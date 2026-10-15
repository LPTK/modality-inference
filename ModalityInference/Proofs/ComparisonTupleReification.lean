import ModalityInference.Proofs.ComparisonOpaqueSlice
import ModalityInference.Proofs.SchemeModeSynthesis

/-! Reconstruction of one finite internal type from a shared nominal head
polynomial and three scalar-dependent coordinates. Positive head formulas keep
their scalar coefficients symbolic; ordered-coordinate consistency may be
conditional on the comparison theory. -/
namespace ModalityInference.ComparisonTupleReification

open ComparisonControls ComparisonOpaqueObserver SymbolicModes

/-- Positive head syntax with scalar coefficients. Scalar coefficients may
contain arbitrary Boolean operations, but head occurrences remain positive. -/
inductive Formula (b : Basis) (α : Type) where
  | head (a : CompareTy) (member : a ∈ b.heads)
  | scalar (value : α)
  | join (a c : Formula b α)
  | meet (a c : Formula b α)

def Formula.eval (scalar : α → Bool) (heads : CompareTy → Bool) : Formula b α → Bool
  | .head a _ => heads a
  | .scalar a => scalar a
  | .join a c => a.eval scalar heads || c.eval scalar heads
  | .meet a c => a.eval scalar heads && c.eval scalar heads

def Formula.All (p : α → Prop) : Formula b α → Prop
  | .head _ _ => True
  | .scalar a => p a
  | .join a c | .meet a c => a.All p ∧ c.All p

def Supported (b : Basis) (axis : Axis) (e : BoolExpr) : Prop :=
  ∀ i ∈ e.atoms, axis.Supports i ∧ atomVariable i ∈ b.modes

/-- Evaluation of a generated type with its supplied heads opaque. -/
def observe (coordinate : Coordinate) (heads : CompareTy → Bool)
    (η : ModVar → Mode) : ComparisonControls.Generated b → Bool
  | .head a _ => heads a
  | .join a c => observe coordinate heads η a || observe coordinate heads η c
  | .meet a c => observe coordinate heads η a && observe coordinate heads η c
  | .modal a m _ => applyMode coordinate (observe coordinate heads η a) (m.complete η)

def Total : ComparisonControls.Generated b → Prop
  | .head _ _ => True
  | .join a c | .meet a c => Total a ∧ Total c
  | .modal a m _ => Total a ∧ ∀ η, m.WellFormed η

private def foldHeads (isJoin : Bool) (a : ComparisonControls.Generated b) :
    (xs : List CompareTy) → (∀x∈xs, x∈b.heads) → ComparisonControls.Generated b
  | [], _ => a
  | x :: xs, hx => foldHeads isJoin
      (if isJoin then .join a (.head x (hx x List.mem_cons_self))
        else .meet a (.head x (hx x List.mem_cons_self))) xs
      (fun x h => hx x (List.mem_cons_of_mem _ h))

def upper (b : Basis) : ComparisonControls.Generated b :=
  foldHeads true (.head b.head List.mem_cons_self) b.rest
    (fun _ h => List.mem_cons_of_mem _ h)

def lower (b : Basis) : ComparisonControls.Generated b :=
  foldHeads false (.head b.head List.mem_cons_self) b.rest
    (fun _ h => List.mem_cons_of_mem _ h)

private theorem foldHeads_total (isJoin : Bool) (a : ComparisonControls.Generated b)
    (xs : List CompareTy) (hx) (ha : Total a) : Total (foldHeads isJoin a xs hx) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    apply ih
    cases isJoin <;> exact ⟨ha, trivial⟩

@[simp] theorem upper_total (b : Basis) : Total (upper b) := foldHeads_total _ _ _ _ trivial
@[simp] theorem lower_total (b : Basis) : Total (lower b) := foldHeads_total _ _ _ _ trivial

private theorem foldHeads_observe (isJoin : Bool) (a : ComparisonControls.Generated b) (xs : List CompareTy)
    (hx) (coordinate : Coordinate) (heads : CompareTy → Bool) (η : ModVar → Mode) :
    observe coordinate heads η (foldHeads isJoin a xs hx) =
      if isJoin then observe coordinate heads η a || xs.any heads
      else observe coordinate heads η a && xs.all heads := by
  induction xs generalizing a with
  | nil => cases isJoin <;> simp [foldHeads]
  | cons x xs ih =>
    cases isJoin <;> simp [foldHeads, ih, observe, Bool.or_assoc, Bool.and_assoc]

@[simp] theorem upper_observe (coordinate : Coordinate) (heads : CompareTy → Bool)
    (η : ModVar → Mode) : observe coordinate heads η (upper b) = b.heads.any heads := by
  simp [upper, foldHeads_observe, observe, Basis.heads]

@[simp] theorem lower_observe (coordinate : Coordinate) (heads : CompareTy → Bool)
    (η : ModVar → Mode) : observe coordinate heads η (lower b) = b.heads.all heads := by
  simp [lower, foldHeads_observe, observe, Basis.heads]

theorem Formula.eval_congr_heads (e : Formula b α) (scalar : α → Bool)
    {heads other : CompareTy → Bool} (h : ∀a∈b.heads, heads a = other a) :
    e.eval scalar heads = e.eval scalar other := by
  induction e <;> simp_all [Formula.eval]

theorem Formula.eval_upper (e : Formula b α) (scalar : α → Bool)
    (heads : CompareTy → Bool) (hi : Bool)
    (hh : ∀a∈b.heads, heads a = true → hi = true)
    (hs : e.All (fun c => scalar c = true → hi = true)) :
    e.eval scalar heads = true → hi = true := by
  induction e with
  | head a ha => exact hh a ha
  | scalar a => exact hs
  | join a c iha ihc =>
    simp only [Formula.eval, Bool.or_eq_true]
    exact fun h => h.elim (iha hs.1) (ihc hs.2)
  | meet a c iha _ => exact fun h => iha hs.1 (Bool.and_eq_true_iff.mp h).1

private theorem supported_reify {b : Basis} {axis : Axis} {e : BoolExpr}
    (h : Supported b axis e) :
    ∃ m, reify axis e = some m ∧
      (∀v∈m.freeVariables, v∈b.modes) ∧
      ∀η, m.eval (some ∘ η) = some (axis.embed (e.eval (encodeModes η))) := by
  obtain ⟨m, hm⟩ := (reify_supported axis e).mpr (fun i hi => (h i hi).1)
  refine ⟨m, hm, ?_, reify_eval hm⟩
  intro v hv
  obtain ⟨i, hi, rfl⟩ := reify_variables hm v ((ModExpr.mem_freeVariables _ _).mp hv)
  exact (h i hi).2

private theorem constant_supported (b : Basis) (m : Mode) :
    ∀v∈(ModExpr.const m).freeVariables, v∈b.modes := by simp [ModExpr.freeVariables]

/-- The low coordinates use a total scalar reification with the other axes neutral. -/
theorem lower_raw {b : Basis} (e : Formula b BoolExpr) (axis : Axis)
    (haxis : axis = .locality ∨ axis = .affinity)
    (hs : e.All (Supported b axis)) :
    ∃ g : ComparisonControls.Generated b, Total g ∧
      ∀ heads η coordinate,
        observe coordinate heads η g =
          if (axis = .locality ∧ coordinate = .locality) ∨
             (axis = .affinity ∧ coordinate = .affinity) then
            b.heads.any heads && e.eval (fun c => c.eval (encodeModes η)) heads
          else e.eval (fun _ => b.heads.any heads) heads := by
  induction e with
  | head a ha =>
    refine ⟨.head a ha, trivial, ?_⟩
    intro heads η coordinate
    have hhi : heads a = true → b.heads.any heads = true :=
      fun h => List.any_eq_true.mpr ⟨a, ha, h⟩
    simp only [observe, Formula.eval]
    split
    · cases he : heads a <;> simp_all
    · rfl
  | scalar c =>
    obtain ⟨m, _, hm, he⟩ := supported_reify hs
    refine ⟨.modal (upper b) m hm, ⟨upper_total b, fun η => by simp [ModExpr.WellFormed, he η]⟩, ?_⟩
    intro heads η coordinate
    have hc := ModExpr.complete_of_eval (he η)
    rcases haxis with rfl | rfl <;> cases coordinate <;>
      simp [observe, Formula.eval, hc, applyMode, Axis.embed]
  | join a c iha ihc =>
    obtain ⟨a', ha, hea⟩ := iha hs.1
    obtain ⟨c', hc, hec⟩ := ihc hs.2
    refine ⟨.join a' c', ⟨ha, hc⟩, ?_⟩
    intro heads η coordinate
    simp only [observe, Formula.eval, hea, hec]
    split <;> simp_all [Bool.and_or_distrib_left]
  | meet a c iha ihc =>
    obtain ⟨a', ha, hea⟩ := iha hs.1
    obtain ⟨c', hc, hec⟩ := ihc hs.2
    refine ⟨.meet a' c', ⟨ha, hc⟩, ?_⟩
    intro heads η coordinate
    simp only [observe, Formula.eval, hea, hec]
    split <;> simp_all [Bool.and_assoc, Bool.and_left_comm]

private theorem Formula.all_of_forall (e : Formula b α) (p : α → Prop)
    (h : ∀x, p x) : e.All p := by
  induction e <;> simp_all [Formula.All]

theorem Formula.eval_lower (e : Formula b α) (scalar : α → Bool)
    (heads : CompareTy → Bool) (lo : Bool)
    (hh : ∀a∈b.heads, lo = true → heads a = true)
    (hs : e.All (fun c => lo = true → scalar c = true)) :
    lo = true → e.eval scalar heads = true := by
  induction e with
  | head a ha => exact hh a ha
  | scalar a => exact hs
  | join a c iha _ => exact fun h => Bool.or_eq_true_iff.mpr (.inl (iha hs.1 h))
  | meet a c iha ihc => exact fun h => Bool.and_eq_true_iff.mpr ⟨iha hs.1 h, ihc hs.2 h⟩

/-- Locality and affinity can be set independently while all other coordinates
retain the common head join. -/
theorem lower_gadget {b : Basis} (e : Formula b BoolExpr) (axis : Axis)
    (haxis : axis = .locality ∨ axis = .affinity)
    (hs : e.All (Supported b axis)) :
    ∃ g : ComparisonControls.Generated b, Total g ∧
      ∀ heads η coordinate,
        observe coordinate heads η g =
          if (axis = .locality ∧ coordinate = .locality) ∨
             (axis = .affinity ∧ coordinate = .affinity) then
            b.heads.any heads && e.eval (fun c => c.eval (encodeModes η)) heads
          else b.heads.any heads := by
  obtain ⟨g, hg, he⟩ := lower_raw e axis haxis hs
  let pad : ComparisonControls.Generated b := .modal (upper b)
    (.const (axis.embed false)) (constant_supported _ _)
  refine ⟨.join g pad, ⟨hg, upper_total b, ?_⟩, ?_⟩
  · intro η; rfl
  intro heads η coordinate
  have hb : e.eval (fun _ => b.heads.any heads) heads = true → b.heads.any heads = true :=
    e.eval_upper _ _ _ (fun a ha hv => List.any_eq_true.mpr ⟨a, ha, hv⟩)
      (e.all_of_forall _ (fun _ => id))
  rcases haxis with rfl | rfl <;> cases coordinate <;>
    simp only [observe, pad, upper_observe, ModExpr.complete, applyMode, Axis.embed, he,
      reduceCtorEq, and_true, and_false, false_or, or_false,
      if_true, if_false, Bool.and_false, Bool.or_false]
  all_goals
    cases h₁ : e.eval (fun _ => b.heads.any heads) heads <;>
      cases h₂ : b.heads.any heads <;> simp_all

/-- Uniqueness is the order-dual channel: its scalar coefficients are added
above the common head meet. The other ordered coordinates are zero. -/
theorem upper_raw {b : Basis} (e : Formula b BoolExpr)
    (hs : e.All (Supported b .uniqueness)) :
    ∃ g : ComparisonControls.Generated b, Total g ∧
      ∀ heads η coordinate,
        observe coordinate heads η g = match coordinate with
          | .unaffected => e.eval (fun _ => b.heads.all heads) heads
          | .locality | .affinity => false
          | .uniqueness => b.heads.all heads || e.eval (fun c => c.eval (encodeModes η)) heads := by
  induction e with
  | head a ha =>
    refine ⟨.modal (.head a ha) (.const Mode.bottom) (constant_supported _ _),
      ⟨trivial, fun _ => rfl⟩, ?_⟩
    intro heads η coordinate
    have hlo : b.heads.all heads = true → heads a = true :=
      fun h => List.all_eq_true.mp h a ha
    cases coordinate <;> simp only [observe, Formula.eval, ModExpr.complete, applyMode,
      Mode.bottom, Bool.and_false, Bool.not_true, Bool.or_false]
    cases h₁ : b.heads.all heads <;> cases h₂ : heads a <;> simp_all
  | scalar c =>
    have hneg : Supported b .uniqueness (.imp c (.const false)) := by
      simpa [Supported, Formula.All, BoolExpr.atoms] using hs
    obtain ⟨m, _, hm, he⟩ := supported_reify hneg
    refine ⟨.modal (.modal (lower b) m hm) (.const Mode.bottom) (constant_supported _ _),
      ⟨⟨lower_total b, fun η => by simp [ModExpr.WellFormed, he η]⟩, fun _ => rfl⟩, ?_⟩
    intro heads η coordinate
    have hc := ModExpr.complete_of_eval (he η)
    cases coordinate <;> simp [observe, Formula.eval, hc, applyMode, Axis.embed,
      ModExpr.complete, Mode.bottom, BoolExpr.eval]
  | join a c iha ihc =>
    obtain ⟨a', ha, hea⟩ := iha hs.1
    obtain ⟨c', hc, hec⟩ := ihc hs.2
    refine ⟨.join a' c', ⟨ha, hc⟩, ?_⟩
    intro heads η coordinate
    cases coordinate <;> simp [observe, Formula.eval, hea, hec, Bool.or_assoc, Bool.or_left_comm]
  | meet a c iha ihc =>
    obtain ⟨a', ha, hea⟩ := iha hs.1
    obtain ⟨c', hc, hec⟩ := ihc hs.2
    refine ⟨.meet a' c', ⟨ha, hc⟩, ?_⟩
    intro heads η coordinate
    cases coordinate <;> simp [observe, Formula.eval, hea, hec, Bool.or_and_distrib_left]

/-- The uniqueness gadget retains the common head meet in the unaffected
coordinate and zero in locality and affinity. -/
theorem upper_gadget {b : Basis} (e : Formula b BoolExpr)
    (hs : e.All (Supported b .uniqueness)) :
    ∃ g : ComparisonControls.Generated b, Total g ∧
      ∀ heads η coordinate,
        observe coordinate heads η g = match coordinate with
          | .unaffected => b.heads.all heads
          | .locality | .affinity => false
          | .uniqueness => b.heads.all heads || e.eval (fun c => c.eval (encodeModes η)) heads := by
  obtain ⟨g, hg, he⟩ := upper_raw e hs
  let pad : ComparisonControls.Generated b := .modal (lower b)
    (.const ⟨false, false, false⟩) (constant_supported _ _)
  refine ⟨.meet g pad, ⟨hg, lower_total b, fun _ => rfl⟩, ?_⟩
  intro heads η coordinate
  have hb : b.heads.all heads = true → e.eval (fun _ => b.heads.all heads) heads = true :=
    e.eval_lower _ _ _ (fun a ha hv => List.all_eq_true.mp hv a ha)
      (e.all_of_forall _ (fun _ => id))
  cases coordinate <;>
    simp only [observe, pad, lower_observe, ModExpr.complete, applyMode, he,
      Bool.and_false, Bool.not_false, Bool.or_true, Bool.and_true]
  cases h₁ : e.eval (fun _ => b.heads.all heads) heads <;>
    cases h₂ : b.heads.all heads <;> simp_all

private theorem Formula.eval_constant (e : Formula b α) (scalar : α → Bool)
    (heads : CompareTy → Bool) (v : Bool)
    (hh : ∀a∈b.heads, heads a = v) (hs : ∀c, scalar c = v) :
    e.eval scalar heads = v := by
  induction e <;> simp_all [Formula.eval]

private theorem heads_bounds (b : Basis) (heads : CompareTy → Bool) :
    b.heads.all heads = true → b.heads.any heads = true := by
  intro h
  exact List.any_eq_true.mpr ⟨b.head, List.mem_cons_self,
    List.all_eq_true.mp h b.head List.mem_cons_self⟩

private theorem nominal_bounds {b : Basis} (p : Formula b Bool)
    (hp0 : p.eval id (fun _ => false) = false)
    (hp1 : p.eval id (fun _ => true) = true) (heads : CompareTy → Bool) :
    (b.heads.all heads = true → p.eval id heads = true) ∧
      (p.eval id heads = true → b.heads.any heads = true) := by
  constructor
  · intro h
    rw [p.eval_congr_heads id (fun a ha => List.all_eq_true.mp h a ha)]
    exact hp1
  · intro h
    cases hh : b.heads.any heads
    · have hz : ∀a∈b.heads, heads a = false := by
        simpa [List.any_eq_false] using hh
      rw [p.eval_congr_heads id hz, hp0] at h
      contradiction
    · rfl

/-- A normalized head polynomial is reified without introducing scalar input
dependence or a lattice extremum outside its finite head family. -/
theorem nominal {b : Basis} (p : Formula b Bool)
    (hp0 : p.eval id (fun _ => false) = false)
    (hp1 : p.eval id (fun _ => true) = true) :
    ∃ g : ComparisonControls.Generated b, Total g ∧
      ∀ heads η coordinate, observe coordinate heads η g = p.eval id heads := by
  have raw (e : Formula b Bool) : ∃ g : ComparisonControls.Generated b, Total g ∧
      ∀heads η coordinate, observe coordinate heads η g =
        e.eval (fun v => if v then b.heads.any heads else b.heads.all heads) heads := by
    induction e with
    | head a ha => exact ⟨.head a ha, trivial, fun _ _ _ => rfl⟩
    | scalar v =>
      cases v
      · exact ⟨lower b, lower_total b, fun _ _ _ => lower_observe _ _ _⟩
      · exact ⟨upper b, upper_total b, fun _ _ _ => upper_observe _ _ _⟩
    | join a c iha ihc =>
      obtain ⟨a', ha, hea⟩ := iha
      obtain ⟨c', hc, hec⟩ := ihc
      exact ⟨.join a' c', ⟨ha, hc⟩, by intros; simp [observe, Formula.eval, hea, hec]⟩
    | meet a c iha ihc =>
      obtain ⟨a', ha, hea⟩ := iha
      obtain ⟨c', hc, hec⟩ := ihc
      exact ⟨.meet a' c', ⟨ha, hc⟩, by intros; simp [observe, Formula.eval, hea, hec]⟩
  obtain ⟨g, hg, he⟩ := raw p
  refine ⟨g, hg, ?_⟩
  intro heads η coordinate
  rw [he]
  cases ha : b.heads.all heads
  · cases ho : b.heads.any heads
    · have hz : ∀a∈b.heads, heads a = false := by simpa [List.any_eq_false] using ho
      rw [p.eval_congr_heads id hz, hp0]
      exact p.eval_constant _ heads false hz (by intro v; cases v <;> rfl)
    · have hs : (fun v : Bool => if v then true else false) = id := by
        funext v; cases v <;> rfl
      rw [hs]
  · have ho := heads_bounds b heads ha
    have hz : ∀a∈b.heads, heads a = true := List.all_eq_true.mp ha
    rw [p.eval_congr_heads id hz, hp1]
    exact p.eval_constant _ heads true hz (by intro v; cases v <;> simp [ho])

private theorem tuple_bits (lo hi p l f u : Bool)
    (hlow : lo = true → p = true) (hhigh : p = true → hi = true)
    (hlp : l = true → p = true) (hfp : f = true → p = true)
    (hpu : p = true → u = true) :
    (((p && hi && hi) || lo) = p) ∧
      ((p && (hi && l) && hi) = l) ∧
      ((p && hi && (hi && f)) = f) ∧
      (((p && hi && hi) || (lo || u)) = u) := by
  cases lo <;> cases hi <;> cases p <;> cases l <;> cases f <;> cases u <;> simp_all

/-- One finite type realizes all four coordinates at every interpretation where
the ordered coordinates bound the shared nominal polynomial. The scalar
inequalities may therefore be available only under the comparison's theory. -/
theorem reify_tuple {b : Basis} (p : Formula b Bool)
    (l f u : Formula b BoolExpr)
    (hp0 : p.eval id (fun _ => false) = false)
    (hp1 : p.eval id (fun _ => true) = true)
    (hl : l.All (Supported b .locality))
    (hf : f.All (Supported b .affinity))
    (hu : u.All (Supported b .uniqueness)) :
    ∃ g : ComparisonControls.Generated b, Total g ∧
      ∀ heads η,
        (l.eval (fun c => c.eval (encodeModes η)) heads = true → p.eval id heads = true) →
        (f.eval (fun c => c.eval (encodeModes η)) heads = true → p.eval id heads = true) →
        (p.eval id heads = true → u.eval (fun c => c.eval (encodeModes η)) heads = true) →
        (observe .unaffected heads η g = p.eval id heads) ∧
        (observe .locality heads η g = l.eval (fun c => c.eval (encodeModes η)) heads) ∧
        (observe .affinity heads η g = f.eval (fun c => c.eval (encodeModes η)) heads) ∧
        (observe .uniqueness heads η g = u.eval (fun c => c.eval (encodeModes η)) heads) := by
  obtain ⟨np, hnp, hep⟩ := nominal p hp0 hp1
  obtain ⟨nl, hnl, hel⟩ := lower_gadget l .locality (.inl rfl) hl
  obtain ⟨nf, hnf, hef⟩ := lower_gadget f .affinity (.inr rfl) hf
  obtain ⟨nu, hnu, heu⟩ := upper_gadget u hu
  refine ⟨.join (.meet (.meet np nl) nf) nu, ⟨⟨⟨hnp, hnl⟩, hnf⟩, hnu⟩, ?_⟩
  intro heads η hlp hfp hpu
  have hb := nominal_bounds p hp0 hp1 heads
  simp only [observe, hep, hel, hef, heu, reduceCtorEq, and_true, and_false,
    or_false, false_or, if_true, if_false, Bool.or_false]
  exact tuple_bits _ _ _ _ _ _ hb.1 hb.2 hlp hfp hpu

/-- The opaque-head evaluation is exactly the existing executable coordinate
formula evaluation, with arbitrary caller-selected atom namespaces. -/
theorem observe_formula {b : Basis} (g : ComparisonControls.Generated b) (ht : Total g)
    (headAtom modeAtom : Nat → Nat) (coordinate : Coordinate) (σ : Nat → Bool) :
    (g.formula headAtom modeAtom coordinate).eval σ =
      observe coordinate (fun a => σ (headAtom (b.heads.idxOf a)))
        (projectedModes (σ ∘ modeAtom)) g := by
  induction g with
  | head a ha => rfl
  | join a c iha ihc | meet a c iha ihc =>
    simp only [ComparisonControls.Generated.formula, BoolExpr.eval, observe, iha ht.1, ihc ht.2]
  | modal a m hm ih =>
    rw [ComparisonControls.Generated.formula,
      modalWith_value _ _ _ _ _ (ht.2 _), observe, ih ht.1]

/-- Total construction labels preserve definedness of all supplied heads. -/
theorem Total.definedUnder {b : Basis} {g : ComparisonControls.Generated b}
    (ht : Total g) {Δ : Bounds} (hh : ∀a∈b.heads, a.DefinedUnder Δ) :
    g.term.DefinedUnder Δ := by
  induction g with
  | head a ha => exact hh a ha
  | join a c iha ihc | meet a c iha ihc =>
    intro η hη d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact iha ht.1 η hη d hd
    · exact ihc ht.2 η hη d hd
  | modal a m hm ih =>
    apply CompareTy.definedUnder_modal_iff.mpr
    exact ⟨ih ht.1, fun η _ => ht.2 η⟩

/-- No modality outside the supplied finite family enters a generated term. -/
theorem supports {b : Basis} (g : ComparisonControls.Generated b)
    (P : TypeVar → Prop) (Q : ModVar → Prop)
    (hh : ∀a∈b.heads, ComparisonInterpolation.Supports P Q a)
    (hm : ∀m∈b.modes, Q m) : ComparisonInterpolation.Supports P Q g.term := by
  induction g with
  | head a ha => exact hh a ha
  | join a c iha ihc | meet a c iha ihc => exact ⟨iha, ihc⟩
  | modal a m hms ih =>
    exact ⟨ih, fun v hv => hm v (hms v ((m.mem_freeVariables v).mpr hv))⟩

/-- Common-shape heads give a legal internal type throughout the construction. -/
theorem shaped {b : Basis} (g : ComparisonControls.Generated b)
    {Δ : Bounds} {shape : ComparisonShape}
    (hh : ∀a∈b.heads, a.WellShaped Δ ∧ ComparisonShape.Equivalent Δ a.shape shape) :
    g.term.WellShaped Δ ∧ ComparisonShape.Equivalent Δ g.term.shape shape := by
  induction g with
  | head a ha => exact hh a ha
  | join a c iha ihc | meet a c iha ihc =>
    exact ⟨⟨iha.1, ihc.1, iha.2.trans ihc.2.symm⟩, iha.2⟩
  | modal a m hm ih => exact ih

def tupleValue (p : Formula b Bool) (l f u : Formula b BoolExpr)
    (heads : CompareTy → Bool) (modes : Nat → Bool) : Coordinate → Bool
  | .unaffected => p.eval id heads
  | .locality => l.eval (fun c => c.eval modes) heads
  | .affinity => f.eval (fun c => c.eval modes) heads
  | .uniqueness => u.eval (fun c => c.eval modes) heads

/-- The constructed tuple is expressible by one positive polynomial over the
actual finite control basis, and the executable type reifier accepts it. -/
theorem reify_tuple_polynomial {b : Basis} (p : Formula b Bool)
    (l f u : Formula b BoolExpr)
    (hp0 : p.eval id (fun _ => false) = false)
    (hp1 : p.eval id (fun _ => true) = true)
    (hl : l.All (Supported b .locality))
    (hf : f.All (Supported b .affinity))
    (hu : u.All (Supported b .uniqueness)) :
    ∃ clauses t, Polynomial b clauses ∧
      ComparisonPropagation.reify b.types clauses = some t ∧
      ∀ basisAtom headAtom modeAtom coordinate σ,
        (b.theoryAt basisAtom headAtom modeAtom coordinate).eval σ = true →
        let heads := fun a => σ (headAtom (b.heads.idxOf a))
        let scalar := fun c : BoolExpr => c.eval (σ ∘ modeAtom)
        (l.eval scalar heads = true → p.eval id heads = true) →
        (f.eval scalar heads = true → p.eval id heads = true) →
        (p.eval id heads = true → u.eval scalar heads = true) →
        (CNFHolds (σ ∘ basisAtom) clauses ↔
          tupleValue p l f u heads (σ ∘ modeAtom) coordinate = true) := by
  obtain ⟨g, hg, he⟩ := reify_tuple p l f u hp0 hp1 hl hf hu
  obtain ⟨clauses, hp, hclauses⟩ := g.representable
  obtain ⟨t, ht⟩ := hp.reify
  refine ⟨clauses, t, hp, ht, ?_⟩
  intro basisAtom headAtom modeAtom coordinate σ htheory
  dsimp only
  intro hlp hfp hpu
  rw [hclauses _ _ _ _ _ htheory, observe_formula g hg]
  have htuple := he (fun a => σ (headAtom (b.heads.idxOf a)))
    (projectedModes (σ ∘ modeAtom))
  simp only [SchemeModeSynthesis.encodeModes_projectedModes] at htuple
  obtain ⟨h₀, h₁, h₂, h₃⟩ := htuple hlp hfp hpu
  cases coordinate <;> simp only [tupleValue, h₀, h₁, h₂, h₃]

end ModalityInference.ComparisonTupleReification
