import ModalityInference.ComparisonControls
import ModalityInference.Proofs.CompactCNF
import ModalityInference.Proofs.SymbolicModes
import ModalityInference.Proofs.SymbolicCNF
import ModalityInference.Proofs.SyntacticEquality
import ModalityInference.Proofs.ComparisonPropagation

/-! Signed controls are total modalities. Compilation preserves finite support
and denotes an exact Boolean polynomial in the chosen endpoint interval. -/
namespace ModalityInference.ComparisonControls

deriving instance ReflBEq for Channel
deriving instance LawfulBEq for Channel
deriving instance ReflBEq for CompareTy, Control, Key
deriving instance LawfulBEq for CompareTy, Control, Key

theorem atomControl_spec {channel i positive c} (h : atomControl channel i positive = some c) :
    c.channel = channel ∧ c.atom = i ∧ c.positive = positive ∧ c.name = SymbolicModes.atomVariable i := by
  have hi : i % 3 < 3 := Nat.mod_lt _ (by decide)
  have hre : (SymbolicModes.atomVariable i).atomIndex (i % 3) = i := by
    by_cases he : i / 3 % 2 = 0 <;>
      simp [SymbolicModes.atomVariable, he, ModVar.atomIndex] <;> omega
  generalize he : i % 3 = k at hi
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  all_goals cases channel <;> simp [atomControl, he] at h
  all_goals cases h; simpa [Control.channel, Control.atom, Control.positive, Control.name, he] using hre

theorem control_project (c : Control) (σ : Nat → Bool) :
    c.expression.project.eval σ = some (c.axis.embed
      (if c.channel == .lower then !(σ c.atom == c.positive) else σ c.atom == c.positive)) := by
  cases c with
  | locality v p => cases p <;>
      simp [Control.expression, Control.channel, Control.positive, Control.bit, Control.axis,
        Control.atom, ModExpr.project, Projection.eval, BoolExpr.eval, BoolExpr.all,
        SymbolicModes.Axis.embed]
  | affinity v u p | uniqueness v u p => cases u <;> cases p <;>
      simp [Control.expression, Control.channel, Control.positive, Control.bit, Control.axis,
        Control.atom, ModExpr.project, Projection.eval, BoolExpr.eval, BoolExpr.all,
        SymbolicModes.Axis.embed, ModExpr.epsilon, Mode.identity]

theorem control_eval (c : Control) (η : ModVar → Mode) :
    c.expression.eval (some ∘ η) = some (c.axis.embed
      (if c.channel == .lower then !(encodeModes η c.atom == c.positive)
       else encodeModes η c.atom == c.positive)) := by
  simpa only [ModExpr.project_correct, projectedModes_encodeModes] using control_project c (encodeModes η)

theorem control_total (c : Control) (η : ModVar → Mode) : c.expression.WellFormed η := by
  simp [ModExpr.WellFormed, control_eval]

theorem formula_interval (b : Basis) (headAtom modeAtom : Nat → Nat) (coordinate : Coordinate)
    (channel : Channel) (σ : Nat → Bool) :
    (b.formula headAtom modeAtom coordinate channel.lowerKey).eval σ = true →
      (b.formula headAtom modeAtom coordinate channel.upperKey).eval σ = true := by
  cases coordinate <;> cases channel <;>
    simp [Basis.formula, Coordinate.modalWith, Channel.lowerKey, Channel.upperKey,
      SymbolicCNF.substitute_eval, ModExpr.project, BoolExpr.eval,
      Mode.bottom, Mode.top, Mode.global, Mode.many]

theorem formula_control (b : Basis) (headAtom modeAtom : Nat → Nat) (coordinate : Coordinate)
    (control : Control) (σ : Nat → Bool) :
    (b.formula headAtom modeAtom coordinate (.control control)).eval σ =
      ((b.formula headAtom modeAtom coordinate control.channel.lowerKey).eval σ ||
        ((b.formula headAtom modeAtom coordinate control.channel.upperKey).eval σ &&
          (σ (modeAtom control.atom) == control.positive))) := by
  cases control with
  | locality v p => cases p <;> cases coordinate <;>
      simp [Basis.formula, Coordinate.modalWith, Channel.lowerKey, Channel.upperKey,
        SymbolicCNF.substitute_eval, ModExpr.project, BoolExpr.eval, BoolExpr.all,
        Mode.top, Mode.global, Control.channel, Control.expression,
        Control.positive, Control.bit, Control.axis, Control.atom, SymbolicModes.Axis.embed] <;> tauto
  | affinity v u p | uniqueness v u p => cases u <;> cases p <;> cases coordinate <;>
      simp [Basis.formula, Coordinate.modalWith, Channel.lowerKey, Channel.upperKey,
        SymbolicCNF.substitute_eval, ModExpr.project, BoolExpr.eval, BoolExpr.all,
        Mode.bottom, Mode.top, Mode.many, Control.channel, Control.expression,
        Control.positive, Control.bit, Control.axis, Control.atom, SymbolicModes.Axis.embed,
        ModExpr.epsilon, Mode.identity] <;> tauto

private theorem mapM_length {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => simpa using h.symm
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨y, hy, rest, hr, rfl⟩ := h
    simpa using ih hr

private theorem mapM_mem {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at h; subst ys; simp at hy
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, rest, hr, rfl⟩ := h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x, by simp, ha⟩
    · obtain ⟨z, hz, he⟩ := ih hr hy
      exact ⟨z, List.mem_cons_of_mem _ hz, he⟩

private theorem mapM_mem_input {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b, hb, rest, hr, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, by simp, hb⟩
    · obtain ⟨z, hz, he⟩ := ih hr hx
      exact ⟨z, List.mem_cons_of_mem _ hz, he⟩

private theorem mapM_exists {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) (P : β → Prop) :
    (∃ y ∈ ys, P y) ↔ ∃ x ∈ xs, ∃ y, f x = some y ∧ P y := by
  constructor
  · rintro ⟨y, hy, hp⟩
    obtain ⟨x, hx, he⟩ := mapM_mem h hy
    exact ⟨x, hx, y, he, hp⟩
  · rintro ⟨x, hx, y, he, hp⟩
    obtain ⟨z, hz, hf⟩ := mapM_mem_input h hx
    have hz' : z = y := Option.some.inj (hf.symm.trans he)
    exact ⟨y, hz' ▸ hz, hp⟩

private theorem mapM_forall {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) (P : β → Prop) :
    (∀ y ∈ ys, P y) ↔ ∀ x ∈ xs, ∃ y, f x = some y ∧ P y := by
  constructor
  · intro hp x hx
    obtain ⟨y, hy, he⟩ := mapM_mem_input h hx
    exact ⟨y, he, hp y hy⟩
  · intro hp y hy
    obtain ⟨x, hx, he⟩ := mapM_mem h hy
    obtain ⟨z, hz, hp⟩ := hp x hx
    exact Option.some.inj (hz.symm.trans he) ▸ hp

theorem index_bound {b k i} (h : Basis.index b k = some i) : i < b.types.length := by
  unfold Basis.index at h
  dsimp only at h
  split at h <;> simp at h
  subst i
  simpa [Basis.types] using ‹b.keys.idxOf k < b.keys.length›

theorem index_lookup {b k i} (h : Basis.index b k = some i) : b.keys[i]? = some k := by
  unfold Basis.index at h
  dsimp only at h
  split at h <;> simp at h
  subst i
  refine List.getElem?_eq_some_iff.mpr ⟨‹_›, ?_⟩
  simpa only [List.idxOf, beq_iff_eq] using
    (List.findIdx_getElem (xs := b.keys) (p := (· == k)) (w := ‹_›))

private theorem all_eval_true (es : List BoolExpr) (σ : Nat → Bool) :
    (BoolExpr.all es).eval σ = true ↔ ∀ e ∈ es, e.eval σ = true := by
  induction es <;> simp_all [BoolExpr.all, BoolExpr.eval]

private theorem equal_eval_true (a b : BoolExpr) (σ : Nat → Bool) :
    (BoolExpr.equal a b).eval σ = true ↔ a.eval σ = b.eval σ := by
  cases ha : a.eval σ <;> cases hb : b.eval σ <;> simp_all [BoolExpr.equal, BoolExpr.eval]

theorem theoryAt_index {b basisAtom headAtom modeAtom coordinate σ k i}
    (h : (Basis.theoryAt b basisAtom headAtom modeAtom coordinate).eval σ = true)
    (hi : b.index k = some i) :
    σ (basisAtom i) = (b.formula headAtom modeAtom coordinate k).eval σ := by
  change (BoolExpr.atom (basisAtom i)).eval σ = _
  apply (equal_eval_true _ _ σ).mp
  apply (all_eval_true _ _).mp h
  exact List.mem_iff_getElem?.mpr ⟨i, by simp [index_lookup hi]⟩

/-- Every output clause is inhabited and consists solely of positive basis atoms. -/
theorem liftClause_shape {b c input output} (h : liftClause b c input = some output) :
    output ≠ [] ∧ ∀ literal ∈ output, literal.2 = true ∧ literal.1 < b.types.length := by
  cases input with
  | nil =>
    cases hi : b.index c.lowerKey <;> simp [liftClause, hi] at h
    subst output
    exact ⟨by simp, by simpa using index_bound hi⟩
  | cons literal rest =>
    have hm := h
    change ((literal :: rest).mapM _ = some output) at hm
    constructor
    · have hn := mapM_length hm
      intro he
      simp [he] at hn
    · intro l hl
      obtain ⟨⟨i, p⟩, hi, hs⟩ := mapM_mem hm hl
      cases hc : atomControl c i p <;> simp [hc] at hs
      rename_i control
      cases hx : b.index (.control control) <;> simp [hx] at hs
      subst l
      exact ⟨rfl, index_bound hx⟩

theorem liftCNF_shape {b c input output} (h : liftCNF b c input = some output) :
    output ≠ [] ∧ ∀ clause ∈ output, clause ≠ [] ∧
      ∀ literal ∈ clause, literal.2 = true ∧ literal.1 < b.types.length := by
  cases input with
  | nil =>
    cases hi : b.index c.upperKey <;> simp [liftCNF, hi] at h
    subst output
    exact ⟨by simp, by simpa using index_bound hi⟩
  | cons clause rest =>
    have hm : (clause :: rest).mapM (liftClause b c) = some output := h
    constructor
    · have hn := mapM_length hm
      intro he
      simp [he] at hn
    · intro d hd
      obtain ⟨a, ha, he⟩ := mapM_mem hm hd
      exact liftClause_shape he

theorem compile_shape {fuel b c positive e output}
    (h : compile fuel b c positive e = .success output) :
    output ≠ [] ∧ ∀ clause ∈ output, clause ≠ [] ∧
      ∀ literal ∈ clause, literal.2 = true ∧ literal.1 < b.types.length := by
  cases hn : CompactCNF.toCNF fuel positive e <;>
    simp [compile, hn, bind, RunResult.bind] at h
  rename_i input
  cases hl : liftCNF b c input <;> simp [hl, pure] at h
  subst output
  exact liftCNF_shape hl

theorem compile_zero {fuel b c positive e output}
    (h : compile fuel b c positive e = .success output) (σ : Nat → Bool)
    (hzero : ∀ i < b.types.length, σ i = false) : ¬ CNFHolds σ output := by
  intro hm
  obtain ⟨clause, hc⟩ := List.exists_mem_of_ne_nil _ (compile_shape h).1
  obtain ⟨i, p, hi, he⟩ := hm clause hc
  have ⟨hp, hb⟩ := ((compile_shape h).2 clause hc).2 (i, p) hi
  exact Bool.noConfusion ((hzero i hb).symm.trans (he.trans hp))

theorem compile_one {fuel b c positive e output}
    (h : compile fuel b c positive e = .success output) (σ : Nat → Bool)
    (hone : ∀ i < b.types.length, σ i = true) : CNFHolds σ output := by
  intro clause hc
  obtain ⟨⟨i, p⟩, hi⟩ := List.exists_mem_of_ne_nil _ ((compile_shape h).2 clause hc).1
  have ⟨hp, hb⟩ := ((compile_shape h).2 clause hc).2 (i, p) hi
  exact ⟨i, p, hi, (hone i hb).trans hp.symm⟩

private theorem high_parts {fuel b m output} (h : high fuel b m = .success output) :
    ∃ locality affine,
      compile fuel b .locality true m.project.locality = .success locality ∧
      compile fuel b .affinity true m.project.affinity = .success affine ∧
      output = ComparisonPropagation.meet locality affine := by
  cases hl : compile fuel b .locality true m.project.locality <;>
    simp [high, hl, bind, RunResult.bind] at h
  rename_i locality
  cases ha : compile fuel b .affinity true m.project.affinity <;> simp [ha, pure] at h
  subst output
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem low_shape {fuel b m output} (h : low fuel b m = .success output) :
    output ≠ [] ∧ ∀ clause ∈ output, clause ≠ [] ∧
      ∀ literal ∈ clause, literal.2 = true ∧ literal.1 < b.types.length := compile_shape h

theorem low_zero {fuel b m output} (h : low fuel b m = .success output) (σ : Nat → Bool)
    (hzero : ∀ i < b.types.length, σ i = false) : ¬ CNFHolds σ output := compile_zero h σ hzero

theorem low_one {fuel b m output} (h : low fuel b m = .success output) (σ : Nat → Bool)
    (hone : ∀ i < b.types.length, σ i = true) : CNFHolds σ output := compile_one h σ hone

theorem high_zero {fuel b m output} (h : high fuel b m = .success output) (σ : Nat → Bool)
    (hzero : ∀ i < b.types.length, σ i = false) : ¬ CNFHolds σ output := by
  obtain ⟨locality, affine, hl, ha, rfl⟩ := high_parts h
  rw [ComparisonPropagation.meet, CompactCNF.clean_correct, cnfHolds_append]
  exact fun hh => compile_zero hl σ hzero hh.1

theorem high_one {fuel b m output} (h : high fuel b m = .success output) (σ : Nat → Bool)
    (hone : ∀ i < b.types.length, σ i = true) : CNFHolds σ output := by
  obtain ⟨locality, affine, hl, ha, rfl⟩ := high_parts h
  rw [ComparisonPropagation.meet, CompactCNF.clean_correct, cnfHolds_append]
  exact ⟨compile_one hl σ hone, compile_one ha σ hone⟩

theorem high_shape {fuel b m output} (h : high fuel b m = .success output) :
    output ≠ [] ∧ ∀ clause ∈ output, clause ≠ [] ∧
      ∀ literal ∈ clause, literal.2 = true ∧ literal.1 < b.types.length := by
  constructor
  · intro he
    exact high_zero h (fun _ => false) (by simp) (by simp [he, CNFHolds])
  · intro clause hc
    constructor
    · intro he
      have hm := high_one h (fun _ => true) (by simp) clause hc
      simp [he, ClauseHolds] at hm
    · intro literal hliteral
      obtain ⟨locality, affine, hl, ha, rfl⟩ := high_parts h
      obtain ⟨d, hd, hdLiteral⟩ := CompactCNF.clean_literal hc hliteral
      rcases List.mem_append.mp hd with hd | hd
      · exact ((compile_shape hl).2 d hd).2 literal hdLiteral
      · exact ((compile_shape ha).2 d hd).2 literal hdLiteral

private abbrev liftLiteral (b : Basis) (c : Channel) (literal : Literal) : Option Literal := do
  let control ← atomControl c literal.1 literal.2
  return (← b.index (.control control), true)

structure IntervalEvaluation (b : Basis) (c : Channel) (σ η : Nat → Bool) (lo hi : Bool) : Prop where
  ordered : lo = true → hi = true
  lower : ∀ i, b.index c.lowerKey = some i → σ i = lo
  upper : ∀ i, b.index c.upperKey = some i → σ i = hi
  literal : ∀ input output, liftLiteral b c input = some output →
    (σ output.1 = output.2 ↔ lo = true ∨ hi = true ∧ η input.1 = input.2)

private theorem clauseHolds_pair (σ : Nat → Bool) (clause : Clause) :
    ClauseHolds σ clause ↔ ∃ literal ∈ clause, σ literal.1 = literal.2 := by
  simp [ClauseHolds]

theorem liftClause_correct {b c σ η lo hi input output}
    (h : liftClause b c input = some output) (hv : IntervalEvaluation b c σ η lo hi) :
    ClauseHolds σ output ↔ lo = true ∨ hi = true ∧ ClauseHolds η input := by
  cases input with
  | nil =>
    cases hx : b.index c.lowerKey <;> simp [liftClause, hx] at h
    subst output
    simp [ClauseHolds, hv.lower _ hx]
  | cons literal rest =>
    have hm : (literal :: rest).mapM (liftLiteral b c) = some output := h
    rw [clauseHolds_pair, mapM_exists hm]
    constructor
    · rintro ⟨x, hx, y, hy, hσ⟩
      rcases (hv.literal x y hy).mp hσ with hlo | ⟨hhi, hη⟩
      · exact .inl hlo
      · exact .inr ⟨hhi, (clauseHolds_pair _ _).mpr ⟨x, hx, hη⟩⟩
    · rintro (hlo | ⟨hhi, hη⟩)
      · obtain ⟨y, hy, he⟩ := mapM_mem_input hm (show literal ∈ literal :: rest by simp)
        exact ⟨literal, by simp, y, he, (hv.literal _ _ he).mpr (.inl hlo)⟩
      · obtain ⟨x, hx, hη⟩ := (clauseHolds_pair _ _).mp hη
        obtain ⟨y, hy, he⟩ := mapM_mem_input hm hx
        exact ⟨x, hx, y, he, (hv.literal _ _ he).mpr (.inr ⟨hhi, hη⟩)⟩

theorem liftCNF_correct {b c σ η lo hi input output}
    (h : liftCNF b c input = some output) (hv : IntervalEvaluation b c σ η lo hi) :
    CNFHolds σ output ↔ lo = true ∨ hi = true ∧ CNFHolds η input := by
  cases input with
  | nil =>
    cases hx : b.index c.upperKey <;> simp [liftCNF, hx] at h
    subst output
    simpa [CNFHolds, ClauseHolds, hv.upper _ hx] using
      (show hi = true ↔ lo = true ∨ hi = true from
        ⟨Or.inr, fun hh => hh.elim hv.ordered id⟩)
  | cons clause rest =>
    have hm : (clause :: rest).mapM (liftClause b c) = some output := h
    change (∀ d ∈ output, ClauseHolds σ d) ↔ _
    rw [mapM_forall hm]
    constructor
    · intro hall
      by_cases hlo : lo = true
      · exact .inl hlo
      · obtain ⟨d, hd, hσ⟩ := hall clause (by simp)
        have hhi := ((liftClause_correct hd hv).mp hσ).resolve_left hlo
        refine .inr ⟨hhi.1, fun a ha => ?_⟩
        obtain ⟨e, he, hσ⟩ := hall a ha
        exact (((liftClause_correct he hv).mp hσ).resolve_left hlo).2
    · rintro (hlo | ⟨hhi, hη⟩) a ha
      · obtain ⟨d, hd, he⟩ := mapM_mem_input hm ha
        exact ⟨d, he, (liftClause_correct he hv).mpr (.inl hlo)⟩
      · obtain ⟨d, hd, he⟩ := mapM_mem_input hm ha
        exact ⟨d, he, (liftClause_correct he hv).mpr (.inr ⟨hhi, hη a ha⟩)⟩

theorem compile_correct {fuel b c positive e output σ η lo hi}
    (h : compile fuel b c positive e = .success output) (hv : IntervalEvaluation b c σ η lo hi) :
    CNFHolds σ output ↔ lo = true ∨ hi = true ∧ e.eval η = positive := by
  cases hn : CompactCNF.toCNF fuel positive e <;>
    simp [compile, hn, bind, RunResult.bind] at h
  rename_i input
  cases hl : liftCNF b c input <;> simp [hl, pure] at h
  subst output
  rw [liftCNF_correct hl hv, CompactCNF.toCNF_correct hn]

theorem theoryAt_interval {b basisAtom headAtom modeAtom coordinate σ}
    (h : (Basis.theoryAt b basisAtom headAtom modeAtom coordinate).eval σ = true)
    (channel : Channel) :
    IntervalEvaluation b channel (σ ∘ basisAtom) (σ ∘ modeAtom)
      ((b.formula headAtom modeAtom coordinate channel.lowerKey).eval σ)
      ((b.formula headAtom modeAtom coordinate channel.upperKey).eval σ) := by
  refine ⟨formula_interval _ _ _ _ _ _, fun i hi => theoryAt_index h hi,
    fun i hi => theoryAt_index h hi, ?_⟩
  rintro ⟨i, p⟩ output hs
  cases hc : atomControl channel i p <;> simp [liftLiteral, hc] at hs
  rename_i control
  cases hi : b.index (.control control) <;> simp [hi] at hs
  subst output
  obtain ⟨hchannel, hatom, hpositive, _⟩ := atomControl_spec hc
  change σ (basisAtom _) = true ↔ _
  rw [theoryAt_index h hi, formula_control]
  simp [hchannel, hatom, hpositive]

theorem compile_theory {fuel b c positive e output basisAtom headAtom modeAtom coordinate σ}
    (h : compile fuel b c positive e = .success output)
    (ht : (Basis.theoryAt b basisAtom headAtom modeAtom coordinate).eval σ = true) :
    CNFHolds (σ ∘ basisAtom) output ↔
      (b.formula headAtom modeAtom coordinate c.lowerKey).eval σ = true ∨
        (b.formula headAtom modeAtom coordinate c.upperKey).eval σ = true ∧
          e.eval (σ ∘ modeAtom) = positive :=
  compile_correct h (theoryAt_interval ht c)

/-- The Boolean projection is interpreted exactly. A ground-mode use additionally
uses `ModExpr.project_correct` and the original modality definedness obligation. -/
theorem low_theory {fuel b m output basisAtom headAtom modeAtom coordinate σ}
    (h : low fuel b m = .success output)
    (ht : (Basis.theoryAt b basisAtom headAtom modeAtom coordinate).eval σ = true) :
    CNFHolds (σ ∘ basisAtom) output ↔
      (coordinate.modalWith modeAtom (b.formula headAtom modeAtom coordinate .bottom) m).eval σ = true := by
  rw [compile_theory h ht]
  cases coordinate <;>
    simp [Basis.formula, Coordinate.modalWith, Channel.lowerKey, Channel.upperKey,
      SymbolicCNF.substitute_eval, ModExpr.project, BoolExpr.eval,
      Mode.bottom, Mode.top, Function.comp_def]
  tauto

theorem high_theory {fuel b m output basisAtom headAtom modeAtom coordinate σ}
    (h : high fuel b m = .success output)
    (ht : (Basis.theoryAt b basisAtom headAtom modeAtom coordinate).eval σ = true) :
    CNFHolds (σ ∘ basisAtom) output ↔
      (coordinate.modalWith modeAtom (b.formula headAtom modeAtom coordinate .top) m).eval σ = true := by
  obtain ⟨locality, affine, hl, ha, rfl⟩ := high_parts h
  rw [ComparisonPropagation.meet, CompactCNF.clean_correct, cnfHolds_append,
    compile_theory hl ht, compile_theory ha ht]
  cases coordinate <;>
    simp [Basis.formula, Coordinate.modalWith, Channel.lowerKey, Channel.upperKey,
      SymbolicCNF.substitute_eval, ModExpr.project, BoolExpr.eval,
      Mode.top, Mode.global, Mode.many, Function.comp_def] <;> tauto

theorem index_exists {b : Basis} {k : Key} (h : k ∈ b.keys) : ∃ i, b.index k = some i := by
  exact ⟨b.keys.idxOf k, by simp [Basis.index, List.idxOf_lt_length_of_mem h]⟩

theorem lower_index_exists (b : Basis) (c : Channel) : ∃ i, b.index c.lowerKey = some i := by
  apply index_exists
  cases c <;> simp [Basis.keys, Channel.lowerKey]

theorem upper_index_exists (b : Basis) (c : Channel) : ∃ i, b.index c.upperKey = some i := by
  apply index_exists
  cases c <;> simp [Basis.keys, Channel.upperKey]

theorem control_index_exists {b : Basis} (c : Control) (h : c.name ∈ b.modes) :
    ∃ i, b.index (.control c) = some i := by
  apply index_exists
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨c, List.mem_flatMap.mpr ⟨c.name, h, ?_⟩, rfl⟩
  cases c with
  | locality v p => cases p <;> simp [Control.name, controls]
  | affinity v u p | uniqueness v u p => cases u <;> cases p <;> simp [Control.name, controls]

private theorem mapM_exists_output {α β : Type} {f : α → Option β} {xs : List α}
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    exact ⟨y :: ys, by simp [hy, hys]⟩

def Available (b : Basis) (c : Channel) (e : BoolExpr) : Prop :=
  ∀ i ∈ e.atoms, ∀ p, ∃ control j,
    atomControl c i p = some control ∧ b.index (.control control) = some j

theorem compile_complete {b c e} (h : Available b c e) (positive : Bool) :
    ∃ n output, ∀ fuel ≥ n, compile fuel b c positive e = .success output := by
  obtain ⟨n, input, hn⟩ := CompactCNF.toCNF_complete e positive
  have hclause (clause : Clause) (hc : clause ∈ input) : ∃ d, liftClause b c clause = some d := by
    cases clause with
    | nil =>
      obtain ⟨i, hi⟩ := lower_index_exists b c
      exact ⟨[(i, true)], by simp [liftClause, hi]⟩
    | cons l rest =>
      apply mapM_exists_output
      rintro ⟨i, p⟩ hi
      obtain ⟨control, j, hcontrol, hj⟩ := h i (CompactCNF.toCNF_literal (hn n le_rfl) hc hi) p
      exact ⟨(j, true), by simp [hcontrol, hj]⟩
  have hout : ∃ output, liftCNF b c input = some output := by
    cases input with
    | nil =>
      obtain ⟨i, hi⟩ := upper_index_exists b c
      exact ⟨[[(i, true)]], by simp [liftCNF, hi]⟩
    | cons clause rest => exact mapM_exists_output hclause
  obtain ⟨output, hout⟩ := hout
  exact ⟨n, output, fun fuel hf => by simp [compile, hn fuel hf, hout, bind, pure, RunResult.bind]⟩

theorem compile_monotone {small large b c positive e output} (hle : small ≤ large)
    (h : compile small b c positive e = .success output) :
    compile large b c positive e = .success output := by
  cases hn : CompactCNF.toCNF small positive e <;>
    simp [compile, hn, bind, RunResult.bind] at h
  simpa [compile, CompactCNF.toCNF_monotone hn large hle, bind, RunResult.bind] using h

theorem low_monotone {small large b m output} (hle : small ≤ large)
    (h : low small b m = .success output) : low large b m = .success output :=
  compile_monotone hle h

theorem high_monotone {small large b m output} (hle : small ≤ large)
    (h : high small b m = .success output) : high large b m = .success output := by
  obtain ⟨locality, affine, hl, ha, rfl⟩ := high_parts h
  simp [high, compile_monotone hle hl, compile_monotone hle ha, bind, pure, RunResult.bind]

theorem atomVariable_atomIndex (v : ModVar) (axis : Nat) (h : axis < 3) :
    SymbolicModes.atomVariable (v.atomIndex axis) = v := by
  obtain rfl | rfl | rfl : axis = 0 ∨ axis = 1 ∨ axis = 2 := by omega
  all_goals cases v <;>
    simp [SymbolicModes.atomVariable, ModVar.atomIndex, Nat.add_mul, Nat.mul_assoc,
      Nat.mul_comm, Nat.add_div, Nat.add_mod, Nat.mul_mod] <;> omega

theorem atomIndex_mod (v : ModVar) (axis : Nat) (h : axis < 3) : (v.atomIndex axis) % 3 = axis := by
  cases v <;> simp [ModVar.atomIndex, Nat.add_mod, Nat.mod_eq_of_lt h]

theorem project_support (m : ModExpr) :
    (∀ i ∈ m.project.locality.atoms, i % 3 = 0 ∧ SymbolicModes.atomVariable i ∈ m.freeVariables) ∧
    (∀ i ∈ m.project.affinity.atoms, i % 3 ≠ 0 ∧ SymbolicModes.atomVariable i ∈ m.freeVariables) ∧
    (∀ i ∈ m.project.uniqueness.atoms, i % 3 ≠ 0 ∧ SymbolicModes.atomVariable i ∈ m.freeVariables) := by
  induction m with
  | var v => simp [ModExpr.project, BoolExpr.atoms, ModExpr.freeVariables,
      atomVariable_atomIndex, atomIndex_mod]
  | const m => simp [ModExpr.project, BoolExpr.atoms]
  | compose a b iha ihb | meet a b iha ihb | join a b iha ihb | leftResidual a b iha ihb | rightResidual a b iha ihb =>
    simp_all only [ModExpr.project, BoolExpr.atoms, ModExpr.freeVariables,
      List.mem_dedup, List.mem_append, or_imp, forall_and]
    aesop
  | close a ih | closeInv a ih | future a ih | capture a ih =>
    simp_all [ModExpr.project, BoolExpr.atoms, ModExpr.freeVariables]

/-- A channel accepts exactly the modality coordinates from which its signed
controls can be constructed. -/
def Channel.Accepts (c : Channel) (i : Nat) : Prop :=
  match c with
  | .locality => i % 3 = 0
  | .lower | .affinity => i % 3 ≠ 0

theorem atomControl_exists (c : Channel) (i : Nat) (p : Bool) (h : c.Accepts i) :
    ∃ control, atomControl c i p = some control := by
  have hi : i % 3 < 3 := Nat.mod_lt _ (by decide)
  cases c with
  | locality => simp only [Channel.Accepts] at h; simp [atomControl, h]
  | lower | affinity =>
    obtain hmod | hmod : i % 3 = 1 ∨ i % 3 = 2 := by simp only [Channel.Accepts] at h; omega
    all_goals simp [atomControl, hmod]

theorem available_of_support {b : Basis} {c : Channel} {e : BoolExpr}
    (h : ∀ i ∈ e.atoms, c.Accepts i ∧ SymbolicModes.atomVariable i ∈ b.modes) :
    Available b c e := by
  intro i hi p
  obtain ⟨control, hc⟩ := atomControl_exists c i p (h i hi).1
  obtain ⟨j, hj⟩ := control_index_exists control (by
    rw [(atomControl_spec hc).2.2.2]
    exact (h i hi).2)
  exact ⟨control, j, hc, hj⟩

theorem project_available {b : Basis} {m : ModExpr}
    (h : ∀ v ∈ m.freeVariables, v ∈ b.modes) :
    Available b .locality m.project.locality ∧
      Available b .affinity m.project.affinity ∧ Available b .lower m.project.uniqueness := by
  obtain ⟨hl, ha, hu⟩ := project_support m
  exact ⟨available_of_support (fun i hi => ⟨(hl i hi).1, h _ (hl i hi).2⟩),
    available_of_support (fun i hi => ⟨(ha i hi).1, h _ (ha i hi).2⟩),
    available_of_support (fun i hi => ⟨(hu i hi).1, h _ (hu i hi).2⟩)⟩

theorem low_complete {b : Basis} {m : ModExpr}
    (h : ∀ v ∈ m.freeVariables, v ∈ b.modes) :
    ∃ n output, ∀ fuel ≥ n, low fuel b m = .success output :=
  compile_complete (project_available h).2.2 false

theorem high_complete {b : Basis} {m : ModExpr}
    (h : ∀ v ∈ m.freeVariables, v ∈ b.modes) :
    ∃ n output, ∀ fuel ≥ n, high fuel b m = .success output := by
  obtain ⟨n, locality, hl⟩ := compile_complete (project_available h).1 true
  obtain ⟨k, affine, ha⟩ := compile_complete (project_available h).2.1 true
  refine ⟨max n k, ComparisonPropagation.meet locality affine, ?_⟩
  intro fuel hf
  simp [high, hl fuel (le_trans (le_max_left _ _) hf),
    ha fuel (le_trans (le_max_right _ _) hf), bind, pure, RunResult.bind]

/-- Both signed controls separate every observed mode bit whenever the channel
interval is nondegenerate at both points. No global incomparability across
coordinate categories or collapsed intervals is assumed. -/
theorem IntervalEvaluation.atoms_eq {b c e σ τ η θ}
    (hs : IntervalEvaluation b c σ η false true)
    (ht : IntervalEvaluation b c τ θ false true)
    (horder : ∀ j < b.types.length, σ j = true → τ j = true)
    (ha : Available b c e) : ∀ i ∈ e.atoms, η i = θ i := by
  intro i hi
  obtain ⟨control, j, hc, hj⟩ := ha i hi (η i)
  have hl : liftLiteral b c (i, η i) = some (j, true) := by simp [liftLiteral, hc, hj]
  have hsj : σ j = true := (hs.literal _ _ hl).mpr (.inr ⟨rfl, rfl⟩)
  have htj := horder j (index_bound hj) hsj
  have hθ := (ht.literal _ _ hl).mp htj
  simp only [Bool.false_eq_true, false_or, true_and] at hθ
  exact hθ.symm

/-- The free finite algebra over the supplied opaque heads. Structural source
normalization must separately justify that a witness lies in this grammar. -/
inductive Generated (b : Basis) where
  | head (type : CompareTy) (member : type ∈ b.heads)
  | join (left right : Generated b)
  | meet (left right : Generated b)
  | modal (type : Generated b) (mode : ModExpr)
      (supported : ∀ v ∈ mode.freeVariables, v ∈ b.modes)

def Generated.term {b : Basis} : Generated b → CompareTy
  | .head a _ => a
  | .join a c => .join a.term c.term
  | .meet a c => .meet a.term c.term
  | .modal a m _ => .modal a.term m

def Generated.formula {b : Basis} (headAtom modeAtom : Nat → Nat) (coordinate : Coordinate) :
    Generated b → BoolExpr
  | .head a _ => b.formula headAtom modeAtom coordinate (.head a)
  | .join a c => .or (a.formula headAtom modeAtom coordinate) (c.formula headAtom modeAtom coordinate)
  | .meet a c => .and (a.formula headAtom modeAtom coordinate) (c.formula headAtom modeAtom coordinate)
  | .modal a m _ => coordinate.modalWith modeAtom (a.formula headAtom modeAtom coordinate) m

private theorem any_eval_true (es : List BoolExpr) (σ : Nat → Bool) :
    (BoolExpr.any es).eval σ = true ↔ ∃ e ∈ es, e.eval σ = true := by
  induction es <;> simp_all [BoolExpr.any, BoolExpr.eval]

private theorem head_formula_bounds {b : Basis} {a : CompareTy} (ha : a ∈ b.heads)
    (headAtom modeAtom : Nat → Nat) (coordinate : Coordinate) (σ : Nat → Bool) :
    ((b.formula headAtom modeAtom coordinate .bottom).eval σ = true →
      (b.formula headAtom modeAtom coordinate (.head a)).eval σ = true) ∧
    ((b.formula headAtom modeAtom coordinate (.head a)).eval σ = true →
      (b.formula headAtom modeAtom coordinate .top).eval σ = true) := by
  have hi : b.heads.idxOf a < b.heads.length := List.idxOf_lt_length_of_mem ha
  have hm : BoolExpr.atom (headAtom (b.heads.idxOf a)) ∈
      b.heads.mapIdx (fun i _ => BoolExpr.atom (headAtom i)) := by
    apply List.mem_iff_getElem?.mpr
    exact ⟨b.heads.idxOf a, by simp [List.getElem?_mapIdx, List.getElem?_eq_getElem hi]⟩
  have hlo := fun h => (all_eval_true _ σ).mp h _ hm
  have hhi := fun h => (any_eval_true _ σ).mpr ⟨_, hm, h⟩
  cases coordinate <;>
    simp_all [Basis.formula, Coordinate.modalWith, SymbolicCNF.substitute_eval,
      ModExpr.project, BoolExpr.eval, Mode.bottom, Mode.top]

theorem Generated.formula_bounds {b : Basis} (e : Generated b)
    (headAtom modeAtom : Nat → Nat) (coordinate : Coordinate) (σ : Nat → Bool) :
    ((b.formula headAtom modeAtom coordinate .bottom).eval σ = true →
      (e.formula headAtom modeAtom coordinate).eval σ = true) ∧
    ((e.formula headAtom modeAtom coordinate).eval σ = true →
      (b.formula headAtom modeAtom coordinate .top).eval σ = true) := by
  induction e with
  | head a ha => exact head_formula_bounds ha _ _ _ _
  | join a c iha ihc | meet a c iha ihc =>
    simp only [Generated.formula, BoolExpr.eval, Bool.or_eq_true, Bool.and_eq_true]
    tauto
  | modal a m hm ih =>
    cases coordinate <;>
      simp_all [Generated.formula, Basis.formula, Coordinate.modalWith, SymbolicCNF.substitute_eval,
        ModExpr.project, BoolExpr.eval, Mode.bottom, Mode.top]

theorem modalWith_clamp {b : Basis} {value : BoolExpr}
    {headAtom modeAtom : Nat → Nat} {coordinate : Coordinate} {σ : Nat → Bool}
    (hlo : (b.formula headAtom modeAtom coordinate .bottom).eval σ = true → value.eval σ = true)
    (hhi : value.eval σ = true → (b.formula headAtom modeAtom coordinate .top).eval σ = true)
    (m : ModExpr) :
    (coordinate.modalWith modeAtom value m).eval σ =
      ((value.eval σ ||
        (coordinate.modalWith modeAtom (b.formula headAtom modeAtom coordinate .bottom) m).eval σ) &&
        (coordinate.modalWith modeAtom (b.formula headAtom modeAtom coordinate .top) m).eval σ) := by
  apply Bool.eq_iff_iff.mpr
  cases coordinate <;>
    simp_all [Basis.formula, Coordinate.modalWith, SymbolicCNF.substitute_eval,
      ModExpr.project, BoolExpr.eval, Mode.bottom, Mode.top] <;> tauto

/-- Positive finite polynomials use only the actual basis and neither empty
lattice extremum. Their endpoint behavior guarantees finite reification. -/
structure Polynomial (b : Basis) (clauses : CNF) : Prop where
  positive : ComparisonPropagation.Positive clauses
  supported : ComparisonPropagation.Supported (List.range b.types.length) clauses
  zero : ¬CNFHolds (fun _ => false) clauses
  one : CNFHolds (fun _ => true) clauses

theorem Polynomial.of_shape {b : Basis} {clauses : CNF}
    (h : clauses ≠ [] ∧ ∀ clause ∈ clauses, clause ≠ [] ∧
      ∀ literal ∈ clause, literal.2 = true ∧ literal.1 < b.types.length) :
    Polynomial b clauses := by
  refine ⟨fun c hc l hl => ((h.2 c hc).2 l hl).1, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨c, hc, p, hp⟩ := CNFPropagation.mem_atoms.mp hi
    exact List.mem_range.mpr (((h.2 c hc).2 (i, p) hp).2)
  · intro hs
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ h.1
    obtain ⟨i, p, hp, he⟩ := hs c hc
    exact Bool.noConfusion (he.trans (((h.2 c hc).2 (i, p) hp).1))
  · intro c hc
    obtain ⟨⟨i, p⟩, hp⟩ := List.exists_mem_of_ne_nil _ (h.2 c hc).1
    exact ⟨i, p, hp, (((h.2 c hc).2 (i, p) hp).1).symm⟩

theorem Polynomial.atom {b : Basis} {i : Nat} (hi : i < b.types.length) :
    Polynomial b [[(i, true)]] := by
  apply Polynomial.of_shape
  simp [hi]

theorem Polynomial.join {b : Basis} {left right : CNF}
    (hl : Polynomial b left) (hr : Polynomial b right) :
    Polynomial b (ComparisonPropagation.join left right) := by
  refine ⟨ComparisonPropagation.join_positive hl.positive hr.positive,
    ComparisonPropagation.join_supported hl.supported hr.supported, ?_, ?_⟩
  · rw [ComparisonPropagation.join_correct]
    exact not_or.mpr ⟨hl.zero, hr.zero⟩
  · exact (ComparisonPropagation.join_correct _ _ _).mpr (.inl hl.one)

theorem Polynomial.meet {b : Basis} {left right : CNF}
    (hl : Polynomial b left) (hr : Polynomial b right) :
    Polynomial b (ComparisonPropagation.meet left right) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc l hm
    obtain ⟨d, hd, hm⟩ := CompactCNF.clean_literal hc hm
    rcases List.mem_append.mp hd with hd | hd
    · exact hl.positive d hd l hm
    · exact hr.positive d hd l hm
  · intro i hi
    obtain ⟨c, hc, p, hp⟩ := CNFPropagation.mem_atoms.mp (CompactCNF.clean_atoms hi)
    rcases List.mem_append.mp hc with hc | hc
    · exact hl.supported i (CNFPropagation.mem_atoms.mpr ⟨c, hc, p, hp⟩)
    · exact hr.supported i (CNFPropagation.mem_atoms.mpr ⟨c, hc, p, hp⟩)
  · exact fun h => hl.zero ((ComparisonPropagation.meet_correct _ _ _).mp h).1
  · exact (ComparisonPropagation.meet_correct _ _ _).mpr ⟨hl.one, hr.one⟩

theorem Polynomial.reify {b : Basis} {clauses : CNF} (h : Polynomial b clauses) :
    ∃ t, ComparisonPropagation.reify b.types clauses = some t :=
  ComparisonPropagation.reify_complete h.positive h.supported h.one h.zero

/-- Every generated expression has one positive finite polynomial valid at all
four coordinate kinds. This is a representation theorem for the stated grammar,
not a claim that structural normalization covers every comparison witness.
Projection equations remain separate from modality definedness. -/
theorem Generated.representable {b : Basis} (e : Generated b) :
    ∃ clauses, Polynomial b clauses ∧
      ∀ basisAtom headAtom modeAtom coordinate σ,
        (b.theoryAt basisAtom headAtom modeAtom coordinate).eval σ = true →
        (CNFHolds (σ ∘ basisAtom) clauses ↔
          (e.formula headAtom modeAtom coordinate).eval σ = true) := by
  induction e with
  | head a ha =>
    obtain ⟨i, hi⟩ := index_exists (b := b) (k := .head a) (by simp [Basis.keys, ha])
    refine ⟨[[(i, true)]], Polynomial.atom (index_bound hi), ?_⟩
    intro basisAtom headAtom modeAtom coordinate σ ht
    simp [CNFHolds, ClauseHolds, Generated.formula, theoryAt_index ht hi]
  | join a c iha ihc =>
    obtain ⟨left, hl, hleft⟩ := iha
    obtain ⟨right, hr, hright⟩ := ihc
    refine ⟨ComparisonPropagation.join left right, hl.join hr, ?_⟩
    intro basisAtom headAtom modeAtom coordinate σ ht
    rw [ComparisonPropagation.join_correct, hleft _ _ _ _ _ ht, hright _ _ _ _ _ ht]
    simp [Generated.formula, BoolExpr.eval]
  | meet a c iha ihc =>
    obtain ⟨left, hl, hleft⟩ := iha
    obtain ⟨right, hr, hright⟩ := ihc
    refine ⟨ComparisonPropagation.meet left right, hl.meet hr, ?_⟩
    intro basisAtom headAtom modeAtom coordinate σ ht
    rw [ComparisonPropagation.meet_correct, hleft _ _ _ _ _ ht, hright _ _ _ _ _ ht]
    simp [Generated.formula, BoolExpr.eval]
  | modal a m hm ih =>
    obtain ⟨clauses, hp, hclauses⟩ := ih
    obtain ⟨n, lower, hlo⟩ := low_complete hm
    obtain ⟨k, upper, hhi⟩ := high_complete hm
    have hl := hlo n le_rfl
    have hu := hhi k le_rfl
    refine ⟨ComparisonPropagation.meet (ComparisonPropagation.join clauses lower) upper,
      (hp.join (Polynomial.of_shape (low_shape hl))).meet
        (Polynomial.of_shape (high_shape hu)), ?_⟩
    intro basisAtom headAtom modeAtom coordinate σ ht
    rw [ComparisonPropagation.meet_correct, ComparisonPropagation.join_correct,
      hclauses _ _ _ _ _ ht, low_theory hl ht, high_theory hu ht]
    have hb := a.formula_bounds headAtom modeAtom coordinate σ
    rw [Generated.formula, modalWith_clamp hb.1 hb.2 m]
    simp only [Bool.and_eq_true, Bool.or_eq_true]

theorem Generated.reconstructs {b : Basis} (e : Generated b) :
    ∃ clauses type, Polynomial b clauses ∧
      ComparisonPropagation.reify b.types clauses = some type ∧
      ∀ basisAtom headAtom modeAtom coordinate σ,
        (b.theoryAt basisAtom headAtom modeAtom coordinate).eval σ = true →
        (CNFHolds (σ ∘ basisAtom) clauses ↔
          (e.formula headAtom modeAtom coordinate).eval σ = true) := by
  obtain ⟨clauses, hp, hsem⟩ := e.representable
  obtain ⟨type, ht⟩ := hp.reify
  exact ⟨clauses, type, hp, ht, hsem⟩

theorem control_vars (c : Control) : c.expression.vars = {c.name} := by
  cases c with
  | locality v p => cases p <;>
    simp [Control.expression, Control.channel, Control.positive, Control.bit, Control.axis,
      Control.name, ModExpr.vars]
  | affinity v u p | uniqueness v u p => cases u <;> cases p <;>
    simp [Control.expression, Control.channel, Control.positive, Control.bit, Control.axis,
      Control.name, ModExpr.vars, ModExpr.epsilon]

private theorem controls_name {v : ModVar} {c : Control} (h : c ∈ controls v) : c.name = v := by
  simp only [controls, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem Basis.supports {b : Basis} {types : TypeVar → Prop} {modes : ModVar → Prop}
    (hh : ∀ a ∈ b.heads, ComparisonInterpolation.Supports types modes a)
    (hm : ∀ v ∈ b.modes, modes v) :
    ∀ a ∈ b.types, ComparisonInterpolation.Supports types modes a := by
  have hlo : ComparisonInterpolation.Supports types modes b.bottom := by
    refine ⟨(ComparisonInterpolation.meet_support_iff _ _ _ _).mpr hh, ?_⟩
    simp [ModExpr.vars]
  have hhi : ComparisonInterpolation.Supports types modes b.top := by
    refine ⟨(ComparisonInterpolation.join_support_iff _ _ _ _).mpr hh, ?_⟩
    simp [ModExpr.vars]
  intro a ha
  obtain ⟨key, hk, rfl⟩ := List.mem_map.mp ha
  cases key with
  | head t =>
    have ht : t ∈ b.heads := by simpa [Basis.keys] using hk
    exact hh t ht
  | bottom => exact hlo
  | top => exact hhi
  | raised => exact ⟨hlo, by simp [ModExpr.vars]⟩
  | localFloor | affineFloor => exact ⟨hhi, by simp [ModExpr.vars]⟩
  | control c =>
    have hc : c ∈ b.modes.flatMap controls := by simpa [Basis.keys] using hk
    obtain ⟨v, hv, hc⟩ := List.mem_flatMap.mp hc
    refine ⟨?_, ?_⟩
    · change ComparisonInterpolation.Supports types modes (if c.channel == .lower then b.bottom else b.top)
      split <;> assumption
    · simp only [control_vars, Finset.mem_singleton]
      intro w hw
      subst w
      exact (controls_name hc).symm ▸ hm v hv

end ModalityInference.ComparisonControls
