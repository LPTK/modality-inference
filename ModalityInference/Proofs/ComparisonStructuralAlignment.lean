import ModalityInference.ComparisonStructuralAlignment
import ModalityInference.Proofs.ComparisonStructuralObservers

/-! The finite alignment query is exact. An actual parent observer selects one
genuine child observer for the whole product or sum family. Constant children
retain their global range; nonconstant children have aligned modal models. -/
namespace ModalityInference.ComparisonStructuralAlignment

open ComparisonControls

def SameInputs (names : List ModVar) (coordinate : Coordinate)
    (σ τ : Nat → Bool) : Prop :=
  match coordinate with
  | .unaffected => True
  | .locality => ∀v∈names, σ (v.atomIndex 0) = τ (v.atomIndex 0)
  | .affinity | .uniqueness => ∀v∈names,
      σ (v.atomIndex 1) = τ (v.atomIndex 1) ∧
      σ (v.atomIndex 2) = τ (v.atomIndex 2)

def Aligned (names : List ModVar) (parent child : Coordinate)
    (σ τ : Nat → Bool) : Prop :=
  child = .unaffected ∨ child = parent ∧ SameInputs names child σ τ

theorem neutralFormula_eval {c atom m σ τ}
    (h : ∀i, σ (atom i) = τ i) :
    (neutralFormula c atom m).eval σ = (neutralFormula c id m).eval τ := by
  cases c <;> simp [neutralFormula, SymbolicCNF.substitute_eval, BoolExpr.eval, h]

theorem neutralFormula_of_project {c m σ value}
    (h : m.project.eval σ = some value) :
    (neutralFormula c id m).eval σ = neutral c value := by
  simp only [Projection.eval] at h
  split at h
  · have he := Option.some.inj h
    cases c <;> simp [neutralFormula, SymbolicCNF.substitute_eval, BoolExpr.eval,
      neutral, ← he]
  · contradiction

theorem neutralFormula_control (c : Coordinate) (q : Control) (σ : Nat → Bool) :
    (neutralFormula c id q.expression).eval σ =
      neutral c (q.axis.embed
        (if q.channel == .lower then !(σ q.atom == q.positive)
         else σ q.atom == q.positive)) :=
  neutralFormula_of_project (control_project q σ)

theorem neutralFormula_const (c : Coordinate) (m : Mode) (σ : Nat → Bool) :
    (neutralFormula c id (.const m)).eval σ = neutral c m := by
  cases c <;> rfl

theorem tests_complete {names parent child σ τ}
    (h : ∀m∈tests names, (neutralFormula parent id m).eval σ = true →
      (neutralFormula child id m).eval τ = true) :
    Aligned names parent child σ τ := by
  have hg : neutral parent Mode.global = true → neutral child Mode.global = true := by
    simpa only [neutralFormula_const] using h (.const Mode.global) (by simp [tests])
  have hm : neutral parent Mode.many = true → neutral child Mode.many = true := by
    simpa only [neutralFormula_const] using h (.const Mode.many) (by simp [tests])
  have ht : neutral parent Mode.top = true → neutral child Mode.top = true := by
    simpa only [neutralFormula_const] using h (.const Mode.top) (by simp [tests])
  have he : child = .unaffected ∨ child = parent := by
    cases parent <;> cases child <;> simp_all [neutral, Mode.global, Mode.many, Mode.top]
  rcases he with he | rfl
  · exact .inl he
  · refine .inr ⟨rfl, ?_⟩
    have hc (q : Control) (hq : q ∈ names.flatMap controls) :=
      h q.expression (List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩))
    cases child with
    | unaffected => trivial
    | locality =>
      intro v hv
      have hp := hc (.locality v true) (List.mem_flatMap.mpr ⟨v, hv, by simp [controls]⟩)
      have hn := hc (.locality v false) (List.mem_flatMap.mpr ⟨v, hv, by simp [controls]⟩)
      simp only [neutralFormula_control, Control.channel, Control.axis, Control.atom,
        Control.positive, SymbolicModes.Axis.embed, neutral] at hp hn
      cases hσ : σ (v.atomIndex 0) <;> cases hτ : τ (v.atomIndex 0) <;> simp_all
    | affinity =>
      intro v hv
      have bits (u : Bool) :
          σ (v.atomIndex (if u then 2 else 1)) = τ (v.atomIndex (if u then 2 else 1)) := by
        have hp := hc (.affinity v u true) (by
          apply List.mem_flatMap.mpr
          exact ⟨v, hv, by cases u <;> simp [controls]⟩)
        have hn := hc (.affinity v u false) (by
          apply List.mem_flatMap.mpr
          exact ⟨v, hv, by cases u <;> simp [controls]⟩)
        simp only [neutralFormula_control, Control.channel, Control.axis, Control.atom,
          Control.positive, SymbolicModes.Axis.embed, neutral] at hp hn
        cases hσ : σ (v.atomIndex (if u then 2 else 1)) <;>
          cases hτ : τ (v.atomIndex (if u then 2 else 1)) <;> simp_all
      exact ⟨bits false, bits true⟩
    | uniqueness =>
      intro v hv
      have bits (u : Bool) :
          σ (v.atomIndex (if u then 2 else 1)) = τ (v.atomIndex (if u then 2 else 1)) := by
        have hp := hc (.uniqueness v u true) (by
          apply List.mem_flatMap.mpr
          exact ⟨v, hv, by cases u <;> simp [controls]⟩)
        have hn := hc (.uniqueness v u false) (by
          apply List.mem_flatMap.mpr
          exact ⟨v, hv, by cases u <;> simp [controls]⟩)
        simp only [neutralFormula_control, Control.channel, Control.axis, Control.atom,
          Control.positive, SymbolicModes.Axis.embed, neutral] at hp hn
        cases hσ : σ (v.atomIndex (if u then 2 else 1)) <;>
          cases hτ : τ (v.atomIndex (if u then 2 else 1)) <;> simp_all
      exact ⟨bits false, bits true⟩

theorem SameInputs.locality {names σ τ} (h : SameInputs names .locality σ τ)
    {i : Nat} (hn : SymbolicModes.atomVariable i ∈ names) (ha : i % 3 = 0) : σ i = τ i := by
  have he : (SymbolicModes.atomVariable i).atomIndex 0 = i := by
    by_cases hv : i / 3 % 2 = 0 <;>
      simp [SymbolicModes.atomVariable, hv, ModVar.atomIndex] <;> omega
  simpa only [he] using h _ hn

theorem SameInputs.other {names σ τ} {c : Coordinate}
    (h : SameInputs names c σ τ) (hc : c = .affinity ∨ c = .uniqueness)
    {i : Nat} (hn : SymbolicModes.atomVariable i ∈ names) (ha : i % 3 ≠ 0) : σ i = τ i := by
  have he : (SymbolicModes.atomVariable i).atomIndex (i % 3) = i := by
    by_cases hv : i / 3 % 2 = 0 <;>
      simp [SymbolicModes.atomVariable, hv, ModVar.atomIndex] <;> omega
  have hi : i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hc with rfl | rfl <;> rcases hi with hi | hi
  all_goals have hv := h _ hn
  all_goals first
    | exact (he ▸ hi ▸ hv.1)
    | exact (he ▸ hi ▸ hv.2)

theorem SameInputs.neutralFormula {names c σ τ} (h : SameInputs names c σ τ)
    {m : ModExpr} (hm : ∀v∈m.freeVariables, v∈names) :
    (neutralFormula c id m).eval σ = (neutralFormula c id m).eval τ := by
  cases c with
  | unaffected => rfl
  | locality =>
    simp only [ComparisonStructuralAlignment.neutralFormula, SymbolicCNF.substitute_eval, BoolExpr.eval, id_eq]
    exact SymbolicModes.eval_congr _ (fun i hi =>
      h.locality (hm _ ((project_support m).1 i hi).2) ((project_support m).1 i hi).1)
  | affinity =>
    simp only [ComparisonStructuralAlignment.neutralFormula, SymbolicCNF.substitute_eval, BoolExpr.eval, id_eq]
    exact SymbolicModes.eval_congr _ (fun i hi =>
      h.other (.inl rfl) (hm _ ((project_support m).2.1 i hi).2) ((project_support m).2.1 i hi).1)
  | uniqueness =>
    simp only [ComparisonStructuralAlignment.neutralFormula, SymbolicCNF.substitute_eval, BoolExpr.eval, id_eq]
    exact SymbolicModes.eval_congr _ (fun i hi =>
      h.other (.inr rfl) (hm _ ((project_support m).2.2 i hi).2) ((project_support m).2.2 i hi).1)

theorem tests_support {names m} (hm : m ∈ tests names) :
    ∀v∈m.freeVariables, v∈names := by
  rcases List.mem_append.mp hm with hm | hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp [ModExpr.vars]
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    obtain ⟨v, hv, hq⟩ := List.mem_flatMap.mp hq
    simpa only [ModExpr.mem_freeVariables, control_vars, Finset.mem_singleton,
      forall_eq, controls_name_mem hq] using hv

theorem tests_sound {names parent child σ τ} (h : Aligned names parent child σ τ) :
    ∀m∈tests names, (neutralFormula parent id m).eval σ = true →
      (neutralFormula child id m).eval τ = true := by
  rcases h with rfl | ⟨rfl, h⟩
  · simp [neutralFormula, BoolExpr.eval]
  · intro m hm he
    exact (h.neutralFormula (tests_support hm)).symm.trans he

private theorem all_eval (es : List BoolExpr) (σ : Nat → Bool) :
    (BoolExpr.all es).eval σ = true ↔ ∀e∈es, e.eval σ = true := by
  induction es <;> simp_all [BoolExpr.all, BoolExpr.eval]

theorem transition_correct {parent child parentAtom childAtom names σ τ world}
    (hp : ∀i, world (parentAtom i) = σ i) (hc : ∀i, world (childAtom i) = τ i) :
    (transition parent child parentAtom childAtom names).eval world = true ↔
      Aligned names parent child σ τ := by
  simp only [transition, all_eval, List.forall_mem_map, BoolExpr.eval_imp_true,
    neutralFormula_eval hp, neutralFormula_eval hc]
  exact ⟨tests_complete, tests_sound⟩

theorem compile_correct {fuel parent child parentAtom childAtom names clauses σ τ world}
    (h : compile fuel parent child parentAtom childAtom names = .success clauses)
    (hp : ∀i, world (parentAtom i) = σ i) (hc : ∀i, world (childAtom i) = τ i) :
    CNFHolds world clauses ↔ Aligned names parent child σ τ :=
  (CompactCNF.toCNF_correct h world).trans (transition_correct hp hc)

theorem compile_complete (parent child : Coordinate) (parentAtom childAtom : Nat → Nat)
    (names : List ModVar) :
    ∃threshold clauses, ∀fuel≥threshold,
      compile fuel parent child parentAtom childAtom names = .success clauses :=
  CompactCNF.toCNF_complete (transition parent child parentAtom childAtom names) true

theorem tests_total {names m} (hm : m ∈ tests names) (η : ModVar → Mode) :
    m.WellFormed η := by
  rcases List.mem_append.mp hm with hm | hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> rfl
  · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
    exact control_total q η

theorem neutralFormula_of_eval {c m η value}
    (h : m.eval (some ∘ η) = some value) :
    (neutralFormula c id m).eval (encodeModes η) = neutral c value := by
  apply neutralFormula_of_project
  simpa only [ModExpr.project_correct, projectedModes_encodeModes] using h

open ComparisonAlgebra

theorem neutral_iff (c : Coordinate) (m : Mode) :
    neutral c m = true ↔ ∀b, coordinateValue c b m = b := by
  cases c <;> cases m with
  | mk l a u => cases l <;> cases a <;> cases u <;>
    simp [neutral, coordinateValue, Bool.forall_bool]

theorem SameInputs.modalWith {names c σ τ} (h : SameInputs names c σ τ)
    {m : ModExpr} (hm : ∀v∈m.freeVariables, v∈names) (b : Bool) :
    (c.modal (.const b) m).eval σ = (c.modal (.const b) m).eval τ := by
  have he := h.neutralFormula hm
  cases c <;> simp_all [Coordinate.modal, Coordinate.modalWith,
    ComparisonStructuralAlignment.neutralFormula, SymbolicCNF.substitute_eval, BoolExpr.eval]

open ComparisonStructuralObservers ComparisonStructuralFamily ComparisonStructuralLattice

theorem observer_modal_extend {Δ : Bounds} {shape : ComparisonShape}
    (f : LatticeHom (Order Δ shape) Bool) (m : GuardedMode Δ)
    (a b : Carrier Δ shape) (ha : observer f a = false) (hb : observer f b = true)
    (c : Coordinate) (value : Mode)
    (hma : observer f (m.act a) = coordinateValue c false value)
    (hmb : observer f (m.act b) = coordinateValue c true value)
    (x : Carrier Δ shape) :
    observer f (m.act x) = coordinateValue c (observer f x) value := by
  cases hx : observer f x
  · exact (observer_modal_congr f m x a (hx.trans ha.symm)).trans hma
  · exact (observer_modal_congr f m x b (hx.trans hb.symm)).trans hmb

theorem actObserver_eq {Δ : Bounds} {shape : ComparisonShape}
    (f : LatticeHom (Order Δ shape) Bool) (m : GuardedMode Δ)
    (h : ∀a, observer f (m.act a) = observer f a) : actObserver f m = f := by
  ext a
  induction a using Antisymmetrization.induction_on
  exact h _

theorem observer_global_realizable {Δ : Bounds} {shape : ComparisonShape}
    (f : LatticeHom (Order Δ shape) Bool) (a b : Carrier Δ shape)
    (ha : observer f a = false) (hb : observer f b = true)
    (labels : List (GuardedMode Δ)) :
    ∃c η, (c = Coordinate.unaffected ∨ ModeModels Δ η) ∧
      ∀x, ∀m∈labels, observer f (m.act x) = coordinateValue c (observer f x) (m.value η) := by
  let lower := a.meet b
  let upper := a.join b
  have hlu : lower ≤ upper := (Carrier.meet_le_left a b).trans (Carrier.le_join_left a b)
  have hlo : observer f (lower.atMode Mode.bottom) = false := by
    have h := observer_mono f (lower.bottom_le_self.trans (Carrier.meet_le_left a b))
    cases he : observer f (lower.atMode Mode.bottom) <;> simp_all
  have hhi : observer f (upper.atMode Mode.top) = true :=
    observer_mono f ((Carrier.le_join_right a b).trans upper.self_le_top) hb
  have hbt : lower.atMode Mode.bottom ≤ upper.atMode Mode.top :=
    lower.bottom_le_self.trans (hlu.trans upper.self_le_top)
  obtain ⟨c, η, hη, hmodel⟩ := observer_modal_realizable f lower upper hlu hlo hhi labels
  refine ⟨c, η, hη, ?_⟩
  intro x m hm
  apply observer_modal_extend f m _ _ hlo hhi c (m.value η) _ _ x
  · simpa only [hlo] using hmodel _ (le_refl _) hbt m hm
  · simpa only [hhi] using hmodel _ hbt (le_refl _) m hm

structure Model {Δ : Bounds} {shape : ComparisonShape}
    (f : LatticeHom (Order Δ shape) Bool) (labels : List (GuardedMode Δ))
    (coordinate : Coordinate) (world : ModVar → Mode) : Prop where
  modeModel : coordinate = .unaffected ∨ ModeModels Δ world
  action : ∀x, ∀m∈labels,
    observer f (m.act x) = coordinateValue coordinate (observer f x) (m.value world)

theorem observer_models_aligned {Δ : Bounds} {parentShape childShape : ComparisonShape}
    {f : LatticeHom (Order Δ parentShape) Bool}
    {g : LatticeHom (Order Δ childShape) Bool}
    {labels : List (GuardedMode Δ)} {names : List ModVar}
    {parent child : Coordinate} {η θ : ModVar → Mode}
    (hparent : Model f labels parent η) (hchild : Model g labels child θ)
    (htests : ∀m∈tests names, ∃n∈labels, n.expression = m)
    (hinherit : ∀m∈labels, (∀x, observer f (m.act x) = observer f x) →
      ∀x, observer g (m.act x) = observer g x)
    (a b : Carrier Δ childShape) (ha : observer g a = false) (hb : observer g b = true) :
    Aligned names parent child (encodeModes η) (encodeModes θ) := by
  apply tests_complete
  intro m hm hp
  obtain ⟨n, hn, he⟩ := htests m hm
  have hpn : neutral parent (n.value η) = true := by
    rcases hparent.modeModel with rfl | hη
    · rfl
    · have hv := neutralFormula_of_eval (c := parent) (n.eval η hη)
      rw [he] at hv
      exact hv.symm.trans hp
  have hgn := hinherit n hn (fun x =>
    (hparent.action x n hn).trans ((neutral_iff parent (n.value η)).mp hpn _))
  have hcn : neutral child (n.value θ) = true := by
    apply (neutral_iff child (n.value θ)).mpr
    intro v
    cases v
    · simpa only [ha] using (hchild.action a n hn).symm.trans (hgn a)
    · simpa only [hb] using (hchild.action b n hn).symm.trans (hgn b)
  rcases hchild.modeModel with rfl | hθ
  · rfl
  · have hv := neutralFormula_of_eval (c := child) (n.eval θ hθ)
    rw [he] at hv
    exact hv.trans hcn

theorem pair_child_profile {Δ : Bounds} {s t : ComparisonShape} (isSum : Bool)
    (f : LatticeHom (Order Δ ((if isSum then Kind.sum else Kind.prod).shape s t)) Bool)
    (a₀ : Carrier Δ s) (b₀ : Carrier Δ t) :
    let k := if isSum then Kind.sum else Kind.prod
    ((∀a b, observer f (opCarrier k a b) = observer (leftObserver k f b₀) a) ∧
      ∀m : GuardedMode Δ, (∀x, observer f (m.act x) = observer f x) →
        ∀a, observer (leftObserver k f b₀) (m.act a) = observer (leftObserver k f b₀) a) ∨
    ((∀a b, observer f (opCarrier k a b) = observer (rightObserver k f a₀) b) ∧
      ∀m : GuardedMode Δ, (∀x, observer f (m.act x) = observer f x) →
        ∀b, observer (rightObserver k f a₀) (m.act b) = observer (rightObserver k f a₀) b) := by
  let unitMode : GuardedMode Δ := ⟨.epsilon, fun _ => Mode.identity, fun _ _ => rfl⟩
  have hi (x) : observer f (unitMode.act x) = observer f x :=
    congrArg f (Carrier.atMode_identity x)
  rcases pair_child_family isSum f a₀ b₀ with hl | hr
  · refine .inl ⟨?_, ?_⟩
    · simpa only [hi, actObserver_eq f unitMode hi] using (hl unitMode).1
    · intro m hm
      simpa only [actObserver_eq f m hm] using (hl m).2
  · refine .inr ⟨?_, ?_⟩
    · simpa only [hi, actObserver_eq f unitMode hi] using (hr unitMode).1
    · intro m hm
      simpa only [actObserver_eq f m hm] using (hr m).2

def Profile {Δ : Bounds} {shape : ComparisonShape}
    (f : LatticeHom (Order Δ shape) Bool) (labels : List (GuardedMode Δ))
    (names : List ModVar) (parent : Coordinate) (η : ModVar → Mode) : Prop :=
  (∃value, ∀x, observer f x = value) ∨
    ∃child θ, Model f labels child θ ∧
      Aligned names parent child (encodeModes η) (encodeModes θ) ∧
      ∃a b, observer f a = false ∧ observer f b = true

theorem inherited_profile {Δ : Bounds} {parentShape childShape : ComparisonShape}
    {f : LatticeHom (Order Δ parentShape) Bool}
    (g : LatticeHom (Order Δ childShape) Bool) (anchor : Carrier Δ childShape)
    {labels : List (GuardedMode Δ)} {names : List ModVar}
    {parent : Coordinate} {η : ModVar → Mode}
    (hparent : Model f labels parent η)
    (htests : ∀m∈tests names, ∃n∈labels, n.expression = m)
    (hinherit : ∀m∈labels, (∀x, observer f (m.act x) = observer f x) →
      ∀x, observer g (m.act x) = observer g x) :
    Profile g labels names parent η := by
  classical
  by_cases hn : ∃a b, observer g a = false ∧ observer g b = true
  · obtain ⟨a, b, ha, hb⟩ := hn
    obtain ⟨child, θ, hθ, haction⟩ := observer_global_realizable g a b ha hb labels
    have hmodel : Model g labels child θ := ⟨hθ, haction⟩
    exact .inr ⟨child, θ, hmodel,
      observer_models_aligned hparent hmodel htests hinherit a b ha hb, a, b, ha, hb⟩
  · left
    refine ⟨observer g anchor, ?_⟩
    intro x
    cases ha : observer g anchor <;> cases hx : observer g x
    · rfl
    · exact False.elim (hn ⟨anchor, x, ha, hx⟩)
    · exact False.elim (hn ⟨x, anchor, hx, ha⟩)
    · rfl

theorem Profile.model {Δ : Bounds} {shape : ComparisonShape}
    {f : LatticeHom (Order Δ shape) Bool} {labels : List (GuardedMode Δ)}
    {names parent η} (h : Profile f labels names parent η) :
    ∃child θ, Model f labels child θ ∧
      Aligned names parent child (encodeModes η) (encodeModes θ) := by
  rcases h with ⟨value, he⟩ | ⟨child, θ, hmodel, halign, _⟩
  · exact ⟨.unaffected, η, ⟨.inl rfl, fun x m _ =>
      (he (m.act x)).trans (he x).symm⟩, .inl rfl⟩
  · exact ⟨child, θ, hmodel, halign⟩

theorem pair_profile_realizable {Δ : Bounds} {s t : ComparisonShape} (isSum : Bool)
    (f : LatticeHom (Order Δ ((if isSum then Kind.sum else Kind.prod).shape s t)) Bool)
    (a₀ : Carrier Δ s) (b₀ : Carrier Δ t)
    {labels : List (GuardedMode Δ)} {names : List ModVar}
    {parent : Coordinate} {η : ModVar → Mode}
    (hparent : Model f labels parent η)
    (htests : ∀m∈tests names, ∃n∈labels, n.expression = m) :
    let k := if isSum then Kind.sum else Kind.prod
    ((∀a b, observer f (opCarrier k a b) = observer (leftObserver k f b₀) a) ∧
      Profile (leftObserver k f b₀) labels names parent η) ∨
    ((∀a b, observer f (opCarrier k a b) = observer (rightObserver k f a₀) b) ∧
      Profile (rightObserver k f a₀) labels names parent η) := by
  rcases pair_child_profile isSum f a₀ b₀ with hl | hr
  · exact .inl ⟨hl.1, inherited_profile _ a₀ hparent htests (fun m _ => hl.2 m)⟩
  · exact .inr ⟨hr.1, inherited_profile _ b₀ hparent htests (fun m _ => hr.2 m)⟩

end ModalityInference.ComparisonStructuralAlignment
