import ModalityInference.Proofs.ComparisonWindowEndpoints
import ModalityInference.Proofs.ComparisonFiniteWindowMachines

/-! The finite header of a checked observer records all finite scalar and type
inputs. The original declared edges bound how many headers may be inspected at
a node. Trees with witnessed legal prefixes are closed under compatible grafts. -/
namespace ModalityInference.ComparisonWindowObservers

open ComparisonWindowPumping ComparisonWindowEndpoints ComparisonDefiniteTreeMachines
  ComparisonStructuralLayout ComparisonControls ComparisonObserverMachine
  ComparisonObserverMachineCheck ComparisonRankedBasis

variable {A I : Type}

abbrev Raw (A I : Type) := List I → A

def sub (x : Raw A I) (p : List I) : Raw A I := fun q => x (p ++ q)

def rawTrees : Trees (Raw A I) A I where
  root x := x []
  child x i := down i x
  paste x cs _ := ⟨graft (x []) cs, rfl, rfl⟩

def Closed {n} (ok : Window A I (n+1) → Prop) :=
  {x : Raw A I // ∀ p, ok (Window.capture (n+1) (sub x p))}

def closedTrees {n} (ok : Window A I (n+1) → Prop) :
    Trees (Closed ok) (Window A I (n+1)) I where
  root x := Window.capture (n+1) x.val
  child x i := ⟨down i x.val, fun p => x.property (i :: p)⟩
  paste x cs h := by
    let u := graft (x.val []) (fun i => (cs i).val)
    have root : Window.capture (n+1) u = Window.capture (n+1) x.val := by
      change (x.val [], fun i => Window.capture n (cs i).val) = _
      change (x.val [], _) = (x.val [], fun i => Window.capture n (down i x.val))
      congr 1
      funext i
      simpa only [Window.trim_capture] using congrArg (Window.trim n) (h i)
    have legal : ∀ p, ok (Window.capture (n+1) (sub u p)) := by
      intro p
      cases p with
      | nil => exact root ▸ x.property []
      | cons i p => exact (cs i).property p
    exact ⟨⟨u, legal⟩, root, funext fun _ => Subtype.ext rfl⟩

def readFields (l : Fields A) (n : Nat) : Fields (Window A I (n+1)) where
  atom w := l.atom w.1
  unit w := l.unit w.1
  credit w := l.credit w.1
  action w := l.action w.1
  left w := l.left w.1
  range w := l.range w.1

private theorem read_raw (l : Fields A) {n} {ok : Window A Constructor (n+1) → Prop}
    (a : CompareTy) (t : Closed ok) :
    value ((readFields l n).nodes (closedTrees ok)) a t =
      value (l.nodes rawTrees) a t.val := by
  induction a generalizing t with
  | var | unit | credit => rfl
  | prod a b ha hb | sum a b ha hb | fn a b ha hb =>
    simp only [value, ha, hb]
    rfl
  | _ => simp_all [value, Fields.nodes, readFields, closedTrees, rawTrees, Window.capture]

private theorem prefix_capture (n : Nat) (x y : Raw A I) :
    Window.capture (n+1) x = Window.capture (n+1) y → rawTrees.Prefix n x y := by
  induction n generalizing x y with
  | zero => exact fun h => congrArg Prod.fst h
  | succ n ih =>
    intro h
    refine ⟨congrArg Prod.fst h, fun i => ih _ _ ?_⟩
    exact congrFun (congrArg Prod.snd h) i
private instance finiteConstructor : Fintype Constructor :=
  ⟨{.prod, .sum, .fn}, by intro k; cases k <;> simp⟩

private instance finiteCoordinate : Fintype Coordinate :=
  ⟨{.unaffected, .locality, .affinity, .uniqueness}, by intro k; cases k <;> simp⟩

private instance finiteMode : Fintype Mode := Fintype.ofEquiv (Bool × Bool × Bool)
  ⟨fun p => ⟨p.1, p.2.1, p.2.2⟩, fun m => (m.isLocal,m.once,m.unique),
   fun _ => rfl, fun _ => rfl⟩

/-- The alphabet is finite even though the original checked description allows
arbitrary lengths of value lists. Only its observable entries are recorded. -/
abbrev Letter (types : List TypeVar) (names : List ModVar) :=
  (↥types.toFinset → Bool) × (↥names.toFinset → Mode) × Coordinate × Bool × Bool ×
    (Constructor → Bool) × (Bool → Bool)

def encode {S} (types : List TypeVar) (names : List ModVar) (d : Description S) :
    Letter types names :=
  (fun v => atomValue types d v.val, fun v => modeValue names d v.val, d.coordinate,
    d.unitValue, d.creditValue, fun k => (d.branch k).left, d.range)

def valuation {types names} (w : Letter types names) (v : ModVar) : Mode :=
  if h : v ∈ names.toFinset then w.2.1 ⟨v, h⟩ else Mode.identity

def fields (types : List TypeVar) (names : List ModVar) : Fields (Letter types names) where
  atom w v := if h : v ∈ types.toFinset then w.1 ⟨v,h⟩ else w.2.2.2.1
  unit w := w.2.2.2.1
  credit w := w.2.2.2.2.1
  action w m x := act w.2.2.1 ((m.eval (some ∘ valuation w)).getD Mode.identity) x
  left w := w.2.2.2.2.2.1
  range w := w.2.2.2.2.2.2

@[simp] private theorem valuation_encode {S} (types names) (d : Description S) :
    valuation (encode types names d) = modeValue names d := by
  funext v
  by_cases h : v ∈ names <;> simp [valuation, encode, h, modeValue]

@[simp] private theorem atom_encode {S} (types names) (d : Description S) (v : TypeVar) :
    (fields types names).atom (encode types names d) v = atomValue types d v := by
  by_cases h : v ∈ types <;> simp [fields, encode, h, atomValue]

@[simp] private theorem action_encode {S} (types names) (d : Description S) (m : ModExpr) (x : Bool) :
    (fields types names).action (encode types names d) m x = action names d m x := by
  change act d.coordinate ((m.eval (some ∘ valuation (encode types names d))).getD _) x = _
  rw [valuation_encode]
  rfl

variable {S : Type}

def walk (D : S → Description S) (i : S) : List Constructor → S
  | [] => i
  | k :: p => walk D ((D i).branch k).next p

def unroll (types names) (D : S → Description S) (i : S) : Raw (Letter types names) Constructor :=
  fun p => encode types names (D (walk D i p))

private theorem unroll_down (types names) (D : S → Description S) (i : S) (k : Constructor) :
    down k (unroll types names D i) = unroll types names D ((D i).branch k).next := rfl

private theorem unroll_root (types names) (D : S → Description S) (i : S) :
    unroll types names D i [] = encode types names (D i) := rfl

private theorem value_unroll (types names) (D : S → Description S) (i : S) (a : CompareTy) :
    value ((fields types names).nodes rawTrees) a (unroll types names D i) =
      value (nodes types names D) a i := by
  induction a generalizing i with
  | var v => exact atom_encode ..
  | unit | credit => rfl
  | modal a m ha =>
    change (fields types names).action (encode types names (D i)) m _ = _
    rw [ha, action_encode]
    rfl
  | join a b ha hb | meet a b ha hb => simp only [value, ha, hb]
  | prod a b ha hb | sum a b ha hb | fn a b ha hb =>
    have child (k : Constructor) : (((fields types names).nodes rawTrees (unroll types names D i)).branch k).next = unroll types names D ((D i).branch k).next := rfl
    simp only [value, child, ha, hb]
    rfl

def declaredRank : Constraint → Nat
  | .sub a b => max (rank (.ofTy a)) (rank (.ofTy b))
  | _ => 0

def radius (Δ : Bounds) : Nat := (Δ.toFinset.sup declaredRank) + 1

private theorem declared_rank_le {Δ : Bounds} {a b : Ty} (h : Constraint.sub a b ∈ Δ) :
    rank (.ofTy a) ≤ radius Δ ∧ rank (.ofTy b) ≤ radius Δ := by
  have e : max (rank (.ofTy a)) (rank (.ofTy b)) ≤ Δ.toFinset.sup declaredRank :=
    Finset.le_sup (f := declaredRank) (List.mem_toFinset.mpr h)
  exact ⟨(Nat.le_max_left ..).trans (Nat.le_succ_of_le e),
    (Nat.le_max_right ..).trans (Nat.le_succ_of_le e)⟩

def checkedPrefix (Δ : Bounds) (types names) (w : Window (Letter types names) Constructor (radius Δ + 1)) : Prop :=
  ∃ (count : Nat) (D : Fin count → Description (Fin count)) (i : Fin count),
    check Δ types names D = true ∧ w = Window.capture _ (unroll types names D i)

abbrev Observer (Δ : Bounds) (types names) := Closed (checkedPrefix Δ types names)

abbrev observerTrees (Δ : Bounds) (types names) := closedTrees (checkedPrefix Δ types names)

abbrev observerFields (Δ : Bounds) (types names) :=
  readFields (I := Constructor) (fields types names) (radius Δ)

abbrev observerNodes (Δ : Bounds) (types names) :=
  (observerFields Δ types names).nodes (observerTrees Δ types names)

private theorem walk_append (D : S → Description S) (i : S) (p q : List Constructor) :
    walk D i (p ++ q) = walk D (walk D i p) q := by
  induction p generalizing i with
  | nil => rfl
  | cons k p ih => exact ih _

def embed {count} {D : Fin count → Description (Fin count)} {Δ types names}
    (h : check Δ types names D = true) (i : Fin count) : Observer Δ types names :=
  ⟨unroll types names D i, fun p => ⟨count,D, walk D i p,h, by
    apply congrArg (Window.capture _)
    funext q
    exact congrArg (fun j => encode types names (D j)) (walk_append D i p q)⟩⟩

@[simp] theorem embed_value {count} {D : Fin count → Description (Fin count)} {Δ types names}
    (h : check Δ types names D = true) (i : Fin count) (a : CompareTy) :
    value (observerNodes Δ types names) a (embed h i) = value (nodes types names D) a i :=
  (read_raw _ _ _).trans (value_unroll _ _ _ _ _)

structure Match {Δ types names} (t : Observer Δ types names) where
  count : Nat
  data : Fin count → Description (Fin count)
  state : Fin count
  valid : check Δ types names data = true
  root : t.val [] = encode types names (data state)
  child : ∀ k, t.val [k] = encode types names (data ((data state).branch k).next)
  read : ∀ a, rank a ≤ radius Δ →
    value (observerNodes Δ types names) a t = value (nodes types names data) a state

private theorem exists_match {Δ types names} (t : Observer Δ types names) : Nonempty (Match t) := by
  obtain ⟨count,D,i,hc,eq⟩ := t.property []
  have same : rawTrees.Prefix (radius Δ) t.val (unroll types names D i) :=
    prefix_capture (radius Δ) _ _ eq
  refine ⟨⟨count, D, i, hc, same.root _, fun k => (same.2 k).root _, fun a ha => ?_⟩⟩
  exact (read_raw _ _ _).trans (((value_reads rawTrees (fields types names) a).mono _ ha _ _ same).trans
    (value_unroll _ _ _ _ _))

private noncomputable def origin {Δ types names} (t : Observer Δ types names) : Match t :=
  Classical.choice (exists_match t)

private abbrev src {Δ types names} {t : Observer Δ types names} (o : Match t) :=
  nodes types names o.data

private theorem Match.action {Δ types names} {t : Observer Δ types names} (o : Match t) :
    (observerNodes Δ types names t).action = (src o o.state).action := by
  funext m x
  change (fields types names).action (t.val []) m x = _
  rw [o.root, action_encode]
  rfl

private theorem Match.atom {Δ types names} {t : Observer Δ types names} (o : Match t) :
    (observerNodes Δ types names t).atom = (src o o.state).atom := by
  funext v
  change (fields types names).atom (t.val []) v = _
  rw [o.root, atom_encode]
  rfl

private theorem Match.unit {Δ types names} {t : Observer Δ types names} (o : Match t) :
    (observerNodes Δ types names t).unitValue = (src o o.state).unitValue :=
  congrArg (fields types names).unit o.root

private theorem Match.credit {Δ types names} {t : Observer Δ types names} (o : Match t) :
    (observerNodes Δ types names t).creditValue = (src o o.state).creditValue :=
  congrArg (fields types names).credit o.root

private theorem Match.left {Δ types names} {t : Observer Δ types names} (o : Match t) (k) :
    ((observerNodes Δ types names t).branch k).left = ((src o o.state).branch k).left :=
  congrFun (congrArg (fields types names).left o.root) k

private theorem Match.range {Δ types names} {t : Observer Δ types names} (o : Match t) :
    (observerNodes Δ types names t).range = (src o o.state).range :=
  congrArg (fields types names).range o.root

private theorem Match.childRange {Δ types names} {t : Observer Δ types names} (o : Match t) (k) :
    (observerNodes Δ types names ((observerNodes Δ types names t).branch k).next).range =
      (src o ((src o o.state).branch k).next).range :=
  congrArg (fields types names).range (o.child k)

private theorem Match.childAction {Δ types names} {t : Observer Δ types names} (o : Match t) (k) :
    (observerNodes Δ types names ((observerNodes Δ types names t).branch k).next).action =
      (src o ((src o o.state).branch k).next).action := by
  funext m x
  change (fields types names).action (t.val [k]) m x = _
  rw [o.child, action_encode]
  rfl

/-- Every locally completed tree is a certified observer of the original
bounds, including recursive edges without any finite shape model. -/
theorem certified (Δ : Bounds) (types names) : Certified Δ (observerNodes Δ types names) := by
  let proof (t : Observer Δ types names) := check_sound (origin t).valid
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro t m h
    rw [(origin t).action]
    exact (proof t).modal.monotone _ m h
  · intro t x
    rw [(origin t).action]
    exact (proof t).modal.epsilon ..
  · intro t m n hm hn x
    rw [(origin t).action]
    exact (proof t).modal.compose _ _ _ hm hn _
  · intro t m n hm hn x
    rw [(origin t).action]
    exact (proof t).modal.join _ _ _ hm hn _
  · intro t m n hm hn x
    rw [(origin t).action]
    exact (proof t).modal.meet _ _ _ hm hn _
  · intro t m n hm x
    rw [(origin t).action]
    exact (proof t).modal.submode _ _ _ hm _
  · intro t v
    rw [(origin t).range, (origin t).atom]
    exact (proof t).range.atom ..
  · intro t
    rw [(origin t).range, (origin t).unit]
    exact (proof t).range.unit ..
  · intro t
    rw [(origin t).range, (origin t).credit]
    exact (proof t).range.credit ..
  · intro t k x
    rw [(origin t).childRange, (origin t).range, (origin t).left]
    exact (proof t).range.branch _ k x
  · intro t m hm x
    rw [(origin t).range, (origin t).action]
    exact (proof t).range.modal _ _ hm _
  · intro t k hk m hm x
    rw [(origin t).childRange, (origin t).childAction, (origin t).action]
    exact (proof t).coherent.pair _ k hk _ hm _
  · intro t m n hmn x
    rw [(origin t).childRange, (origin t).left, (origin t).action]
    exact (proof t).coherent.fn _ _ _ hmn _
  · intro t a b hab
    obtain ⟨ha, hb⟩ := declared_rank_le hab
    rw [(origin t).read _ ha, (origin t).read _ hb]
    exact (proof t).bounds _ _ _ hab

/-- The finite alphabet and the simultaneous output arity are determined by the
prepared comparison. Every accepted finite observer embeds in this domain. -/
def observationBound (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (es : List (Ty × Ty)) : Nat :=
  Trees.windowBound (Fintype.card (Window (Letter types names) Constructor (radius Δ + 1)))
    (2 ^ (written es).card)

theorem prepared_window {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hw : ComparisonPreparation.PreparedWitnessUnder
      (SchemePreparation.prepare ambient source target) σ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined) :
    let p := SchemePreparation.prepare ambient source target
    let es := ComparisonSignedObservation.endpoints p
    let keys := ComparisonSelectedBases.inputTypeKeys p
    let types := (ComparisonWitnessRestriction.inputTypes p).toList
    let names := (ComparisonWitnessRestriction.inputModes p).toList
    let s := observerTrees p.assumptions types names
    let l := observerFields p.assumptions types names
    ∃ bits : Observer p.assumptions types names → Nat → Bool,
      s.Reads (observationBound p.assumptions types names es) bits ∧
      ∀ a b, (a,b) ∈ es → ∀ t,
        eval s l keys σ.mode bits a t ≤ eval s l keys σ.mode bits b t := by
  intro p es keys types names s l
  exact prepared_window_bound hw hΔ s l (certified p.assumptions types names)

end ModalityInference.ComparisonWindowObservers
