import ModalityInference.Proofs.ComparisonWindowPumping
import ModalityInference.Proofs.ComparisonRankedEndpointReflection

/-! Local signed clauses for all public comparison endpoints and one common
mode substitution. Each subterm has one bit, including each repeated quantified
name. The leaf bits are arbitrary functions of the same observer tree. -/
namespace ModalityInference.ComparisonWindowEndpoints

open ComparisonWindowPumping ComparisonWindowPumping.Trees ComparisonStructuralLayout
  ComparisonObserverMachine ComparisonRankedDecision

variable {T A : Type}

/-- Fields of the finite input root label used to read a type. -/
structure Fields (A : Type) where
  atom : A → TypeVar → Bool
  unit : A → Bool
  credit : A → Bool
  action : A → ModExpr → Bool → Bool
  left : A → Constructor → Bool
  range : A → Bool → Bool

def Fields.nodes (l : Fields A) (s : Trees T A Constructor) (t : T) : Node T where
  atom := l.atom (s.root t)
  unitValue := l.unit (s.root t)
  creditValue := l.credit (s.root t)
  action := l.action (s.root t)
  branch i := ⟨l.left (s.root t) i, s.child t i⟩
  range := l.range (s.root t)

/-- Public subterms are join-free. Quantified images may still use both internal
lattice operations. -/
def parts : Ty → Finset Ty
  | a@(.var _) | a@(.unit) | a@(.credit) => {a}
  | t@(.prod a b) | t@(.sum a b) | t@(.fn a b) => insert t (parts a ∪ parts b)
  | t@(.modal a _) => insert t (parts a)

@[simp] theorem self_parts (a : Ty) : a ∈ parts a := by cases a <;> simp [parts]

def written (es : List (Ty × Ty)) : Finset Ty :=
  insert .unit (es.toFinset.biUnion (fun p => parts p.1 ∪ parts p.2))

abbrev Slot (es : List (Ty × Ty)) := ↥(written es)

def slot (es : List (Ty × Ty)) (a : Ty) : Slot es :=
  if h : a ∈ written es then ⟨a, h⟩ else ⟨.unit, Finset.mem_insert_self ..⟩

@[simp] theorem slot_val_of_mem {es a} (h : a ∈ written es) : (slot es a).val = a := by
  simp [slot, h]

@[simp] theorem slot_val {es} (j : Slot es) : slot es j.val = j := Subtype.ext (slot_val_of_mem j.property)

def eval (s : Trees T A Constructor) (l : Fields A) (keys : List Nat)
    (modes : ModVar → ModExpr) (images : T → Nat → Bool) : Ty → T → Bool
  | .var (.flex k), t => if keys.contains k then images t k else l.atom (s.root t) (.flex k)
  | .var (.rigid k), t => l.atom (s.root t) (.rigid k)
  | .unit, t => l.unit (s.root t)
  | .credit, t => l.credit (s.root t)
  | .prod a b, t => if l.left (s.root t) .prod then eval s l keys modes images a (s.child t .prod)
                    else eval s l keys modes images b (s.child t .prod)
  | .sum a b, t => if l.left (s.root t) .sum then eval s l keys modes images a (s.child t .sum)
                   else eval s l keys modes images b (s.child t .sum)
  | .fn a b, t => if l.left (s.root t) .fn then !(eval s l keys modes images a (s.child t .fn))
                  else eval s l keys modes images b (s.child t .fn)
  | .modal a m, t => l.action (s.root t) (m.subst modes) (eval s l keys modes images a t)

theorem eval_instantiated (s : Trees T A Constructor) (l : Fields A) (keys : List Nat)
    (modes : ModVar → ModExpr) (images : Nat → CompareTy) (a : Ty) (t : T) :
    eval s l keys modes (fun u k => value (l.nodes s) (images k) u) a t =
      value (l.nodes s) (instantiate keys images modes a) t := by
  induction a generalizing t with
  | var v =>
    cases v with
    | rigid => rfl
    | flex k =>
      by_cases hk : k ∈ keys <;> simp [eval, instantiate, CompareTy.ofTy, CompareTy.subst,
        imageTypes, Fields.nodes, value, hk]
  | _ => simp_all [eval, instantiate, CompareTy.ofTy, CompareTy.subst, Fields.nodes, value]

def unary {J} (f : Bool → Bool) (x : Port Constructor J) : Port Constructor J :=
  match f false, f true with
  | false, false => .const false
  | false, true => x
  | true, false => .neg x
  | true, true => .const true

private theorem unary_eval {J} (f : Bool → Bool) (x : Port Constructor J) (p : J → Bool)
    (c : Constructor → J → Bool) : (unary f x).eval p c = f (x.eval p c) := by
  cases h : x.eval p c <;> cases h0 : f false <;> cases h1 : f true <;>
    simp [unary, h0, h1, Port.eval, h]

def rhs (es : List (Ty × Ty)) (l : Fields A) (keys : List Nat)
    (modes : ModVar → ModExpr) (x : A) : Ty → Port Constructor (Slot es)
  | .var (.flex k) => if keys.contains k then .here (slot es (.var (.flex k)))
                      else .const (l.atom x (.flex k))
  | .var (.rigid k) => .const (l.atom x (.rigid k))
  | .unit => .const (l.unit x)
  | .credit => .const (l.credit x)
  | .prod a b => if l.left x .prod then .child .prod (slot es a) else .child .prod (slot es b)
  | .sum a b => if l.left x .sum then .child .sum (slot es a) else .child .sum (slot es b)
  | .fn a b => if l.left x .fn then .neg (.child .fn (slot es a)) else .child .fn (slot es b)
  | .modal a m => unary (l.action x (m.subst modes)) (.here (slot es a))

inductive Rule (es : List (Ty × Ty)) (l : Fields A) (keys : List Nat)
    (modes : ModVar → ModExpr) (x : A) :
    Port Constructor (Slot es) → Port Constructor (Slot es) → Prop where
  | read (j : Slot es) : Rule es l keys modes x (.here j) (rhs es l keys modes x j.val)
  | bind (j : Slot es) : Rule es l keys modes x (rhs es l keys modes x j.val) (.here j)
  | edge {a b} (h : (a,b) ∈ es) : Rule es l keys modes x (.here (slot es a)) (.here (slot es b))

private theorem parts_trans {a b : Ty} (h : b ∈ parts a) : parts b ⊆ parts a := by
  induction a with
  | var | unit | credit => simp_all [parts]
  | modal a m ih =>
    obtain rfl | hb := Finset.mem_insert.mp h
    · exact Finset.Subset.refl _
    · exact (ih hb).trans (Finset.subset_insert ..)
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    obtain rfl | hc := Finset.mem_insert.mp h
    · exact Finset.Subset.refl _
    · rcases Finset.mem_union.mp hc with ha | hb
      · exact (ia ha).trans (Finset.subset_union_left.trans (Finset.subset_insert ..))
      · exact (ib hb).trans (Finset.subset_union_right.trans (Finset.subset_insert ..))

private theorem written_closed {es a} (h : a ∈ written es) : parts a ⊆ written es := by
  obtain rfl | h := Finset.mem_insert.mp h
  · exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self ..)
  · obtain ⟨p, hp, ha⟩ := Finset.mem_biUnion.mp h
    have ins : parts p.1 ∪ parts p.2 ⊆ written es :=
      (Finset.subset_biUnion_of_mem (fun p : Ty × Ty => parts p.1 ∪ parts p.2) hp).trans
        (Finset.subset_insert ..)
    rcases Finset.mem_union.mp ha with h | h
    · exact (parts_trans h).trans (Finset.subset_union_left.trans ins)
    · exact (parts_trans h).trans (Finset.subset_union_right.trans ins)

private theorem endpoints_written {es a b} (h : (a,b) ∈ es) : a ∈ written es ∧ b ∈ written es := by
  have ins : parts a ∪ parts b ⊆ written es :=
    (Finset.subset_biUnion_of_mem (fun p : Ty × Ty => parts p.1 ∪ parts p.2) (List.mem_toFinset.mpr h)).trans
      (Finset.subset_insert ..)
  exact ⟨ins (Finset.mem_union_left _ (self_parts _)), ins (Finset.mem_union_right _ (self_parts _))⟩

private def children : Ty → List Ty
  | .prod a b | .sum a b | .fn a b => [a,b]
  | .modal a _ => [a]
  | _ => []

private theorem children_mem {a b : Ty} (h : b ∈ children a) : b ∈ parts a := by
  cases a <;> simp_all [children, parts] <;> grind [self_parts]

def entries {es} (F : T → Slot es → Bool) (t : T) (a : Ty) : Bool := F t (slot es a)

private theorem rhs_agree {es : List (Ty × Ty)} (s : Trees T A Constructor) (l : Fields A)
    (keys : List Nat) (modes : ModVar → ModExpr) (images : T → Nat → Bool)
    (F : T → Slot es → Bool) (a : Ty)
    (childrenOk : ∀ b ∈ children a, ∀ t, entries F t b = eval s l keys modes images b t)
    (imagesOk : ∀ k, a = .var (.flex k) → k ∈ keys → ∀ t, entries F t a = images t k)
    (t : T) :
    (rhs es l keys modes (s.root t) a).eval (F t) (fun i => F (s.child t i)) =
      eval s l keys modes images a t := by
  cases a with
  | var v =>
    cases v with
    | rigid => rfl
    | flex k =>
      by_cases hk : k ∈ keys
      · simpa only [rhs, eval, List.contains_iff_mem.mpr hk, if_true, Port.eval, entries] using imagesOk k rfl hk t
      · simp [rhs, eval, hk, Port.eval]
  | unit | credit => rfl
  | modal a m => simpa only [rhs, unary_eval, Port.eval, eval, entries] using congrArg (l.action (s.root t) (m.subst modes)) (childrenOk a (by simp [children]) t)
  | prod a b | sum a b | fn a b =>
    have ha := childrenOk a (by simp [children])
    have hb := childrenOk b (by simp [children])
    simp only [entries] at ha hb
    simp only [rhs, eval]
    split <;> simp [Port.eval, ha, hb]

def canonical {es : List (Ty × Ty)} (s : Trees T A Constructor) (l : Fields A)
    (keys : List Nat) (modes : ModVar → ModExpr) (images : T → Nat → Bool) (t : T)
    (j : Slot es) : Bool := eval s l keys modes images j.val t

private theorem rhs_canonical (es : List (Ty × Ty)) (s : Trees T A Constructor) (l : Fields A)
    (keys : List Nat) (modes : ModVar → ModExpr) (images : T → Nat → Bool) (t : T)
    (j : Slot es) :
    (rhs es l keys modes (s.root t) j.val).eval (canonical s l keys modes images t)
        (fun i => canonical s l keys modes images (s.child t i)) = canonical s l keys modes images t j := by
  apply rhs_agree
  · intro b hb x
    simp only [entries, canonical, slot_val_of_mem (written_closed j.property (children_mem hb))]
  · rintro k eq hk x
    change eval s l keys modes images (slot es j.val).val x = _
    rw [slot_val, eq]
    simp [eval, hk]

theorem canonical_clauses_iff (es : List (Ty × Ty)) (s : Trees T A Constructor) (l : Fields A)
    (keys : List Nat) (modes : ModVar → ModExpr) (images : T → Nat → Bool) :
    (∀ t, Clauses (Rule es l keys modes) (s.root t) (canonical s l keys modes images t)
      (fun i => canonical s l keys modes images (s.child t i))) ↔
      ∀ a b, (a,b) ∈ es → ∀ t, eval s l keys modes images a t ≤ eval s l keys modes images b t := by
  constructor
  · intro h a b hab t
    simpa only [Port.eval, canonical, slot_val_of_mem (endpoints_written hab).1,
      slot_val_of_mem (endpoints_written hab).2] using h t _ _ (.edge hab)
  · intro h t u v rule
    cases rule with
    | read j => exact (rhs_canonical es s l keys modes images t j).symm.le
    | bind j => exact (rhs_canonical es s l keys modes images t j).le
    | edge hp => simpa only [Port.eval, canonical, slot_val_of_mem (endpoints_written hp).1,
        slot_val_of_mem (endpoints_written hp).2] using h _ _ hp t

private theorem children_lt {a b : Ty} (h : b ∈ children a) : sizeOf b < sizeOf a := by
  cases a <;> simp_all [children] <;> grind

def imageBits {es} (F : T → Slot es → Bool) (t : T) (k : Nat) : Bool :=
  entries F t (.var (.flex k))

private theorem reflect {es : List (Ty × Ty)} (s : Trees T A Constructor) (l : Fields A)
    (keys : List Nat) (modes : ModVar → ModExpr) (F : T → Slot es → Bool)
    (h : ∀ t, Clauses (Rule es l keys modes) (s.root t) (F t) (fun i => F (s.child t i)))
    (a : Ty) (ha : a ∈ written es) (t : T) :
    entries F t a = eval s l keys modes (imageBits F) a t := by
  let j : Slot es := ⟨a,ha⟩
  have eq := le_antisymm (h t _ _ (.read j)) (h t _ _ (.bind j))
  have he : entries F t a = (rhs es l keys modes (s.root t) a).eval (F t) (fun i => F (s.child t i)) := by
    simpa only [entries, slot, dif_pos ha, j, Port.eval] using eq
  refine he.trans (rhs_agree s l keys modes (imageBits F) F a ?_ ?_ t)
  · exact fun b hb x => reflect s l keys modes F h b (written_closed ha (children_mem hb)) x
  · exact fun k e _ _ => e ▸ rfl
termination_by sizeOf a
decreasing_by exact children_lt hb

theorem clauses_iff_canonical {es : List (Ty × Ty)} (s : Trees T A Constructor) (l : Fields A)
    (keys : List Nat) (modes : ModVar → ModExpr) (F : T → Slot es → Bool) :
    (∀ t, Clauses (Rule es l keys modes) (s.root t) (F t) (fun i => F (s.child t i))) ↔
      F = canonical s l keys modes (imageBits F) ∧
        ∀ a b, (a,b) ∈ es → ∀ t,
          eval s l keys modes (imageBits F) a t ≤ eval s l keys modes (imageBits F) b t := by
  constructor
  · intro h
    have eq : F = canonical s l keys modes (imageBits F) := funext fun t => funext fun j => by
      simpa only [entries, slot_val, canonical] using reflect s l keys modes F h j.val j.property t
    exact ⟨eq, (canonical_clauses_iff es s l keys modes (imageBits F)).mp
      (fun t => by simpa only [← eq] using h t)⟩
  · rintro ⟨eq, h⟩ t
    simpa only [← eq] using (canonical_clauses_iff es s l keys modes (imageBits F)).mpr h t

open ComparisonRankedBasis

theorem value_reads (s : Trees T A Constructor) (l : Fields A) (a : CompareTy) :
    s.Reads (rank a) (value (l.nodes s) a) := by
  induction a with
  | var | unit | credit =>
    intro x y h
    simp only [value, Fields.nodes, h.root s]
  | modal a m ih =>
    intro x y h
    simp only [value, Fields.nodes, h.root s, ih x y h]
  | join a b ha hb | meet a b ha hb =>
    intro x y h
    have eqA := ha.mono s (Nat.le_max_left (rank a) (rank b)) x y h
    have eqB := hb.mono s (Nat.le_max_right (rank a) (rank b)) x y h
    simp only [value, eqA, eqB]
  | prod a b ha hb | sum a b ha hb | fn a b ha hb =>
    intro x y h
    have eqA := fun c => ha.mono s (Nat.le_max_left (rank a) (rank b)) _ _ (h.2 c)
    have eqB := fun c => hb.mono s (Nat.le_max_right (rank a) (rank b)) _ _ (h.2 c)
    simp only [value, Fields.nodes, h.1, eqA, eqB]

theorem canonical_reads (es : List (Ty × Ty)) (s : Trees T A Constructor) (l : Fields A)
    (keys : List Nat) (modes : ModVar → ModExpr) (images : Nat → CompareTy) :
    ∃ n, s.Reads n (canonical (es := es) s l keys modes
      (fun t k => value (l.nodes s) (images k) t)) := by
  let r : Slot es → Nat := fun j => rank (instantiate keys images modes j.val)
  refine ⟨Finset.univ.sup r, fun x y h => funext fun j => ?_⟩
  simp only [canonical, eval_instantiated]
  exact (value_reads s l _).mono s (Finset.le_sup (f := r) (Finset.mem_univ j)) x y h

private theorem semantic_endpoints {p : SchemePreparation.Prepared} {τ : CompareSubstitution}
    (hw : ComparisonPreparation.PreparedWitnessUnder p τ) (hΔ : p.assumptions.TypeBoundsDefined)
    (pair : CompareTy × CompareTy) (hp : pair ∈ ComparisonStructuralEndpoints.all p τ) :
    AlgebraSubtype p.assumptions pair.1 pair.2 ∧ pair.1.DefinedUnder p.assumptions ∧
      pair.2.DefinedUnder p.assumptions := by
  rcases List.mem_append.mp hp with hd | hs
  · have hg := ComparisonStructuralEndpoints.declared_guarded p hΔ pair hd
    exact ⟨hg.subtype, hg.left_defined, hg.right_defined⟩
  · rcases List.mem_append.mp hs with hs | hb
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
      obtain ⟨c, hc, hq⟩ := List.mem_flatMap.mp hq
      exact ComparisonStructuralEndpoints.constraintPairs_semantic
        (hw.1.2.2.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)) q hq
    · cases List.mem_singleton.mp hb
      exact ⟨hw.1.2.2.2, hw.2.2, (CompareTy.definedUnder_ofTy _ _).mpr
        (ComparisonPartialBoundary.public_defined_of_above hΔ hw.2.2 hw.1.2.2.2)⟩

/-- Every prepared witness supplies a solution on a certified observer domain
closed under compatible grafts. One input-only window suffices for all body and
bound occurrences. -/
theorem prepared_window_bound [Fintype A] {ambient : Bounds} {source target : Scheme}
    {σ : CompareSubstitution}
    (hw : ComparisonPreparation.PreparedWitnessUnder
      (SchemePreparation.prepare ambient source target) σ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    (s : Trees T A Constructor) (l : Fields A)
    (hc : Certified (SchemePreparation.prepare ambient source target).assumptions (l.nodes s)) :
    let p := SchemePreparation.prepare ambient source target
    let es := ComparisonSignedObservation.endpoints p
    let keys := ComparisonSelectedBases.inputTypeKeys p
    ∃ bits : T → Nat → Bool,
      s.Reads (windowBound (Fintype.card A) (2 ^ (written es).card)) bits ∧
      ∀ a b, (a,b) ∈ es → ∀ t,
        eval s l keys σ.mode bits a t ≤ eval s l keys σ.mode bits b t := by
  intro p es keys
  let images := fun k => σ.type (.flex k)
  let v := fun t k => value (l.nodes s) (images k) t
  have observed : ∀ a b, (a,b) ∈ es → ∀ t,
      eval s l keys σ.mode v a t ≤ eval s l keys σ.mode v b t := by
    intro a b hab t
    have hin := ComparisonSelectedBases.inputAction_prepared hw
    obtain ⟨hsub, ha, hb⟩ := semantic_endpoints hin hΔ _
      (ComparisonSignedObservation.prepared_interpreted_mem hin hab)
    simp only [v, eval_instantiated, images, keys, instantiate_inputAction]
    exact subtype_mono hc.modal hc.range hc.coherent hc.bounds hΔ ha hb hsub t
  obtain ⟨n, hn⟩ := canonical_reads es s l keys σ.mode images
  obtain ⟨F, hF, valid⟩ := s.finite_window_bound (Rule es l keys σ.mode)
    (canonical s l keys σ.mode v) hn ((canonical_clauses_iff es s l keys σ.mode v).mpr observed)
  refine ⟨imageBits F, ?_, ((clauses_iff_canonical s l keys σ.mode F).mp valid).2⟩
  intro x y h
  have eq := hF x y (by simpa only [Slot, Fintype.card_coe] using h)
  exact funext fun k => congrFun eq (slot es (.var (.flex k)))
