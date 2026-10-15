import ModalityInference.Proofs.ComparisonPartialCapsule

namespace ModalityInference.ComparisonPartialStructuredCapsule

open ComparisonPartialCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Token := List Bool × (CompareTy × ModExpr)
abbrev Suffix := Option ModExpr

def Suffix.apply (suffix : Suffix) (a : CompareTy) : CompareTy :=
  match suffix with
  | none => a
  | some m => .modal a m

def Suffix.total (Δ : Bounds) : Suffix → Prop
  | none => True
  | some m => Entails Δ (.defined m)

def Suffix.prepend (m : ModExpr) : Suffix → Suffix
  | none => some m
  | some n => some (.compose m n)

def Suffix.Equivalent (Δ : Bounds) (left right : Suffix) : Prop :=
  (left.total Δ ↔ right.total Δ) ∧
    ∀ a, ComparisonPartialCapsule.observe Δ (left.apply a) =
      ComparisonPartialCapsule.observe Δ (right.apply a)

 theorem Suffix.observe_prepend (Δ : Bounds) (suffix : Suffix) (m : ModExpr) (a : CompareTy) :
    ComparisonPartialCapsule.observe Δ ((suffix.prepend m).apply a) =
      ComparisonPartialCapsule.observe Δ (suffix.apply (.modal a m)) := by
  cases suffix with
  | none => rfl
  | some n => exact ComparisonPartialCapsule.observe_compose Δ a m n

 theorem Suffix.total_prepend (Δ : Bounds) (suffix : Suffix) (m : ModExpr) :
    (suffix.prepend m).total Δ ↔ Entails Δ (.defined m) ∧ suffix.total Δ := by
  cases suffix with
  | none => simp [Suffix.prepend, Suffix.total]
  | some n => exact Entails.defined_compose_iff

 theorem Suffix.Equivalent.prepend {Δ : Bounds} {left right : Suffix}
    (h : Suffix.Equivalent Δ left right) (m : ModExpr) :
    Suffix.Equivalent Δ (left.prepend m) (right.prepend m) := by
  constructor
  · rw [Suffix.total_prepend, Suffix.total_prepend, h.1]
  · intro a
    rw [Suffix.observe_prepend, Suffix.observe_prepend]
    exact h.2 (.modal a m)

 theorem Suffix.total_equivalent_none {Δ : Bounds} {suffix : Suffix}
    (h : suffix.total Δ) : Suffix.Equivalent Δ suffix none := by
  refine ⟨by simp only [Suffix.total]; exact iff_true_intro h, ?_⟩
  intro a
  cases suffix with
  | none => rfl
  | some m => exact ComparisonPartialCapsule.observe_modal_total h a

structure Observation where
  positive : Set Token
  negative : Set Token

def Observation.empty : Observation := ⟨∅, ∅⟩

def atPath (side : Bool) (tokens : Set Token) : Set Token :=
  (fun t => (side :: t.1, t.2)) '' tokens

def Observation.fork (left right : Observation) : Observation :=
  ⟨atPath false left.positive ∪ atPath true right.positive,
   atPath false left.negative ∪ atPath true right.negative⟩

def Observation.flip (a : Observation) : Observation := ⟨a.negative, a.positive⟩

def Observation.join (a b : Observation) : Observation :=
  ⟨a.positive ∪ b.positive, a.negative ∩ b.negative⟩

def Observation.meet (a b : Observation) : Observation :=
  ⟨a.positive ∩ b.positive, a.negative ∪ b.negative⟩

def literal (Δ : Bounds) (a : CompareTy) (suffix : Suffix) : Observation :=
  let tokens := (fun t => ([], t)) '' ComparisonPartialCapsule.observe Δ (suffix.apply a)
  ⟨tokens, tokens⟩

/-- Product and sum paths inherit the whole modal suffix. A partial action at
any other constructor remains a literal capsule; root composition is retained
as a syntactic context rather than reassociated under a partial action. -/
def observe (Δ : Bounds) : CompareTy → Suffix → Observation
  | .modal a m, suffix => observe Δ a (suffix.prepend m)
  | .prod a b, suffix | .sum a b, suffix =>
      (observe Δ a suffix).fork (observe Δ b suffix)
  | .fn a b, suffix =>
      if suffix.total Δ then (observe Δ a none).flip.fork (observe Δ b none)
      else literal Δ (.fn a b) suffix
  | .join a b, suffix =>
      if suffix.total Δ then (observe Δ a none).join (observe Δ b none)
      else literal Δ (.join a b) suffix
  | .meet a b, suffix =>
      if suffix.total Δ then (observe Δ a none).meet (observe Δ b none)
      else literal Δ (.meet a b) suffix
  | a, suffix => literal Δ a suffix

 theorem observe_suffix_congr {Δ : Bounds} {left right : Suffix}
    (h : Suffix.Equivalent Δ left right) (a : CompareTy) :
    observe Δ a left = observe Δ a right := by
  induction a generalizing left right with
  | modal a m ih => exact ih (h.prepend m)
  | prod a b ia ib | sum a b ia ib => simp only [observe, ia h, ib h]
  | fn a b ia ib | join a b ia ib | meet a b ia ib =>
      simp only [observe, h.1, literal, h.2]
  | var | unit | credit => simp only [observe, literal, h.2]

 theorem observe_total {Δ : Bounds} {suffix : Suffix} (h : suffix.total Δ) (a : CompareTy) :
    observe Δ a suffix = observe Δ a none := observe_suffix_congr (Suffix.total_equivalent_none h) a

 theorem observe_modal_total {Δ : Bounds} {m : ModExpr} (h : Entails Δ (.defined m))
    (a : CompareTy) : observe Δ (.modal a m) none = observe Δ a none :=
  observe_total (suffix := some m) h a

 theorem observe_compose (Δ : Bounds) (a : CompareTy) (m n : ModExpr) :
    observe Δ (.modal a (.compose m n)) none = observe Δ (.modal (.modal a m) n) none := rfl

 theorem observe_defined {Δ : Bounds} {a : CompareTy} (h : a.DefinedUnder Δ) :
    observe Δ a none = .empty := by
  induction a with
  | var | unit | credit =>
      simp only [observe, literal, Suffix.apply, ComparisonPartialCapsule.observe,
        Set.image_empty, Observation.empty]
  | prod a b ia ib | sum a b ia ib =>
      obtain ⟨ha, hb⟩ := CompareTy.definedUnder_prod_iff.mp h
      simp only [observe, ia ha, ib hb, Observation.empty, Observation.fork, atPath,
        Set.image_empty, Set.empty_union]
  | fn a b ia ib =>
      obtain ⟨ha, hb⟩ := CompareTy.definedUnder_fn_iff.mp h
      simp only [observe, Suffix.total, ↓reduceIte, ia ha, ib hb, Observation.empty,
        Observation.flip, Observation.fork, atPath, Set.image_empty, Set.empty_union]
  | join a b ia ib =>
      obtain ⟨ha, hb⟩ := CompareTy.definedUnder_join_iff.mp h
      simp only [observe, Suffix.total, ↓reduceIte, ia ha, ib hb, Observation.empty,
        Observation.join, Set.empty_union, Set.empty_inter]
  | meet a b ia ib =>
      obtain ⟨ha, hb⟩ := CompareTy.definedUnder_meet_iff.mp h
      simp only [observe, Suffix.total, ↓reduceIte, ia ha, ib hb, Observation.empty,
        Observation.meet, Set.empty_union, Set.empty_inter]
  | modal a m ih =>
      obtain ⟨ha, hm⟩ := CompareTy.definedUnder_modal_iff.mp h
      rw [observe_modal_total hm, ih ha]


def Observation.Related (a b : Observation) : Prop :=
  a.positive ⊆ b.positive ∧ b.negative ⊆ a.negative

 theorem Observation.Related.refl (a : Observation) : a.Related a :=
  ⟨Set.Subset.rfl, Set.Subset.rfl⟩

 theorem Observation.Related.trans {a b c : Observation} (h : a.Related b) (g : b.Related c) :
    a.Related c := ⟨h.1.trans g.1, g.2.trans h.2⟩

 theorem Observation.Related.flip {a b : Observation} (h : a.Related b) : b.flip.Related a.flip :=
  ⟨h.2, h.1⟩

 theorem Observation.Related.fork {a b c d : Observation} (h : a.Related c) (g : b.Related d) :
    (a.fork b).Related (c.fork d) := by
  constructor
  · exact Set.union_subset_union (Set.image_mono h.1) (Set.image_mono g.1)
  · exact Set.union_subset_union (Set.image_mono h.2) (Set.image_mono g.2)

 theorem Observation.joinLeft (a b : Observation) : a.Related (a.join b) :=
  ⟨Set.subset_union_left, Set.inter_subset_left⟩

 theorem Observation.joinRight (a b : Observation) : b.Related (a.join b) :=
  ⟨Set.subset_union_right, Set.inter_subset_right⟩

 theorem Observation.meetLeft (a b : Observation) : (a.meet b).Related a :=
  ⟨Set.inter_subset_left, Set.subset_union_left⟩

 theorem Observation.meetRight (a b : Observation) : (a.meet b).Related b :=
  ⟨Set.inter_subset_right, Set.subset_union_right⟩

 theorem Observation.Related.joinLeast {a b c : Observation} (h : a.Related c) (g : b.Related c) :
    (a.join b).Related c :=
  ⟨Set.union_subset h.1 g.1, Set.subset_inter h.2 g.2⟩

 theorem Observation.Related.meetGreatest {a b c : Observation} (h : a.Related b)
    (g : a.Related c) : a.Related (b.meet c) :=
  ⟨Set.subset_inter h.1 g.1, Set.union_subset h.2 g.2⟩

 theorem observe_fn_total {Δ : Bounds} {m : ModExpr} (hm : Entails Δ (.defined m))
    (a b : CompareTy) : observe Δ (.modal (.fn a b) m) none =
      (observe Δ a none).flip.fork (observe Δ b none) := by
  rw [observe_modal_total hm]
  simp only [observe, Suffix.total, ↓reduceIte]

 theorem shaped_sound {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a b : CompareTy} (h : ShapedSubtype Δ a b) :
    (observe Δ a none).Related (observe Δ b none) := by
  induction h
  case refl => exact .refl _
  case trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  case bound a b hab =>
    rw [observe_defined ((CompareTy.definedUnder_ofTy _ _).mpr (hΔ a b hab).1),
      observe_defined ((CompareTy.definedUnder_ofTy _ _).mpr (hΔ a b hab).2)]
    exact .refl _
  case identity a ha => rw [observe_modal_total (m := .epsilon) (fun _ _ => rfl)]; exact .refl _
  case identityRev a ha => rw [observe_modal_total (m := .epsilon) (fun _ _ => rfl)]; exact .refl _
  case compose a m n ha => rw [observe_compose]; exact .refl _
  case composeRev a m n ha => rw [observe_compose]; exact .refl _
  case congr hab hm ih =>
    simpa only [observe_modal_total hm.defined.1, observe_modal_total hm.defined.2] using ih
  case prod hab hcd ih₁ ih₂ => exact ih₁.fork ih₂
  case sum hab hcd ih₁ ih₂ => exact ih₁.fork ih₂
  case fn hca hbd hmn ih₁ ih₂ =>
    obtain ⟨hn, _⟩ := Entails.defined_compose_iff.mp hmn.defined.2
    rw [observe_fn_total hmn.defined.1, observe_fn_total hn]
    exact ih₁.flip.fork ih₂
  case joinLeft =>
    simp only [observe, Suffix.total, ↓reduceIte]
    exact Observation.joinLeft _ _
  case joinRight =>
    simp only [observe, Suffix.total, ↓reduceIte]
    exact Observation.joinRight _ _
  case meetLeft =>
    simp only [observe, Suffix.total, ↓reduceIte]
    exact Observation.meetLeft _ _
  case meetRight =>
    simp only [observe, Suffix.total, ↓reduceIte]
    exact Observation.meetRight _ _
  case joinLeast _ _ ih₁ ih₂ =>
    simp only [observe, Suffix.total, ↓reduceIte]
    exact ih₁.joinLeast ih₂
  case meetGreatest _ _ ih₁ ih₂ =>
    simp only [observe, Suffix.total, ↓reduceIte]
    exact ih₁.meetGreatest ih₂

/-- The structured capsule observation validates every algebra rule, including
partial product/sum actions and literal root composition. -/
 theorem algebra_sound {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a b : CompareTy} (h : AlgebraSubtype Δ a b) :
    (observe Δ a none).Related (observe Δ b none) := by
  induction h
  case shaped h => exact shaped_sound hΔ h
  case trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  case equation he =>
    rw [observe_defined (ComparisonDefinedCovers.equation_defined he).1,
      observe_defined (ComparisonDefinedCovers.equation_defined he).2]
    exact .refl _
  case equationRev he =>
    rw [observe_defined (ComparisonDefinedCovers.equation_defined he).1,
      observe_defined (ComparisonDefinedCovers.equation_defined he).2]
    exact .refl _
  case congr hab hm ih =>
    simpa only [observe_modal_total hm.defined.1, observe_modal_total hm.defined.2] using ih
  case prod hab hcd ih₁ ih₂ => exact ih₁.fork ih₂
  case sum hab hcd ih₁ ih₂ => exact ih₁.fork ih₂
  case fn hca hbd hmn ih₁ ih₂ =>
    obtain ⟨hn, _⟩ := Entails.defined_compose_iff.mp hmn.defined.2
    rw [observe_fn_total hmn.defined.1, observe_fn_total hn]
    exact ih₁.flip.fork ih₂
  case joinLeast _ _ ih₁ ih₂ =>
    simp only [observe, Suffix.total, ↓reduceIte]
    exact ih₁.joinLeast ih₂
  case meetGreatest _ _ ih₁ ih₂ =>
    simp only [observe, Suffix.total, ↓reduceIte]
    exact ih₁.meetGreatest ih₂
  case clamp hba hat hm h₁ h₂ ih₁ ih₂ =>
    rw [observe_defined (ComparisonDefinedCovers.clamp_endpoints_defined hba hat hm).1,
      observe_defined (ComparisonDefinedCovers.clamp_endpoints_defined hba hat hm).2]
    exact .refl _
  case clampRev hba hat hm h₁ h₂ ih₁ ih₂ =>
    rw [observe_defined (ComparisonDefinedCovers.clamp_endpoints_defined hba hat hm).1,
      observe_defined (ComparisonDefinedCovers.clamp_endpoints_defined hba hat hm).2]
    exact .refl _

 theorem carrier_balanced {Δ : Bounds} {a : CompareTy} (ha : Carrier Δ a) (suffix : Suffix) :
    (observe Δ a suffix).positive = (observe Δ a suffix).negative := by
  induction a generalizing suffix with
  | var | unit | credit => rfl
  | modal a m ih => exact ih ha (suffix.prepend m)
  | prod a b ia ib | sum a b ia ib =>
    simp only [observe, Observation.fork, ia ha.1 suffix, ib ha.2 suffix]
  | fn a b ia ib =>
    simp only [observe]
    split
    · simp only [Observation.fork, Observation.flip, ia ha.1 none, ib ha.2 none]
    · rfl
  | join a b ia ib =>
    simp only [observe]
    split
    · rw [observe_defined ha.1, observe_defined ha.2]
      simp only [Observation.empty, Observation.join,
        Set.empty_union, Set.empty_inter]
    · rfl
  | meet a b ia ib =>
    simp only [observe]
    split
    · rw [observe_defined ha.1, observe_defined ha.2]
      simp only [Observation.empty, Observation.meet,
        Set.empty_union, Set.empty_inter]
    · rfl

/-- Comparable carriers have exactly the same literal partial capsules at every
product, sum, and function path, with inherited modal contexts intact. -/
 theorem carrier_observation_eq {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a b : CompareTy} (ha : Carrier Δ a) (hb : Carrier Δ b) (h : AlgebraSubtype Δ a b) :
    (observe Δ a none).positive = (observe Δ b none).positive := by
  have ho := algebra_sound hΔ h
  apply Set.Subset.antisymm ho.1
  simpa only [carrier_balanced ha none, carrier_balanced hb none] using ho.2

end
end ModalityInference.ComparisonPartialStructuredCapsule
