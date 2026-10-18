import ModalityInference.ComparisonSignedRelations
import ModalityInference.Proofs.ComparisonPropagation
import Mathlib.Logic.Relation

namespace ModalityInference.ComparisonSignedRelations

open ComparisonPropagation

def value (parameters input output : Nat → Bool) (v : Nat) : Bool :=
  if v%3=0 then input (v/3) else if v%3=1 then output (v/3) else parameters (v/3)

def joinedValue (parameters input middle output : Nat → Bool) (v : Nat) : Bool :=
  if v%4=0 then input (v/4) else if v%4=1 then middle (v/4)
  else if v%4=2 then output (v/4) else parameters (v/4)

def Holds (parameters : Nat → Bool) (relation : CNF) (input output : Nat → Bool) : Prop :=
  CNFHolds (value parameters input output) relation

@[simp] theorem joined_first (p a m b : Nat → Bool) (v : Nat) :
    joinedValue p a m b (first v)=value p a m v := by
  have hv : v%3<3 := Nat.mod_lt _ (by omega)
  rcases (by omega : v%3=0 ∨ v%3=1 ∨ v%3=2) with h|h|h
  all_goals simp [first,joinedValue,value,h] <;> congr 1 <;> omega

@[simp] theorem joined_second (p a m b : Nat → Bool) (v : Nat) :
    joinedValue p a m b (second v)=value p m b v := by
  have hv : v%3<3 := Nat.mod_lt _ (by omega)
  rcases (by omega : v%3=0 ∨ v%3=1 ∨ v%3=2) with h|h|h
  all_goals simp [second,joinedValue,value,h]
  all_goals congr 1
  all_goals omega

theorem joined_retained (p a m b : Nat → Bool) {v : Nat} (hv : v%4≠1) :
    joinedValue p a m b v=value p a b (retained v) := by
  have hr : v%4<4 := Nat.mod_lt _ (by omega)
  rcases (by omega : v%4=0 ∨ v%4=2 ∨ v%4=3) with h|h|h
  all_goals simp [retained,joinedValue,value,h] <;> congr 1 <;> omega

theorem joined_middle (p a m b : Nat → Bool) (i : Nat) :
    joinedValue p a m b (4*i+1)=m i := by
  simp [joinedValue]
  congr 1
  omega

theorem combined_correct (p a m b : Nat → Bool) (left right : CNF) :
    CNFHolds (joinedValue p a m b) (rename first left ++ rename second right) ↔
      Holds p left a m ∧ Holds p right m b := by
  simp only [cnfHolds_append,rename_correct,Function.comp_def,joined_first,joined_second,Holds]

/-- Composition quantifies the intermediate tuple while retaining exactly the
same parameter valuation in both relations. -/
theorem compose_correct (p a b : Nat → Bool) (left right : CNF) :
    Holds p (compose left right) a b ↔ ∃m,Holds p left a m ∧ Holds p right m b := by
  rw [Holds,compose,rename_correct,project_complete]
  constructor
  · rintro ⟨world,hw,hc⟩
    let m := fun i => world (4*i+1)
    have he : world=joinedValue p a m b := by
      funext v
      by_cases hv : v%4=1
      · have he : 4*(v/4)+1=v := by omega
        simp only [joinedValue,hv,show ¬1=0 by decide,if_false,if_true]
        exact (congrArg world he).symm
      · rw [joined_retained p a m b hv]
        exact hw v (by simp [intermediate,hv])
    exact ⟨m,(combined_correct p a m b left right).mp (by simpa only [he] using hc)⟩
  · rintro ⟨m,hl,hr⟩
    let combined := rename first left ++ rename second right
    let world := fun v => if v∈intermediate combined then joinedValue p a m b v
      else value p a b (retained v)
    refine ⟨world,?_,?_⟩
    · intro v hv
      simp only [world,combined,if_neg hv,Function.comp_def]
    · apply (CNFPropagation.holds_congr (σ := joinedValue p a m b) (τ := world) ?_).mp
        ((combined_correct p a m b left right).mpr ⟨hl,hr⟩)
      intro v hv
      by_cases hm : v%4=1
      · have hm' : v∈intermediate combined := by simp [intermediate,combined,hv,hm]
        simp only [world,if_pos hm']
      · have hm' : v∉intermediate combined := by simp [intermediate,hm]
        simp only [world,if_neg hm']
        exact joined_retained p a m b hm

@[simp] theorem value_input (p a b : Nat → Bool) (i : Nat) :
    value p a b (3*i)=a i := by simp [value]

@[simp] theorem value_output (p a b : Nat → Bool) (i : Nat) :
    value p a b (3*i+1)=b i := by
  simp [value]
  congr 1
  omega

def Same (width : Nat) (a b : Nat → Bool) : Prop := ∀i<width,a i=b i

def Depends (width : Nat) (relation : CNF) : Prop :=
  ∀p a b a' b',Same width a a' → Same width b b' →
    (Holds p relation a b ↔ Holds p relation a' b')

theorem depends_of_atoms {width relation}
    (hs : ∀v∈CNFPropagation.atoms relation,v%3≠2 → v/3<width) : Depends width relation := by
  intro p a b a' b' ha hb
  apply CNFPropagation.holds_congr
  intro v hv
  dsimp [value]
  split
  next h => exact ha _ (hs v hv (by omega))
  next =>
    split
    next h => exact hb _ (hs v hv (by omega))
    next => rfl

theorem diagonal_correct (width : Nat) (p a b : Nat → Bool) :
    Holds p (diagonal width) a b ↔ Same width a b := by
  simp only [Holds,diagonal,CNFHolds,List.forall_mem_flatMap,List.mem_range,
    List.forall_mem_cons,Same]
  apply forall_congr' fun i => imp_congr_right fun _ => ?_
  cases ha : a i <;> cases hb : b i <;> simp [ClauseHolds,exists_or,ha,hb]

theorem diagonal_depends (width : Nat) : Depends width (diagonal width) := by
  intro p a b a' b' ha hb
  rw [diagonal_correct,diagonal_correct]
  apply forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [ha i hi,hb i hi]

theorem compose_depends {width left right}
    (hl : Depends width left) (hr : Depends width right) : Depends width (compose left right) := by
  intro p a b a' b' ha hb
  rw [compose_correct,compose_correct]
  apply exists_congr fun m => and_congr (hl p a m a' m ha (fun _ _ => rfl))
    (hr p m b m b' (fun _ _ => rfl) hb)

theorem step_correct (p a b : Nat → Bool) (edges reached : CNF) :
    Holds p (step edges reached) a b ↔
      Holds p reached a b ∨ ∃m,Holds p reached a m ∧ Holds p edges m b := by
  change CNFHolds _ (join _ _) ↔ _
  rw [join_correct]
  exact or_congr_right (compose_correct p a b reached edges)

theorem step_depends {width edges reached}
    (he : Depends width edges) (hr : Depends width reached) : Depends width (step edges reached) := by
  intro p a b a' b' ha hb
  change CNFHolds _ (join _ _) ↔ CNFHolds _ (join _ _)
  rw [join_correct,join_correct]
  exact or_congr (hr p a b a' b' ha hb) (compose_depends hr he p a b a' b' ha hb)

theorem iterate_depends {width edges reached}
    (he : Depends width edges) (hr : Depends width reached) (n : Nat) :
    Depends width (iterate edges n reached) := by
  induction n generalizing reached with
  | zero => exact hr
  | succ n ih => exact ih (step_depends he hr)

theorem iterate_succ (edges reached : CNF) (n : Nat) :
    iterate edges (n+1) reached=step edges (iterate edges n reached) := by
  induction n generalizing reached with
  | zero => rfl
  | succ n ih => exact ih (step edges reached)

theorem iterate_fixed {edges reached : CNF} (h : step edges reached=reached) (n : Nat) :
    iterate edges n reached=reached := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [iterate,h] using ih

theorem saturate_eq_iterate (edges reached : CNF) (n : Nat) :
    saturate edges n reached=iterate edges n reached := by
  induction n generalizing reached with
  | zero => rfl
  | succ n ih =>
    by_cases h : step edges reached=reached
    · simp only [saturate,if_pos h,iterate_fixed h]
    · simpa only [saturate,if_neg h,iterate] using ih (step edges reached)

def reach {α : Type*} (r : α → α → Prop) : Nat → α → α → Prop
  | 0,a,b => a=b
  | n+1,a,b => reach r n a b ∨ ∃m,reach r n a m ∧ r m b

theorem reach_refl {α} (r : α → α → Prop) (n : Nat) (a : α) : reach r n a a := by
  induction n with
  | zero => rfl
  | succ n ih => exact .inl ih

theorem reach_sound {α} {r : α → α → Prop} {n a b} (h : reach r n a b) :
    Relation.ReflTransGen r a b := by
  induction n generalizing a b with
  | zero => cases h; exact .refl
  | succ n ih =>
    rcases h with h|⟨m,hm,hr⟩
    · exact ih h
    · exact (ih hm).tail hr

theorem reach_fixed {α} {r : α → α → Prop} {n : Nat}
    (h : reach r n=reach r (n+1)) (k : Nat) : reach r (n+k)=reach r n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext a b
    change (reach r (n+k) a b ∨ ∃m,reach r (n+k) a m ∧ r m b)=reach r n a b
    rw [ih]
    exact congrFun (congrFun h.symm a) b

private theorem finite_chain_stable {α : Type*} [Fintype α] (s : Nat → Finset α)
    (hsub : ∀n,s n⊆s (n+1))
    (hfixed : ∀n k,s n=s (n+1) → s n=s (n+k)) :
    s (Fintype.card α)=s (Fintype.card α+1) := by
  by_contra hn
  have hne : ∀n≤Fintype.card α,s n≠s (n+1) := by
    intro n hle he
    have h₁ := hfixed n (Fintype.card α-n) he
    have h₂ := hfixed n (Fintype.card α+1-n) he
    rw [Nat.add_sub_of_le hle] at h₁
    rw [Nat.add_sub_of_le (by omega : n≤Fintype.card α+1)] at h₂
    exact hn (h₁.symm.trans h₂)
  have hcard : ∀n≤Fintype.card α+1,n≤(s n).card := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hle
      have hi := ih (by omega)
      have hg := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨hsub n,hne n (by omega)⟩)
      omega
  have hg := hcard (Fintype.card α+1) (by omega)
  have hu := (s (Fintype.card α+1)).card_le_univ
  omega

theorem reach_stable {α : Type*} [Fintype α] (r : α → α → Prop) :
    reach r (Fintype.card (α×α))=reach r (Fintype.card (α×α)+1) := by
  classical
  let states := fun n => Finset.univ.filter (fun ab : α×α => reach r n ab.1 ab.2)
  have he {n m} : states n=states m ↔ reach r n=reach r m := by
    constructor
    · intro h
      funext a b
      apply propext
      have hh := congrArg (fun s => (a,b)∈s) h
      simpa only [states,Finset.mem_filter,Finset.mem_univ,true_and] using hh.to_iff
    · intro h
      simp only [states,h]
  apply he.mp
  apply finite_chain_stable states
  · intro n ab hab
    simp only [states,Finset.mem_filter,Finset.mem_univ,true_and] at hab ⊢
    exact .inl hab
  · intro n k hn
    exact he.mpr (reach_fixed (he.mp hn) k).symm

theorem reach_complete {α : Type*} [Fintype α] {r : α → α → Prop} {a b}
    (h : Relation.ReflTransGen r a b) : reach r (Fintype.card (α×α)) a b := by
  induction h with
  | refl => exact reach_refl r _ _
  | @tail b c _ h ih =>
    rw [reach_stable r]
    exact .inr ⟨b,ih,h⟩

theorem reach_iff {α : Type*} [Fintype α] (r : α → α → Prop) (a b : α) :
    reach r (Fintype.card (α×α)) a b ↔ Relation.ReflTransGen r a b :=
  ⟨reach_sound,reach_complete⟩

abbrev Point (width : Nat) := Fin width → Bool

def expand {width} (a : Point width) (i : Nat) : Bool :=
  if h : i<width then a ⟨i,h⟩ else false

def restrict (width : Nat) (a : Nat → Bool) : Point width := fun i => a i

@[simp] theorem expand_fin {width} (a : Point width) (i : Fin width) : expand a i=a i := by
  simp [expand,i.isLt]

theorem expand_restrict (width : Nat) (a : Nat → Bool) : Same width a (expand (restrict width a)) := by
  intro i hi
  simp [expand,restrict,hi]

def relation (width : Nat) (p : Nat → Bool) (r : CNF) (a b : Point width) : Prop :=
  Holds p r (expand a) (expand b)

theorem diagonal_finite (width : Nat) (p : Nat → Bool) (a b : Point width) :
    Holds p (diagonal width) (expand a) (expand b) ↔ a=b := by
  rw [diagonal_correct]
  constructor
  · intro h
    funext i
    simpa only [expand_fin] using h i i.isLt
  · intro h
    subst b
    exact fun _ _ => rfl

theorem iterate_finite {width : Nat} {r : CNF} (hr : Depends width r)
    (p : Nat → Bool) (n : Nat) (a b : Point width) :
    Holds p (iterate r n (diagonal width)) (expand a) (expand b) ↔
      reach (relation width p r) n a b := by
  induction n generalizing a b with
  | zero => exact diagonal_finite width p a b
  | succ n ih =>
    rw [iterate_succ,step_correct]
    change _ ↔ (reach _ n a b ∨ ∃m,reach _ n a m ∧ relation width p r m b)
    apply or_congr (ih a b)
    constructor
    · rintro ⟨m,hm,he⟩
      refine ⟨restrict width m,?_,?_⟩
      · apply (ih a _).mp
        exact (iterate_depends hr (diagonal_depends width) n p (expand a) m
          (expand a) (expand (restrict width m)) (fun _ _ => rfl) (expand_restrict width m)).mp hm
      · exact (hr p m (expand b) (expand (restrict width m)) (expand b)
          (expand_restrict width m) (fun _ _ => rfl)).mp he
    · rintro ⟨m,hm,he⟩
      exact ⟨expand m,(ih a m).mpr hm,he⟩

/-- The concrete symbolic closure computes full reachability at every fixed
parameter valuation. The implementation never constructs Boolean points. -/
theorem closure_correct {width : Nat} {r : CNF} (hr : Depends width r)
    (p a b : Nat → Bool) :
    Holds p (closure width r) a b ↔
      Relation.ReflTransGen (relation width p r) (restrict width a) (restrict width b) := by
  rw [closure,saturate_eq_iterate]
  rw [iterate_depends hr (diagonal_depends width) _ p a b
    (expand (restrict width a)) (expand (restrict width b))
    (expand_restrict width a) (expand_restrict width b)]
  rw [iterate_finite hr]
  have hcard : Fintype.card (Point width×Point width)=2^(2*width) := by
    simp [Point,Nat.two_mul,Nat.pow_add]
  rw [←hcard,reach_iff]

theorem closure_correct_of_atoms {width : Nat} {r : CNF}
    (hs : ∀v∈CNFPropagation.atoms r,v%3≠2 → v/3<width) (p a b : Nat → Bool) :
    Holds p (closure width r) a b ↔
      Relation.ReflTransGen (relation width p r) (restrict width a) (restrict width b) :=
  closure_correct (depends_of_atoms hs) p a b

end ModalityInference.ComparisonSignedRelations
