import ModalityInference.ComparisonSignedPolynomials
import ModalityInference.Proofs.ComparisonSignedRelations
import ModalityInference.Proofs.ComparisonSignedCanonical

namespace ModalityInference.ComparisonSignedPolynomials
open ComparisonPropagation ComparisonSignedRelations

def substValue (s : Nat → Sum Bool Nat) (v : Nat → Bool) (i : Nat) : Bool :=
  match s i with
  | .inl b => b
  | .inr n => v n

theorem literal_correct (s : Nat → Sum Bool Nat) (v : Nat → Bool) (l : Literal) :
    CNFHolds v (literal s l) ↔ substValue s v l.1=l.2 := by
  cases h : s l.1 <;> simp [literal,substValue,h,CNFHolds,ClauseHolds]

theorem clause_specialize (s : Nat → Sum Bool Nat) (v : Nat → Bool) (c : Clause) :
    CNFHolds v (c.foldr (fun l rest => join (literal s l) rest) [[]]) ↔
      ClauseHolds (substValue s v) c := by
  induction c with
  | nil => simp [CNFHolds,ClauseHolds]
  | cons l c ih =>
      rcases l with ⟨i,b⟩
      simp [join_correct,literal_correct,ih,ClauseHolds,exists_or]

theorem specialize_correct (s : Nat → Sum Bool Nat) (v : Nat → Bool) (cs : CNF) :
    CNFHolds v (specialize s cs) ↔ CNFHolds (substValue s v) cs := by
  induction cs with
  | nil => simp [specialize,CNFHolds]
  | cons c cs ih =>
      change CNFHolds v (c.foldr (fun l rest => join (literal s l) rest) [[]] ++
        specialize s cs) ↔ CNFHolds (substValue s v) (c::cs)
      rw [cnfHolds_append,clause_specialize,ih]
      simp [CNFHolds]


def tuple (key : List Bool) (size : Nat) (sign : Bool) (v : Nat → Bool) (i : Nat) : Bool :=
  if i < key.length+1 then (sign::key)[i]?.getD false
  else if i < key.length+1+size then v (i-(key.length+1)) else false

@[simp] theorem tuple_zero (key : List Bool) (size : Nat) (sign : Bool) (v : Nat → Bool) :
    tuple key size sign v 0=sign := by
  simp [tuple]

@[simp] theorem tuple_basis (key : List Bool) {size i : Nat} (hi : i<size)
    (sign : Bool) (v : Nat → Bool) : tuple key size sign v (key.length+1+i)=v i := by
  simp [tuple,show ¬key.length+1+i<key.length+1 by omega,show key.length+1+i<key.length+1+size by omega]

theorem imageSubst_value (p : Nat → Bool) (key : List Bool) (size : Nat) (v : Nat → Bool) :
    substValue (imageSubst p key size) v=value p (tuple key size true v) (fun _=>false) := by
  funext i
  have hi : i%3<3 := Nat.mod_lt _ (by omega)
  rcases (by omega : i%3=0 ∨ i%3=1 ∨ i%3=2) with h|h|h
  all_goals
    by_cases hk : i/3<key.length+1
    all_goals
      by_cases hs : i/3<key.length+1+size
      all_goals simp [substValue,imageSubst,value,tuple,h,hk,hs]

theorem endpoints_tuple (p : Nat → Bool) (key : List Bool) (size : Nat)
    (left right : Bool) (a b : Nat → Bool) :
    Holds p (endpoints key left right) (tuple key size left a) (tuple key size right b) := by
  simp only [Holds,endpoints,cnfHolds_append]
  constructor
  all_goals
    intro c hc
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    have hi := List.mem_range.mp hi
    simp [ClauseHolds,value,tuple,hi,show (3*i+1)/3=i by omega]

theorem increasing_tuple (p : Nat → Bool) (key : List Bool) (size : Nat)
    (a b : Nat → Bool) (hle : ∀i<size,a i=true → b i=true) :
    Holds p (increasing key size) (tuple key size true a) (tuple key size true b) := by
  change CNFHolds _ (_ ++ _)
  rw [cnfHolds_append]
  refine ⟨endpoints_tuple p key size true true a b,?_⟩
  intro c hc
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
  have hi := List.mem_range.mp hi
  cases ha : a i
  · exact ⟨3*(key.length+1+i),false,by simp,by simp [tuple_basis key hi,ha]⟩
  · exact ⟨3*(key.length+1+i)+1,true,by simp,by simp [tuple_basis key hi,hle i hi ha]⟩

theorem boundary_tuple (p : Nat → Bool) (key : List Bool) (size : Nat) (b : Bool) :
    Holds p (boundary key size b) (tuple key size (!b) (fun _=>b))
      (tuple key size b (fun _=>b)) := by
  change CNFHolds _ (_ ++ _)
  rw [cnfHolds_append]
  refine ⟨endpoints_tuple p key size (!b) b (fun _=>b) (fun _=>b),?_⟩
  intro c hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi := List.mem_range.mp hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl
  · exact ⟨3*(key.length+1+i),b,by simp,by simp [tuple_basis key hi]⟩
  · exact ⟨3*(key.length+1+i)+1,b,by simp,by simp [tuple_basis key hi]⟩

theorem toggle_tuple (key : List Bool) (size : Nat) (sign : Bool) (v : Nat → Bool) :
    ComparisonSignedCanonical.toggle 0 (tuple key size sign v)=tuple key size (!sign) v := by
  funext i
  cases i <;> simp [ComparisonSignedCanonical.toggle,tuple]

theorem model_monotone {width : Nat} (g : ComparisonSignedGraph.Graph (Point width))
    (p : Nat → Bool) (key : List Bool) (size : Nat)
    (he : ∀a b,Holds p (edges key size) a b → g.edge (restrict width a) (restrict width b))
    {model : Point width → Bool} (hm : g.Model model)
    (a b : Nat → Bool) (hle : ∀i<size,a i=true → b i=true) :
    model (restrict width (tuple key size true a)) ≤
      model (restrict width (tuple key size true b)) := by
  apply hm.edge
  apply he
  exact (join_correct _ _ _).mpr (.inl (increasing_tuple p key size a b hle))

theorem model_boundary {width : Nat} (hw : 0<width)
    (g : ComparisonSignedGraph.Graph (Point width))
    (hc : ∀a,g.complement a=ComparisonSignedCanonical.complement ⟨0,hw⟩ a)
    (p : Nat → Bool) (key : List Bool) (size : Nat)
    (he : ∀a b,Holds p (edges key size) a b → g.edge (restrict width a) (restrict width b))
    {model : Point width → Bool} (hm : g.Model model) (b : Bool) :
    model (restrict width (tuple key size true (fun _=>b)))=b := by
  have hh : Holds p (edges key size)
      (tuple key size (!b) (fun _=>b)) (tuple key size b (fun _=>b)) := by
    apply (join_correct _ _ _).mpr
    right
    apply (join_correct _ _ _).mpr
    right
    apply (join_correct _ _ _).mpr
    cases b
    · exact .inl (boundary_tuple p key size false)
    · exact .inr (boundary_tuple p key size true)
  have hle := hm.edge (he _ _ hh)
  have hn := hm.complement (restrict width (tuple key size true (fun _=>b)))
  rw [hc,←ComparisonSignedCanonical.restrict_toggle] at hn
  change model (restrict width (ComparisonSignedCanonical.toggle 0
    (tuple key size true (fun _=>b))))= _ at hn
  rw [toggle_tuple] at hn
  cases b <;> cases hv : model (restrict width (tuple key size true (fun _=>_))) <;> simp_all [Bool.le_iff_imp]

theorem polynomial_model {width : Nat} (g : ComparisonSignedGraph.Graph (Point width))
    (p : Nat → Bool) (key : List Bool) (size : Nat) (formula : CNF)
    (he : ∀a b,Holds p (edges key size) a b → g.edge (restrict width a) (restrict width b))
    {model : Point width → Bool} (hm : g.Model model)
    (hf : ∀a,Holds p formula a (fun _=>false) ↔ model (restrict width a)=true)
    (v : Nat → Bool) :
    CNFHolds v (polynomial p key size formula) ↔
      model (restrict width (tuple key size true v))=true := by
  rw [polynomial,upward_correct]
  simp only [specialize_correct,imageSubst_value]
  change (∃a,Holds p formula (tuple key size true a) (fun _=>false) ∧
    ∀i∈List.range size,a i=true → v i=true) ↔ _
  simp only [hf,List.mem_range]
  constructor
  · rintro ⟨a,ha,hle⟩
    exact Bool.le_iff_imp.mp (model_monotone g p key size he hm a v hle) ha
  · intro hv
    exact ⟨v,hv,fun _ _ h=>h⟩

theorem reconstruct_model {width : Nat} (hw : 0<width)
    (g : ComparisonSignedGraph.Graph (Point width))
    (hc : ∀a,g.complement a=ComparisonSignedCanonical.complement ⟨0,hw⟩ a)
    (p : Nat → Bool) (key : List Bool) (basis : List CompareTy) (formula : CNF)
    (he : ∀a b,Holds p (edges key basis.length) a b → g.edge (restrict width a) (restrict width b))
    {model : Point width → Bool} (hm : g.Model model)
    (hf : ∀a,Holds p formula a (fun _=>false) ↔ model (restrict width a)=true) :
    ∃t,reconstruct p key basis formula=some t ∧
      ∀(value : CompareTy → Bool)
        (_hj : ∀a b,value (.join a b)=(value a || value b))
        (_hm : ∀a b,value (.meet a b)=(value a && value b)),
        value t=true ↔ model (restrict width (tuple key basis.length true (basisValue basis value)))=true := by
  have hp := polynomial_model g p key basis.length formula he hm hf
  have hone : CNFHolds (fun _=>true) (polynomial p key basis.length formula) :=
    (hp _).mpr (model_boundary hw g hc p key basis.length he hm true)
  have hzero : ¬CNFHolds (fun _=>false) (polynomial p key basis.length formula) := by
    rw [hp,model_boundary hw g hc p key basis.length he hm false]
    simp
  obtain ⟨t,ht⟩ := reify_complete (upward_positive _ _) (upward_supported _ _) hone hzero
  refine ⟨t,ht,?_⟩
  intro value hj hm
  exact (reify_correct ht value hj hm).trans (hp _)

/-- A consistent symbolic graph reconstructs an actual finite type for this
image. Monotonicity and endpoint edges are obligations of the compiled graph. -/
theorem closure_reconstruct {width : Nat} (hw : 0<width) (p : Nat → Bool)
    (key : List Bool) (basis : List CompareTy) {r : CNF}
    (hd : Depends width r)
    (hc : ∀{a b : Point width},relation width p r a b →
      relation width p r (ComparisonSignedCanonical.complement ⟨0,hw⟩ b)
        (ComparisonSignedCanonical.complement ⟨0,hw⟩ a))
    (he : ∀a b,Holds p (edges key basis.length) a b → Holds p r a b)
    (h : Holds p (ComparisonSignedCanonical.consistent 0 (closure width r))
      (fun _=>false) (fun _=>false)) :
    ∃t,reconstruct p key basis (ComparisonSignedCanonical.assignment width 0 (closure width r))=some t ∧
      ∀(value : CompareTy → Bool)
        (_hj : ∀a b,value (.join a b)=(value a || value b))
        (_hm : ∀a b,value (.meet a b)=(value a && value b)),
        value t=true ↔
          Holds p (ComparisonSignedCanonical.assignment width 0 (closure width r))
            (tuple key basis.length true (basisValue basis value)) (fun _=>false) := by
  let g := ComparisonSignedCanonical.graph ⟨0,hw⟩ p r hc
  let model := @ComparisonSignedGraph.Graph.canonical _ inferInstance
    (ComparisonSignedCanonical.pointOrder width) g
  have hcanonical := ComparisonSignedCanonical.assignment_canonical ⟨0,hw⟩ g
    (fun _=>rfl) p (closure width r) (closure_correct hd p)
  have hcons : g.Consistent :=
    (ComparisonSignedCanonical.consistent_graph ⟨0,hw⟩ g (fun _=>rfl) p
      (closure width r) (closure_correct hd p) _ _).mp h
  have hm : g.Model model := @ComparisonSignedGraph.Graph.canonical_model _ inferInstance
    (ComparisonSignedCanonical.pointOrder width) g hcons
  have hedges : ∀a b,Holds p (edges key basis.length) a b →
      g.edge (restrict width a) (restrict width b) := by
    intro a b hab
    exact (hd p a b _ _ (expand_restrict width a) (expand_restrict width b)).mp (he a b hab)
  obtain ⟨t,ht,hvalue⟩ := reconstruct_model hw g (fun _=>rfl) p key basis
    (ComparisonSignedCanonical.assignment width 0 (closure width r)) hedges hm
      (fun a=>hcanonical a (fun _=>false))
  refine ⟨t,ht,?_⟩
  intro value hj hm
  exact (hvalue value hj hm).trans (hcanonical _ _).symm

theorem reconstruct_property {p : Nat → Bool} {key : List Bool}
    {basis : List CompareTy} {formula : CNF} {t : CompareTy}
    (h : reconstruct p key basis formula=some t) (P : CompareTy → Prop)
    (hb : ∀a∈basis,P a) (hj : ∀a b,P a → P b → P (.join a b))
    (hm : ∀a b,P a → P b → P (.meet a b)) : P t :=
  reify_property h P hb hj hm

def Fixed (key : List Bool) (sign : Bool) (a : Nat → Bool) : Prop :=
  ∀i<key.length+1,a i=(sign::key)[i]?.getD false

theorem fixedPrefix_correct (lane : Nat) (key : List Bool) (sign : Bool) (v : Nat → Bool) :
    CNFHolds v (fixedPrefix lane key sign) ↔
      ∀i<key.length+1,v (3*i+lane)=(sign::key)[i]?.getD false := by
  constructor
  · intro h i hi
    simpa [ClauseHolds] using h _ (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)
  · intro h c hc
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    exact ⟨_,_,by simp,h i (List.mem_range.mp hi)⟩

theorem endpoints_correct (p : Nat → Bool) (key : List Bool) (left right : Bool)
    (a b : Nat → Bool) :
    Holds p (endpoints key left right) a b ↔ Fixed key left a ∧ Fixed key right b := by
  simp only [Holds,endpoints,cnfHolds_append,fixedPrefix_correct,value_input,value_output,Fixed,Nat.add_zero]

theorem ordered_clause (v : Nat → Bool) (i j : Nat) :
    ClauseHolds v [(i,false),(j,true)] ↔ v i≤v j := by
  cases hi : v i <;> cases hj : v j <;> simp [ClauseHolds,exists_or,hi,hj,Bool.le_iff_imp]

theorem mapped_holds {α : Type*} (v : Nat → Bool) (xs : List α) (f : α → Clause) :
    CNFHolds v (xs.map f) ↔ ∀x∈xs,ClauseHolds v (f x) := by
  simp [CNFHolds]

theorem increasing_correct (p : Nat → Bool) (key : List Bool) (size : Nat) (a b : Nat → Bool) :
    Holds p (increasing key size) a b ↔ (Fixed key true a ∧ Fixed key true b) ∧
      ∀i<size,a (key.length+1+i)≤b (key.length+1+i) := by
  simp only [Holds,increasing,endpoints,cnfHolds_append,fixedPrefix_correct,mapped_holds,
    List.mem_range,ordered_clause,Nat.add_zero,value_input,value_output,Fixed]

theorem decreasing_correct (p : Nat → Bool) (key : List Bool) (size : Nat) (a b : Nat → Bool) :
    Holds p (decreasing key size) a b ↔ (Fixed key false a ∧ Fixed key false b) ∧
      ∀i<size,b (key.length+1+i)≤a (key.length+1+i) := by
  simp only [Holds,decreasing,endpoints,cnfHolds_append,fixedPrefix_correct,mapped_holds,
    List.mem_range,ordered_clause,Nat.add_zero,value_input,value_output,Fixed]

theorem flatMap_holds {α : Type*} (v : Nat → Bool) (xs : List α) (f : α → CNF) :
    CNFHolds v (xs.flatMap f) ↔ ∀x∈xs,CNFHolds v (f x) := by
  constructor
  · intro h x hx c hc
    exact h c (List.mem_flatMap.mpr ⟨x,hx,hc⟩)
  · intro h c hc
    obtain ⟨x,hx,hc⟩ := List.mem_flatMap.mp hc
    exact h x hx c hc

theorem boundary_correct (p : Nat → Bool) (key : List Bool) (size : Nat)
    (s : Bool) (a b : Nat → Bool) :
    Holds p (boundary key size s) a b ↔ (Fixed key (!s) a ∧ Fixed key s b) ∧
      ∀i<size,a (key.length+1+i)=s ∧ b (key.length+1+i)=s := by
  simp only [Holds,boundary,endpoints,cnfHolds_append,fixedPrefix_correct,flatMap_holds,
    List.mem_range,Nat.add_zero,value_input,value_output,Fixed]
  simp [CNFHolds,ClauseHolds]

theorem Fixed.toggle {key : List Bool} {sign : Bool} {a : Nat → Bool}
    (h : Fixed key sign a) : Fixed key (!sign) (ComparisonSignedCanonical.toggle 0 a) := by
  intro i hi
  cases i with
  | zero => simpa [ComparisonSignedCanonical.toggle] using congrArg Bool.not (h 0 hi)
  | succ i => simpa [ComparisonSignedCanonical.toggle] using h (i+1) hi

@[simp] theorem toggle_basis (key : List Bool) (a : Nat → Bool) (i : Nat) :
    ComparisonSignedCanonical.toggle 0 a (key.length+1+i)=a (key.length+1+i) := by
  simp [ComparisonSignedCanonical.toggle]

theorem edges_correct (p : Nat → Bool) (key : List Bool) (size : Nat) (a b : Nat → Bool) :
    Holds p (edges key size) a b ↔ Holds p (increasing key size) a b ∨
      Holds p (decreasing key size) a b ∨ Holds p (boundary key size false) a b ∨
        Holds p (boundary key size true) a b := by
  simp only [Holds,edges,join_correct]

theorem edges_contrapose (p : Nat → Bool) (key : List Bool) (size : Nat)
    {a b : Nat → Bool} (h : Holds p (edges key size) a b) :
    Holds p (edges key size) (ComparisonSignedCanonical.toggle 0 b)
      (ComparisonSignedCanonical.toggle 0 a) := by
  apply (edges_correct p key size _ _).mpr
  rcases (edges_correct p key size a b).mp h with h|h|h|h
  · obtain ⟨⟨ha,hb⟩,hle⟩ := (increasing_correct p key size a b).mp h
    exact .inr (.inl ((decreasing_correct p key size _ _).mpr
      ⟨⟨hb.toggle,ha.toggle⟩,by simpa only [toggle_basis] using hle⟩))
  · obtain ⟨⟨ha,hb⟩,hle⟩ := (decreasing_correct p key size a b).mp h
    exact .inl ((increasing_correct p key size _ _).mpr
      ⟨⟨hb.toggle,ha.toggle⟩,by simpa only [toggle_basis] using hle⟩)
  · obtain ⟨⟨ha,hb⟩,hle⟩ := (boundary_correct p key size false a b).mp h
    exact .inr (.inr (.inl ((boundary_correct p key size false _ _).mpr
      ⟨⟨hb.toggle,ha.toggle⟩,fun i hi=>by simpa only [toggle_basis] using (hle i hi).symm⟩)))
  · obtain ⟨⟨ha,hb⟩,hle⟩ := (boundary_correct p key size true a b).mp h
    exact .inr (.inr (.inr ((boundary_correct p key size true _ _).mpr
      ⟨⟨hb.toggle,ha.toggle⟩,fun i hi=>by simpa only [toggle_basis] using (hle i hi).symm⟩)))

theorem edges_depends {width : Nat} (key : List Bool) (size : Nat)
    (hw : key.length+1+size≤width) : Depends width (edges key size) := by
  intro p a b a' b' ha hb
  have hfixed (s : Bool) : Fixed key s a ↔ Fixed key s a' := by
    apply forall_congr' fun i=>imp_congr_right fun hi=>?_
    rw [ha i (by omega)]
  have hfixed' (s : Bool) : Fixed key s b ↔ Fixed key s b' := by
    apply forall_congr' fun i=>imp_congr_right fun hi=>?_
    rw [hb i (by omega)]
  have hle : (∀i<size,a (key.length+1+i)≤b (key.length+1+i)) ↔
      ∀i<size,a' (key.length+1+i)≤b' (key.length+1+i) := by
    apply forall_congr' fun i=>imp_congr_right fun hi=>?_
    rw [ha _ (by omega),hb _ (by omega)]
  have hle' : (∀i<size,b (key.length+1+i)≤a (key.length+1+i)) ↔
      ∀i<size,b' (key.length+1+i)≤a' (key.length+1+i) := by
    apply forall_congr' fun i=>imp_congr_right fun hi=>?_
    rw [ha _ (by omega),hb _ (by omega)]
  have hbound (s : Bool) : (∀i<size,a (key.length+1+i)=s ∧ b (key.length+1+i)=s) ↔
      ∀i<size,a' (key.length+1+i)=s ∧ b' (key.length+1+i)=s := by
    apply forall_congr' fun i=>imp_congr_right fun hi=>?_
    rw [ha _ (by omega),hb _ (by omega)]
  simp only [edges_correct,increasing_correct,decreasing_correct,boundary_correct,
    hfixed,hfixed',hle,hle',hbound]

end ModalityInference.ComparisonSignedPolynomials
