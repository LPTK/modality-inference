import ModalityInference.ComparisonSignedCanonical
import ModalityInference.Proofs.ComparisonSignedRelations
import ModalityInference.Proofs.ComparisonSignedGraph

/-! Exact semantics of symbolic signed-graph canonical assignment. The compiled
formulas retain one shared parameter valuation while eliminating tuple lanes;
the successor-set order is compiled by a coordinate recursion. -/
namespace ModalityInference.ComparisonSignedCanonical
open ComparisonPropagation ComparisonSignedRelations

/-- Complement one distinguished bit, keeping every other coordinate fixed. -/
def toggle (sign : Nat) (a : Nat → Bool) (i : Nat) : Bool :=
  if i=sign then !a i else a i

@[simp] theorem toggle_toggle (sign : Nat) (a : Nat → Bool) :
    toggle sign (toggle sign a)=a := by
  funext i
  by_cases h : i=sign <;> simp [toggle,h]

private theorem map_correct (f : Literal → Literal) (cs : CNF) (left right : Nat → Bool)
    (hf : ∀l,left (f l).1=(f l).2 ↔ right l.1=l.2) :
    CNFHolds left (cs.map (fun c => c.map f)) ↔ CNFHolds right cs := by
  constructor
  · intro h c hc
    obtain ⟨v,b,hv,he⟩ := h _ (List.mem_map.mpr ⟨c,hc,rfl⟩)
    obtain ⟨⟨w,p⟩,hw,hf'⟩ := List.mem_map.mp hv
    exact ⟨w,p,hw,(hf (w,p)).mp (by simpa only [hf'] using he)⟩
  · intro h c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    obtain ⟨v,b,hv,he⟩ := h d hd
    exact ⟨(f (v,b)).1,(f (v,b)).2,List.mem_map.mpr ⟨(v,b),hv,rfl⟩,
      (hf (v,b)).mpr he⟩

theorem flip_input_correct (p a b : Nat → Bool) (sign : Nat) (cs : CNF) :
    Holds p (flip 0 sign cs) a b ↔ Holds p cs (toggle sign a) b := by
  apply map_correct
  rintro ⟨v,q⟩
  by_cases h0 : v%3=0
  · by_cases hs : v/3=sign
    · simp only [flipLiteral,h0,hs,and_self,if_true,value,toggle]
      cases a (v/3) <;> cases q <;> simp
    · simp [flipLiteral,value,toggle,h0,hs]
  · simp [flipLiteral,value,h0]

theorem flip_output_correct (p a b : Nat → Bool) (sign : Nat) (cs : CNF) :
    Holds p (flip 1 sign cs) a b ↔ Holds p cs a (toggle sign b) := by
  apply map_correct
  rintro ⟨v,q⟩
  by_cases h0 : v%3=0
  · simp [flipLiteral,value,h0]
  · by_cases h1 : v%3=1
    · by_cases hs : v/3=sign
      · simp only [flipLiteral,h1,hs,and_self,if_true,value,toggle]
        cases b (v/3) <;> cases q <;> simp
      · simp [flipLiteral,value,toggle,h1,hs]
    · simp [flipLiteral,value,h0,h1]

theorem plug_correct (p a b : Nat → Bool) (sign : Nat) (left right : Bool) (cs : CNF) :
    Holds p (plug sign left right cs) a b ↔
      Holds p cs (if left then toggle sign a else a) (if right then toggle sign a else a) := by
  apply map_correct
  rintro ⟨v,q⟩
  by_cases h0 : v%3=0
  · by_cases hs : v/3=sign
    all_goals cases left <;> cases a (v/3) <;> cases q <;>
      simp [plugLiteral,value,toggle,h0,hs]
  · by_cases h1 : v%3=1
    · by_cases hs : v/3=sign
      all_goals cases right <;> cases a (v/3) <;> cases q <;>
        simp [plugLiteral,value,toggle,h1,hs]
    · simp [plugLiteral,value,h0,h1]

def Earlier (width : Nat) (a b : Nat → Bool) : Prop :=
  ∃i<width,a i=false ∧ b i=true ∧ ∀j<width,a j=true → b j=false → j<i

theorem earlier_succ (n : Nat) (a b : Nat → Bool) :
    Earlier (n+1) a b ↔
      (a n=false ∧ b n=true) ∨ (a n=b n ∧ Earlier n a b) := by
  constructor
  · rintro ⟨i,hi,ha,hb,hmax⟩
    by_cases he : i=n
    · exact .inl ⟨he ▸ ha,he ▸ hb⟩
    · have hin : i<n := by omega
      have hab : ¬(a n=true ∧ b n=false) := by
        rintro ⟨han,hbn⟩
        have := hmax n (by omega) han hbn
        omega
      cases han : a n <;> cases hbn : b n
      · exact .inr ⟨rfl,i,hin,ha,hb,fun j hj => hmax j (by omega)⟩
      · exact .inl ⟨rfl,rfl⟩
      · exact False.elim (hab ⟨han,hbn⟩)
      · exact .inr ⟨rfl,i,hin,ha,hb,fun j hj => hmax j (by omega)⟩
  · rintro (⟨ha,hb⟩ | ⟨he,i,hi,ha,hb,hmax⟩)
    · refine ⟨n,by omega,ha,hb,?_⟩
      intro j hj hja hjb
      by_contra hn
      have hjn : j=n := by omega
      simp [hjn,ha] at hja
    · refine ⟨i,by omega,ha,hb,?_⟩
      intro j hj hja hjb
      have hjn : j<n := by
        by_contra hn
        have hjn : j=n := by omega
        subst j
        simp [hja,hjb] at he
      exact hmax j hjn hja hjb

theorem less_correct (width : Nat) (p a b : Nat → Bool) :
    Holds p (less width) a b ↔ Earlier width a b := by
  induction width with
  | zero => simp [Holds,less,Earlier,CNFHolds,ClauseHolds]
  | succ n ih =>
    rw [earlier_succ]
    change CNFHolds _ (join _ _) ↔ _
    rw [join_correct,cnfHolds_append]
    change (_ ∨ _ ∧ Holds p (less n) a b) ↔ _
    rw [ih]
    cases ha : a n <;> cases hb : b n <;>
      simp [CNFHolds,ClauseHolds,exists_or,ha,hb]


theorem quantify_output_correct (p a b : Nat → Bool) (cs : CNF) :
    Holds p (quantify 1 cs) a b ↔ ∃m,Holds p cs a m := by
  rw [Holds,quantify,project_complete]
  constructor
  · rintro ⟨world,hw,hc⟩
    let m := fun i => world (3*i+1)
    have he : world=value p a m := by
      funext v
      by_cases hv : v%3=1
      · have he : 3*(v/3)+1=v := by omega
        simp only [value,hv,show ¬1=0 by decide,if_false,if_true]
        exact (congrArg world he).symm
      · rw [hw v (by simp [hv])]
        simp [value,hv]
    exact ⟨m,by simpa only [he] using hc⟩
  · rintro ⟨m,hm⟩
    let domain := (CNFPropagation.atoms cs).filter (fun v=>v%3=1)
    let world := fun v => if v∈domain then value p a m v else value p a b v
    refine ⟨world,?_,?_⟩
    · intro v hv
      exact if_neg hv
    · apply (CNFPropagation.holds_congr (σ:=value p a m) (τ:=world) ?_).mp hm
      intro v hv
      by_cases ho : v%3=1
      · have hd : v∈domain := by simp [domain,hv,ho]
        simp only [world,if_pos hd]
      · have hd : v∉domain := by simp [domain,ho]
        simp only [world,if_neg hd]
        simp [value,ho]

theorem quantify_input_correct (p a b : Nat → Bool) (cs : CNF) :
    Holds p (quantify 0 cs) a b ↔ ∃m,Holds p cs m b := by
  rw [Holds,quantify,project_complete]
  constructor
  · rintro ⟨world,hw,hc⟩
    let m := fun i => world (3*i)
    have he : world=value p m b := by
      funext v
      by_cases hv : v%3=0
      · have he : 3*(v/3)=v := by omega
        simp only [value,hv,if_true]
        exact (congrArg world he).symm
      · rw [hw v (by simp [hv])]
        simp [value,hv]
    exact ⟨m,by simpa only [he] using hc⟩
  · rintro ⟨m,hm⟩
    let domain := (CNFPropagation.atoms cs).filter (fun v=>v%3=0)
    let world := fun v => if v∈domain then value p m b v else value p a b v
    refine ⟨world,?_,?_⟩
    · intro v hv
      exact if_neg hv
    · apply (CNFPropagation.holds_congr (σ:=value p m b) (τ:=world) ?_).mp hm
      intro v hv
      by_cases ho : v%3=0
      · have hd : v∈domain := by simp [domain,hv,ho]
        simp only [world,if_pos hd]
      · have hd : v∉domain := by simp [domain,ho]
        simp only [world,if_neg hd]
        simp [value,ho]

def bits {width : Nat} (a : Point width) : Finset (Fin width) :=
  Finset.univ.filter (fun i => a i=true)

@[simp] theorem mem_bits {width} (a : Point width) (i : Fin width) :
    i∈bits a ↔ a i=true := by simp [bits]

theorem bits_injective (width : Nat) : Function.Injective (@bits width) := by
  intro a b he
  funext i
  have h := congrArg (fun s=>i∈s) he
  apply Bool.eq_iff_iff.mpr
  simpa only [mem_bits] using h.to_iff

noncomputable def pointOrder (width : Nat) : LinearOrder (Point width) :=
  LinearOrder.lift' (fun a=>toColex (bits a))
    (toColex.injective.comp (bits_injective width))

theorem less_points (width : Nat) (p : Nat → Bool) (a b : Point width) :
    Holds p (less width) (expand a) (expand b) ↔
      toColex (bits a)<toColex (bits b) := by
  rw [less_correct]
  rw [Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt]
  simp only [mem_bits,Bool.not_eq_true]
  constructor
  · rintro ⟨i,hi,ha,hb,hmax⟩
    refine ⟨⟨i,hi⟩,?_,?_,?_⟩
    · simpa only [expand,hi,↓reduceDIte] using hb
    · simpa only [expand,hi,↓reduceDIte] using ha
    · intro j hja hjb
      exact hmax j j.isLt (by simpa using hja) (by simpa using hjb)
  · rintro ⟨i,hbi,hai,hmax⟩
    refine ⟨i,i.isLt,by simpa using hai,by simpa using hbi,?_⟩
    intro j hj hja hjb
    exact hmax ⟨j,hj⟩ (by simpa only [expand,hj,↓reduceDIte] using hja)
      (by simpa only [expand,hj,↓reduceDIte] using hjb)


theorem difference_correct (p a b : Nat → Bool) (sign : Nat) (reached : CNF) :
    Holds p (difference sign reached) a b ↔
      Holds p reached a b ∧ ¬Holds p reached (toggle sign a) b := by
  change CNFHolds _ (_ ++ _) ↔ _
  rw [cnfHolds_append,negate_correct]
  exact and_congr_right (fun _ => not_congr (flip_input_correct p a b sign reached))

theorem bad_correct (p a b : Nat → Bool) (width sign : Nat) (reached : CNF) :
    Holds p (bad width sign reached) a b ↔
      ∃c,Holds p reached a c ∧ ¬Holds p reached (toggle sign a) c ∧ ¬Earlier width c b := by
  rw [bad,compose_correct]
  apply exists_congr fun c => ?_
  rw [difference_correct]
  change (_ ∧ _) ∧ CNFHolds _ (negate _) ↔ _
  rw [negate_correct]
  change (_ ∧ _) ∧ ¬Holds p (less width) c b ↔ _
  rw [less_correct]
  tauto

theorem assignment_correct (p a b : Nat → Bool) (width sign : Nat) (reached : CNF) :
    Holds p (assignment width sign reached) a b ↔
      ∃c,Holds p reached (toggle sign a) c ∧ ¬Holds p reached a c ∧
        ∀d,Holds p reached a d → ¬Holds p reached (toggle sign a) d → Earlier width d c := by
  rw [assignment,quantify_output_correct]
  apply exists_congr fun c => ?_
  change CNFHolds _ (_ ++ _) ↔ _
  rw [cnfHolds_append,cnfHolds_append,negate_correct,negate_correct]
  change (Holds p (flip 0 sign reached) a c ∧ _) ∧ ¬Holds p (bad width sign reached) a c ↔ _
  rw [flip_input_correct,bad_correct]
  constructor
  · rintro ⟨⟨hc,hn⟩,hb⟩
    refine ⟨hc,hn,?_⟩
    intro d hd hnd
    by_contra h
    exact hb ⟨d,hd,hnd,h⟩
  · rintro ⟨hc,hn,hm⟩
    exact ⟨⟨hc,hn⟩,fun ⟨d,hd,hnd,he⟩ => he (hm d hd hnd)⟩

theorem consistent_correct (p a b : Nat → Bool) (sign : Nat) (reached : CNF) :
    Holds p (consistent sign reached) a b ↔
      ∀c,¬(Holds p reached c (toggle sign c) ∧ Holds p reached (toggle sign c) c) := by
  change CNFHolds _ (negate _) ↔ _
  rw [negate_correct]
  change ¬Holds p (quantify 0 _) a b ↔ _
  rw [quantify_input_correct]
  simp only [not_exists]
  apply forall_congr' fun c => not_congr ?_
  change CNFHolds _ (_ ++ _) ↔ _
  rw [cnfHolds_append]
  change (Holds p (plug sign false true reached) c b ∧
    Holds p (plug sign true false reached) c b) ↔ _
  simp only [plug_correct,Bool.false_eq_true,if_false,if_true]

/-- Complement is the distinguished sign coordinate of the finite vertex. -/
def complement {width : Nat} (sign : Fin width) (a : Point width) : Point width :=
  fun i => if i=sign then !a i else a i

@[simp] theorem complement_involutive {width : Nat} (sign : Fin width) :
    Function.Involutive (complement sign) := by
  intro a
  funext i
  by_cases h : i=sign <;> simp [complement,h]

@[simp] theorem restrict_toggle {width : Nat} (sign : Fin width) (a : Nat → Bool) :
    restrict width (toggle sign a)=complement sign (restrict width a) := by
  funext i
  simp [restrict,toggle,complement,Fin.ext_iff]

@[simp] theorem restrict_expand {width : Nat} (a : Point width) :
    restrict width (expand a)=a := by
  funext i
  simp [restrict]

theorem earlier_restrict (width : Nat) (a b : Nat → Bool) :
    Earlier width a b ↔
      toColex (bits (restrict width a))<toColex (bits (restrict width b)) := by
  rw [←less_points width (fun _=>false),less_correct]
  unfold Earlier
  apply exists_congr fun i => and_congr_right fun hi => ?_
  simp only [expand,hi,↓reduceDIte,restrict]
  apply and_congr_right fun _ => and_congr_right fun _ => ?_
  apply forall_congr' fun j => imp_congr_right fun hj => ?_
  simp only [hj,↓reduceDIte]

/-- The concrete relational formula is exactly successor-set canonical choice. -/
theorem assignment_canonical {width : Nat} (sign : Fin width)
    (g : ComparisonSignedGraph.Graph (Point width))
    (hc : ∀a,g.complement a=complement sign a)
    (p : Nat → Bool) (reached : CNF)
    (hr : ∀a b,Holds p reached a b ↔ g.Reaches (restrict width a) (restrict width b))
    (a b : Nat → Bool) :
    Holds p (assignment width sign reached) a b ↔
      @ComparisonSignedGraph.Graph.canonical _ inferInstance (pointOrder width) g
        (restrict width a)=true := by
  rw [assignment_correct]
  rw [@ComparisonSignedGraph.Graph.canonical_iff _ inferInstance (pointOrder width)]
  simp only [hr,restrict_toggle,←hc,earlier_restrict]
  constructor
  · rintro ⟨c,hc₁,hc₂,hm⟩
    refine ⟨restrict width c,hc₁,hc₂,?_⟩
    intro d hd₁ hd₂
    have hd := hm (expand d) (by simpa using hd₁) (by simpa using hd₂)
    simpa only [restrict_expand] using hd
  · rintro ⟨c,hc₁,hc₂,hm⟩
    refine ⟨expand c,by simpa using hc₁,by simpa using hc₂,?_⟩
    intro d hd₁ hd₂
    have hd := hm (restrict width d) hd₁ hd₂
    simpa only [restrict_expand] using hd

/-- The residual formula expresses the exact obstruction to a common model. -/
theorem consistent_graph {width : Nat} (sign : Fin width)
    (g : ComparisonSignedGraph.Graph (Point width))
    (hc : ∀a,g.complement a=complement sign a)
    (p : Nat → Bool) (reached : CNF)
    (hr : ∀a b,Holds p reached a b ↔ g.Reaches (restrict width a) (restrict width b))
    (a b : Nat → Bool) :
    Holds p (consistent sign reached) a b ↔ g.Consistent := by
  rw [consistent_correct]
  simp only [hr,restrict_toggle,←hc]
  constructor
  · intro h c
    simpa only [restrict_expand] using h (expand c)
  · intro h c
    exact h (restrict width c)


/-- Any Boolean evaluation of the concrete formula is the graph's common model. -/
theorem assignment_model {width : Nat} (sign : Fin width)
    (g : ComparisonSignedGraph.Graph (Point width))
    (hc : ∀a,g.complement a=complement sign a)
    (p : Nat → Bool) (reached : CNF)
    (hr : ∀a b,Holds p reached a b ↔ g.Reaches (restrict width a) (restrict width b))
    {value : Point width → Bool}
    (hv : ∀a,value a=true ↔ Holds p (assignment width sign reached) (expand a) (fun _=>false))
    (h : Holds p (consistent sign reached) (fun _=>false) (fun _=>false)) :
    g.Model value := by
  have he : value=@ComparisonSignedGraph.Graph.canonical _ inferInstance (pointOrder width) g := by
    funext a
    apply Bool.eq_iff_iff.mpr
    simpa only [restrict_expand] using (hv a).trans
      (assignment_canonical sign g hc p reached hr (expand a) (fun _=>false))
  rw [he]
  exact @ComparisonSignedGraph.Graph.canonical_model _ inferInstance (pointOrder width) g
    ((consistent_graph sign g hc p reached hr _ _).mp h)

theorem consistent_iff_model {width : Nat} (sign : Fin width)
    (g : ComparisonSignedGraph.Graph (Point width))
    (hc : ∀a,g.complement a=complement sign a)
    (p : Nat → Bool) (reached : CNF)
    (hr : ∀a b,Holds p reached a b ↔ g.Reaches (restrict width a) (restrict width b))
    (a b : Nat → Bool) :
    Holds p (consistent sign reached) a b ↔ ∃value,g.Model value := by
  rw [consistent_graph sign g hc p reached hr]
  exact (@ComparisonSignedGraph.Graph.model_iff _ inferInstance (pointOrder width) g).symm

/-- The concrete relation determines the edge relation; contraposition is the
signed-implication invariant supplied by its compiler. -/
def graph {width : Nat} (sign : Fin width) (p : Nat → Bool) (edges : CNF)
    (h : ∀{a b : Point width},relation width p edges a b →
      relation width p edges (complement sign b) (complement sign a)) :
    ComparisonSignedGraph.Graph (Point width) where
  complement := complement sign
  involutive := complement_involutive sign
  edge := relation width p edges
  contrapose := h

theorem closure_assignment_model {width : Nat} (sign : Fin width) {edges : CNF}
    (he : Depends width edges) (p : Nat → Bool)
    (hc : ∀{a b : Point width},relation width p edges a b →
      relation width p edges (complement sign b) (complement sign a))
    {value : Point width → Bool}
    (hv : ∀a,value a=true ↔
      Holds p (assignment width sign (closure width edges)) (expand a) (fun _=>false))
    (h : Holds p (consistent sign (closure width edges)) (fun _=>false) (fun _=>false)) :
    (graph sign p edges hc).Model value :=
  assignment_model sign (graph sign p edges hc) (fun _=>rfl) p _ (closure_correct he p) hv h

theorem closure_consistent_iff {width : Nat} (sign : Fin width) {edges : CNF}
    (he : Depends width edges) (p : Nat → Bool)
    (hc : ∀{a b : Point width},relation width p edges a b →
      relation width p edges (complement sign b) (complement sign a))
    (a b : Nat → Bool) :
    Holds p (consistent sign (closure width edges)) a b ↔
      ∃value,(graph sign p edges hc).Model value :=
  consistent_iff_model sign (graph sign p edges hc) (fun _=>rfl) p _ (closure_correct he p) a b

end ModalityInference.ComparisonSignedCanonical
