import ModalityInference.ComparisonSignedSynthesis
import ModalityInference.Proofs.ComparisonSignedPolynomials

namespace ModalityInference.ComparisonSignedSynthesis
open ComparisonPropagation ComparisonSignedRelations ComparisonSignedPolynomials

@[simp] theorem Input.key_length (input : Input) (name : Nat) :
    (input.key name).length=input.keys.length := by
  simp [Input.key]

theorem Input.key_injective (input : Input) {a b : Nat} (ha : a∈input.keys)
    (h : input.key a=input.key b) : a=b := by
  simpa [Input.key] using List.map_inj_left.mp h a ha

private theorem payload_le (bases : Nat → List CompareTy) (keys : List Nat)
    {name : Nat} (h : name∈keys) :
    (bases name).length≤keys.foldr (fun k rest=>max (bases k).length rest) 0 := by
  induction keys with
  | nil => simp at h
  | cons k keys ih =>
      rcases List.mem_cons.mp h with rfl|h
      · simp
      · exact (ih h).trans (Nat.le_max_right _ _)

theorem Input.payload_bound (input : Input) {name : Nat} (h : name∈input.keys) :
    (input.bases name).length≤input.payload := payload_le input.bases input.keys h

@[simp] theorem Input.width_pos (input : Input) : 0<input.width := by
  simp [Input.width]

theorem Input.image_width (input : Input) {name : Nat} (h : name∈input.keys) :
    (input.key name).length+1+(input.bases name).length≤input.width := by
  have := input.payload_bound h
  simp only [Input.key_length,Input.width]
  omega

theorem fold_join {α : Type*} (v : Nat → Bool) (xs : List α) (f : α → CNF) :
    CNFHolds v (xs.foldr (fun x rest=>join (f x) rest) [[]]) ↔
      ∃x∈xs,CNFHolds v (f x) := by
  induction xs with
  | nil => simp [CNFHolds,ClauseHolds]
  | cons x xs ih =>
      rw [List.foldr_cons,join_correct,ih]
      simp

theorem Input.polynomialEdges_correct (input : Input) (p a b : Nat → Bool) :
    Holds p input.polynomialEdges a b ↔
      ∃name∈input.keys,Holds p (ComparisonSignedPolynomials.edges
        (input.key name) (input.bases name).length) a b := fold_join _ _ _

theorem Input.edges_correct (input : Input) (r : CNF) (p a b : Nat → Bool) :
    Holds p (input.edges r) a b ↔ Holds p r a b ∨
      ∃name∈input.keys,Holds p (ComparisonSignedPolynomials.edges
        (input.key name) (input.bases name).length) a b :=
  (join_correct _ _ _).trans (or_congr Iff.rfl (input.polynomialEdges_correct p a b))

theorem Input.polynomialEdges_depends (input : Input) : Depends input.width input.polynomialEdges := by
  intro p a b a' b' ha hb
  simp only [input.polynomialEdges_correct]
  apply exists_congr fun name=>and_congr_right fun hn=>?_
  exact ComparisonSignedPolynomials.edges_depends (input.key name) (input.bases name).length
    (input.image_width hn) p a b a' b' ha hb

theorem Input.edges_depends (input : Input) {r : CNF} (h : Depends input.width r) :
    Depends input.width (input.edges r) := by
  intro p a b a' b' ha hb
  change CNFHolds _ (join _ _) ↔ CNFHolds _ (join _ _)
  exact (join_correct _ _ _).trans ((or_congr (h p a b a' b' ha hb)
    (input.polynomialEdges_depends p a b a' b' ha hb)).trans (join_correct _ _ _).symm)

theorem Input.polynomialEdges_contrapose (input : Input) (p : Nat → Bool) {a b : Nat → Bool}
    (h : Holds p input.polynomialEdges a b) :
    Holds p input.polynomialEdges (ComparisonSignedCanonical.toggle 0 b)
      (ComparisonSignedCanonical.toggle 0 a) := by
  obtain ⟨name,hn,h⟩ := (input.polynomialEdges_correct p a b).mp h
  exact (input.polynomialEdges_correct p _ _).mpr
    ⟨name,hn,ComparisonSignedPolynomials.edges_contrapose p _ _ h⟩

theorem Input.edges_contrapose (input : Input) {r : CNF} (p : Nat → Bool)
    (hc : ∀{a b},Holds p r a b → Holds p r (ComparisonSignedCanonical.toggle 0 b)
      (ComparisonSignedCanonical.toggle 0 a)) {a b : Nat → Bool}
    (h : Holds p (input.edges r) a b) :
    Holds p (input.edges r) (ComparisonSignedCanonical.toggle 0 b)
      (ComparisonSignedCanonical.toggle 0 a) := by
  rcases (join_correct _ _ _).mp h with h|h
  · exact (join_correct _ _ _).mpr (.inl (hc h))
  · exact (join_correct _ _ _).mpr (.inr (input.polynomialEdges_contrapose p h))

theorem finite_contrapose {width : Nat} (hw : 0<width) {r : CNF}
    (hd : Depends width r) (p : Nat → Bool)
    (hc : ∀{a b},Holds p r a b → Holds p r (ComparisonSignedCanonical.toggle 0 b)
      (ComparisonSignedCanonical.toggle 0 a)) {a b : Point width}
    (h : relation width p r a b) :
    relation width p r (ComparisonSignedCanonical.complement ⟨0,hw⟩ b)
      (ComparisonSignedCanonical.complement ⟨0,hw⟩ a) := by
  have hh := hc h
  have hn := (hd p _ _ _ _ (expand_restrict width (ComparisonSignedCanonical.toggle 0 (expand b)))
    (expand_restrict width (ComparisonSignedCanonical.toggle 0 (expand a)))).mp hh
  have hb : restrict width (ComparisonSignedCanonical.toggle 0 (expand b))=
      ComparisonSignedCanonical.complement ⟨0,hw⟩ b := by
    simpa only [ComparisonSignedCanonical.restrict_expand] using
      ComparisonSignedCanonical.restrict_toggle ⟨0,hw⟩ (expand b)
  have ha : restrict width (ComparisonSignedCanonical.toggle 0 (expand a))=
      ComparisonSignedCanonical.complement ⟨0,hw⟩ a := by
    simpa only [ComparisonSignedCanonical.restrict_expand] using
      ComparisonSignedCanonical.restrict_toggle ⟨0,hw⟩ (expand a)
  simpa only [hb,ha] using hn

private theorem mapM_exists {α β : Type} (xs : List α) (f : α → Option β)
    (h : ∀x∈xs,∃y,f x=some y) : ∃ys,xs.mapM f=some ys := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
      obtain ⟨y,hy⟩ := h x (by simp)
      obtain ⟨ys,hys⟩ := ih (fun a ha=>h a (List.mem_cons_of_mem _ ha))
      exact ⟨y::ys,by simp [hy,hys]⟩

theorem Input.reconstruct_complete (input : Input) {r : CNF}
    (hd : Depends input.width r) (p : Nat → Bool)
    (hc : ∀{a b},Holds p r a b → Holds p r (ComparisonSignedCanonical.toggle 0 b)
      (ComparisonSignedCanonical.toggle 0 a))
    (h : Holds p (input.consistent r) (fun _=>false) (fun _=>false)) :
    ∃images,input.reconstruct r p=some images := by
  apply mapM_exists
  intro name hn
  have hc' : ∀{a b : Point input.width},relation input.width p (input.edges r) a b →
      relation input.width p (input.edges r)
        (ComparisonSignedCanonical.complement ⟨0,input.width_pos⟩ b)
        (ComparisonSignedCanonical.complement ⟨0,input.width_pos⟩ a) :=
    fun {_ _} h=>finite_contrapose input.width_pos (input.edges_depends hd) p
      (input.edges_contrapose p hc) h
  obtain ⟨t,ht,_⟩ := ComparisonSignedPolynomials.closure_reconstruct input.width_pos p
    (input.key name) (input.bases name) (input.edges_depends hd) hc'
      (fun a b hab=>(input.edges_correct r p a b).mpr (.inr ⟨name,hn,hab⟩)) h
  have ht' : ComparisonSignedPolynomials.reconstruct p (input.key name)
      (input.bases name) (input.assignment r)=some t := ht
  exact ⟨(name,t),by simp [ht']⟩

private theorem mapM_pairs {α β : Type} (xs : List α) (f : α → Option β)
    {ys : List (α × β)} (h : xs.mapM (fun x=>do return (x,←f x))=some ys) :
    ys.map Prod.fst=xs ∧ ∀y∈ys,f y.1=some y.2 := by
  induction xs generalizing ys with
  | nil =>
      have he : ys=[] := by simpa using h.symm
      simp [he]
  | cons x xs ih =>
      simp only [List.mapM_cons,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at h
      obtain ⟨pair,⟨y,hy,rfl⟩,rest,hr,rfl⟩ := h
      obtain ⟨hkeys,hvalues⟩ := ih hr
      constructor
      · simp [hkeys]
      · intro z hz
        rcases List.mem_cons.mp hz with rfl|hz
        · exact hy
        · exact hvalues z hz

theorem Input.reconstruct_spec (input : Input) {r : CNF} {p : Nat → Bool}
    {images : List (Nat × CompareTy)} (h : input.reconstruct r p=some images) :
    images.map Prod.fst=input.keys ∧ ∀image∈images,
      ComparisonSignedPolynomials.reconstruct p (input.key image.1)
        (input.bases image.1) (input.assignment r)=some image.2 :=
  mapM_pairs input.keys _ h


noncomputable def Input.readImage (input : Input) (images : Nat → (Nat → Bool) → Bool)
    (bits : Nat → Bool) : Bool := by
  classical
  exact if h : ∃name∈input.keys,input.key name=(List.range input.keys.length).map bits then
    images (Classical.choose h) (fun i=>bits (input.keys.length+i))
  else false

noncomputable def Input.readValue (input : Input) (images : Nat → (Nat → Bool) → Bool)
    (a : Nat → Bool) : Bool :=
  input.readImage images (fun i=>a (i+1)) == a 0

theorem Input.readImage_tagged (input : Input) (images : Nat → (Nat → Bool) → Bool)
    (bits : Nat → Bool) {name : Nat} (hn : name∈input.keys)
    (ht : input.key name=(List.range input.keys.length).map bits) :
    input.readImage images bits=images name (fun i=>bits (input.keys.length+i)) := by
  classical
  unfold Input.readImage
  split
  · next h =>
    have he := input.key_injective (Classical.choose_spec h).1
      ((Classical.choose_spec h).2.trans ht.symm)
    rw [he]
  · next h => exact False.elim (h ⟨name,hn,ht⟩)

theorem Input.readValue_complement (input : Input) (images : Nat → (Nat → Bool) → Bool)
    (a : Nat → Bool) :
    input.readValue images (ComparisonSignedCanonical.toggle 0 a)=!input.readValue images a := by
  simp only [Input.readValue,ComparisonSignedCanonical.toggle,Nat.add_eq_zero_iff,
    Nat.one_ne_zero,and_false,if_false,if_true]
  cases hi : input.readImage images (fun i=>a (i+1)) <;> cases h : a 0 <;> rfl

theorem Input.key_of_fixed (input : Input) {name : Nat} {sign : Bool} {a : Nat → Bool}
    (h : Fixed (input.key name) sign a) :
    input.key name=(List.range input.keys.length).map (fun i=>a (i+1)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hv := h (i+1) (by omega)
    simpa [List.getElem?_eq_getElem hi] using hv.symm

theorem Input.readValue_fixed (input : Input) (images : Nat → (Nat → Bool) → Bool)
    {name : Nat} (hn : name∈input.keys) {sign : Bool} {a : Nat → Bool}
    (h : Fixed (input.key name) sign a) :
    input.readValue images a=(images name (fun i=>a (input.keys.length+1+i)) == sign) := by
  have hz : a 0=sign := by simpa using h 0 (by omega)
  rw [Input.readValue,input.readImage_tagged images _ hn (input.key_of_fixed h),hz]
  congr 2
  funext i
  congr 1
  omega

structure Family (input : Input) (images : Nat → (Nat → Bool) → Bool) : Prop where
  monotone : ∀name∈input.keys,∀a b,(∀i<(input.bases name).length,a i=true → b i=true) →
    images name a≤images name b
  zero : ∀name∈input.keys,images name (fun _=>false)=false
  one : ∀name∈input.keys,images name (fun _=>true)=true

theorem Family.congr {input : Input} {images : Nat → (Nat → Bool) → Bool}
    (h : Family input images) {name : Nat} (hn : name∈input.keys)
    {a b : Nat → Bool} (he : ∀i<(input.bases name).length,a i=b i) : images name a=images name b := by
  apply le_antisymm
  · exact h.monotone name hn a b (fun i hi ha=>(he i hi) ▸ ha)
  · exact h.monotone name hn b a (fun i hi hb=>(he i hi).symm ▸ hb)

theorem Family.constant {input : Input} {images : Nat → (Nat → Bool) → Bool}
    (h : Family input images) {name : Nat} (hn : name∈input.keys)
    {a : Nat → Bool} (b : Bool) (he : ∀i<(input.bases name).length,a i=b) : images name a=b := by
  rw [h.congr hn he]
  cases b
  · exact h.zero name hn
  · exact h.one name hn

theorem Family.respects {input : Input} {images : Nat → (Nat → Bool) → Bool}
    (h : Family input images) (p : Nat → Bool) {a b : Nat → Bool}
    (he : Holds p input.polynomialEdges a b) : input.readValue images a≤input.readValue images b := by
  obtain ⟨name,hn,he⟩ := (input.polynomialEdges_correct p a b).mp he
  rcases (ComparisonSignedPolynomials.edges_correct p _ _ a b).mp he with he|he|he|he
  · obtain ⟨⟨ha,hb⟩,hab⟩ := (increasing_correct p _ _ a b).mp he
    rw [input.readValue_fixed images hn ha,input.readValue_fixed images hn hb]
    have hl := h.monotone name hn
      (fun i=>a (input.keys.length+1+i)) (fun i=>b (input.keys.length+1+i))
        (fun i hi hai=>Bool.le_iff_imp.mp (by simpa only [Input.key_length] using hab i hi) hai)
    have ht (x : Bool) : (x==true)=x := by cases x <;> rfl
    simpa only [ht] using hl
  · obtain ⟨⟨ha,hb⟩,hab⟩ := (decreasing_correct p _ _ a b).mp he
    rw [input.readValue_fixed images hn ha,input.readValue_fixed images hn hb]
    have hl := h.monotone name hn
      (fun i=>b (input.keys.length+1+i)) (fun i=>a (input.keys.length+1+i))
        (fun i hi hbi=>Bool.le_iff_imp.mp (by simpa only [Input.key_length] using hab i hi) hbi)
    cases hx : images name (fun i=>a (input.keys.length+1+i)) <;>
      cases hy : images name (fun i=>b (input.keys.length+1+i)) <;>
      simp_all [Bool.le_iff_imp]
  · obtain ⟨⟨ha,hb⟩,hab⟩ := (boundary_correct p _ _ false a b).mp he
    rw [input.readValue_fixed images hn ha,input.readValue_fixed images hn hb]
    rw [h.constant hn false (fun i hi=>by simpa only [Input.key_length] using (hab i hi).1),
      h.constant hn false (fun i hi=>by simpa only [Input.key_length] using (hab i hi).2)]
    decide
  · obtain ⟨⟨ha,hb⟩,hab⟩ := (boundary_correct p _ _ true a b).mp he
    rw [input.readValue_fixed images hn ha,input.readValue_fixed images hn hb]
    rw [h.constant hn true (fun i hi=>by simpa only [Input.key_length] using (hab i hi).1),
      h.constant hn true (fun i hi=>by simpa only [Input.key_length] using (hab i hi).2)]
    decide

theorem Input.tuple_fixed (input : Input) (name : Nat) (sign : Bool) (a : Nat → Bool) :
    Fixed (input.key name) sign (tuple (input.key name) (input.bases name).length sign a) := by
  intro i hi
  simp only [tuple,hi,if_true]

theorem Family.readValue_tuple {input : Input} {images : Nat → (Nat → Bool) → Bool}
    (h : Family input images) {name : Nat} (hn : name∈input.keys) (a : Nat → Bool) :
    input.readValue images (tuple (input.key name) (input.bases name).length true a)=images name a := by
  rw [input.readValue_fixed images hn (input.tuple_fixed name true a)]
  have he : images name (fun i=>tuple (input.key name) (input.bases name).length true a
      (input.keys.length+1+i))=images name a := by
    apply h.congr hn
    intro i hi
    simpa only [Input.key_length] using tuple_basis (input.key name) hi true a
  rw [he]
  cases images name a <;> rfl

theorem Input.fixed_of_key (input : Input) {name : Nat} {a : Nat → Bool}
    (h : input.key name=(List.range input.keys.length).map (fun i=>a (i+1))) :
    Fixed (input.key name) (a 0) a := by
  intro i hi
  cases i with
  | zero => simp
  | succ i =>
      have hi' : i<input.keys.length := by simpa only [Input.key_length] using Nat.lt_of_succ_lt_succ hi
      have he := congrArg (fun xs : List Bool=>xs[i]?.getD false) h
      simpa [List.getElem?_map,List.getElem?_range hi'] using he.symm

theorem Input.tail_key_congr (input : Input) {a b : Nat → Bool} (h : Same input.width a b) :
    (List.range input.keys.length).map (fun i=>a (i+1))=
      (List.range input.keys.length).map (fun i=>b (i+1)) := by
  apply List.map_inj_left.mpr
  intro i hi
  apply h
  have hi := List.mem_range.mp hi
  simp only [Input.width]
  omega

theorem Family.readValue_congr {input : Input} {images : Nat → (Nat → Bool) → Bool}
    (h : Family input images) {a b : Nat → Bool} (hs : Same input.width a b) :
    input.readValue images a=input.readValue images b := by
  classical
  have ht := input.tail_key_congr hs
  have hz := hs 0 input.width_pos
  by_cases hk : ∃name∈input.keys,input.key name=(List.range input.keys.length).map (fun i=>a (i+1))
  · obtain ⟨name,hn,hname⟩ := hk
    rw [input.readValue_fixed images hn (input.fixed_of_key hname),
      input.readValue_fixed images hn (input.fixed_of_key (hname.trans ht)),hz]
    congr 1
    apply h.congr hn
    intro i hi
    apply hs
    have hb := input.payload_bound hn
    simp only [Input.width]
    omega
  · have hk' : ¬∃name∈input.keys,input.key name=(List.range input.keys.length).map (fun i=>b (i+1)) := by
      simpa only [←ht] using hk
    simp only [Input.readValue,Input.readImage,dif_neg hk,dif_neg hk',hz]

theorem Family.consistent {input : Input} {images : Nat → (Nat → Bool) → Bool}
    (hfamily : Family input images) {r : CNF} (hd : Depends input.width r) (p : Nat → Bool)
    (hc : ∀{a b},Holds p r a b → Holds p r (ComparisonSignedCanonical.toggle 0 b)
      (ComparisonSignedCanonical.toggle 0 a))
    (hr : ∀a b,Holds p r a b → input.readValue images a≤input.readValue images b) :
    Holds p (input.consistent r) (fun _=>false) (fun _=>false) := by
  have hc' : ∀{a b : Point input.width},relation input.width p (input.edges r) a b →
      relation input.width p (input.edges r)
        (ComparisonSignedCanonical.complement ⟨0,input.width_pos⟩ b)
        (ComparisonSignedCanonical.complement ⟨0,input.width_pos⟩ a) :=
    fun {_ _} h=>finite_contrapose input.width_pos (input.edges_depends hd) p
      (input.edges_contrapose p hc) h
  apply (ComparisonSignedCanonical.closure_consistent_iff ⟨0,input.width_pos⟩
    (input.edges_depends hd) p hc' _ _).mpr
  refine ⟨fun a=>input.readValue images (expand a),⟨?_,?_⟩⟩
  · intro a
    have hs : Same input.width
        (expand (ComparisonSignedCanonical.complement ⟨0,input.width_pos⟩ a))
        (ComparisonSignedCanonical.toggle 0 (expand a)) := by
      intro i hi
      simp [expand,ComparisonSignedCanonical.complement,ComparisonSignedCanonical.toggle,hi,Fin.ext_iff]
    exact (hfamily.readValue_congr hs).trans (input.readValue_complement images _)
  · intro a b hab
    rcases (join_correct _ _ _).mp hab with hab|hab
    · exact hr _ _ hab
    · exact hfamily.respects p hab

def polynomialValue (clauses : CNF) (v : Nat → Bool) : Bool :=
  clauses.all (CNFPropagation.clauseValue v)

theorem polynomialValue_correct (clauses : CNF) (v : Nat → Bool) :
    polynomialValue clauses v=true ↔ CNFHolds v clauses := by
  simp [polynomialValue,List.all_eq_true,CNFPropagation.clauseValue_correct,CNFHolds]

theorem polynomial_family (input : Input) (clauses : Nat → CNF)
    (hp : ∀name∈input.keys,Positive (clauses name))
    (hs : ∀name∈input.keys,Supported (List.range (input.bases name).length) (clauses name))
    (hz : ∀name∈input.keys,¬CNFHolds (fun _=>false) (clauses name))
    (ho : ∀name∈input.keys,CNFHolds (fun _=>true) (clauses name)) :
    Family input (fun name=>polynomialValue (clauses name)) where
  monotone := by
    intro name hn a b hab
    apply Bool.le_iff_imp.mpr
    intro ha
    apply (polynomialValue_correct _ _).mpr
    apply Positive.monotone_supported (hp name hn) (hs name hn)
      (fun i hi=>hab i (List.mem_range.mp hi))
    exact (polynomialValue_correct _ _).mp ha
  zero := by
    intro name hn
    apply Bool.eq_false_iff.mpr
    intro hh
    exact hz name hn ((polynomialValue_correct _ _).mp hh)
  one := fun name hn=>(polynomialValue_correct _ _).mpr (ho name hn)

end ModalityInference.ComparisonSignedSynthesis

