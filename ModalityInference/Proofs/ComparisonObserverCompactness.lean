import ModalityInference.Proofs.ComparisonAlgebraOrder

/-! Finite-observation compactness for actual Boolean lattice observers.
The limit preserves lattice operations and a finite shared index; it is not
an unconstrained table of independent observation values. -/
namespace ModalityInference.ComparisonObserverCompactness

private theorem separator {ι : Type*} (F : _root_.Order.PFilter (Set ι))
    (he : (∅ : Set ι) ∉ F) :
    ∃ u : LatticeHom (Set ι) Bool,
      u ∅ = false ∧ (∀ s ∈ F, u s = true) := by
  classical
  have hd : Disjoint (F : Set (Set ι))
      ((_root_.Order.Ideal.principal (∅ : Set ι) : _root_.Order.Ideal (Set ι)) : Set (Set ι)) := by
    refine Set.disjoint_left.mpr ?_
    intro s hs hs'
    exact he (Set.Subset.antisymm hs' (Set.empty_subset s) ▸ hs)
  obtain ⟨J,hJ,heJ,hFJ⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hd
  let u : LatticeHom (Set ι) Bool :=
    { toFun := fun s => decide (s ∉ J)
      map_sup' := by
        intro s t
        have he : s ∪ t ∈ J ↔ s ∈ J ∧ t ∈ J := _root_.Order.Ideal.sup_mem_iff
        apply Bool.eq_iff_iff.mpr
        simp [he]
      map_inf' := by
        intro s t
        have he : s ∩ t ∈ J ↔ s ∈ J ∨ t ∈ J :=
          ⟨hJ.mem_or_mem,fun h => h.elim (J.lower inf_le_left) (J.lower inf_le_right)⟩
        apply Bool.eq_iff_iff.mpr
        simp [he] }
  refine ⟨u,?_,?_⟩
  · exact decide_eq_false (not_not_intro (heJ _root_.Order.Ideal.mem_principal_self))
  · intro s hs
    exact decide_eq_true (Set.disjoint_left.mp hFJ hs)

private theorem cofinal_limit (α : Type*) :
    ∃ u : LatticeHom (Set (Finset α)) Bool,
      u ∅ = false ∧ ∀ p, u {q | p ⊆ q} = true := by
  classical
  let F : Set (Set (Finset α)) := {s | ∃p, ∀q, p ⊆ q → q ∈ s}
  have hF : _root_.Order.IsPFilter F := by
    refine _root_.Order.IsPFilter.of_def ?_ ?_ ?_
    · exact ⟨Set.univ,∅,fun _ _ => trivial⟩
    · rintro s ⟨p,hp⟩ t ⟨q,hq⟩
      exact ⟨s ∩ t,⟨p ∪ q,fun r hr => ⟨hp r (Finset.union_subset_iff.mp hr).1,
        hq r (Finset.union_subset_iff.mp hr).2⟩⟩,Set.inter_subset_left,Set.inter_subset_right⟩
    · rintro s t hst ⟨p,hp⟩
      exact ⟨p,fun q hq => hst (hp q hq)⟩
  obtain ⟨u,hu,hp⟩ := separator hF.toPFilter (by
    rintro ⟨p,hp⟩
    exact hp p Finset.Subset.rfl)
  exact ⟨u,hu,fun p => hp _ ⟨p,fun _ h => h⟩⟩

private theorem complement {ι : Type*} (u : LatticeHom (Set ι) Bool)
    (he : u ∅ = false) (hu : u Set.univ = true) (s : Set ι) :
    u sᶜ = !(u s) := by
  have hjoin := u.map_sup' s sᶜ
  have hmeet := u.map_inf' s sᶜ
  simp only [Set.sup_eq_union,Set.inf_eq_inter,Set.union_compl_self,
    Set.inter_compl_self,Bool.max_eq_or,Bool.min_eq_and] at hjoin hmeet
  change u Set.univ = (u s || u sᶜ) at hjoin
  change u ∅ = (u s && u sᶜ) at hmeet
  rw [hu] at hjoin
  rw [he] at hmeet
  cases hs : u s <;> cases hc : u sᶜ <;>
    simp only [hs,hc] at hjoin hmeet <;>
    first | rfl | exact Bool.noConfusion hjoin | exact Bool.noConfusion hmeet

private theorem nonempty {ι : Type*} (u : LatticeHom (Set ι) Bool)
    (he : u ∅ = false) {s : Set ι} (hs : u s = true) : s.Nonempty := by
  by_contra hn
  rw [Set.not_nonempty_iff_eq_empty.mp hn,he] at hs
  exact Bool.noConfusion hs

private theorem finite_all {ι κ : Type*} (u : LatticeHom (Set ι) Bool)
    (hu : u Set.univ = true) (p : Finset κ) (s : κ → Set ι)
    (hs : ∀a ∈ p,u (s a) = true) : u {i | ∀a ∈ p,i ∈ s a} = true := by
  classical
  induction p using Finset.induction_on with
  | empty => simpa only [Finset.notMem_empty,IsEmpty.forall_iff,implies_true,forall_const] using hu
  | @insert a p ha ih =>
    have he : {i | ∀b ∈ insert a p,i ∈ s b} = s a ∩ {i | ∀b ∈ p,i ∈ s b} := by
      ext i
      simp
    rw [he,show u (s a ∩ {i | ∀b ∈ p,i ∈ s b}) =
      (u (s a) && u {i | ∀b ∈ p,i ∈ s b}) from u.map_inf' _ _,
      hs a (Finset.mem_insert_self a p),
      ih (fun b hb => hs b (Finset.mem_insert_of_mem hb))]
    rfl

private noncomputable def limit {ι L : Type*} [Lattice L]
    (u : LatticeHom (Set ι) Bool) (f : ι → LatticeHom L Bool) : LatticeHom L Bool where
  toFun a := u {i | f i a = true}
  map_sup' a b := by
    have he : {i | f i (a ⊔ b) = true} = {i | f i a = true} ∪ {i | f i b = true} := by
      ext i
      simp
    exact he ▸ u.map_sup' _ _
  map_inf' a b := by
    have he : {i | f i (a ⊓ b) = true} = {i | f i a = true} ∩ {i | f i b = true} := by
      ext i
      simp
    exact he ▸ u.map_inf' _ _

private theorem limit_equal {ι L : Type*} [Lattice L]
    (u : LatticeHom (Set ι) Bool) (f : ι → LatticeHom L Bool)
    (he : u ∅ = false) (hu : u Set.univ = true) (a : L) :
    u {i | f i a = limit u f a} = true := by
  change u {i | f i a = u {j | f j a = true}} = true
  cases h : u {j | f j a = true} with
  | false =>
    have hs : {i | f i a = false} = {i | f i a = true}ᶜ := by
      ext i
      simp
    rw [hs,complement u he hu,h]
    rfl
  | true => exact h

private theorem finite_choice {ι κ : Type*} [Fintype κ]
    (u : LatticeHom (Set ι) Bool) (he : u ∅ = false) (hu : u Set.univ = true)
    (f : ι → κ) : ∃k,u {i | f i = k} = true := by
  classical
  have h (p : Finset κ) : u {i | f i ∈ p} = true →
      ∃ k ∈ p,u {i | f i = k} = true := by
    induction p using Finset.induction_on with
    | empty =>
      intro hp
      have hz : {i | f i ∈ (∅ : Finset κ)} = ∅ := by ext; simp
      rw [hz,he] at hp
      exact Bool.noConfusion hp
    | @insert a p ha ih =>
      intro hp
      have hz : {i | f i ∈ insert a p} = {i | f i = a} ∪ {i | f i ∈ p} := by
        ext; simp
      rw [hz,show u ({i | f i = a} ∪ {i | f i ∈ p}) =
        (u {i | f i = a} || u {i | f i ∈ p}) from u.map_sup' _ _,Bool.or_eq_true] at hp
      rcases hp with hp | hp
      · exact ⟨a,Finset.mem_insert_self a p,hp⟩
      · obtain ⟨k,hk,hv⟩ := ih hp
        exact ⟨k,Finset.mem_insert_of_mem hk,hv⟩
  obtain ⟨k,_,hk⟩ := h Finset.univ (by simpa using hu)
  exact ⟨k,hk⟩

/-- Finitely observed, nested demands on genuine lattice observers have the
finite-intersection property. The resulting observer is a lattice homomorphism,
not an unconstrained Boolean table. -/
theorem compact {L K : Type*} [Lattice L] [Fintype K]
    (bad : Finset L → K → LatticeHom L Bool → Prop)
    (depends : ∀p k f g,(∀a ∈ p,f a = g a) → (bad p k f ↔ bad p k g))
    (restrict : ∀p q,p ⊆ q → ∀k f,bad q k f → bad p k f)
    (inhabited : ∀p,∃k f,bad p k f) :
    ∃k f,∀p,bad p k f := by
  classical
  choose k f hf using inhabited
  obtain ⟨u,he,hu⟩ := cofinal_limit L
  have htop : u Set.univ = true := by simpa using hu ∅
  obtain ⟨c,hc⟩ := finite_choice u he htop k
  refine ⟨c,limit u f,?_⟩
  intro p
  have hm : u {q | ∀a ∈ p,f q a = limit u f a} = true :=
    finite_all u htop p (fun a => {q | f q a = limit u f a})
      (fun a _ => limit_equal u f he htop a)
  have hboth : u ({q | p ⊆ q} ∩
      ({q | k q = c} ∩ {q | ∀a ∈ p,f q a = limit u f a})) = true := by
    have hi₁ := u.map_inf' {q | p ⊆ q}
      ({q | k q = c} ∩ {q | ∀a ∈ p,f q a = limit u f a})
    have hi₂ := u.map_inf' {q | k q = c} {q | ∀a ∈ p,f q a = limit u f a}
    change u _ = (u {q | p ⊆ q} && u _) at hi₁
    change u _ = (u {q | k q = c} && u _) at hi₂
    simp only [Set.inf_eq_inter] at hi₁ hi₂
    rw [hi₁,hi₂,hu p,hc,hm]
    rfl
  obtain ⟨q,hpq,hkc,hfq⟩ := nonempty u he hboth
  exact (depends p c (f q) (limit u f) hfq).mp (hkc ▸ restrict p q hpq (k q) (f q) (hf q))

end ModalityInference.ComparisonObserverCompactness

