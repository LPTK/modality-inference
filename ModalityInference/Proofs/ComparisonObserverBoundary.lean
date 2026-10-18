import ModalityInference.ComparisonObserverBoundary
import ModalityInference.Proofs.ComparisonObserverFiniteMachine

/-! The finite observer boundary and its size bound are computed from the
written endpoints and original declared bounds. Port closure and modality
support impose no additional hypotheses on those inputs. -/
namespace ModalityInference.ComparisonObserverBoundary

open ComparisonAlgebra ComparisonObserverGluing ComparisonObserverRepresentatives
  ComparisonObserverFiniteMachine ComparisonInterpolation

theorem mem_subterms (a : CompareTy) : a ∈ subterms a := by cases a <;> simp [subterms]

theorem subterms_trans {a b c : CompareTy} (hb : b ∈ subterms a) (hc : c ∈ subterms b) :
    c ∈ subterms a := by
  induction a with
  | var | unit | credit => simp_all [subterms]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb | join a b iha ihb | meet a b iha ihb =>
    simp only [subterms, List.mem_cons, List.mem_append] at hb ⊢
    rcases hb with rfl | h | h
    · simpa only [subterms, List.mem_cons, List.mem_append] using hc
    · exact Or.inr (Or.inl (iha h))
    · exact Or.inr (Or.inr (ihb h))
  | modal a m ih =>
    simp only [subterms, List.mem_cons] at hb ⊢
    rcases hb with rfl | h
    · simpa only [subterms, List.mem_cons] using hc
    · exact Or.inr (ih h)

theorem ports_subterms (a : CompareTy) : ∀ p ∈ ports a, p.2 ∈ subterms a := by
  induction a with
  | var | unit | credit => simp [ports]
  | prod a b | sum a b | fn a b =>
    intro p hp
    simp only [ports, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [subterms, mem_subterms]
  | join a b iha ihb | meet a b iha ihb =>
    intro p hp
    rcases List.mem_append.mp hp with ha | hb
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (iha p ha))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihb p hb))
  | modal a m ih => exact fun p hp => List.mem_cons_of_mem _ (ih p hp)

theorem mem_closure {inputs : List CompareTy} {a : CompareTy} (ha : a ∈ inputs) :
    a ∈ closure inputs := List.mem_flatMap.mpr ⟨a, ha, mem_subterms a⟩

theorem closure_ports_closed (inputs : List CompareTy) : PortsClosed (closure inputs) := by
  intro a ha p hp
  obtain ⟨b, hb, hab⟩ := List.mem_flatMap.mp ha
  exact List.mem_flatMap.mpr ⟨b, hb, subterms_trans hab (ports_subterms a p hp)⟩

theorem subterms_support {P : TypeVar → Prop} {Q : ModVar → Prop}
    {a b : CompareTy} (hs : Supports P Q a) (hb : b ∈ subterms a) : Supports P Q b := by
  induction a with
  | var | unit | credit => simp_all [subterms]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb | join a b iha ihb | meet a b iha ihb =>
    simp only [subterms, List.mem_cons, List.mem_append] at hb
    rcases hb with rfl | h | h
    · exact hs
    · exact iha hs.1 h
    · exact ihb hs.2 h
  | modal a m ih =>
    simp only [subterms, List.mem_cons] at hb
    rcases hb with rfl | h
    · exact hs
    · exact ih hs.1 h

theorem closure_support {P : TypeVar → Prop} {Q : ModVar → Prop} {inputs : List CompareTy}
    (hs : ∀ a ∈ inputs, Supports P Q a) : ∀ a ∈ closure inputs, Supports P Q a := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := List.mem_flatMap.mp ha
  exact subterms_support (hs b hb) hab

theorem support_iff {Q : ModVar → Prop} (a : CompareTy) :
    Supports (fun _ => True) Q a ↔ ∀ v ∈ modes a, Q v := by
  induction a <;> simp_all [Supports, modes, or_imp, forall_and]

theorem modes_subset {inputs : List CompareTy} {a : CompareTy} (ha : a ∈ inputs) :
    modes a ⊆ allModes inputs := by
  induction inputs with
  | nil => simp at ha
  | cons b rest ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Finset.subset_union_left
    · exact (ih ha).trans Finset.subset_union_right

theorem declared_types (Δ : Bounds) : DeclaredIn Δ (declaredTypes Δ) := by
  intro a b hab
  exact ⟨List.mem_flatMap.mpr ⟨.sub a b, hab, by simp⟩,
    List.mem_flatMap.mpr ⟨.sub a b, hab, by simp⟩⟩

theorem boundary_declared (Δ : Bounds) (queries : List CompareTy) : DeclaredIn Δ (boundary Δ queries) := by
  intro a b hab
  exact ⟨mem_closure (List.mem_append_left _ (declared_types Δ a b hab).1),
    mem_closure (List.mem_append_left _ (declared_types Δ a b hab).2)⟩

theorem boundary_query {Δ : Bounds} {queries : List CompareTy} {a : CompareTy} (ha : a ∈ queries) :
    a ∈ boundary Δ queries := mem_closure (List.mem_append_right _ ha)

theorem boundary_support (Δ : Bounds) (queries : List CompareTy) :
    ∀ a ∈ boundary Δ queries, Supports (fun _ => True) (· ∈ names Δ queries) a := by
  apply closure_support
  intro a ha
  apply (support_iff a).mpr
  intro v hv
  exact Finset.mem_union_right _ (modes_subset ha hv)

theorem type_support_iff {P : TypeVar → Prop} (a : CompareTy) :
    Supports P (fun _ => True) a ↔ ∀ v ∈ types a, P v := by
  induction a <;> simp_all [Supports, types, or_imp, forall_and]

theorem types_subset {inputs : List CompareTy} {a : CompareTy} (ha : a ∈ inputs) :
    types a ⊆ allTypes inputs := by
  induction inputs with
  | nil => simp at ha
  | cons b rest ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Finset.subset_union_left
    · exact (ih ha).trans Finset.subset_union_right

theorem supports_combine {P : TypeVar → Prop} {Q : ModVar → Prop} {a : CompareTy}
    (ht : Supports P (fun _ => True) a) (hm : Supports (fun _ => True) Q a) : Supports P Q a := by
  induction a <;> simp_all [Supports]

theorem boundary_full_support (Δ : Bounds) (queries : List CompareTy) :
    ∀ a ∈ boundary Δ queries, Supports (· ∈ (typeNames Δ queries).toList) (· ∈ (names Δ queries).toList) a := by
  have ht : ∀ a ∈ boundary Δ queries, Supports (· ∈ (typeNames Δ queries).toList) (fun _ => True) a := by
    apply closure_support
    intro a ha
    apply (type_support_iff a).mpr
    exact fun _ hv => Finset.mem_toList.mpr (types_subset ha hv)
  intro a ha
  apply supports_combine (ht a ha)
  apply (support_iff a).mpr
  exact fun v hv => Finset.mem_toList.mpr ((support_iff a).mp (boundary_support Δ queries a ha) v hv)

theorem mem_typeList (a : CompareTy) (v : TypeVar) : v ∈ typeList a ↔ v ∈ types a := by
  induction a <;> simp_all [typeList, types]

theorem mem_modeList (a : CompareTy) (v : ModVar) : v ∈ modeList a ↔ v ∈ modes a := by
  induction a <;> simp_all [modeList, modes, ModExpr.mem_freeVariables]

theorem mem_allTypes (as : List CompareTy) (v : TypeVar) :
    v ∈ allTypes as ↔ ∃ a ∈ as, v ∈ types a := by
  induction as <;> simp_all [allTypes]

theorem mem_allModes (as : List CompareTy) (v : ModVar) :
    v ∈ allModes as ↔ ∃ a ∈ as, v ∈ modes a := by
  induction as <;> simp_all [allModes]

theorem mem_retainedTypes (Δ : Bounds) (queries : List CompareTy) (v : TypeVar) :
    v ∈ retainedTypes Δ queries ↔ v ∈ typeNames Δ queries := by
  simp [retainedTypes, typeNames, mem_allTypes, mem_typeList]

theorem mem_retainedModes (Δ : Bounds) (queries : List CompareTy) (v : ModVar) :
    v ∈ retainedModes Δ queries ↔ v ∈ names Δ queries := by
  simp [retainedModes, names, mem_allModes, mem_modeList]

theorem boundary_retained_support (Δ : Bounds) (queries : List CompareTy) :
    ∀ a ∈ boundary Δ queries, Supports (· ∈ retainedTypes Δ queries) (· ∈ retainedModes Δ queries) a := by
  intro a ha
  have h := boundary_full_support Δ queries a ha
  have he : ∀ a, Supports (· ∈ (typeNames Δ queries).toList) (· ∈ (names Δ queries).toList) a ↔
      Supports (· ∈ retainedTypes Δ queries) (· ∈ retainedModes Δ queries) a := by
    intro a
    induction a <;> simp_all [Supports, mem_retainedTypes, mem_retainedModes]
  exact (he a).mp h

theorem input_bounded_machine {Δ : Bounds}
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (queries : List CompareTy) :
    ∃ count ≤ sizeBound Δ queries, ∃ machine : ComparisonObserverMachine.Machine count,
      ComparisonObserverMachine.Certified Δ machine ∧
      ∀ f : LatticeHom (Order Δ .unit) Bool, ∃ i : Fin count,
        ∀ a ∈ queries, a.DefinedUnder Δ →
          ComparisonObserverMachine.value machine a i = booleanValue f a := by
  obtain ⟨count, hc, machine, hm, hf⟩ := bounded_machine
    (show Δ.modVars ⊆ names Δ queries from Finset.subset_union_left) hn hΔ
    (boundary Δ queries) (closure_ports_closed _) (boundary_declared Δ queries)
    (boundary_support Δ queries)
  refine ⟨count, hc, machine, hm, ?_⟩
  intro f
  obtain ⟨i, hi⟩ := hf f
  exact ⟨i, fun a ha had => hi a (boundary_query ha) had⟩

/-- Fixed endpoint comparisons require no independently supplied finite
boundary, support set, or finite-model hypothesis. The declared context may
have recursive shape equations. -/
theorem subtype_iff_input_bounded_machines {Δ : Bounds}
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    {a b : CompareTy} (had : a.DefinedUnder Δ) (hbd : b.DefinedUnder Δ) :
    AlgebraSubtype Δ a b ↔
      ∀ count ≤ sizeBound Δ [a, b], ∀ machine : ComparisonObserverMachine.Machine count,
      ComparisonObserverMachine.Certified Δ machine → ∀ i,
        ComparisonObserverMachine.value machine a i ≤ ComparisonObserverMachine.value machine b i :=
  subtype_iff_bounded_machines
    (show Δ.modVars ⊆ names Δ [a, b] from Finset.subset_union_left) hn hΔ
    (boundary Δ [a, b]) (closure_ports_closed _) (boundary_declared Δ [a, b])
    (boundary_support Δ [a, b]) (boundary_query (by simp)) (boundary_query (by simp)) had hbd

end ModalityInference.ComparisonObserverBoundary
