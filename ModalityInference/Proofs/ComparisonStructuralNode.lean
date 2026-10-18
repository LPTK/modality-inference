import ModalityInference.ComparisonStructuralNode
import ModalityInference.Proofs.ComparisonStructuralSharedWorld
import ModalityInference.Proofs.ComparisonLatticeCompiler

/-! Exact compilation of finite structural node queries. Actual modal models
satisfy the signed-control theory and every whole declared endpoint inequality. -/
namespace ModalityInference.ComparisonStructuralNode

open ComparisonControls

open ComparisonAlgebra ComparisonStructuralAlignment ComparisonPropagation

theorem clauses_correct (basisAtom : Nat → Nat) (bounds : List Bound) (world : Nat → Bool) :
    CNFHolds world (clauses basisAtom bounds) ↔
      ∀bound∈bounds, CNFHolds (world ∘ basisAtom) bound.left →
        CNFHolds (world ∘ basisAtom) bound.right := by
  induction bounds with
  | nil => simp [clauses, CNFHolds]
  | cons bound rest ih =>
    change CNFHolds world (rename basisAtom (implies bound.left bound.right) ++ clauses basisAtom rest) ↔ _
    rw [cnfHolds_append, rename_correct, implies_correct, ih]
    simp

theorem compile_correct {fuel basis basisAtom headAtom modeAtom coordinate bounds output}
    (h : compile fuel basis basisAtom headAtom modeAtom coordinate bounds = .success output)
    (world : Nat → Bool) :
    CNFHolds world output ↔
      (basis.theoryAt basisAtom headAtom modeAtom coordinate).eval world = true ∧
      ∀bound∈bounds, CNFHolds (world ∘ basisAtom) bound.left →
        CNFHolds (world ∘ basisAtom) bound.right := by
  cases hc : CompactCNF.toCNF fuel true (basis.theoryAt basisAtom headAtom modeAtom coordinate) <;>
    simp [compile, hc, bind, pure, RunResult.bind] at h
  subst output
  rw [cnfHolds_append, CompactCNF.toCNF_correct hc, clauses_correct]

theorem compile_complete (basis : Basis) (basisAtom headAtom modeAtom : Nat → Nat)
    (coordinate : Coordinate) (bounds : List Bound) :
    ∃threshold output, ∀fuel≥threshold,
      compile fuel basis basisAtom headAtom modeAtom coordinate bounds = .success output := by
  obtain ⟨threshold, controls, hc⟩ := CompactCNF.toCNF_complete
    (basis.theoryAt basisAtom headAtom modeAtom coordinate) true
  exact ⟨threshold, controls ++ clauses basisAtom bounds, fun fuel hf => by
    simp [compile, hc fuel hf, bind, pure, RunResult.bind]⟩


theorem prepare_spec {basis : Basis} {input : List (CompareTy × CompareTy)} {bounds : List Bound}
    (h : prepare basis input = some bounds) :
    List.Forall₂ (fun pair bound =>
      ComparisonLatticeCompiler.compile basis pair.1 = some bound.left ∧
      ComparisonLatticeCompiler.compile basis pair.2 = some bound.right) input bounds := by
  induction input generalizing bounds with
  | nil => simp [prepare] at h; subst bounds; exact .nil
  | cons pair rest ih =>
    obtain ⟨left, right⟩ := pair
    cases hl : ComparisonLatticeCompiler.compile basis left <;> simp [prepare, hl] at h
    rename_i lower
    cases hr : ComparisonLatticeCompiler.compile basis right <;> simp [hr] at h
    rename_i upper
    cases ht : prepare basis rest <;> simp [ht] at h
    subst bounds
    exact .cons ⟨hl, hr⟩ (ih ht)

theorem prepare_complete {basis : Basis} {input : List (CompareTy × CompareTy)}
    (h : ∀pair∈input, LatticeForm basis.types pair.1 ∧ LatticeForm basis.types pair.2) :
    ∃bounds, prepare basis input = some bounds := by
  induction input with
  | nil => exact ⟨[], rfl⟩
  | cons pair rest ih =>
    obtain ⟨left, right⟩ := pair
    obtain ⟨lower, hl⟩ := ComparisonLatticeCompiler.compile_complete (h _ List.mem_cons_self).1
    obtain ⟨upper, hr⟩ := ComparisonLatticeCompiler.compile_complete (h _ List.mem_cons_self).2
    obtain ⟨tail, ht⟩ := ih (fun pair hp => h pair (List.mem_cons_of_mem _ hp))
    exact ⟨⟨lower, upper⟩ :: tail, by simp [prepare, hl, hr, ht]⟩

theorem compiled_value {basis : Basis} {type : CompareTy} {output : CNF}
    (h : ComparisonLatticeCompiler.compile basis type = some output)
    (value : CompareTy → Bool)
    (hj : ∀a b, value (.join a b) = (value a || value b))
    (hm : ∀a b, value (.meet a b) = (value a && value b))
    {basisAtom : Nat → Nat} {world : Nat → Bool}
    (hb : ∀i (hi : i < basis.types.length), world (basisAtom i) = value basis.types[i]) :
    CNFHolds (world ∘ basisAtom) output ↔ value type = true := by
  refine (CNFPropagation.holds_congr ?_).trans (ComparisonLatticeCompiler.compile_value h value hj hm)
  intro i hi
  have hir := List.mem_range.mp ((ComparisonLatticeCompiler.compile_polynomial h).2.supported i hi)
  simpa [basisValue, List.getElem?_eq_getElem hir] using hb i hir

theorem prepare_value {basis : Basis} {input : List (CompareTy × CompareTy)} {bounds : List Bound}
    (h : prepare basis input = some bounds)
    (value : CompareTy → Bool)
    (hj : ∀a b, value (.join a b) = (value a || value b))
    (hm : ∀a b, value (.meet a b) = (value a && value b))
    {basisAtom : Nat → Nat} {world : Nat → Bool}
    (hb : ∀i (hi : i < basis.types.length), world (basisAtom i) = value basis.types[i]) :
    (∀bound∈bounds, CNFHolds (world ∘ basisAtom) bound.left → CNFHolds (world ∘ basisAtom) bound.right) ↔
      ∀pair∈input, value pair.1 = true → value pair.2 = true := by
  have hs := prepare_spec h
  clear h
  induction hs with
  | nil => simp
  | cons hpair hrest ih =>
    simp only [List.forall_mem_cons, compiled_value hpair.1 value hj hm hb,
      compiled_value hpair.2 value hj hm hb, ih]

theorem model_boolean_modal {Δ : Bounds} {shape : ComparisonShape}
    {f : LatticeHom (Order Δ shape) Bool} {labels : List (GuardedMode Δ)}
    {coordinate : Coordinate} {η : ModVar → Mode}
    (hmodel : ComparisonStructuralAlignment.Model f labels coordinate η)
    {t : CompareTy} (ht : Representable Δ shape t)
    {m : ModExpr} (hm : ∃n∈labels, n.expression = m)
    {modeAtom : Nat → Nat} {world : Nat → Bool}
    (hworld : ∀i, world (modeAtom i) = encodeModes η i) :
    booleanValue f (.modal t m) =
      (coordinate.modalWith modeAtom (.const (booleanValue f t)) m).eval world := by
  obtain ⟨n, hn, rfl⟩ := hm
  change booleanValue f (n.act (represented ht)).type = _
  rw [booleanValue_carrier, booleanValue_represented f t ht]
  exact (hmodel.action (represented ht) n hn).trans
    (Coordinate.modalWith_eval (value := .const (observer f (represented ht))) hworld
      (hmodel.modeModel.imp_right (n.eval η))).symm

theorem model_basis_theoryAt {Δ : Bounds} {shape : ComparisonShape}
    {f : LatticeHom (Order Δ shape) Bool} {labels : List (GuardedMode Δ)}
    {coordinate : Coordinate} {η : ModVar → Mode}
    (hmodel : ComparisonStructuralAlignment.Model f labels coordinate η)
    (basis : Basis) (hheads : ∀t∈basis.heads, Representable Δ shape t)
    (hlabels : ∀p∈basis.modalPairs, ∃m∈labels, m.expression = p.2)
    {basisAtom headAtom modeAtom : Nat → Nat} {world : Nat → Bool}
    (hh : ∀i (hi : i < basis.heads.length), world (headAtom i) = booleanValue f basis.heads[i])
    (hb : ∀i (hi : i < basis.types.length), world (basisAtom i) = booleanValue f basis.types[i])
    (hm : ∀i, world (modeAtom i) = encodeModes η i) :
    (basis.theoryAt basisAtom headAtom modeAtom coordinate).eval world = true := by
  obtain ⟨_, _, _, _, _, _, _, hpairs⟩ := basis.carrier_interval CompareTy.var ModExpr.var
    (by simpa only [CompareTy.subst_id] using hheads) (fun _ _ _ _ => rfl)
  simp only [CompareTy.subst_id] at hpairs
  exact basis.theoryAt_of_modal basisAtom headAtom modeAtom coordinate world (booleanValue f)
    (booleanValue_join f) (booleanValue_meet f) hh hb
    (fun a m hp => model_boolean_modal hmodel (hpairs (a, m) hp).1 (hlabels (a, m) hp) hm)

theorem prepare_forms {basis : Basis} {input : List (CompareTy × CompareTy)} {bounds : List Bound}
    (h : prepare basis input = some bounds) :
    ∀pair∈input, LatticeForm basis.types pair.1 ∧ LatticeForm basis.types pair.2 := by
  have hs := prepare_spec h
  clear h
  induction hs with
  | nil => simp
  | cons hpair hrest ih =>
    exact List.forall_mem_cons.mpr ⟨⟨(ComparisonLatticeCompiler.compile_polynomial hpair.1).1,
      (ComparisonLatticeCompiler.compile_polynomial hpair.2).1⟩, ih⟩

theorem basis_representable {Δ : Bounds} {shape : ComparisonShape} (basis : Basis)
    (hheads : ∀t∈basis.heads, Representable Δ shape t) :
    ∀t∈basis.types, Representable Δ shape t := by
  obtain ⟨_, _, _, _, _, _, htypes, _⟩ := basis.carrier_interval CompareTy.var ModExpr.var
    (by simpa only [CompareTy.subst_id] using hheads) (fun _ _ _ _ => rfl)
  simp only [CompareTy.subst_id] at htypes
  exact fun t ht => (htypes t ht).1

theorem compile_semantics {fuel basis input bounds output basisAtom headAtom modeAtom coordinate}
    (hp : prepare basis input = some bounds)
    (hc : compile fuel basis basisAtom headAtom modeAtom coordinate bounds = .success output)
    (value : CompareTy → Bool)
    (hj : ∀a b, value (.join a b) = (value a || value b))
    (hm : ∀a b, value (.meet a b) = (value a && value b))
    (world : Nat → Bool)
    (hb : ∀i (hi : i < basis.types.length), world (basisAtom i) = value basis.types[i]) :
    CNFHolds world output ↔
      (basis.theoryAt basisAtom headAtom modeAtom coordinate).eval world = true ∧
      ∀pair∈input, value pair.1 = true → value pair.2 = true := by
  rw [compile_correct hc, prepare_value hp value hj hm hb]

theorem compile_observer {Δ : Bounds} {shape : ComparisonShape}
    {f : LatticeHom (Order Δ shape) Bool} {labels : List (GuardedMode Δ)}
    {coordinate : Coordinate} {η : ModVar → Mode}
    (hmodel : ComparisonStructuralAlignment.Model f labels coordinate η)
    {fuel : Nat} {basis : Basis} {input : List (CompareTy × CompareTy)} {bounds : List Bound} {output : CNF}
    (hp : prepare basis input = some bounds)
    {basisAtom headAtom modeAtom : Nat → Nat} {world : Nat → Bool}
    (hc : compile fuel basis basisAtom headAtom modeAtom coordinate bounds = .success output)
    (hheads : ∀t∈basis.heads, Representable Δ shape t)
    (hlabels : ∀p∈basis.modalPairs, ∃m∈labels, m.expression = p.2)
    (hinput : ∀pair∈input, AlgebraSubtype Δ pair.1 pair.2)
    (hh : ∀i (hi : i < basis.heads.length), world (headAtom i) = booleanValue f basis.heads[i])
    (hb : ∀i (hi : i < basis.types.length), world (basisAtom i) = booleanValue f basis.types[i])
    (hm : ∀i, world (modeAtom i) = encodeModes η i) :
    CNFHolds world output := by
  apply (compile_semantics hp hc (booleanValue f) (booleanValue_join f) (booleanValue_meet f) world hb).mpr
  refine ⟨model_basis_theoryAt hmodel basis hheads hlabels hh hb hm, ?_⟩
  intro pair hpair hleft
  have hforms := prepare_forms hp pair hpair
  have ha := ComparisonStructuralLattice.lattice_representable (basis_representable basis hheads) hforms.1
  have hd := ComparisonStructuralLattice.lattice_representable (basis_representable basis hheads) hforms.2
  rw [booleanValue_represented f _ ha] at hleft
  rw [booleanValue_represented f _ hd]
  exact observer_mono f (a := represented ha) (b := represented hd) (hinput pair hpair) hleft

theorem run_spec {fuel basis basisAtom headAtom modeAtom coordinate input output}
    (h : run fuel basis basisAtom headAtom modeAtom coordinate input = .success output) :
    ∃bounds, prepare basis input = some bounds ∧
      compile fuel basis basisAtom headAtom modeAtom coordinate bounds = .success output := by
  cases hp : prepare basis input <;> simp [run, hp] at h
  exact ⟨_, rfl, h⟩

theorem run_complete {basis : Basis} {input : List (CompareTy × CompareTy)}
    (h : ∀pair∈input, LatticeForm basis.types pair.1 ∧ LatticeForm basis.types pair.2)
    (basisAtom headAtom modeAtom : Nat → Nat) (coordinate : Coordinate) :
    ∃threshold output, ∀fuel≥threshold,
      run fuel basis basisAtom headAtom modeAtom coordinate input = .success output := by
  obtain ⟨bounds, hp⟩ := prepare_complete h
  obtain ⟨threshold, output, hc⟩ := compile_complete basis basisAtom headAtom modeAtom coordinate bounds
  exact ⟨threshold, output, fun fuel hf => by simp only [run, hp]; exact hc fuel hf⟩

theorem run_semantics {fuel basis input output basisAtom headAtom modeAtom coordinate}
    (h : run fuel basis basisAtom headAtom modeAtom coordinate input = .success output)
    (value : CompareTy → Bool)
    (hj : ∀a b, value (.join a b) = (value a || value b))
    (hm : ∀a b, value (.meet a b) = (value a && value b))
    (world : Nat → Bool)
    (hb : ∀i (hi : i < basis.types.length), world (basisAtom i) = value basis.types[i]) :
    CNFHolds world output ↔
      (basis.theoryAt basisAtom headAtom modeAtom coordinate).eval world = true ∧
      ∀pair∈input, value pair.1 = true → value pair.2 = true := by
  obtain ⟨bounds, hp, hc⟩ := run_spec h
  exact compile_semantics hp hc value hj hm world hb

theorem run_observer {Δ : Bounds} {shape : ComparisonShape}
    {f : LatticeHom (Order Δ shape) Bool} {labels : List (GuardedMode Δ)}
    {coordinate : Coordinate} {η : ModVar → Mode}
    (hmodel : ComparisonStructuralAlignment.Model f labels coordinate η)
    {fuel : Nat} {basis : Basis} {input : List (CompareTy × CompareTy)} {output : CNF}
    {basisAtom headAtom modeAtom : Nat → Nat} {world : Nat → Bool}
    (h : run fuel basis basisAtom headAtom modeAtom coordinate input = .success output)
    (hheads : ∀t∈basis.heads, Representable Δ shape t)
    (hlabels : ∀p∈basis.modalPairs, ∃m∈labels, m.expression = p.2)
    (hinput : ∀pair∈input, AlgebraSubtype Δ pair.1 pair.2)
    (hh : ∀i (hi : i < basis.heads.length), world (headAtom i) = booleanValue f basis.heads[i])
    (hb : ∀i (hi : i < basis.types.length), world (basisAtom i) = booleanValue f basis.types[i])
    (hm : ∀i, world (modeAtom i) = encodeModes η i) :
    CNFHolds world output := by
  obtain ⟨bounds, hp, hc⟩ := run_spec h
  exact compile_observer hmodel hp hc hheads hlabels hinput hh hb hm

end ModalityInference.ComparisonStructuralNode
