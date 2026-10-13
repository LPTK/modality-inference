import ModalityInference.Proofs.Projection
import ModalityInference.Proofs.SyntacticEquality
import ModalityInference.Proofs.VariableOccurrences
import ModalityInference.Constraints

/-! Correctness of the finite consistency search and its returned witness. -/
namespace ModalityInference

theorem ClauseHolds.filter_assigned {σ : Nat → Bool} {v b} (hv : σ v = b) (c : Clause) :
    ClauseHolds σ (c.filter (fun lit => lit != (v, !b))) ↔ ClauseHolds σ c := by
  constructor
  · rintro ⟨w, p, hp, he⟩
    exact ⟨w, p, (List.mem_filter.mp hp).1, he⟩
  · rintro ⟨w, p, hp, he⟩
    refine ⟨w, p, List.mem_filter.mpr ⟨hp, ?_⟩, he⟩
    apply bne_iff_ne.mpr
    rintro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    cases b <;> simp_all

theorem assignCNF_correct {σ : Nat → Bool} {v b} (hv : σ v = b) (cs : CNF) :
    CNFHolds σ (assignCNF cs v b) ↔ CNFHolds σ cs := by
  constructor
  · intro h c hc
    by_cases hvb : (v, b) ∈ c
    · exact ⟨v, b, hvb, hv⟩
    · apply (ClauseHolds.filter_assigned hv c).mp
      exact h _ (List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, by simpa using hvb⟩, rfl⟩)
  · intro h c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (ClauseHolds.filter_assigned hv d).mpr (h d (List.mem_filter.mp hd).1)

abbrev CNF.atoms (cs : CNF) : List Nat := cs.flatMap (List.map Prod.fst)

theorem CNF.mem_atoms {cs : CNF} {v} :
    v ∈ cs.atoms ↔ ∃ c ∈ cs, ∃ b, (v, b) ∈ c := by
  simp [CNF.atoms, List.mem_flatMap, List.mem_map, Prod.exists]

theorem assignCNF_atoms {cs v b w} (hw : w ∈ (assignCNF cs v b).atoms) :
    w ∈ cs.atoms ∧ w ≠ v := by
  obtain ⟨c, hc, p, hp⟩ := CNF.mem_atoms.mp hw
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simp at hd hp
  exact ⟨CNF.mem_atoms.mpr ⟨d, hd.1, p, hp.1⟩,
    fun h => hd.2 (by simpa [h, hp.2 h] using hp.1)⟩

theorem CNF.atoms_ne_nil {cs : CNF} (hcs : cs ≠ []) (hc : [] ∉ cs) : cs.atoms ≠ [] := by
  cases cs with
  | nil => contradiction
  | cons c cs => cases c <;> simp_all [CNF.atoms]

theorem CNF.minimum_mem {cs : CNF} (hcs : cs.atoms ≠ []) :
    cs.atoms.foldl min (cs.atoms.headD 0) ∈ cs.atoms := by
  generalize he : cs.atoms = atoms at *
  cases atoms with
  | nil => contradiction
  | cons v vs =>
    simpa only [List.headD, List.foldl, min_self] using
      (List.min?_mem (xs := v :: vs) (a := vs.foldl min v) rfl)

theorem CNF.find_unit_mem {cs : CNF} {lit : Literal}
    (h : cs.findSome? (fun c => match c with | [x] => some x | _ => none) = some lit) :
    [lit] ∈ cs := by
  obtain ⟨c, hc, he⟩ := List.exists_of_findSome?_eq_some h
  split at he <;> cases he
  exact hc

def booleanValuation (σ : List (Nat × Bool)) (v : Nat) : Bool := (σ.lookup v).getD false

theorem assignCNF_recover {cs v b σ result} (hv : v ∈ cs.atoms)
    (hc : CNFHolds (booleanValuation result) (assignCNF cs v b))
    (hf : ∀ w, w ∉ (assignCNF cs v b).atoms → result.lookup w = ((v,b) :: σ).lookup w) :
    CNFHolds (booleanValuation result) cs ∧
      ∀ w, w ∉ cs.atoms → result.lookup w = σ.lookup w := by
  have hn : v ∉ (assignCNF cs v b).atoms := fun h => (assignCNF_atoms h).2 rfl
  have hval : booleanValuation result v = b := by simp [booleanValuation, hf v hn]
  refine ⟨(assignCNF_correct hval cs).mp hc, ?_⟩
  intro w hw
  have hwv : (w == v) = false := by simpa using (show w ≠ v from fun h => hw (h ▸ hv))
  simpa only [List.lookup_cons, hwv] using hf w (fun h => hw (assignCNF_atoms h).1)

theorem searchCNF_sound {fuel todo result} (h : searchCNF fuel todo = .success result) :
    ∃ cs σ, (cs, σ) ∈ todo ∧ CNFHolds (booleanValuation result) cs ∧
      ∀ v, v ∉ cs.atoms → result.lookup v = σ.lookup v := by
  induction fuel generalizing todo
  case zero => cases h
  case succ fuel ih =>
    cases todo with
    | nil => cases h
    | cons node todo =>
      obtain ⟨cs, σ⟩ := node
      simp only [searchCNF] at h
      split at h
      · obtain ⟨ds, τ, hm, hd, hf⟩ := ih h
        exact ⟨ds, τ, List.mem_cons_of_mem _ hm, hd, hf⟩
      · next hfalse =>
        split at h
        · next hempty =>
          have hcs : cs = [] := by simpa using hempty
          subst cs
          cases h
          exact ⟨[], result, by simp, by simp [CNFHolds], fun _ _ => rfl⟩
        · next hnonempty =>
          split at h
          · next v b he =>
            have hv : v ∈ cs.atoms :=
              CNF.mem_atoms.mpr ⟨[(v,b)], CNF.find_unit_mem he, b, by simp⟩
            obtain ⟨ds, τ, hm, hd, hf⟩ := ih h
            simp only [List.mem_cons, Prod.mk.injEq] at hm
            rcases hm with ⟨rfl, rfl⟩ | hm
            · exact ⟨cs, σ, by simp, assignCNF_recover hv hd hf⟩
            · exact ⟨ds, τ, List.mem_cons_of_mem _ hm, hd, hf⟩
          · have hv : cs.atoms.foldl min (cs.atoms.headD 0) ∈ cs.atoms :=
              CNF.minimum_mem (CNF.atoms_ne_nil (by simpa using hnonempty)
                (fun hc => hfalse (List.any_eq_true.mpr ⟨[], hc, rfl⟩)))
            obtain ⟨ds, τ, hm, hd, hf⟩ := ih h
            simp only [List.mem_cons, Prod.mk.injEq] at hm
            rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
            · exact ⟨cs, σ, by simp, assignCNF_recover hv hd hf⟩
            · exact ⟨cs, σ, by simp, assignCNF_recover hv hd hf⟩
            · exact ⟨ds, τ, List.mem_cons_of_mem _ hm, hd, hf⟩

theorem searchCNF_single_sound {fuel cs σ result}
    (h : searchCNF fuel [(cs, σ)] = .success result) :
    CNFHolds (booleanValuation result) cs := by
  obtain ⟨ds, τ, hm, hd, _⟩ := searchCNF_sound h
  obtain ⟨rfl, rfl⟩ : ds = cs ∧ τ = σ := by simpa using hm
  exact hd

private theorem lookup_map_self {α β : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (f : α → β) {v} (hv : v ∈ xs) :
    (xs.map (fun w => (w, f w))).lookup v = some (f v) := by
  induction xs with
  | nil => contradiction
  | cons w xs ih =>
    by_cases h : v = w
    · subst w; simp
    · have he : (v == w) = false := by simpa using h
      simpa only [List.map_cons, List.lookup_cons, he] using
        ih ((List.mem_cons.mp hv).resolve_left h)

theorem satisfiableModes_witness {fuel cs result}
    (h : satisfiableModes fuel cs = .success result) :
    ∃ η, ModeModels cs η ∧ ∀ v ∈ cs.modVars, result.lookup v = some (η v) := by
  unfold satisfiableModes at h
  cases hc : toCNF fuel true (boundsModeFormula cs) <;>
    simp [hc, bind, RunResult.bind] at h
  rename_i clauses
  cases hs : searchCNF fuel [(clauses, [])] <;> simp [hs, pure] at h
  rename_i σ
  subst result
  refine ⟨projectedModes (booleanValuation σ), ?_, ?_⟩
  · exact (boundsModeFormula_correct _ _).mp ((toCNF_correct hc _).mp (searchCNF_single_sound hs))
  · exact fun v hv => lookup_map_self cs.modeVariables _ ((cs.mem_modeVariables v).mpr hv)

theorem ModeSatisfies.congr (c : Constraint) {η θ : ModVar → Mode}
    (h : ∀ v ∈ c.modVars, η v = θ v) : ModeSatisfies η c ↔ ModeSatisfies θ c := by
  cases c <;> simp only [ModeSatisfies, Constraint.modVars, Finset.mem_union,
    or_imp, forall_and] at *
  case mode a b =>
    simp only [ModExpr.Below,
      a.eval_congr (σ := some ∘ η) (τ := some ∘ θ) (fun v hv => congrArg some (h.1 v hv)),
      b.eval_congr (σ := some ∘ η) (τ := some ∘ θ) (fun v hv => congrArg some (h.2 v hv))]
  case defined a =>
    simp only [ModExpr.WellFormed,
      a.eval_congr (σ := some ∘ η) (τ := some ∘ θ) (fun v hv => congrArg some (h v hv))]

theorem ModeModels.congr (cs : Bounds) {η θ : ModVar → Mode}
    (h : ∀ v ∈ cs.modVars, η v = θ v) : ModeModels cs η ↔ ModeModels cs θ := by
  induction cs <;> simp_all [Bounds.modVars_cons, ModeModels, Finset.mem_union, or_imp, forall_and]
  exact fun _ => ModeSatisfies.congr _ h.1

def ModeAssignment.total (σ : ModeAssignment) (v : ModVar) : Mode :=
  (σ.lookup v).getD Mode.identity

theorem satisfiableModes_sound {fuel cs result}
    (h : satisfiableModes fuel cs = .success result) : ModeModels cs result.total := by
  obtain ⟨η, hη, hv⟩ := satisfiableModes_witness h
  exact (ModeModels.congr cs (fun v hm => by simp [ModeAssignment.total, hv v hm])).mpr hη

theorem solveFrom_mode_witness {fuel nt nm cs result}
    (h : solveFrom fuel nt nm cs = .success result) :
    ModeModels result.bounds result.witness.total := by
  unfold solveFrom at h
  cases hs : runSolver fuel {pending := cs, nextType := nt, nextMode := nm} <;>
    simp [hs, bind, RunResult.bind] at h
  rename_i state
  cases hm : satisfiableModes fuel state.bounds <;> simp [hm, pure] at h
  cases h
  exact satisfiableModes_sound hm

theorem solve_mode_witness {fuel cs result} (h : solve fuel cs = .success result) :
    ModeModels result.bounds result.witness.total := solveFrom_mode_witness h

end ModalityInference
