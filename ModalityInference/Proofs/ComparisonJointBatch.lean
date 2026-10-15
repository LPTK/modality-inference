import ModalityInference.ComparisonJointBatch
import ModalityInference.Proofs.ComparisonJointReindex
import ModalityInference.Proofs.ComparisonJointAssemblyGroup
import ModalityInference.Proofs.ComparisonJointAssemblyReification

namespace ModalityInference.ComparisonJointBatch

open ComparisonPropagation ComparisonJointGuarded

@[simp] theorem project_embed (size : Entry → Nat) (entries : List Entry)
    (i : Fin entries.length) (j : Fin (size entries[i])) :
    project size entries i (embed size entries i j).val = j.val := by
  simp only [project, embed]
  split <;> omega

theorem project_lt {size : Entry → Nat} {entries : List Entry} {i : Fin entries.length}
    (hne : 0 < size entries[i]) (v : Nat) : project size entries i v < size entries[i] := by
  unfold project
  split <;> omega

def SolutionCorrect (side : Nat → Bool) (entries : List Entry) (minimumModes : Nat) (scalar : CNF)
    (result : Result entries flex) : Prop :=
  result.solution.types.Polynomial (total Entry.heads entries) ∧
    ModalSynthesis.Uniform side flex (fun world v => (result.solution.modes.substitute v).eval world) ∧
    Holds (fun i => result.solution.constants[i]) result.solution.types
      (fun world v => (result.solution.modes.substitute v).eval world)
      (compile side entries minimumModes scalar)

theorem run_solution {fuel minimumModes : Nat} {side : Nat → Bool} {flex : List Nat}
    {entries : List Entry} {scalar : CNF} {result : Result entries flex}
    (h : run fuel side flex entries minimumModes scalar = .success result) :
    ComparisonJointGuarded.run fuel side flex (compile side entries minimumModes scalar) =
      .success result.solution := by
  unfold run at h
  cases hs : ComparisonJointGuarded.run fuel side flex (compile side entries minimumModes scalar) with
  | exhausted | rejected => simp [hs, bind, RunResult.bind] at h
  | success solution =>
    simp only [hs, bind, RunResult.bind, pure, RunResult.success.injEq] at h
    cases h
    rfl

theorem run_sound {fuel minimumModes : Nat} {side : Nat → Bool} {flex : List Nat}
    {entries : List Entry} {scalar : CNF} {result : Result entries flex}
    (h : run fuel side flex entries minimumModes scalar = .success result) :
    SolutionCorrect side entries minimumModes scalar result :=
  ComparisonJointGuarded.run_sound (run_solution h)

theorem local_solution_correct {minimumModes : Nat} {side : Nat → Bool} {flex : List Nat}
    {entries : List Entry} {scalar : CNF} {result : Result entries flex}
    (h : SolutionCorrect side entries minimumModes scalar result) (i : Fin entries.length)
    (hne : 0 < entries[i].heads) :
    ComparisonJointAssembly.SolutionCorrect side entries[i].count entries[i].heads entries[i].input
      minimumModes (localSolution entries result i) := by
  refine ⟨ComparisonJointReindex.store_polynomial h.1 (fun v _ => project_lt hne v), h.2.1, ?_⟩
  have hc : Holds (fun j => result.solution.constants[j]) result.solution.types
      (fun world v => (result.solution.modes.substitute v).eval world)
      (ComparisonJointReindex.clauses (embed Entry.heads entries i) (embed Entry.count entries i)
        (embed constants entries i)
        (ComparisonJointAssembly.compile side entries[i].count entries[i].heads entries[i].input minimumModes)) := by
    intro headWorld modeWorld c hmem
    exact h.2.2 headWorld modeWorld c (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hmem⟩))
  have hl := ComparisonJointReindex.holds_project (project_embed Entry.heads entries i)
    (embed Entry.count entries i) (embed constants entries i)
    (fun j => result.solution.constants[j]) result.solution.types
    (fun world v => (result.solution.modes.substitute v).eval world) _ hc
  convert hl using 1
  funext j
  exact Vector.getElem_ofFn j.isLt

theorem run_local_correct {fuel minimumModes : Nat} {side : Nat → Bool} {flex : List Nat}
    {entries : List Entry} {scalar : CNF} {result : Result entries flex}
    (h : run fuel side flex entries minimumModes scalar = .success result) (i : Fin entries.length)
    (hne : 0 < entries[i].heads) :
    ComparisonJointAssembly.SolutionCorrect side entries[i].count entries[i].heads entries[i].input
      minimumModes (localSolution entries result i) :=
  local_solution_correct (run_sound h) i hne

theorem scalar_correct {minimumModes : Nat} {side : Nat → Bool} {flex : List Nat}
    {entries : List Entry} {scalar : CNF} {result : Result entries flex}
    (h : SolutionCorrect side entries minimumModes scalar result) :
    ∀ world, CNFHolds (fun v => (result.solution.modes.substitute v).eval world) scalar := by
  apply (ComparisonJointAssembly.scalarClauses_correct _ _ _ _).mp
  intro headWorld modeWorld c hc
  exact h.2.2 headWorld modeWorld c (List.mem_append_right _ hc)

theorem run_scalar {fuel minimumModes : Nat} {side : Nat → Bool} {flex : List Nat}
    {entries : List Entry} {scalar : CNF} {result : Result entries flex}
    (h : run fuel side flex entries minimumModes scalar = .success result) :
    ∀ world, CNFHolds (fun v => (result.solution.modes.substitute v).eval world) scalar :=
  scalar_correct (run_sound h)

@[simp] theorem localSolution_modes (entries : List Entry) (result : Result entries flex)
    (i : Fin entries.length) : (localSolution entries result i).modes = result.solution.modes := rfl

@[simp] theorem localResult_modes (side : Nat → Bool) (entries : List Entry)
    (result : Result entries flex) (i : Fin entries.length) (minimumModes : Nat) :
    (localResult side entries result i minimumModes).solution.modes = result.solution.modes := rfl

theorem run_mode_atoms {fuel minimumModes : Nat} {side : Nat → Bool} {flex : List Nat}
    {entries : List Entry} {scalar : CNF} {result : Result entries flex}
    (h : run fuel side flex entries minimumModes scalar = .success result)
    {v w : Nat} (hw : w ∈ (result.solution.modes.substitute v).atoms) :
    side w = side v ∧ (v ∈ flex → w ∉ flex) :=
  ComparisonJointAssemblyReification.guarded_run_modes_atoms (run_solution h) hw

theorem run_complete {side : Nat → Bool} {flex : List Nat} {entries : List Entry}
    {minimumModes : Nat} {scalar : CNF}
    (h : ∃ choice store, store.Polynomial (total Entry.heads entries) ∧ ∃ strategy,
      ModalSynthesis.Uniform side flex strategy ∧
        Holds choice store strategy (compile side entries minimumModes scalar)) :
    ∃ n, ∀ fuel ≥ n, ∃ result, run fuel side flex entries minimumModes scalar = .success result := by
  obtain ⟨n, hn⟩ := ComparisonJointGuarded.run_complete h
  refine ⟨n, ?_⟩
  intro fuel hf
  obtain ⟨solution, hs⟩ := hn fuel hf
  exact ⟨⟨solution⟩, by simp [run, hs, bind, RunResult.bind, pure]⟩

theorem run_stable {n minimumModes : Nat} {side : Nat → Bool} {flex : List Nat}
    {entries : List Entry} {scalar : CNF} {result : RunResult (Result entries flex)}
    (hne : result ≠ .exhausted) (h : run n side flex entries minimumModes scalar = result) :
    ∀ fuel ≥ n, run fuel side flex entries minimumModes scalar = result := by
  intro fuel hf
  cases hs : ComparisonJointGuarded.run n side flex (compile side entries minimumModes scalar) with
  | exhausted => exact False.elim (hne (by simpa [run, hs, bind, RunResult.bind] using h.symm))
  | rejected message =>
    have he := ComparisonJointGuarded.run_stable (by simp) hs fuel hf
    simpa [run, he, hs, bind, RunResult.bind] using h
  | success solution =>
    have he := ComparisonJointGuarded.run_stable (by simp) hs fuel hf
    simpa [run, he, hs, bind, RunResult.bind, pure] using h

theorem run_terminates (side : Nat → Bool) (flex : List Nat) (entries : List Entry)
    (minimumModes : Nat := 0) (scalar : CNF := []) :
    ∃ n, ∀ fuel ≥ n, run fuel side flex entries minimumModes scalar ≠ .exhausted := by
  obtain ⟨n, hn⟩ := ComparisonJointGuarded.run_terminates side flex (compile side entries minimumModes scalar)
  refine ⟨n, ?_⟩
  intro fuel hf
  cases hs : ComparisonJointGuarded.run fuel side flex (compile side entries minimumModes scalar) with
  | exhausted => exact False.elim (hn fuel hf hs)
  | rejected | success => simp [run, hs, bind, RunResult.bind, pure]

end ModalityInference.ComparisonJointBatch
