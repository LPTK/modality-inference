import ModalityInference.Proofs.ComparisonGuardedEndpointQueries
import ModalityInference.Proofs.ComparisonPreparedScalar

namespace ModalityInference.ComparisonJointModes
open ModalSynthesis

theorem image_atom_origin {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    {σ : Nat → Bool} {v w : Nat} (hv : v ∈ flex)
    (h : w ∈ (image side (prepare side flex locality other) σ v).atoms) :
    2*w ∈ CNFPropagation.atoms (if side v then locality else other) := by
  obtain ⟨u,hu,hw⟩ := SymbolicCNF.substitute_atoms h
  have hup : 2*v ∈ pivots side (side v) flex := mem_pivots.mpr ⟨hv,rfl⟩
  rw [prepare_part] at hu
  obtain ⟨hua,_⟩ := SymbolicCNF.solve_atoms hup hu
  have hus : selector u = false := by
    cases hs : selector u with
    | false => rfl
    | true => simp [decode,hs,BoolExpr.atoms] at hw
  have hwu : w=u/2 := by simpa [decode,hus,BoolExpr.atoms] using hw
  have hu0 : u%2=0 := by simpa [selector] using hus
  have he : 2*w=u := by omega
  simpa only [he] using hua

end ModalityInference.ComparisonJointModes

namespace ModalityInference.ComparisonWorldModes
open ComparisonWorldClauses

theorem component_even_origin {side : Nat → Bool} {axis : Bool}
    {entries : List (Nat × Clause)} {v : Nat}
    (h : 2*v ∈ CNFPropagation.atoms (component side axis entries)) :
    ∃entry∈entries, ∃polarity, (v,polarity)∈entry.2 := by
  obtain ⟨c,hc,polarity,hp⟩ := CNFPropagation.mem_atoms.mp h
  obtain ⟨⟨entry,i⟩,hei,rfl⟩ := List.mem_map.mp hc
  rcases List.mem_append.mp hp with hp|hp
  · simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp
    rcases hp with ⟨he,_⟩|⟨he,_⟩
    · simp only [worldConstant] at he
      omega
    · simp only [axisConstant] at he
      omega
  · obtain ⟨⟨w,p⟩,hw,he⟩ := List.mem_map.mp hp
    have hvw : v=w := by have := congrArg Prod.fst he; dsimp at this; omega
    subst w
    exact ⟨entry,List.fst_mem_of_mem_zipIdx hei,p,(List.mem_filter.mp hw).1⟩

theorem scalarBlocks_origin {cs : List WorldClause} {entry : Nat × Clause}
    (he : entry∈scalarBlocks cs) {v : Nat} {polarity : Bool}
    (hv : (v,polarity)∈entry.2) :
    ∃c∈cs, ∃b, b≠0 ∧ (b,(v,polarity))∈c := by
  obtain ⟨⟨c,i⟩,hci,he⟩ := List.mem_flatMap.mp he
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp he
  have hb0 : b≠0 := by simpa using (List.mem_filter.mp hb).2
  obtain ⟨⟨d,literal⟩,hl,hm⟩ := List.mem_filterMap.mp hv
  split at hm
  next he =>
    cases Option.some.inj hm
    exact ⟨c,List.fst_mem_of_mem_zipIdx hci,b,hb0,by simpa [show d=b from he] using hl⟩
  next => contradiction

end ModalityInference.ComparisonWorldModes

namespace ModalityInference.ComparisonWorldModes
open ComparisonWorldClauses

theorem witness_atom_origin {side : Nat → Bool} {flex : List Nat}
    {cs : List WorldClause} {selectors : Nat → Bool} {v w : Nat}
    (hv : v∈flex) (hw : w∈((witness side flex cs selectors).substitute v).atoms) :
    ∃c∈cs, ∃b, b≠0 ∧ ∃polarity, (b,(w,polarity))∈c := by
  change w∈((ModalSynthesis.witness side flex
    (ComparisonJointModes.prepare side flex
      (component side true (scalarBlocks cs))
      (component side false (scalarBlocks cs))) selectors).substitute v).atoms at hw
  rw [ComparisonJointModes.witness_substitute] at hw
  have ho := ComparisonJointModes.image_atom_origin hv hw
  have hpart : 2*w∈CNFPropagation.atoms (component side (side v) (scalarBlocks cs)) := by
    cases he : side v <;> simpa [he] using ho
  obtain ⟨entry,he,polarity,hp⟩ := component_even_origin hpart
  obtain ⟨c,hc,b,hb,hp⟩ := scalarBlocks_origin he hp
  exact ⟨c,hc,b,hb,polarity,hp⟩

/-- Scalar components introduce no input names beyond their original blocks. -/
def Supported (P : Nat → Prop) (cs : List WorldClause) : Prop :=
  ∀c∈cs, ∀b v polarity, b≠0 → (b,(v,polarity))∈c → P v

theorem witness_supported {side : Nat → Bool} {flex : List Nat}
    {cs : List WorldClause} {selectors : Nat → Bool} {P : Nat → Prop}
    (hs : Supported P cs) {v w : Nat} (hv : v∈flex)
    (hw : w∈((witness side flex cs selectors).substitute v).atoms) : P w := by
  obtain ⟨c,hc,b,hb,polarity,hp⟩ := witness_atom_origin hv hw
  exact hs c hc b w polarity hb hp

end ModalityInference.ComparisonWorldModes

namespace ModalityInference.SymbolicModes.Elimination

theorem mode_variables {flex : List Nat} {s : Elimination flex} {v : ModVar} {m : ModExpr}
    (hm : s.mode v=some m) {w : ModVar} (hw : w∈m.vars) :
    ∃axis<3, ∃i∈(s.substitute (v.atomIndex axis)).atoms, atomVariable i=w := by
  cases hl : reify .locality (s.substitute (v.atomIndex 0)) <;>
    cases ha : reify .affinity (s.substitute (v.atomIndex 1)) <;>
    cases hu : reify .uniqueness (s.substitute (v.atomIndex 2)) <;>
    simp [mode,hl,ha,hu] at hm
  cases hm
  simp only [ModExpr.vars,Finset.mem_union] at hw
  rcases hw with hw|hw|hw
  · exact ⟨0,by decide,reify_variables hl w hw⟩
  · exact ⟨1,by decide,reify_variables ha w hw⟩
  · exact ⟨2,by decide,reify_variables hu w hw⟩

end ModalityInference.SymbolicModes.Elimination

namespace ModalityInference.ComparisonPreparedScalar

theorem assemble_world_supported {p : SchemePreparation.Prepared}
    {cs : List ComparisonWorldClauses.WorldClause} {selectors : Nat → Bool}
    {action : Substitution} {P : ModVar → Prop}
    (ha : assemble p (ComparisonWorldModes.witness ModalSynthesis.locality
      (flexibleAtoms p) cs selectors)=some action)
    (hs : ComparisonWorldModes.Supported (fun i=>P (SymbolicModes.atomVariable i)) cs)
    {v w : ModVar} (hv : P v) (hw : w∈(action.mode v).vars) : P w := by
  cases v with
  | rigid n =>
    have he : w=ModVar.rigid n := by simpa [Substitution.mode,ModExpr.vars] using hw
    simpa only [he] using hv
  | flex n =>
    by_cases hn : n∈modeIds p
    · have hm := SymbolicSchemeModes.assemble_action ha
        (SchemeModeSynthesis.parameters_lookup hn)
      obtain ⟨axis,haxis,i,hi,he⟩ := SymbolicModes.Elimination.mode_variables hm hw
      have hflex : (ModVar.flex n).atomIndex axis ∈ flexibleAtoms p :=
        (SchemeModeSynthesis.mem_atoms_flex haxis).mpr hn
      simpa only [he] using ComparisonWorldModes.witness_supported hs hflex hi
    · rw [assemble_fixed ha (by intro key hk he; cases he; exact hn hk)] at hw
      have he : w=ModVar.flex n := by simpa [ModExpr.vars] using hw
      simpa only [he] using hv

end ModalityInference.ComparisonPreparedScalar
