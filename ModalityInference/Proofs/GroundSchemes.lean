import ModalityInference.Proofs.GroundInstantiation
import ModalityInference.Proofs.GroundAssignment

/-! The resource interpretation of a scheme depends only on its free identifiers.
Rebasing ground instances preserves the full quantified-domain condition. -/
namespace ModalityInference

theorem Scheme.mem_freeTypes_iff (s : Scheme) (v : TypeVar) :
    v ∈ s.freeTypes ↔ (v ∈ s.body.typeVars ∨ v ∈ s.bounds.typeVars) ∧
      v ∉ s.typeParams.map TypeVar.flex := by
  cases v <;> simp [Scheme.freeTypes]

theorem Scheme.mem_freeModes_iff (s : Scheme) (v : ModVar) :
    v ∈ s.freeModes ↔ (v ∈ s.body.modVars ∨ v ∈ s.bounds.modVars) ∧
      v ∉ s.modParams.map ModVar.flex := by
  cases v <;> simp [Scheme.freeModes]

/-- Preserve the ambient assignment except at the scheme's quantified identifiers. -/
def Scheme.rebase (s : Scheme) (ambient values : GroundAssignment) : GroundAssignment :=
  ⟨fun (v : TypeVar) => if v ∈ (s.typeParams.map TypeVar.flex).toFinset then values.types v else ambient.types v,
   fun (v : ModVar) => if v ∈ (s.modParams.map ModVar.flex).toFinset then values.modes v else ambient.modes v⟩

theorem GroundInstantiates.rebase_agrees {ρ η ξ : GroundAssignment} {s : Scheme}
    (h : GroundInstantiates η s ξ)
    (ht : ∀ v ∈ s.freeTypes, ρ.types v = η.types v)
    (hm : ∀ v ∈ s.freeModes, ρ.modes v = η.modes v) :
    (∀ v ∈ s.body.typeVars ∪ s.bounds.typeVars, (s.rebase ρ ξ).types v = ξ.types v) ∧
    (∀ v ∈ s.body.modVars ∪ s.bounds.modVars, (s.rebase ρ ξ).modes v = ξ.modes v) := by
  refine ⟨?_, ?_⟩
  all_goals intro v hv
  all_goals simp only [Scheme.rebase]
  all_goals split_ifs with hq
  all_goals first
    | rfl
    | exact let hn := fun hx => hq (List.mem_toFinset.mpr hx)
      (ht v ((s.mem_freeTypes_iff v).mpr ⟨Finset.mem_union.mp hv, hn⟩)).trans (h.1 v hn).symm
    | exact let hn := fun hx => hq (List.mem_toFinset.mpr hx)
      (hm v ((s.mem_freeModes_iff v).mpr ⟨Finset.mem_union.mp hv, hn⟩)).trans (h.2.1 v hn).symm

theorem GroundInstantiates.rebase {ρ η ξ : GroundAssignment} {s : Scheme}
    (h : GroundInstantiates η s ξ)
    (ht : ∀ v ∈ s.freeTypes, ρ.types v = η.types v)
    (hm : ∀ v ∈ s.freeModes, ρ.modes v = η.modes v) :
    GroundInstantiates ρ s (s.rebase ρ ξ) ∧
      s.body.realize (s.rebase ρ ξ) = s.body.realize ξ := by
  have hr := h.rebase_agrees ht hm
  exact ⟨⟨fun v hv => if_neg (fun hq => hv (List.mem_toFinset.mp hq)),
    fun v hv => if_neg (fun hq => hv (List.mem_toFinset.mp hq)),
    (GroundModels.congr s.bounds
      (fun v hv => hr.1 v (Finset.mem_union.mpr (.inr hv)))
      (fun v hv => hr.2 v (Finset.mem_union.mpr (.inr hv)))).mpr h.2.2⟩,
    s.body.realize_congr
      (fun v hv => hr.1 v (Finset.mem_union.mpr (.inl hv)))
      (fun v hv => hr.2 v (Finset.mem_union.mpr (.inl hv)))⟩

theorem ResourceSchemeInterpretation.ambient_congr {ρ η : GroundAssignment} {w s v reserved}
    (h : ResourceSchemeInterpretation ρ w s v reserved)
    (ht : ∀ x ∈ s.freeTypes, ρ.types x = η.types x)
    (hm : ∀ x ∈ s.freeModes, ρ.modes x = η.modes x) :
    ResourceSchemeInterpretation η w s v reserved :=
  ⟨h.1, fun ξ t hξ hx =>
    let ⟨hr, hb⟩ := hξ.rebase ht hm
    h.2 (s.rebase ρ ξ) t hr (hb.trans hx)⟩

end ModalityInference
