import ModalityInference.Proofs.ComparisonLayoutWorlds

namespace ModalityInference.ComparisonLayoutWorlds
open ComparisonSignedEndpoints ComparisonSignedObservation ComparisonStructuralLayout

theorem decode_injective : Function.Injective decode := by
  intro a b he
  by_cases ha : (location a).2%4=2 <;> by_cases hb : (location b).2%4=2
  · simp only [decode,ha,hb,ite_true] at he
    have hroute:=routeCode_injective (Nat.add_right_cancel (congrArg Prod.fst he))
    have hslot : (location a).2=(location b).2 := by
      have hquot:=congrArg Prod.snd he
      omega
    have hloc : location a=location b := Prod.ext hroute hslot
    exact (location_inverse a).symm.trans (hloc ▸ location_inverse b)
  · have he':=(congrArg Prod.fst he)
    simp [decode,ha,hb] at he'
  · have he':=(congrArg Prod.fst he)
    simp [decode,ha,hb] at he'
  · exact congrArg Prod.snd (by simpa only [decode,ha,hb,ite_false] using he : (0,a)=(0,b))

theorem rawValue_surjective (world : Nat→Bool) :
    ∃blocks,ComparisonSignedWorlds.rawValue decode id id blocks=world := by
  classical
  refine ⟨fun i j=>world (Function.invFun decode (i,j)),?_⟩
  funext v
  simp only [ComparisonSignedWorlds.rawValue,ComparisonWorldClauses.shared]
  split <;> exact congrArg world (Function.leftInverse_invFun decode_injective v)

end ModalityInference.ComparisonLayoutWorlds
