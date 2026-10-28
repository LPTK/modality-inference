import ModalityInference.Proofs.VariableOccurrences
import ModalityInference.Proofs.ComparisonObserverBoundary

/-! Deterministic occurrence lists have the same support and deduplicated
length as their declarative finite sets. -/
namespace ModalityInference.ComparisonVariableListSupport

open ComparisonObserverBoundary

@[simp] theorem dedup_toFinset {α : Type*} [DecidableEq α] (xs : List α) :
    xs.dedup.toFinset = xs.toFinset :=
  Finset.ext fun x => by simp only [List.mem_toFinset, List.mem_dedup]

@[simp] theorem freeVariables_toFinset (m : ModExpr) : m.freeVariables.toFinset = m.vars :=
  Finset.ext fun v => by simp only [List.mem_toFinset, ModExpr.mem_freeVariables]

@[simp] theorem freeVariables_dedup_length (m : ModExpr) :
    m.freeVariables.dedup.length = m.vars.card := by
  rw [← List.card_toFinset, freeVariables_toFinset]

@[simp] theorem typeModeVariables_toFinset (a : Ty) : a.modeVariables.toFinset = a.modVars :=
  Finset.ext fun v => by simp only [List.mem_toFinset, TypeExpr.mem_modeVariables]

@[simp] theorem typeModeVariables_dedup_length (a : Ty) :
    a.modeVariables.dedup.length = a.modVars.card := by
  rw [← List.card_toFinset, typeModeVariables_toFinset]

@[simp] theorem boundsModeVariables_toFinset (Δ : Bounds) : Δ.modeVariables.toFinset = Δ.modVars :=
  Finset.ext fun v => by simp only [List.mem_toFinset, Bounds.mem_modeVariables]

@[simp] theorem boundsModeVariables_dedup_length (Δ : Bounds) :
    Δ.modeVariables.dedup.length = Δ.modVars.card := by
  rw [← List.card_toFinset, boundsModeVariables_toFinset]

@[simp] theorem typeList_toFinset (a : CompareTy) : (typeList a).toFinset = types a :=
  Finset.ext fun v => by simp only [List.mem_toFinset, mem_typeList]

@[simp] theorem typeList_dedup_length (a : CompareTy) :
    (typeList a).dedup.length = (types a).card := by
  rw [← List.card_toFinset, typeList_toFinset]

@[simp] theorem modeList_toFinset (a : CompareTy) : (modeList a).toFinset = modes a :=
  Finset.ext fun v => by simp only [List.mem_toFinset, mem_modeList]

@[simp] theorem modeList_dedup_length (a : CompareTy) :
    (modeList a).dedup.length = (modes a).card := by
  rw [← List.card_toFinset, modeList_toFinset]

end ModalityInference.ComparisonVariableListSupport
