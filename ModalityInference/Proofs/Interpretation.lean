import ModalityInference.Semantics

/-! Properties of the concrete semantic interpretation, independent of the
deferred fundamental theorem. -/
namespace ModalityInference

@[simp] theorem GroundTy.modal_identity (t : GroundTy) : t.modal Mode.identity = t := by
  cases t <;> simp [GroundTy.modal, Mode.compose, Mode.identity]

theorem ValueInterpretation.global_references {ρ w t ambient v}
    (hv : ValueInterpretation ρ w t ambient v)
    (hg : (t.mode.compose ambient).isLocal = false) :
    ∀ l, References v l → HeapLocation l := by
  induction t generalizing ambient v
  case prod a b m iha ihb =>
    cases v <;> simp only [ValueInterpretation, GroundTy.mode, and_false] at hv
    rintro l hl
    cases hl
    case pairLeft hl =>
      exact iha hv.2.2.1 (show (a.mode.isLocal && (m.compose ambient).isLocal) = false by
        simp [show (m.compose ambient).isLocal = false from hg]) _ hl
    case pairRight hl =>
      exact ihb hv.2.2.2.1 (show (b.mode.isLocal && (m.compose ambient).isLocal) = false by
        simp [show (m.compose ambient).isLocal = false from hg]) _ hl
    case pairCell => simpa [show (m.compose ambient).isLocal = false from hg] using hv.2.1
  case sum a b m iha ihb =>
    cases v <;> simp only [ValueInterpretation, GroundTy.mode, and_false] at hv
    all_goals rintro l hl
    all_goals cases hl
    case inl.inl hl =>
      exact iha hv.2 (show (a.mode.isLocal && (m.compose ambient).isLocal) = false by
        simp [show (m.compose ambient).isLocal = false from hg]) _ hl
    case inr.inr hl =>
      exact ihb hv.2 (show (b.mode.isLocal && (m.compose ambient).isLocal) = false by
        simp [show (m.compose ambient).isLocal = false from hg]) _ hl
  case fn a b m _ _ =>
    cases v <;> simp only [ValueInterpretation, GroundTy.mode, and_false] at hv
    rintro l hl
    cases hl
    exact hv.2.1 hg l ⟨_, ‹_›, ‹_›⟩
  all_goals cases v <;> simp only [ValueInterpretation, GroundTy.mode, and_false] at hv
  all_goals rintro l hl
  all_goals cases hl
  all_goals simp_all [GroundTy.mode]

theorem ValueInterpretation.shared_support {ρ w t ambient v}
    (hv : ValueInterpretation ρ w t ambient v)
    (hm : (t.mode.compose ambient).once = false)
    (ha : (t.mode.compose ambient).unique = false) :
    ∀ l, ¬ Owns ρ v (t.modal ambient) l := by
  induction t generalizing ambient v
  all_goals simp only [GroundTy.mode, Mode.compose] at hm ha
  case fn a b m _ _ =>
    rintro l ho
    cases ho
    exact hv.2.2.1 hm l ⟨_, _, _, ‹_›, ‹_›, _, _, ‹_›, ‹_›, ‹_›⟩
  case prod a b m iha ihb =>
    rintro l ho
    cases ho
    case pairFirst ho =>
      exact iha hv.2.2.1 (by simp only [GroundTy.mode, Mode.compose, hm, Bool.and_false])
        (by simp only [GroundTy.mode, Mode.compose, ha, Bool.and_false]) l ho
    case pairSecond ho =>
      exact ihb hv.2.2.2.1 (by simp only [GroundTy.mode, Mode.compose, hm, Bool.and_false])
        (by simp only [GroundTy.mode, Mode.compose, ha, Bool.and_false]) l ho
    case pairCell hu => simp only [Mode.compose, ha, Bool.false_eq_true] at hu
  case sum a b m iha ihb =>
    rintro l ho
    cases ho
    case inl ho =>
      exact iha hv.2 (by simp only [GroundTy.mode, Mode.compose, hm, Bool.and_false])
        (by simp only [GroundTy.mode, Mode.compose, ha, Bool.and_false]) l ho
    case inr ho =>
      exact ihb hv.2 (by simp only [GroundTy.mode, Mode.compose, hm, Bool.and_false])
        (by simp only [GroundTy.mode, Mode.compose, ha, Bool.and_false]) l ho
  all_goals rintro l ho
  all_goals cases ho
  all_goals simp_all only [Mode.compose, Bool.false_eq_true]

end ModalityInference
