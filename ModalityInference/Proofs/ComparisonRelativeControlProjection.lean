import ModalityInference.Proofs.ComparisonRelativeControlMap
import ModalityInference.Proofs.ComparisonFiniteControlProjection

/-! The supported finite control monoid interprets every originally total
label through the fixed-name projection. -/
namespace ModalityInference.ComparisonFiniteControlProjection

open ComparisonFiniteControls ComparisonRelativeCoordinates

noncomputable def controlMap {Δ : Bounds} {names : List ModVar}
    (hnames : Δ.modVars ⊆ names.toFinset) : ControlMap Δ (Control Δ names) FutureLe where
  toFun := project hnames
  epsilon := project_epsilon hnames _
  compose m n hm hn := project_compose hnames m n hm hn _
  submode := project_submode hnames
  fnorder h := project_future hnames h.defined.1 (Entails.defined_compose_iff.mp h.defined.2).1 h

end ModalityInference.ComparisonFiniteControlProjection
