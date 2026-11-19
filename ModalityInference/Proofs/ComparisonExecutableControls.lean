import ModalityInference.ComparisonExecutableControls
import ModalityInference.Proofs.ComparisonFiniteControlEncoding
import ModalityInference.Proofs.ComparisonRelativeControlMap

/-! The executable control representation validates the original total-label
rules, including function order and projection of names outside the boundary. -/
namespace ModalityInference.ComparisonExecutableControls

open ComparisonFiniteControlEncoding ComparisonRelativeCoordinates

variable {Δ : Bounds} {names : List ModVar}

theorem future_iff (m n : Code Δ names) :
    future m n = true ↔ ComparisonFiniteControls.FutureLe (decode m) (decode n) := by
  change m ≤ n * top Δ names ↔ _
  simp only [order_iff,decode_mul,decode_top,ComparisonFiniteControls.FutureLe]

theorem future_refl (m : Code Δ names) : future m m = true :=
  (future_iff m m).mpr (ComparisonFiniteControls.le_future_self (decode m))

theorem future_trans {m n r : Code Δ names} (h : future m n = true) (k : future n r = true) :
    future m r = true :=
  (future_iff m r).mpr (((future_iff m n).mp h).trans ((future_iff n r).mp k))

theorem order_future {m n : Code Δ names} (h : m ≤ n) : future m n = true :=
  (future_iff m n).mpr (((order_iff m n).mp h).trans
    (ComparisonFiniteControls.le_future_self (decode n)))

theorem future_post {m n : Code Δ names} (h : future m n = true) (r : Code Δ names) :
    future (m * r) (n * r) = true := by
  apply (future_iff _ _).mpr
  simpa only [decode_mul] using ((future_iff m n).mp h).post (decode r)

theorem mul_mono (m : Code Δ names) : Monotone (m * ·) := fun a b h =>
  (order_iff _ _).mpr (by simpa only [decode_mul] using
    ComparisonFiniteControls.mul_mono (decode m) ((order_iff a b).mp h))

theorem project_epsilon : project Δ names .epsilon = 1 := rfl

theorem project_top : project Δ names .top = top Δ names := rfl

theorem project_compose (hnames : Δ.modVars ⊆ names.toFinset) (m n : ModExpr)
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n)) :
    project Δ names (.compose m n) = project Δ names m * project Δ names n := by
  apply decode_injective
  simpa only [decode_mul,decode_project hnames _ hm,decode_project hnames _ hn,
    decode_project hnames _ (Entails.defined_compose_iff.mpr ⟨hm,hn⟩)] using
      ComparisonFiniteControlProjection.project_compose hnames m n hm hn
        (Entails.defined_compose_iff.mpr ⟨hm,hn⟩)

theorem project_future (hnames : Δ.modVars ⊆ names.toFinset) {m n : ModExpr}
    (h : Submode Δ m (.compose n .top)) :
    future (project Δ names m) (project Δ names n) = true :=
  (future_iff _ _).mpr (by
    simpa only [decode_project hnames _ h.defined.1,
      decode_project hnames _ (Entails.defined_compose_iff.mp h.defined.2).1] using
        ComparisonFiniteControlProjection.project_future hnames h.defined.1
          (Entails.defined_compose_iff.mp h.defined.2).1 h)

def controlMap (hnames : Δ.modVars ⊆ names.toFinset) :
    ControlMap Δ (Code Δ names) (fun m n => future m n = true) where
  toFun m _ := project Δ names m
  epsilon := project_epsilon
  compose m n hm hn := project_compose hnames m n hm hn
  submode := project_submode hnames
  fnorder := project_future hnames

theorem controlMap_toFun (hnames : Δ.modVars ⊆ names.toFinset) (m : ModExpr)
    (hm : Entails Δ (.defined m)) : (controlMap hnames).toFun m hm = project Δ names m := rfl

theorem order_refl (m : Code Δ names) : order m m = true := le_refl m

theorem order_trans {m n r : Code Δ names} (h : order m n = true) (k : order n r = true) :
    order m r = true := le_trans (a := m) (b := n) (c := r) h k

end ModalityInference.ComparisonExecutableControls
