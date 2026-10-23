import ModalityInference.Proofs.ComparisonRawHeadModeOrbits
import Mathlib.Data.Fintype.Pi

/-! The total labels on a fixed name boundary form a finite ordered monoid.
Equality is semantic equality under the original scalar assumptions. -/
namespace ModalityInference.ComparisonFiniteControls

open ComparisonAlgebra ComparisonRawHeadModeOrbits

noncomputable section

abbrev Model (Δ : Bounds) := {η : ModVar → Mode // ModeModels Δ η}

structure Label (Δ : Bounds) (names : List ModVar) where
  mode : GuardedMode Δ
  support : mode.expression.vars ⊆ names.toFinset

def Label.value {Δ : Bounds} {names : List ModVar} (m : Label Δ names) : Model Δ → Mode :=
  fun η => m.mode.value η.val

abbrev Control (Δ : Bounds) (names : List ModVar) :=
  {f : Model Δ → Mode // ∃ m : Label Δ names, m.value = f}

def ofLabel {Δ : Bounds} {names : List ModVar} (m : Label Δ names) : Control Δ names :=
  ⟨m.value,m,rfl⟩

def label {Δ : Bounds} {names : List ModVar} (m : Control Δ names) : Label Δ names := m.property.choose

theorem label_value {Δ : Bounds} {names : List ModVar} (m : Control Δ names) : (label m).value = m.val :=
  m.property.choose_spec

@[ext] theorem control_ext {Δ : Bounds} {names : List ModVar} {m n : Control Δ names}
    (h : ∀ η, m.val η = n.val η) : m = n := Subtype.ext (funext h)

private theorem mode_antisymm {a b : Mode}
    (hab : a.le b = true) (hba : b.le a = true) : a = b := by
  rcases a with ⟨a₁,a₂,a₃⟩; rcases b with ⟨b₁,b₂,b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> simp_all [Mode.le]

instance {Δ : Bounds} {names : List ModVar} : PartialOrder (Control Δ names) where
  le m n := ∀ η, (m.val η).le (n.val η) = true
  le_refl _ _ := Mode.le_refl _
  le_trans _ _ _ h k η := Mode.le_trans (h η) (k η)
  le_antisymm _ _ h k := control_ext (fun η => mode_antisymm (h η) (k η))

def expression {Δ : Bounds} {names : List ModVar} (m : Control Δ names) : ModExpr := (label m).mode.expression

theorem expression_defined {Δ : Bounds} {names : List ModVar} (m : Control Δ names) :
    Entails Δ (.defined (expression m)) := (label m).mode.defined

theorem expression_support {Δ : Bounds} {names : List ModVar} (m : Control Δ names) :
    (expression m).vars ⊆ names.toFinset := (label m).support

theorem expression_eval {Δ : Bounds} {names : List ModVar} (m : Control Δ names) (η : Model Δ) :
    (expression m).eval (some ∘ η.val) = some (m.val η) := by
  simpa only [← label_value m] using (label m).mode.eval η.val η.property

def encode {Δ : Bounds} {names : List ModVar} (m : ModExpr) (hm : Entails Δ (.defined m))
    (hs : m.vars ⊆ names.toFinset) : Control Δ names :=
  ofLabel ⟨GuardedMode.ofDefined m hm, hs⟩

theorem encode_eval {Δ : Bounds} {names : List ModVar} (m : ModExpr) (hm : Entails Δ (.defined m))
    (hs : m.vars ⊆ names.toFinset) (η : Model Δ) :
    m.eval (some ∘ η.val) = some ((encode m hm hs).val η) :=
  (GuardedMode.ofDefined m hm).eval η.val η.property

theorem le_iff_submode {Δ : Bounds} {names : List ModVar} (m n : Control Δ names) :
    m ≤ n ↔ Submode Δ (expression m) (expression n) := by
  exact ⟨fun h => .valid (fun η hη => ⟨m.val ⟨η,hη⟩,n.val ⟨η,hη⟩,
    expression_eval m ⟨η,hη⟩,expression_eval n ⟨η,hη⟩,h ⟨η,hη⟩⟩),
    fun h η => by
      obtain ⟨a,b,ha,hb,hab⟩ := h.denote η.property
      exact (congrArg₂ Mode.le
        (Option.some.inj ((expression_eval m η).symm.trans ha))
        (Option.some.inj ((expression_eval n η).symm.trans hb))).trans hab⟩

instance {Δ : Bounds} {names : List ModVar} : One (Control Δ names) :=
  ⟨encode .epsilon (fun _ _ => rfl) (by simp [ModExpr.epsilon,ModExpr.vars])⟩

instance {Δ : Bounds} {names : List ModVar} : Mul (Control Δ names) :=
  ⟨fun m n => encode (.compose (expression m) (expression n))
    (Entails.defined_compose_iff.mpr ⟨expression_defined m,expression_defined n⟩)
    (Finset.union_subset (expression_support m) (expression_support n))⟩

@[simp] theorem one_val {Δ : Bounds} {names : List ModVar} (η : Model Δ) :
    (1 : Control Δ names).val η = Mode.identity := rfl

theorem mul_val {Δ : Bounds} {names : List ModVar} (m n : Control Δ names) (η : Model Δ) :
    (m * n).val η = (m.val η).compose (n.val η) := by
  exact Option.some.inj ((encode_eval _ _ _ η).symm.trans
    (by simp [ModExpr.eval,expression_eval]))

instance {Δ : Bounds} {names : List ModVar} : CommMonoid (Control Δ names) where
  mul_assoc m n r := control_ext (fun η => by simp only [mul_val,Mode.compose_assoc])
  one_mul m := control_ext (fun η => by simp only [mul_val,one_val,Mode.identity_compose])
  mul_one m := control_ext (fun η => by simp only [mul_val,one_val,Mode.compose_identity])
  mul_comm m n := control_ext (fun η => by simp only [mul_val,Mode.compose_comm])

theorem mul_mono {Δ : Bounds} {names : List ModVar} (m : Control Δ names) :
    Monotone (m * ·) := fun _ _ h η => by
  simpa only [mul_val] using Mode.compose_le_left (m.val η) (h η)

theorem encode_expression {Δ : Bounds} {names : List ModVar} (m : Control Δ names) :
    encode (expression m) (expression_defined m) (expression_support m) = m :=
  control_ext (fun η => Option.some.inj ((encode_eval _ _ _ η).symm.trans (expression_eval m η)))

theorem encode_le_iff {Δ : Bounds} {names : List ModVar} (m n : ModExpr)
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (hs : m.vars ⊆ names.toFinset) (ht : n.vars ⊆ names.toFinset) :
    encode m hm hs ≤ encode n hn ht ↔ Submode Δ m n := by
  exact ⟨fun h => .valid (fun η hη => ⟨(encode m hm hs).val ⟨η,hη⟩,
    (encode n hn ht).val ⟨η,hη⟩,encode_eval m hm hs ⟨η,hη⟩,encode_eval n hn ht ⟨η,hη⟩,h ⟨η,hη⟩⟩),
    fun h η => by
      obtain ⟨a,b,ha,hb,hab⟩ := h.denote η.property
      exact (congrArg₂ Mode.le
        (Option.some.inj ((encode_eval m hm hs η).symm.trans ha))
        (Option.some.inj ((encode_eval n hn ht η).symm.trans hb))).trans hab⟩

abbrev Representative (names : List ModVar) := {r : ModExpr // r ∈ representatives names}

instance (names : List ModVar) : Fintype (Representative names) :=
  Fintype.ofFinset (representatives names).toFinset (fun _ => List.mem_toFinset)

def canonical {Δ : Bounds} {names : List ModVar} (r : Representative names) : Control Δ names :=
  encode r.val (representatives_total r.property) (representatives_support r.property)

theorem canonical_surjective {Δ : Bounds} {names : List ModVar} :
    Function.Surjective (canonical (Δ := Δ) (names := names)) := by
  intro m
  obtain ⟨r,hr,hmr,hrm⟩ := representatives_complete (expression_defined m) (expression_support m)
  refine ⟨⟨r,hr⟩,?_⟩
  exact (le_antisymm
    ((encode_le_iff r (expression m) _ _ _ _).mpr hrm)
    ((encode_le_iff (expression m) r _ _ _ _).mpr hmr)).trans (encode_expression m)

instance {Δ : Bounds} {names : List ModVar} : Finite (Control Δ names) :=
  Finite.of_surjective canonical canonical_surjective

theorem expression_equivalent {Δ : Bounds} {names : List ModVar}
    (m : Control Δ names) (a : ModExpr)
    (ha : ∀ η : Model Δ, a.eval (some ∘ η.val) = some (m.val η)) :
    Submode Δ (expression m) a ∧ Submode Δ a (expression m) :=
  ⟨.valid (fun η hη => ⟨m.val ⟨η,hη⟩,m.val ⟨η,hη⟩,
      expression_eval m ⟨η,hη⟩,ha ⟨η,hη⟩,Mode.le_refl _⟩),
   .valid (fun η hη => ⟨m.val ⟨η,hη⟩,m.val ⟨η,hη⟩,
      ha ⟨η,hη⟩,expression_eval m ⟨η,hη⟩,Mode.le_refl _⟩)⟩

theorem expression_one {Δ : Bounds} {names : List ModVar} :
    Submode Δ (expression (1 : Control Δ names)) .epsilon ∧
      Submode Δ .epsilon (expression (1 : Control Δ names)) :=
  expression_equivalent 1 .epsilon (fun _ => rfl)

theorem expression_mul {Δ : Bounds} {names : List ModVar} (m n : Control Δ names) :
    Submode Δ (expression (m * n)) (.compose (expression m) (expression n)) ∧
      Submode Δ (.compose (expression m) (expression n)) (expression (m * n)) :=
  expression_equivalent (m * n) _ (fun η => by simp [ModExpr.eval,expression_eval,mul_val])

def top {Δ : Bounds} {names : List ModVar} : Control Δ names :=
  encode .top (fun _ _ => rfl) (by simp [ModExpr.top,ModExpr.vars])

@[simp] theorem top_val {Δ : Bounds} {names : List ModVar} (η : Model Δ) :
    (top : Control Δ names).val η = Mode.top := rfl

def FutureLe {Δ : Bounds} {names : List ModVar} (m n : Control Δ names) : Prop := m ≤ n * top

theorem le_future_self {Δ : Bounds} {names : List ModVar} (m : Control Δ names) :
    FutureLe m m := fun η => by simp [mul_val,Mode.le_iff,Mode.compose,Mode.top]

theorem top_idempotent {Δ : Bounds} {names : List ModVar} :
    (top : Control Δ names) * top = top :=
  control_ext (fun _ => by simp [mul_val,Mode.compose_self])

theorem FutureLe.trans {Δ : Bounds} {names : List ModVar} {m n r : Control Δ names}
    (h : FutureLe m n) (k : FutureLe n r) : FutureLe m r := by
  exact le_trans h (by simpa only [FutureLe,mul_comm top,mul_assoc,top_idempotent] using mul_mono top k)

theorem FutureLe.post {Δ : Bounds} {names : List ModVar} {m n : Control Δ names}
    (h : FutureLe m n) (r : Control Δ names) : FutureLe (m * r) (n * r) := by
  simpa only [FutureLe,mul_left_comm,mul_comm,mul_assoc] using mul_mono r h

theorem futureLe_iff_submode {Δ : Bounds} {names : List ModVar} (m n : Control Δ names) :
    FutureLe m n ↔ Submode Δ (expression m) (.compose (expression n) .top) := by
  have he := expression_equivalent (n * top) (.compose (expression n) .top)
    (fun η => by simp [ModExpr.eval,expression_eval,mul_val,ModExpr.top])
  exact ⟨fun h => ((le_iff_submode m (n * top)).mp h).trans he.1,
    fun h => (le_iff_submode m (n * top)).mpr (h.trans he.2)⟩

theorem expression_encode {Δ : Bounds} {names : List ModVar} (m : ModExpr)
    (hm : Entails Δ (.defined m)) (hs : m.vars ⊆ names.toFinset) :
    Submode Δ (expression (encode m hm hs)) m ∧
      Submode Δ m (expression (encode m hm hs)) :=
  expression_equivalent (encode m hm hs) m (encode_eval m hm hs)

end
end ModalityInference.ComparisonFiniteControls
