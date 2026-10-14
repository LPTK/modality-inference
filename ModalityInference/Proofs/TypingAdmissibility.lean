import ModalityInference.Proofs.SubsumptionInstances
import ModalityInference.Proofs.SolverDefinedness
import ModalityInference.Proofs.TypingInstances
import ModalityInference.Proofs.ResourceRestriction

/-! Syntactic admissibility of used bindings when ambient subtype assumptions
have defined operands. Successful solver residuals satisfy this condition. -/
namespace ModalityInference

def Bounds.TypeBoundsDefined (Δ : Bounds) : Prop :=
  ∀ a b, Constraint.sub a b ∈ Δ → a.DefinedUnder Δ ∧ b.DefinedUnder Δ

theorem ModExpr.wellFormed_compose {η : ModVar → Mode} {m n : ModExpr} :
    (m.compose n).WellFormed η ↔ m.WellFormed η ∧ n.WellFormed η := by
  cases hm : m.eval (some ∘ η) <;> cases hn : n.eval (some ∘ η) <;>
    simp [WellFormed, eval, hm, hn]

theorem Entails.defined_compose_iff {Δ m n} :
    Entails Δ (.defined (.compose m n)) ↔
      Entails Δ (.defined m) ∧ Entails Δ (.defined n) := by
  simp only [Entails, ModExpr.wellFormed_compose, forall_and]

theorem Subtype.definedUnder_iff {Δ a b} (h : Subtype Δ a b)
    (hΔ : Δ.TypeBoundsDefined) : a.DefinedUnder Δ ↔ b.DefinedUnder Δ := by
  induction h
  case fn a b c d m n hca hbd hm ihca ihbd =>
    have hn := (Entails.defined_compose_iff.mp hm.defined.2).1
    simpa only [TypeExpr.definedUnder_modal, TypeExpr.definedUnder_fn] using
      and_congr (and_congr ihca.symm ihbd) (iff_of_true hm.defined.1 hn)
  case credit m n hm =>
    have hmn := (Entails.defined_compose_iff.mp hm.defined.1).1
    simpa only [TypeExpr.definedUnder_modal] using
      and_congr (Iff.rfl (a := TypeExpr.credit.DefinedUnder Δ)) (iff_of_true hmn hm.defined.2)
  case prod | sum =>
    simp_all only [TypeExpr.definedUnder_modal, TypeExpr.definedUnder_prod, TypeExpr.definedUnder_sum]
    tauto
  case refl => exact Iff.rfl
  case trans _ _ ihab ihbc => exact ihab.trans ihbc
  case bound a b hc => exact iff_of_true (hΔ a b hc).1 (hΔ a b hc).2
  case congr _ hm ih =>
    simpa only [TypeExpr.definedUnder_modal] using and_congr ih (iff_of_true hm.defined.1 hm.defined.2)
  case identity | identityRev =>
    simp [TypeExpr.definedUnder_modal, ModExpr.WellFormed, ModExpr.epsilon, ModExpr.eval]
  case compose | composeRev =>
    simp only [TypeExpr.definedUnder_modal, ModExpr.wellFormed_compose, forall_and, and_assoc]

theorem solveFrom_typeBoundsDefined {fuel nt nm cs result}
    (h : solveFrom fuel nt nm cs = .success result) : result.bounds.TypeBoundsDefined :=
  fun a b hc => ⟨fun η hη => (solveFrom_typeBounds_defined h η hη a b hc).1,
    fun η hη => (solveFrom_typeBounds_defined h η hη a b hc).2⟩

theorem solve_typeBoundsDefined {fuel cs result} (h : solve fuel cs = .success result) :
    result.bounds.TypeBoundsDefined := solveFrom_typeBoundsDefined h

theorem Typing.definedUnder {Δ Γ t a} (h : Typing Δ Γ t a)
    (hΔ : Δ.TypeBoundsDefined) : a.DefinedUnder Δ := by
  induction h
  case subs _ _ _ _ _ _ _ _ hs ih => exact (hs.definedUnder_iff hΔ).mp (ih hΔ)
  all_goals try simp_all [TypeExpr.definedUnder_modal, TypeExpr.definedUnder_fn,
    TypeExpr.definedUnder_prod, TypeExpr.definedUnder_sum,
    ← TypeExpr.definedUnder_iff_entails_wellFormed]
  case unit => exact ⟨by simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels], ‹_›⟩
  case lam => assumption
  case stackPair _ _ _ _ _ _ _ _ _ _ _ _ _ hm _ _ _ => exact hm.defined.2

def Scheme.Admissible (s : Scheme) (Δ : Bounds) : Prop :=
  ∃ θ, Instantiates s θ ∧ EntailsAll Δ (θ.bounds s.bounds) ∧ (θ.ty s.body).DefinedUnder Δ

theorem Subsumes.admissible {Δ s t} (h : Subsumes Δ s t) (hΔ : Δ.TypeBoundsDefined)
    (ht : t.Admissible Δ) : s.Admissible Δ := by
  obtain ⟨θ, hi, hb, hd⟩ := ht
  obtain ⟨σ, hi, hb, hs⟩ := h.instantiate hi hb hd
  exact ⟨σ, hi, hb, (hs.definedUnder_iff hΔ).mpr hd⟩

theorem Scheme.Admissible.of_modal {s : Scheme} {m Δ} (h : (s.modal m).Admissible Δ) :
    s.Admissible Δ := by
  obtain ⟨θ, hi, hb, hd⟩ := h
  exact ⟨θ, hi, hb, (TypeExpr.definedUnder_modal.mp hd).1⟩

theorem Scheme.Admissible.modal_const {s : Scheme} {Δ} (h : s.Admissible Δ) (m : Mode) :
    (s.modal (.const m)).Admissible Δ := by
  obtain ⟨θ, hi, hb, hd⟩ := h
  exact ⟨θ, hi, hb, TypeExpr.definedUnder_modal.mpr ⟨hd, fun _ _ => rfl⟩⟩

theorem ContextJoin.left_admissible {Δ Γ Γ₁ Γ₂} (h : ContextJoin Δ Γ₁ Γ₂ Γ)
    {i : Nat} {s : Scheme} (hi : Γ₁[i]? = some (some s)) (hs : s.Admissible Δ) :
    ∃ t, Γ[i]? = some (some t) ∧ t.Admissible Δ := by
  induction h generalizing i
  all_goals cases i <;> simp_all
  exact hs.modal_const Mode.many

theorem ContextJoin.right_admissible {Δ Γ Γ₁ Γ₂} (h : ContextJoin Δ Γ₁ Γ₂ Γ)
    {i : Nat} {s : Scheme} (hi : Γ₂[i]? = some (some s)) (hs : s.Admissible Δ) :
    ∃ t, Γ[i]? = some (some t) ∧ t.Admissible Δ := by
  induction h generalizing i
  all_goals cases i <;> simp_all
  exact hs.modal_const Mode.many

theorem Typing.freeVars_admissible {Δ Γ t a} (h : Typing Δ Γ t a)
    (hΔ : Δ.TypeBoundsDefined) {i : Nat} (hi : i ∈ t.freeVars) :
    ∃ s, Γ[i]? = some (some s) ∧ s.Admissible Δ := by
  induction h generalizing i
  case subs _ _ _ _ _ _ _ hctx _ ih =>
    obtain ⟨s, hs, ha⟩ := ih hΔ hi
    exact let ⟨s', hs', hsub⟩ := hctx.kept hs
      ⟨s', hs', hsub.admissible hΔ ha⟩
  case lam Δ Γ captured t a b m _ _ hlock _ ih =>
    obtain ⟨s, hs, ha⟩ := ih hΔ ((t.mem_freeVars_add 0 1 i).mp hi)
    exact let ⟨s', hs', he, _⟩ := hlock.kept (i := i) (t := s) (by simpa using hs)
      ⟨s', hs', (he ▸ ha).of_modal⟩
  case var Δ Γ j s σ hlookup hσ hb hw =>
    have hij : i = j := by simpa [Term.freeVars] using hi
    exact ⟨s, hij ▸ hlookup, σ, hσ, hb, (σ.ty s.body).definedUnder_iff_entails_wellFormed Δ |>.mpr hw⟩
  case split Δ Γ Γ₁ Γ₂ a b c t u m hj _ _ iht ihu =>
    rcases Finset.mem_union.mp hi with hi | hi
    · exact let ⟨s, hs, ha⟩ := iht hΔ hi; hj.left_admissible hs ha
    · obtain ⟨s, hs, ha⟩ := ihu hΔ ((u.mem_freeVars_add 0 3 i).mp hi)
      exact hj.right_admissible (i := i) (s := s) (by simpa using hs) ha
  case case Δ Γ Γ₁ Γ₂ a b c t u v m hj _ _ _ iht ihu ihv =>
    rcases Finset.mem_union.mp hi with hi | hi
    · rcases Finset.mem_union.mp hi with hi | hi
      · exact let ⟨s, hs, ha⟩ := iht hΔ hi; hj.left_admissible hs ha
      · obtain ⟨s, hs, ha⟩ := ihu hΔ ((u.mem_freeVars_add 0 1 i).mp hi)
        exact hj.right_admissible (i := i) (s := s) (by simpa using hs) ha
    · obtain ⟨s, hs, ha⟩ := ihv hΔ ((v.mem_freeVars_add 0 1 i).mp hi)
      exact hj.right_admissible (i := i) (s := s) (by simpa using hs) ha
  case defn Δ Γ rhs body a b rhsBounds hrhs _ _ _ ihb =>
    rcases Finset.mem_union.mp hi with hi | hi
    · simp [hrhs.closed] at hi
    · simpa using ihb hΔ ((body.mem_freeVars_add 0 1 i).mp hi)
  case reuse Δ Γ Γ₁ Γ₂ Γ₃ Γ₂₃ t u v a b m k hj hj' _ _ _ _ _ iht ihu ihv =>
    simp only [Term.freeVars, Finset.mem_union] at hi
    exact hi.elim (fun h => h.elim
      (fun h => let ⟨s, hs, ha⟩ := iht hΔ h; hj'.left_admissible hs ha)
      (fun h => let ⟨s, hs, ha⟩ := ihu hΔ h
                let ⟨s', hs', ha'⟩ := hj.left_admissible hs ha
                hj'.right_admissible hs' ha'))
      (fun h => let ⟨s, hs, ha⟩ := ihv hΔ h
                let ⟨s', hs', ha'⟩ := hj.right_admissible hs ha
                hj'.right_admissible hs' ha')
  all_goals try simp_all [Term.freeVars]
  case app _ _ _ _ _ _ _ _ hj _ _ iht ihu
     | pair _ _ _ _ _ _ _ _ _ hj _ _ iht ihu
     | stackPair _ _ _ _ _ _ _ _ _ _ hj _ _ _ _ iht ihu =>
    exact hi.elim
      (fun h => let ⟨s, hs, ha⟩ := iht h; hj.left_admissible hs ha)
      (fun h => let ⟨s, hs, ha⟩ := ihu h; hj.right_admissible hs ha)

theorem Typing.lam_capture_admissible {Δ Γ captured body a}
    (h : Typing Δ Γ (.lam captured body) a) (hΔ : Δ.TypeBoundsDefined)
    {i : Nat} (hi : i ∈ body.freeVars 1) :
    ∃ s, captured[i]? = some (some s) ∧ s.Admissible Δ := by
  generalize he : Term.lam captured body = t at h
  induction h
  all_goals cases he
  case subs.refl => solve_by_elim
  case lam.refl =>
    obtain ⟨s, hs, ha⟩ := (show Typing _ _ body _ from ‹_›).freeVars_admissible hΔ
      ((body.mem_freeVars_add 0 1 i).mp hi)
    exact ⟨s, Context.restrict_present.mpr ⟨hi, by simpa using hs⟩, ha⟩

end ModalityInference
