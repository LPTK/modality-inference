import ModalityInference.Proofs.ResourceSubsumption
import ModalityInference.Proofs.TypingDefinedness
import ModalityInference.Proofs.TypingScope

/-! A binding actually read by a well-typed term has an admissible ground instance.
No nonemptiness assumption is imposed on arbitrary unused context schemes. -/
namespace ModalityInference

/-- There is an admissible ground instance with a defined body. -/
def Scheme.Realizable (s : Scheme) (ρ : GroundAssignment) : Prop :=
  ∃ η a, GroundInstantiates ρ s η ∧ s.body.realize η = some a

theorem Subsumes.realizable {ρ Δ s t} (h : Subsumes Δ s t) (hΔ : GroundModels ρ Δ)
    (ht : t.Realizable ρ) : s.Realizable ρ := by
  obtain ⟨η, ground, hη, ht⟩ := ht
  obtain ⟨θ, hb, he, hft, hfm⟩ := hη.skolemize (s := s) hΔ
  have hb := hb.assumptions_right
  obtain ⟨σ, hσ, hcs, hab⟩ := h
  obtain ⟨source, hsource⟩ := Option.isSome_iff_exists.mp
    (show ((σ.ty s.body).realize θ).isSome = true from
      (hab.realize_defined hb).trans (by rw [he, ht]; rfl))
  have hi := hσ.ground (hcs.groundModels hb)
  exact let ⟨hreb, hbody⟩ := hi.rebase hft hfm
    ⟨s.rebase ρ (σ.ground θ), source, hreb, hbody.trans (s.body.realize_ground hsource)⟩

theorem Scheme.Realizable.of_modal {s : Scheme} {m ρ} (h : (s.modal m).Realizable ρ) :
    s.Realizable ρ := by
  obtain ⟨η, a, hη, ha⟩ := h
  cases ht : s.body.realize η <;> simp [Scheme.modal, TypeExpr.realize, ht] at ha
  exact ⟨η, _, hη, ht⟩

theorem Scheme.Realizable.modal_const {s : Scheme} {ρ} (h : s.Realizable ρ) (m : Mode) :
    (s.modal (.const m)).Realizable ρ := by
  obtain ⟨η, a, hη, ha⟩ := h
  exact ⟨η, a.modal m, hη, by simp [Scheme.modal, TypeExpr.realize, ModExpr.eval, ha]⟩

theorem ContextJoin.left_realizable {Δ Γ Γ₁ Γ₂ ρ} (h : ContextJoin Δ Γ₁ Γ₂ Γ)
    {i : Nat} {s : Scheme} (hi : Γ₁[i]? = some (some s)) (hs : s.Realizable ρ) :
    ∃ t, Γ[i]? = some (some t) ∧ t.Realizable ρ := by
  induction h generalizing i
  all_goals cases i <;> simp_all
  exact hs.modal_const Mode.many

theorem ContextJoin.right_realizable {Δ Γ Γ₁ Γ₂ ρ} (h : ContextJoin Δ Γ₁ Γ₂ Γ)
    {i : Nat} {s : Scheme} (hi : Γ₂[i]? = some (some s)) (hs : s.Realizable ρ) :
    ∃ t, Γ[i]? = some (some t) ∧ t.Realizable ρ := by
  induction h generalizing i
  all_goals cases i <;> simp_all
  exact hs.modal_const Mode.many

theorem Typing.freeVars_realizable {Δ Γ t a} (h : Typing Δ Γ t a)
    {ρ} (hΔ : GroundModels ρ Δ) {i : Nat} (hi : i ∈ t.freeVars) :
    ∃ s, Γ[i]? = some (some s) ∧ s.Realizable ρ := by
  induction h generalizing i ρ
  case lam Δ Γ captured t a b m _ _ hlock _ ih =>
    obtain ⟨s, hs, hr⟩ := ih hΔ ((t.mem_freeVars_add 0 1 i).mp hi)
    exact let ⟨s', hs', he, _⟩ := hlock.kept (i := i) (t := s) (by simpa using hs)
      ⟨s', hs', (he ▸ hr).of_modal⟩
  case subs _ _ _ _ _ _ _ hctx _ ih =>
    obtain ⟨s, hs, hr⟩ := ih hΔ hi
    exact let ⟨s', hs', hsub⟩ := hctx.kept hs
      ⟨s', hs', hsub.realizable hΔ hr⟩
  case var Δ Γ j s σ hlookup hσ hb hw =>
    have hij : i = j := by simpa [Term.freeVars] using hi
    exact let ⟨ground, hg⟩ := Option.isSome_iff_exists.mp (hw.realize_defined hΔ)
      ⟨s, hij ▸ hlookup, σ.ground ρ, ground,
        hσ.ground (hb.groundModels hΔ), s.body.realize_ground hg⟩
  case split Δ Γ Γ₁ Γ₂ a b c t u m hj _ _ iht ihu =>
    rcases Finset.mem_union.mp hi with hi | hi
    · exact let ⟨s, hs, hr⟩ := iht hΔ hi; hj.left_realizable hs hr
    · obtain ⟨s, hs, hr⟩ := ihu hΔ ((u.mem_freeVars_add 0 3 i).mp hi)
      exact hj.right_realizable (i := i) (s := s) (by simpa using hs) hr
  case case Δ Γ Γ₁ Γ₂ a b c t u v m hj _ _ _ iht ihu ihv =>
    rcases Finset.mem_union.mp hi with hi | hi
    · rcases Finset.mem_union.mp hi with hi | hi
      · exact let ⟨s, hs, hr⟩ := iht hΔ hi; hj.left_realizable hs hr
      · obtain ⟨s, hs, hr⟩ := ihu hΔ ((u.mem_freeVars_add 0 1 i).mp hi)
        exact hj.right_realizable (i := i) (s := s) (by simpa using hs) hr
    · obtain ⟨s, hs, hr⟩ := ihv hΔ ((v.mem_freeVars_add 0 1 i).mp hi)
      exact hj.right_realizable (i := i) (s := s) (by simpa using hs) hr
  case defn Δ Γ rhs body a b rhsBounds hrhs _ _ _ ihb =>
    rcases Finset.mem_union.mp hi with hi | hi
    · simp [hrhs.closed] at hi
    · simpa using ihb hΔ ((body.mem_freeVars_add 0 1 i).mp hi)
  case reuse Δ Γ Γ₁ Γ₂ Γ₃ Γ₂₃ t u v a b m k hj hj' _ _ _ _ _ iht ihu ihv =>
    simp only [Term.freeVars, Finset.mem_union] at hi
    exact hi.elim (fun h => h.elim
      (fun h => let ⟨s, hs, hr⟩ := iht hΔ h; hj'.left_realizable hs hr)
      (fun h => let ⟨s, hs, hr⟩ := ihu hΔ h
                let ⟨s', hs', hr'⟩ := hj.left_realizable hs hr
                hj'.right_realizable hs' hr'))
      (fun h => let ⟨s, hs, hr⟩ := ihv hΔ h
                let ⟨s', hs', hr'⟩ := hj.right_realizable hs hr
                hj'.right_realizable hs' hr')
  all_goals try simp_all [Term.freeVars]
  case app _ _ _ _ _ _ _ _ hj _ _ iht ihu
     | pair _ _ _ _ _ _ _ _ _ hj _ _ iht ihu
     | stackPair _ _ _ _ _ _ _ _ _ _ hj _ _ _ _ iht ihu =>
    exact hi.elim
      (fun h => let ⟨s, hs, hr⟩ := iht hΔ h; hj.left_realizable hs hr)
      (fun h => let ⟨s, hs, hr⟩ := ihu hΔ h; hj.right_realizable hs hr)

theorem ResourceSchemeInterpretation.valid {ρ w s v reserved}
    (h : ResourceSchemeInterpretation ρ w s v reserved) (hs : s.Realizable ρ) :
    w.ValidValue v :=
  let ⟨η, a, hη, ha⟩ := hs
  let ⟨_, _, hv⟩ := h.2 η a hη ha
  hv.valid

end ModalityInference
