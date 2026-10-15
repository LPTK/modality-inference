import ModalityInference.Proofs.ComparisonContext
import ModalityInference.Proofs.ComparisonExactContext
import ModalityInference.Proofs.BoundedSupport

/-! Positive context matching only introduces bounded target subexpressions.
These bounds keep its images disjoint from subsequent fresh allocation. -/
namespace ModalityInference

theorem Substitution.Bounded.compose {before after : Substitution} {nt nm : Nat}
    (hb : before.Bounded nt nm) (ha : after.Bounded nt nm) :
    (after.compose before).Bounded nt nm := by
  constructor <;> intro name image hi
  all_goals simp only [Substitution.compose, List.mem_append, List.mem_map, List.mem_filter] at hi
  · rcases hi with ⟨⟨n, t⟩, ht, he⟩ | ⟨hi, _⟩
    · cases he
      exact ⟨(hb.types n t ht).1, ha.ty (hb.types n t ht).2⟩
    · exact ha.types name image hi
  · rcases hi with ⟨⟨n, m⟩, hm, he⟩ | ⟨hi, _⟩
    · cases he
      exact ⟨(hb.modes n m hm).1, (hb.modes n m hm).2.subst ha.mode⟩
    · exact ha.modes name image hi

namespace ComparisonInstance

theorem bindType_bounded {name image before after nt nm}
    (h : bindType name image before = some after) (hn : name < nt)
    (hi : image.Bounded nt nm) (hb : before.Bounded nt nm) : after.Bounded nt nm := by
  unfold bindType at h
  split at h
  · cases h
    refine ⟨?_, hb.modes⟩
    intro n t ht
    rcases List.mem_cons.mp ht with he | ht
    · cases he; exact ⟨hn, hi⟩
    · exact hb.types n t ht
  · split at h
    · cases h; exact hb
    · contradiction

theorem bindMode_bounded {name image before after nt nm}
    (h : bindMode name image before = some after) (hn : name < nm)
    (hi : image.Bounded nm) (hb : before.Bounded nt nm) : after.Bounded nt nm := by
  unfold bindMode at h
  split at h
  · cases h
    refine ⟨hb.types, ?_⟩
    intro n m hm
    rcases List.mem_cons.mp hm with he | hm
    · cases he; exact ⟨hn, hi⟩
    · exact hb.modes n m hm
  · split at h
    · cases h; exact hb
    · contradiction

theorem matchMode_bounded {p : Prepared} {source target : ModExpr} {before after : Substitution}
    (h : matchMode p source target before = some after)
    (ht : target.Bounded p.nextMode) (hb : before.Bounded p.nextType p.nextMode) :
    after.Bounded p.nextType p.nextMode := by
  induction source generalizing target before after
  case compose a b iha ihb | meet a b iha ihb | join a b iha ihb |
      leftResidual a b iha ihb | rightResidual a b iha ihb =>
    cases target <;> simp only [matchMode] at h <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hl, hr⟩ := h
    exact ihb hr ht.2 (iha hl ht.1 hb)
  case var v =>
    cases v with
    | flex n =>
      simp only [matchMode] at h
      split at h
      · next hn =>
        apply bindMode_bounded h ?_ ht hb
        simp only [modeAllowed, Bool.and_eq_true, decide_eq_true_eq] at hn
        exact hn.2
      · split at h
        · cases h; exact hb
        · contradiction
    | rigid n =>
      cases target <;> (try simp only [matchMode] at h) <;> try contradiction
      next v =>
        cases v <;> simp only [matchMode] at h <;> try contradiction
        split at h
        · cases h; exact hb
        · contradiction
  case const m =>
    cases target <;> simp only [matchMode] at h <;> try contradiction
    split at h
    · cases h; exact hb
    · contradiction
  case close a ih | closeInv a ih | future a ih | capture a ih =>
    cases target <;> simp only [matchMode] at h <;> try contradiction
    exact ih h ht hb

theorem matchType_bounded {p : Prepared} {source target : Ty} {before after : Substitution}
    (h : matchType p source target before = some after)
    (ht : target.Bounded p.nextType p.nextMode) (hb : before.Bounded p.nextType p.nextMode) :
    after.Bounded p.nextType p.nextMode := by
  induction source generalizing target before after
  case prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    cases target <;> simp only [matchType] at h <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hl, hr⟩ := h
    exact ihb hr ht.2 (iha hl ht.1 hb)
  case modal a m ih =>
    cases target <;> simp only [matchType] at h <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hl, hr⟩ := h
    exact matchMode_bounded hr ht.2 (ih hl ht.1 hb)
  case var v =>
    cases v with
    | flex n =>
      simp only [matchType] at h
      split at h
      · next hn =>
        apply bindType_bounded h ?_ ht hb
        simp only [typeAllowed, Bool.and_eq_true, decide_eq_true_eq] at hn
        exact hn.2
      · split at h
        · cases h; exact hb
        · contradiction
    | rigid n =>
      cases target <;> (try simp only [matchType] at h) <;> try contradiction
      next v =>
        cases v <;> simp only [matchType] at h <;> try contradiction
        split at h
        · cases h; exact hb
        · contradiction
  case unit | credit =>
    cases target <;> simp only [matchType] at h <;> try contradiction
    cases h; exact hb

end ComparisonInstance

namespace ComparisonContext

theorem closeComponent_property (support : α → List Nat) (fuel : Nat) (P : α → Prop)
    (group pending : List α) (hg : ∀ x ∈ group, P x) (hp : ∀ x ∈ pending, P x) :
    (∀ x ∈ (closeComponent support fuel group pending).1, P x) ∧
      ∀ x ∈ (closeComponent support fuel group pending).2, P x := by
  induction fuel generalizing group pending with
  | zero => exact ⟨hg, hp⟩
  | succ fuel ih =>
    simp only [closeComponent]
    split
    · exact ⟨hg, hp⟩
    · apply ih
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hg x hx
        · exact hp x (List.mem_filter.mp hx).1
      · intro x hx
        exact hp x (List.mem_filter.mp hx).1

theorem componentsFuel_property (support : α → List Nat) (fuel : Nat) (P : α → Prop)
    (requests : List α) (h : ∀ x ∈ requests, P x) :
    ∀ group ∈ componentsFuel support fuel requests, ∀ x ∈ group, P x := by
  induction fuel generalizing requests with
  | zero => simp [componentsFuel]
  | succ fuel ih =>
    cases requests with
    | nil => simp [componentsFuel]
    | cons request requests =>
      have hc := closeComponent_property support requests.length P [request] requests
        (by simpa using h request List.mem_cons_self)
        (fun x hx => h x (List.mem_cons_of_mem _ hx))
      intro group hg x hx
      simp only [componentsFuel, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact hc.1 x hx
      · exact ih _ hc.2 group hg x hx

theorem components_property (support : α → List Nat) (P : α → Prop)
    (requests : List α) (h : ∀ x ∈ requests, P x) :
    ∀ group ∈ components support requests, ∀ x ∈ group, P x :=
  componentsFuel_property support requests.length P requests h

private theorem foldlM_property {f : β → α → Option β} {requests : List α}
    {before after : β} (P : β → Prop) (h : requests.foldlM f before = some after)
    (hb : P before) (hs : ∀ r ∈ requests, ∀ a b, P a → f a r = some b → P b) : P after := by
  induction requests generalizing before with
  | nil => cases h; exact hb
  | cons r requests ih =>
    simp only [List.foldlM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hm, h⟩ := h
    exact ih h (hs r List.mem_cons_self before middle hb hm)
      (fun r hr => hs r (List.mem_cons_of_mem _ hr))

private theorem foldl_property {f : β → α → β} {requests : List α} {initial : β}
    (P : β → Prop) (hi : P initial)
    (hs : ∀ r ∈ requests, ∀ a, P a → P (f a r)) : P (requests.foldl f initial) := by
  induction requests generalizing initial with
  | nil => exact hi
  | cons r requests ih =>
    exact ih (hs r List.mem_cons_self initial hi)
      (fun r hr => hs r (List.mem_cons_of_mem _ hr))

theorem solvePriorityComponents_property (support : α → List Nat) (compound : α → Bool)
    (matchRequest : α → β → Option β) (requests : List α) (initial : β)
    (P : β → Prop) (Q : α → Prop) (hi : P initial) (hq : ∀ r ∈ requests, Q r)
    (hs : ∀ r, Q r → ∀ before after, P before → matchRequest r before = some after → P after) :
    P (solvePriorityComponents support compound matchRequest requests initial) := by
  apply foldl_property P hi
  intro group hg before hb
  have hgroup := components_property support Q requests hq group hg
  have hmatch (filter : α → Bool) :
      ∀ r ∈ group.filter filter, ∀ a b, P a → matchRequest r a = some b → P b :=
    fun r hr => hs r (hgroup r (List.mem_filter.mp hr).1)
  split
  · exact hb
  · next selected hselected =>
    have hp := foldlM_property P hselected hb (hmatch compound)
    cases he : (group.filter fun r => !compound r).foldlM
        (fun a r => matchRequest r a) selected with
    | none => exact hp
    | some after => exact foldlM_property P he hp (hmatch (fun r => !compound r))

theorem requests_bounded {source target : Ty} (total : ModExpr → Bool) {nt nm : Nat}
    (ht : target.Bounded nt nm) :
    ∀ request ∈ requests total source target, request.2.Bounded nm := by
  induction source generalizing target <;> cases target <;> intro request hr <;>
    simp only [requests, List.mem_append, List.not_mem_nil] at hr <;> try contradiction
  case prod.prod a b iha ihb c d | sum.sum a b iha ihb c d | fn.fn a b iha ihb c d =>
    exact hr.elim (iha ht.1 request) (ihb ht.2 request)
  case modal.modal a m ih b n =>
    rcases hr with hr | hr
    · exact ih ht.1 request hr
    · split at hr
      · contradiction
      · obtain rfl := List.mem_singleton.mp hr
        exact ht.2

theorem independent_bounded (p : Prepared) (total : ModExpr → Bool)
    (ht : p.targetType.Bounded p.nextType p.nextMode) :
    (independent p total).Bounded p.nextType p.nextMode :=
  solvePriorityComponents_property _ _ _ _ _
    (Substitution.Bounded p.nextType p.nextMode) (fun request : Request => request.2.Bounded p.nextMode)
    (Substitution.bounded_empty _ _) (requests_bounded total ht)
    (fun _ hr _ _ hb h => ComparisonInstance.matchMode_bounded h hr hb)

theorem prepare_bounded {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) (ht : p.targetType.Bounded p.nextType p.nextMode) :
    action.Bounded p.nextType p.nextMode := by
  unfold prepare at h
  split at h
  · dsimp only at h
    split at h
    · cases h; exact independent_bounded p total ht
    · contradiction
  · contradiction

end ComparisonContext

namespace ComparisonExactContext

theorem matchRequest_bounded {p : Prepared} {request : Request} {before after : Substitution}
    (h : matchRequest p request before = some after)
    (ht : request.2.Bounded p.nextType p.nextMode) (hb : before.Bounded p.nextType p.nextMode) :
    after.Bounded p.nextType p.nextMode := by
  unfold matchRequest at h
  split at h
  · split at h
    · next a n he hn =>
      apply ComparisonInstance.bindMode_bounded h ?_ trivial hb
      simp only [Bool.and_eq_true, ComparisonInstance.modeAllowed, decide_eq_true_eq] at hn
      exact hn.1.2
    · exact ComparisonInstance.matchType_bounded h ht hb
  · exact ComparisonInstance.matchType_bounded h ht hb

theorem requests_bounded {p : Prepared} {source target : Ty} (total : ModExpr → Bool)
    {nt nm : Nat} (ht : target.Bounded nt nm) :
    ∀ request ∈ requests p total source target, request.2.Bounded nt nm := by
  induction source generalizing target with
  | var v =>
    cases v with
    | rigid n => simp [requests]
    | flex n =>
      intro request hr
      simp only [requests] at hr
      split at hr
      · obtain rfl := List.mem_singleton.mp hr
        exact ht
      · contradiction
  | unit | credit => simp [requests]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    cases target <;> intro request hr <;>
      simp only [requests, List.mem_append, List.not_mem_nil] at hr
    exact hr.elim (iha ht.1 request) (ihb ht.2 request)
  | modal a m ih =>
    cases target <;> intro request hr <;>
      simp only [requests, List.not_mem_nil] at hr
    split at hr
    · exact ih ht.1 request hr
    · obtain rfl := List.mem_singleton.mp hr
      exact ht

theorem independent_bounded (p : Prepared) (total : ModExpr → Bool)
    (ht : p.targetType.Bounded p.nextType p.nextMode) :
    (independent p total).Bounded p.nextType p.nextMode :=
  ComparisonContext.solvePriorityComponents_property _ _ _ _ _
    (Substitution.Bounded p.nextType p.nextMode)
    (fun request : Request => request.2.Bounded p.nextType p.nextMode)
    (Substitution.bounded_empty _ _) (requests_bounded total ht)
    (fun _ hr _ _ hb h => matchRequest_bounded h hr hb)

theorem prepare_bounded {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) (ht : p.targetType.Bounded p.nextType p.nextMode) :
    action.Bounded p.nextType p.nextMode := by
  rw [← (prepare_spec h).2.1]
  exact independent_bounded p total ht

theorem neutral_bounded (p : Prepared) : (neutral p).Bounded p.nextType p.nextMode := by
  constructor
  · simp [neutral]
  · intro name image hi
    simp only [neutral, List.mem_map] at hi
    obtain ⟨m, hm, he⟩ := hi
    cases he
    have hn := neutral_mode_spec hm
    simp only [ComparisonInstance.modeAllowed, Bool.and_eq_true, decide_eq_true_eq] at hn
    exact ⟨hn.2, trivial⟩

end ComparisonExactContext

end ModalityInference
