import ModalityInference.Proofs.ComparisonExecutableSyntax
import ModalityInference.Proofs.ComparisonObserverShadowModel

/-! Finite key lists represent the literal-prefix table family exactly. Keys
are compared as syntax; an absent prefix selects the empty table. -/
namespace ModalityInference.ComparisonExecutableFamilies

/-- The first matching key wins, even if the list contains duplicate keys. -/
def lookup {K V : Type*} [DecidableEq K] (fallback : V) (rows : List (K × V)) (key : K) : V :=
  ((rows.find? (fun row => decide (row.1 = key))).map Prod.snd).getD fallback

theorem lookup_map_mem {K V : Type*} [DecidableEq K] (fallback : V) (keys : List K)
    (f : K → V) {key : K} (h : key ∈ keys) :
    lookup fallback (keys.map fun k => (k,f k)) key = f key := by
  induction keys with
  | nil => cases h
  | cons k keys ih =>
    by_cases hk : k = key
    · subst k; simp [lookup]
    · have ht : key ∈ keys := (List.mem_cons.mp h).resolve_left (Ne.symm hk)
      simpa [lookup,hk] using ih ht

theorem lookup_map_not_mem {K V : Type*} [DecidableEq K] (fallback : V) (keys : List K)
    (f : K → V) {key : K} (h : key ∉ keys) :
    lookup fallback (keys.map fun k => (k,f k)) key = fallback := by
  induction keys with
  | nil => rfl
  | cons k keys ih =>
    have hk : k ≠ key := fun he => h (he ▸ List.mem_cons_self)
    have ht : key ∉ keys := fun he => h (List.mem_cons_of_mem _ he)
    simpa [lookup,hk] using ih ht


/-- Mapping stored values leaves duplicate-key selection unchanged. -/
theorem lookup_map_values {K V W : Type*} [DecidableEq K] (f : V → W)
    (fallback : V) (rows : List (K × V)) (key : K) :
    lookup (f fallback) (rows.map fun row => (row.1,f row.2)) key =
      f (lookup fallback rows key) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    by_cases hk : row.1 = key
    · simp [lookup,hk]
    · simpa [lookup,hk] using ih

structure Family (V : Type*) where
  ordinary : V
  literals : List (ModExpr × V)
  fallback : V

def Family.get {V : Type*} (F : Family V) : Option ModExpr → V
  | none => F.ordinary
  | some p => lookup F.fallback F.literals p


def Family.map {V W : Type*} (f : V → W) (F : Family V) : Family W :=
  ⟨f F.ordinary,F.literals.map (fun row => (row.1,f row.2)),f F.fallback⟩

theorem Family.map_get {V W : Type*} (f : V → W) (F : Family V) (p : Option ModExpr) :
    (F.map f).get p = f (F.get p) := by
  cases p with
  | none => rfl
  | some p => exact lookup_map_values f F.fallback F.literals p

open ComparisonRelativeTables ComparisonRelativeCoordinates
  ComparisonObserverShadowModel ComparisonRawHeadFiniteOrbits ComparisonFiniteControls
  ComparisonObserverShadowPresentation ComparisonObserverShadowActionRows
  ComparisonObserverShadowActions ComparisonObserverFiniteRange ComparisonRelativeSyntax

private theorem table_ext {A O : Type*} {e : A → O → Bool} {p q : Bool}
    {T U : Table e p q} (h : ∀ a b c, T.entry a b c ↔ U.entry a b c) : T = U := by
  have he : T.entry = U.entry := funext fun a => funext fun b => funext fun c => propext (h a b c)
  cases T; cases U; cases he; rfl

private theorem indexedTable_ext {A O M : Type*} {e : A → O → Bool} {p q : Bool}
    {T U : IndexedTable e M p q} (hl : T.le = U.le)
    (h : ∀ m a b c, (T.table m).entry a b c ↔ (U.table m).entry a b c) : T = U := by
  have ht : T.table = U.table := funext fun m => table_ext (h m)
  cases T; cases U; cases hl; cases ht; rfl

def emptyTable {A O M : Type*} [Preorder M] (e : A → O → Bool) (p q : Bool) :
    IndexedTable e M p q where
  table _ := { entry := fun _ _ _ => False, mono := fun h => h.elim }
  le := (· ≤ ·)
  refl := le_refl
  trans := le_trans
  cross_mono := fun _ h => h.elim

noncomputable section

variable {Δ : Bounds} {hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ}
  {B : Boundary Δ} {names : List ModVar} {base : Nat}
  {extra : List (RawRow hn (assign hn B names base))}
  (R : Realization hn B names base extra)

def prefixTables {k : ComparisonStructuralLayout.Constructor} (hk : k = .prod ∨ k = .sum) :=
  (ComparisonRawHeadPrefixRows.prefixes B).map fun p =>
    (p,ComparisonRawHeadPrefixRows.indexedTable R.interval hk p)

theorem prefix_lookup {k : ComparisonStructuralLayout.Constructor}
    (hk : k = .prod ∨ k = .sum) (p : ModExpr) :
    lookup (emptyTable R.interval.embed false false) (prefixTables R hk) p =
      ComparisonRawHeadPrefixRows.indexedTable R.interval hk p := by
  by_cases hp : p ∈ ComparisonRawHeadPrefixRows.prefixes B
  · exact lookup_map_mem _ _ _ hp
  · rw [prefixTables,lookup_map_not_mem _ _ _ hp]
    apply indexedTable_ext
    · rfl
    · intro m a b c
      exact ⟨False.elim,fun h => hp (ComparisonRawHeadPrefixRows.entry_prefix_mem h)⟩

variable {R} (T : Tables R)

def prodFamily : Family (IndexedTable R.interval.embed (Control Δ names) false false) :=
  ⟨T.prod,prefixTables R (Or.inl rfl),emptyTable R.interval.embed false false⟩

def sumFamily : Family (IndexedTable R.interval.embed (Control Δ names) false false) :=
  ⟨T.sum,prefixTables R (Or.inr rfl),emptyTable R.interval.embed false false⟩

theorem prodFamily_get (p : Option ModExpr) : (prodFamily T).get p = T.prodTable p := by
  cases p with
  | none => rfl
  | some p => exact prefix_lookup R (Or.inl rfl) p

theorem sumFamily_get (p : Option ModExpr) : (sumFamily T).get p = T.sumTable p := by
  cases p with
  | none => rfl
  | some p => exact prefix_lookup R (Or.inr rfl) p

def finiteModel (hnames : Δ.modVars ⊆ names.toFinset) (sites : List RawSite)
    (tag : RawSite → ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) :=
  { T.model hnames sites tag with
    prodTable := (prodFamily T).get
    prod_order := fun p {m n} h => by rw [prodFamily_get]; exact T.prod_order p h
    sumTable := (sumFamily T).get
    sum_order := fun p {m n} h => by rw [sumFamily_get]; exact T.sum_order p h }

theorem finiteModel_eq (hnames : Δ.modVars ⊆ names.toFinset) (sites : List RawSite)
    (tag : RawSite → ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) :
    finiteModel T hnames sites tag = T.model hnames sites tag := by
  have hp : (prodFamily T).get = T.prodTable := funext (prodFamily_get T)
  have hs : (sumFamily T).get = T.sumTable := funext (sumFamily_get T)
  unfold finiteModel
  simp only [hp,hs]
  rfl

theorem finiteModel_denote (hnames : Δ.modVars ⊆ names.toFinset) (sites : List RawSite)
    (tag : RawSite → ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) (a : CompareTy) (p : Option ModExpr) :
    (finiteModel T hnames sites tag).denote a p = (T.model hnames sites tag).denote a p := by
  rw [finiteModel_eq]

theorem frozen_lookup (hnames : Δ.modVars ⊆ names.toFinset) (sites : List RawSite)
    (tag : RawSite → ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) (a : CompareTy) :
    lookup ⊥ (rawFrozen sites (fun s => R.orbit (tag s))) a =
      (T.model hnames sites tag).frozenValue a := rfl

end
end ModalityInference.ComparisonExecutableFamilies
