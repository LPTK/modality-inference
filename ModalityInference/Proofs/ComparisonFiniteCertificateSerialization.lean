import ModalityInference.Proofs.ComparisonFiniteCertificateChecks
import ModalityInference.Proofs.ComparisonFiniteCertificateEmbedding
import ModalityInference.Proofs.ComparisonFiniteCertificateTables
import ModalityInference.Proofs.ComparisonExecutableDefinedAgreement
import ModalityInference.Proofs.ComparisonExecutableTableSerialization
import ModalityInference.Proofs.ComparisonExecutableFamilies
import ModalityInference.Proofs.ComparisonExecutableScalarSyntax
import ModalityInference.Proofs.ComparisonExecutableSyntaxMap

/-! A finite model with checked inner machine and finitely supported literal
tables serializes to the actual executable certificate format. -/
namespace ModalityInference.ComparisonFiniteCertificate.Serialization

open ComparisonFiniteControlEncoding ComparisonExecutableControls ComparisonRelativeTables
  ComparisonRelativeCoordinates ComparisonRelativeSyntax ComparisonObserverMachine
  ComparisonObserverMachineCheck ComparisonExecutableDefinedAgreement

noncomputable section

variable {Δ : Bounds} {names : List ModVar} {states tags observations : Nat}

theorem checked_laws {types : List TypeVar} {modes : List ModVar}
    {machine : Fin states → Description (Fin states)}
    (h : ComparisonObserverMachineCheck.check (shadow Δ) types modes machine = true) :
    ModalValid Δ (nodes types modes machine) ∧ RangeClosed Δ (nodes types modes machine) ∧
      Coherent Δ (nodes types modes machine) :=
  ComparisonObserverMachineModeTransport.certified_modes
    (fun η hη => (ComparisonBalancedProjection.modeModels_shadow Δ η).mp hη)
    (by simpa only [shadow_eq] using ComparisonObserverMachineCheck.check_sound h)

structure Source (Δ : Bounds) (names : List ModVar) (states tags observations : Nat) where
  types : List TypeVar
  modes : List ModVar
  machine : Fin states → Description (Fin states)
  embed : Fin tags → Fin observations → Bool
  model : Model Δ (Code Δ names) (Fin tags) (Fin observations) embed
  checked : ComparisonObserverMachineCheck.check (shadow Δ) types modes machine = true
  names_supported : Δ.modVars ⊆ names.toFinset
  keys : List ModExpr
  prod_relation : ∀ p m n, order m n = true ↔ (model.prodTable p).le m n
  sum_relation : ∀ p m n, order m n = true ↔ (model.sumTable p).le m n
  fn_relation : ∀ m n, future m n = true ↔ model.fnTable.le m n
  prod_empty : ∀ p, p ∉ keys → ∀ m a b c, ¬ ((model.prodTable (some p)).table m).entry a b c
  sum_empty : ∀ p, p ∉ keys → ∀ m a b c, ¬ ((model.sumTable (some p)).table m).entry a b c
  embedding : LatticeHom (ComparisonObserverFiniteRange.Value (nodes types modes machine))
    (ComparisonRelativeCoordinates.Coordinates (Code Δ names) (Fin observations → Bool))
  agreement : CodeDefinedAgreement model (checked_laws checked).1 (checked_laws checked).2.1 embedding

namespace Source

variable (S : Source Δ names states tags observations)

abbrev Range := ComparisonObserverFiniteRange.Value (nodes S.types S.modes S.machine)

def rows {p q : Bool} (T : IndexedTable S.embed (Code Δ names) p q) :=
  ComparisonExecutableTables.serialize (indices Δ names) (List.finRange tags) T

def definedArray (x : ComparisonObserverRangeEncoding.Bits states) :
    ComparisonFiniteCertificate.Coordinates Δ names observations :=
  if hx : ComparisonObserverRangeEncoding.admitted S.machine x = true then
    fun m => S.embedding (ComparisonObserverRangeEncoding.unpack x hx) m
  else fun _ _ => false

def candidate : Candidate Δ names where
  states := states
  tags := tags
  observations := observations
  types := S.types
  modes := S.modes
  machine := S.machine
  embed := S.embed
  prodRows := S.rows (S.model.prodTable none)
  sumRows := S.rows (S.model.sumTable none)
  fnRows := S.rows S.model.fnTable
  prodLiterals := S.keys.map fun p => (p,S.rows (S.model.prodTable (some p)))
  sumLiterals := S.keys.map fun p => (p,S.rows (S.model.sumTable (some p)))
  frozen := S.model.frozen.map fun row => (row.1,fun m => row.2 m)
  defined := S.definedArray

@[simp] theorem defined_pack (x : S.Range) :
    S.candidate.defined (ComparisonObserverRangeEncoding.pack x) = fun m => S.embedding x m := by
  simp only [candidate,definedArray,dif_pos (ComparisonObserverRangeEncoding.pack_admitted x)]
  rfl

theorem rows_entry {p q : Bool} (T : IndexedTable S.embed (Code Δ names) p q)
    (m : Code Δ names) (a b c : Fin tags) :
    ComparisonExecutableTables.Row.mk m a b c ∈ S.rows T ↔ (T.table m).entry a b c :=
  ComparisonExecutableTables.serialize_entry (indices Δ names) (List.finRange tags)
    index_mem (fun _ => List.mem_finRange _) T m a b c

theorem rows_checked {p q : Bool} (T : IndexedTable S.embed (Code Δ names) p q)
    (le : Code Δ names → Code Δ names → Bool) (hl : ∀ m n, le m n = true ↔ T.le m n) :
    ComparisonExecutableTables.check S.candidate.obs S.embed le p q (S.rows T) = true :=
  ComparisonExecutableTables.serialize_checked S.candidate.obs S.candidate.obs_mem
    (indices Δ names) (List.finRange tags) index_mem (fun _ => List.mem_finRange _) S.embed le p q T hl

theorem literalRows_entry (T : Option ModExpr → IndexedTable S.embed (Code Δ names) false false)
    (he : ∀ p, p ∉ S.keys → ∀ m a b c, ¬ ((T (some p)).table m).entry a b c)
    (p : Option ModExpr) (m : Code Δ names) (a b c : Fin tags) :
    ComparisonExecutableTables.Row.mk m a b c ∈
      literalRows (S.rows (T none)) (S.keys.map fun k => (k,S.rows (T (some k)))) p ↔
        ((T p).table m).entry a b c := by
  cases p with
  | none => exact S.rows_entry _ m a b c
  | some p =>
    change ComparisonExecutableTables.Row.mk m a b c ∈
      ComparisonExecutableFamilies.lookup [] (S.keys.map fun k => (k,S.rows (T (some k)))) p ↔ _
    by_cases hp : p ∈ S.keys
    · rw [ComparisonExecutableFamilies.lookup_map_mem _ _ _ hp]
      exact S.rows_entry _ m a b c
    · rw [ComparisonExecutableFamilies.lookup_map_not_mem _ _ _ hp]
      exact ⟨fun h => (List.not_mem_nil h).elim,fun h => (he p hp m a b c h).elim⟩

theorem prodAt_entry (p : Option ModExpr) (m : Code Δ names) (a b c : Fin tags) :
    ComparisonExecutableTables.Row.mk m a b c ∈ S.candidate.prodAt p ↔
      ((S.model.prodTable p).table m).entry a b c :=
  S.literalRows_entry S.model.prodTable S.prod_empty p m a b c

theorem sumAt_entry (p : Option ModExpr) (m : Code Δ names) (a b c : Fin tags) :
    ComparisonExecutableTables.Row.mk m a b c ∈ S.candidate.sumAt p ↔
      ((S.model.sumTable p).table m).entry a b c :=
  S.literalRows_entry S.model.sumTable S.sum_empty p m a b c

theorem prod_extend (p : Option ModExpr) (m : Code Δ names) (x y : Fin observations → Bool) :
    ComparisonExecutableTables.extend S.candidate.obs S.candidate.embed order false false
      (S.candidate.prodAt p) m x y = (S.model.prodTable p).extend m x y :=
  ComparisonExecutableTables.extend_eq_of_table S.candidate.obs S.candidate.obs_mem S.embed order false false
    _ _ (S.prod_relation p) (S.prodAt_entry p) m x y

theorem sum_extend (p : Option ModExpr) (m : Code Δ names) (x y : Fin observations → Bool) :
    ComparisonExecutableTables.extend S.candidate.obs S.candidate.embed order false false
      (S.candidate.sumAt p) m x y = (S.model.sumTable p).extend m x y :=
  ComparisonExecutableTables.extend_eq_of_table S.candidate.obs S.candidate.obs_mem S.embed order false false
    _ _ (S.sum_relation p) (S.sumAt_entry p) m x y

theorem fn_extend (m : Code Δ names) (x y : Fin observations → Bool) :
    ComparisonExecutableTables.extend S.candidate.obs S.candidate.embed future true false
      S.candidate.fnRows m x y = S.model.fnTable.extend m x y :=
  ComparisonExecutableTables.extend_eq_of_table S.candidate.obs S.candidate.obs_mem S.embed future true false
    _ _ S.fn_relation (S.rows_entry S.model.fnTable) m x y

theorem literals_checked (T : Option ModExpr → IndexedTable S.embed (Code Δ names) false false)
    (hl : ∀ p m n, order m n = true ↔ (T p).le m n) :
    (S.keys.map fun p => (p,S.rows (T (some p)))).all
      (fun row => ComparisonExecutableTables.check S.candidate.obs S.embed order false false row.2) = true := by
  simp only [List.all_map,List.all_eq_true,Function.comp_def]
  exact fun p _ => S.rows_checked (T (some p)) order (hl (some p))

theorem tables_checked : S.candidate.tablesCheck = true := by
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨S.rows_checked (S.model.prodTable none) order (S.prod_relation none),
      S.rows_checked (S.model.sumTable none) order (S.sum_relation none)⟩,
      S.rows_checked S.model.fnTable future S.fn_relation⟩,
      S.literals_checked S.model.prodTable S.prod_relation⟩,
      S.literals_checked S.model.sumTable S.sum_relation⟩

theorem frozen_checked : S.candidate.frozen.all (fun row => S.candidate.monotoneCheck row.2) = true := by
  simp only [candidate,List.all_map,List.all_eq_true,Function.comp_def]
  exact fun row _ => (S.candidate.monotoneCheck_correct _).mpr row.2.monotone

theorem embedding_valid : ComparisonExecutableAgreement.Valid
    (ComparisonExecutableRangeAgreement.semanticOperations (checked_laws S.checked).2.1
      order (· * ·) expression expression_defined
      (S.candidate.pair S.candidate.prodRows) (S.candidate.pair S.candidate.sumRows) S.candidate.function)
    (fun x => fun m => S.embedding x m) where
  index x _ _ h := (S.embedding x).monotone h
  join x y := congrArg (fun X : ComparisonRelativeCoordinates.Coordinates (Code Δ names) (Fin observations → Bool) => fun m => X m) (map_sup S.embedding x y)
  meet x y := congrArg (fun X : ComparisonRelativeCoordinates.Coordinates (Code Δ names) (Fin observations → Bool) => fun m => X m) (map_inf S.embedding x y)
  reflect x y h := (ComparisonObserverRangeEncoding.le_correct _ _).mpr
    ((ComparisonObserverRangeEncoding.pack_le x y).mpr (S.agreement.reflect h))
  action m x := funext fun n => funext fun o =>
    (congrArg (fun X => X n o) (S.agreement.action m x)).trans
      (congrArg (fun v => S.embedding v n o)
        (ComparisonExecutableRangeAgreement.modal_decode (checked_laws S.checked).2.1
          (checked_laws S.checked).1 m x).symm)
  prod x y := funext fun m => funext fun o =>
    (congrFun (S.prod_extend none m (S.embedding x m) (S.embedding y m)) o).trans
      (congrArg (fun X => X m o) (S.agreement.prod x y))
  sum x y := funext fun m => funext fun o =>
    (congrFun (S.sum_extend none m (S.embedding x m) (S.embedding y m)) o).trans
      (congrArg (fun X => X m o) (S.agreement.sum x y))
  fn x y := funext fun m => funext fun o =>
    (congrFun (S.fn_extend m (S.embedding x 1) (S.embedding y 1)) o).trans
      (congrArg (fun X => X m o) (S.agreement.fn x y))

theorem embedding_checked : S.candidate.embeddingCheck = true := by
  apply (ComparisonExecutableRangeAgreement.check_correct (checked_laws S.checked).2.1
    order (· * ·) expression expression_defined (S.candidate.pair S.candidate.prodRows)
    (S.candidate.pair S.candidate.sumRows) S.candidate.function
    (indices Δ names) S.candidate.obs index_mem S.candidate.obs_mem S.candidate.defined).mpr
  simpa only [S.defined_pack] using S.embedding_valid

theorem structure_checked : S.candidate.structureCheck = true :=
  Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨by simpa only [decide_eq_true_eq] using S.names_supported,S.checked⟩,
      S.tables_checked⟩,S.embedding_checked⟩,S.frozen_checked⟩

def sourceData : ComparisonExecutableSyntax.Data (Code Δ names)
    (ComparisonRelativeCoordinates.Coordinates (Code Δ names) (Fin observations → Bool)) where
  total := ScalarDecision.defined Δ
  control := project Δ names
  shift m x := shift S.model.mul_mono m x
  prod p := ComparisonRelativeCoordinates.pair (S.model.prodTable p) (S.model.prod_order p)
  sum p := ComparisonRelativeCoordinates.pair (S.model.sumTable p) (S.model.sum_order p)
  fn := ComparisonRelativeCoordinates.fn S.model.fnTable S.model.fn_order
  join := (· ⊔ ·)
  meet := (· ⊓ ·)
  atom := S.model.atom
  unit := S.model.unit
  credit := S.model.credit
  bottom := ⊥
  frozen := S.model.frozen

def sourceAgreement : ComparisonExecutableSyntax.Agreement S.sourceData S.model id id where
  shift _ _ := rfl
  prod _ _ _ := rfl
  sum _ _ _ := rfl
  fn _ _ := rfl
  join _ _ := rfl
  meet _ _ := rfl
  atom _ := rfl
  unit := rfl
  credit := rfl
  bottom := rfl
  frozen := List.map_id _

def sourceDataMap : ComparisonExecutableSyntax.DataMap S.sourceData S.candidate.data
    (fun x => fun m => x m) id where
  total := rfl
  control _ := rfl
  shift _ _ := rfl
  prod p x y := funext fun m => (S.prod_extend p m (x m) (y m)).symm
  sum p x y := funext fun m => (S.sum_extend p m (x m) (y m)).symm
  fn x y := funext fun m => (S.fn_extend m (x 1) (y 1)).symm
  join _ _ := rfl
  meet _ _ := rfl
  atom v := (congrArg (fun X : ComparisonRelativeCoordinates.Coordinates (Code Δ names) (Fin observations → Bool) =>
    fun m => X m) (S.agreement.atom v)).trans (S.defined_pack _).symm
  unit := (congrArg (fun X : ComparisonRelativeCoordinates.Coordinates (Code Δ names) (Fin observations → Bool) =>
    fun m => X m) S.agreement.unit).trans (S.defined_pack _).symm
  credit := (congrArg (fun X : ComparisonRelativeCoordinates.Coordinates (Code Δ names) (Fin observations → Bool) =>
    fun m => X m) S.agreement.credit).trans (S.defined_pack _).symm
  bottom := rfl
  frozen := rfl

theorem eval_eq (a : CompareTy) (p : Option ModExpr) :
    S.candidate.data.eval a p = fun m => S.model.denote a p m :=
  (S.sourceDataMap.eval_eq a p).symm.trans
    (congrArg (fun X : ComparisonRelativeCoordinates.Coordinates (Code Δ names) (Fin observations → Bool) =>
      fun m => X m) (S.sourceAgreement.eval_eq_scalar rfl
        (fun m _ hm => (S.agreement.controls m hm).symm) p))

theorem evalRaw_eq (a : Ty) :
    S.candidate.data.evalRaw a = fun m => S.model.denote (.ofTy a) none m :=
  S.eval_eq (.ofTy a) none

theorem checked_of_bounds
    (hb : ∀ a b, Constraint.sub a b ∈ Δ → S.model.Related (.ofTy a) (.ofTy b)) :
    S.candidate.check = true :=
  S.candidate.check_correct.mpr ⟨S.structure_checked,fun a b hab => by
    simpa only [S.evalRaw_eq,Model.Related] using hb a b hab⟩

theorem separates_of_not_related
    (hb : ∀ a b, Constraint.sub a b ∈ Δ → S.model.Related (.ofTy a) (.ofTy b))
    {a b : CompareTy} (hab : ¬ S.model.Related a b) : S.candidate.separates a b = true :=
  (S.candidate.separates_correct a b).mpr ⟨S.checked_of_bounds hb,by
    simpa only [S.eval_eq,Model.Related] using hab⟩

end Source
end
end ModalityInference.ComparisonFiniteCertificate.Serialization
