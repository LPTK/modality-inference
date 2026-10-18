import ModalityInference.Proofs.ComparisonLayoutWorlds
import ModalityInference.Proofs.ComparisonSignedObservation
import ModalityInference.Proofs.ComparisonSignedPoints

/-! One symbolic modality substitution acts uniformly across every observer
route. Actual endpoint compilation, nominal point equations and constant-selector
separation preserve this shared strategy without changing the original theory. -/
namespace ModalityInference.ComparisonLayoutWorlds
open ComparisonSignedEndpoints ComparisonSignedObservation ComparisonStructuralLayout
open ComparisonControls SchemeModeSynthesis

/-- Coordinate projection commutes with the shared symbolic action even away
from the declared guard. Definedness is kept in its separate original formula. -/
theorem project_subst (modes : ModVar → ModExpr) (input : Nat → Bool) (m : ModExpr) :
    (m.subst modes).project.locality.eval input=m.project.locality.eval (strategy modes input) ∧
    (m.subst modes).project.affinity.eval input=m.project.affinity.eval (strategy modes input) ∧
    (m.subst modes).project.uniqueness.eval input=m.project.uniqueness.eval (strategy modes input) := by
  induction m <;> simp_all [ModExpr.subst,ModExpr.project,BoolExpr.eval,
    strategy_coordinate modes input _ 0 (by decide),
    strategy_coordinate modes input _ 1 (by decide),
    strategy_coordinate modes input _ 2 (by decide),coordinate]

theorem route_action (modes : ModVar → ModExpr) (world : Nat → Nat → Bool)
    (route : Route) (m : ModExpr) (value : Bool) :
    (rename (routeAtom route) (action (m.subst modes) value)).eval
        (ComparisonSignedWorlds.rawValue decode id id world)=
      (rename (routeAtom route) (action m value)).eval
        (ComparisonSignedWorlds.rawValue decode id (strategy modes) world) := by
  have hp := project_subst modes (world (routeCode route+1)) m
  simp only [rename,SymbolicCNF.substitute_eval,action,BoolExpr.any,List.map_cons,List.map_nil,
    List.foldr_cons,List.foldr_nil,BoolExpr.eval,coordinateTest,BoolExpr.equal,coordinateBits,
    Coordinate.modalWith,rawValue_choice,rawValue_mode,id_eq,hp.1,hp.2.1,hp.2.2]

theorem context_fixed (modes : ModVar → ModExpr) (world : Nat → Nat → Bool)
    (layout : Layout) (route : Route) (a : Ty) :
    ((context layout modes).fixed route a).eval
        (ComparisonSignedWorlds.rawValue decode id id world)=
      ((context layout ModExpr.var).fixed route a).eval
        (ComparisonSignedWorlds.rawValue decode id (strategy modes) world) := by
  simp only [context]
  cases nodeAt layout route <;> simp [BoolExpr.eval]

theorem context_choose (modes : ModVar → ModExpr) (world : Nat → Nat → Bool)
    (layout : Layout) (route : Route) :
    ((context layout modes).choose route).eval
        (ComparisonSignedWorlds.rawValue decode id id world)=
      ((context layout ModExpr.var).choose route).eval
        (ComparisonSignedWorlds.rawValue decode id (strategy modes) world) := by
  simp [context,BoolExpr.eval]

theorem context_action (modes : ModVar → ModExpr) (world : Nat → Nat → Bool)
    (layout : Layout) (route : Route) (m : ModExpr) :
    (((context layout modes).action route m).1.eval
        (ComparisonSignedWorlds.rawValue decode id id world)=
      ((context layout ModExpr.var).action route m).1.eval
        (ComparisonSignedWorlds.rawValue decode id (strategy modes) world)) ∧
    (((context layout modes).action route m).2.eval
        (ComparisonSignedWorlds.rawValue decode id id world)=
      ((context layout ModExpr.var).action route m).2.eval
        (ComparisonSignedWorlds.rawValue decode id (strategy modes) world)) := by
  simpa only [context,ModExpr.subst_id] using
    And.intro (route_action modes world route m false) (route_action modes world route m true)

/-- Substituting one symbolic modality image family in every public endpoint
is exactly evaluating its unchanged syntax with one strategy at every route. -/
theorem interpret_strategy (modes : ModVar → ModExpr) (world : Nat → Nat → Bool)
    (layout : Layout) (keys : List Nat) (images : Call → Bool) (route : Route) (a : Ty) :
    interpret keys (context layout modes) (ComparisonSignedWorlds.rawValue decode id id world)
        images route a=
      interpret keys (context layout ModExpr.var)
        (ComparisonSignedWorlds.rawValue decode id (strategy modes) world) images route a := by
  induction a generalizing route with
  | var v =>
    cases v with
    | rigid n => exact context_fixed modes world layout route _
    | flex n =>
      simp only [interpret,reference]
      split
      · rfl
      · exact context_fixed modes world layout route _
  | unit | credit => exact context_fixed modes world layout route _
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [interpret,context_choose modes world layout route,iha,ihb]
  | modal a m ih =>
    simp only [interpret,ih,(context_action modes world layout route m).1,
      (context_action modes world layout route m).2]

theorem basisImages_strategy (size : Nat → Nat) (images : Nat → (Nat → Bool) → Bool)
    (scalar : (Nat → Bool) → Nat → Bool) (world : Nat → Nat → Bool) :
    ComparisonSignedPoints.basisImages size images
        (ComparisonSignedPoints.raw decode scalar world)=
      ComparisonSignedPoints.basisImages size images
        (ComparisonSignedPoints.raw decode id world) := by
  funext call
  apply congrArg (images call.name)
  funext i
  simp [ComparisonSignedPoints.basisPoint,ComparisonSignedPoints.raw]

theorem compiled_strategy {fuel keys layout left right clauses}
    (h : compileGuards fuel (ComparisonSignedEndpoints.compile keys
      (context layout ModExpr.var) left right)=.success clauses)
    (modes : ModVar → ModExpr) (world : Nat → Nat → Bool)
    (images : Call → Bool) :
    (∀c∈clauses,c.Holds (ComparisonSignedPoints.raw decode (strategy modes) world) images) ↔
      (interpret keys (context layout modes) (ComparisonSignedPoints.raw decode id world)
          images [] left=true →
       interpret keys (context layout modes) (ComparisonSignedPoints.raw decode id world)
          images [] right=true) := by
  rw [compileGuards_correct h,ComparisonSignedEndpoints.compile_correct]
  have hl : interpret keys (context layout modes) (ComparisonSignedPoints.raw decode id world)
      images [] left = interpret keys (context layout ModExpr.var)
        (ComparisonSignedPoints.raw decode (strategy modes) world) images [] left :=
    interpret_strategy modes world layout keys images [] left
  have hr : interpret keys (context layout modes) (ComparisonSignedPoints.raw decode id world)
      images [] right = interpret keys (context layout ModExpr.var)
        (ComparisonSignedPoints.raw decode (strategy modes) world) images [] right :=
    interpret_strategy modes world layout keys images [] right
  rw [hl,hr]

/-- The concrete point query is equivalent to all endpoint clauses under the
same scalar strategy and the same image function at every occurrence. -/
theorem pointQuery_valid (size : Nat → Nat) (theory : CNF) (clauses : List CompiledClause)
    (scalar : (Nat → Bool) → Nat → Bool) (images : Nat → (Nat → Bool) → Bool) :
    ComparisonWorldClauses.Valid
      (ComparisonSignedWorlds.nominalValue
        (ComparisonSignedWorlds.calls (clauses.map ComparisonSignedPoints.clause)) id
        (ComparisonSignedPoints.nominalImages (ComparisonSignedWorlds.calls clauses) size images))
      scalar (pointQuery size theory clauses) ↔
    ∀world,∀c∈clauses,CNFHolds (ComparisonSignedPoints.raw decode scalar world) theory →
      c.Holds (ComparisonSignedPoints.raw decode scalar world)
        (ComparisonSignedPoints.basisImages size images (ComparisonSignedPoints.raw decode scalar world)) := by
  exact (ComparisonSignedWorlds.query_valid _ _ _ _ _ _).trans
    (ComparisonSignedPoints.abstract_valid size decode scalar images theory clauses).symm

theorem compiled_basis_strategy {fuel keys layout left right clauses}
    (h : compileGuards fuel (ComparisonSignedEndpoints.compile keys
      (context layout ModExpr.var) left right)=.success clauses)
    (size : Nat → Nat) (theory : CNF) (modes : ModVar → ModExpr)
    (images : Nat → (Nat → Bool) → Bool) :
    (∀world,∀c∈clauses,CNFHolds (ComparisonSignedPoints.raw decode (strategy modes) world) theory →
      c.Holds (ComparisonSignedPoints.raw decode (strategy modes) world)
        (ComparisonSignedPoints.basisImages size images
          (ComparisonSignedPoints.raw decode (strategy modes) world))) ↔
    ∀world,CNFHolds (ComparisonSignedPoints.raw decode (strategy modes) world) theory →
      (interpret keys (context layout modes) (ComparisonSignedPoints.raw decode id world)
          (ComparisonSignedPoints.basisImages size images (ComparisonSignedPoints.raw decode id world)) [] left=true →
       interpret keys (context layout modes) (ComparisonSignedPoints.raw decode id world)
          (ComparisonSignedPoints.basisImages size images (ComparisonSignedPoints.raw decode id world)) [] right=true) := by
  simp only [basisImages_strategy]
  constructor
  · intro hv world ht
    apply (compiled_strategy h modes world _).mp
    exact fun c hc=>hv world c hc ht
  · intro hv world c hc ht
    exact (compiled_strategy h modes world _).mpr (hv world ht) c hc

/-- Actual endpoint compilation, route tagging and finite point abstraction all
share one symbolic modality substitution before constant-selector separation. -/
theorem endpoint_selectors_iff {fuel keys layout left right clauses}
    (h : compileGuards fuel (ComparisonSignedEndpoints.compile keys
      (context layout ModExpr.var) left right)=.success clauses)
    (size : Nat → Nat) (theory : CNF) (modes : ModVar → ModExpr)
    (images : Nat → (Nat → Bool) → Bool) :
    (∀world,CNFHolds (ComparisonSignedPoints.raw decode (strategy modes) world) theory →
      (interpret keys (context layout modes) (ComparisonSignedPoints.raw decode id world)
          (ComparisonSignedPoints.basisImages size images (ComparisonSignedPoints.raw decode id world)) [] left=true →
       interpret keys (context layout modes) (ComparisonSignedPoints.raw decode id world)
          (ComparisonSignedPoints.basisImages size images (ComparisonSignedPoints.raw decode id world)) [] right=true)) ↔
    ∃choice,ComparisonWorldClauses.SelectedValid
      (ComparisonSignedWorlds.nominalValue
        (ComparisonSignedWorlds.calls (clauses.map ComparisonSignedPoints.clause)) id
        (ComparisonSignedPoints.nominalImages (ComparisonSignedWorlds.calls clauses) size images))
      (strategy modes) (pointQuery size theory clauses) choice := by
  rw [←ComparisonWorldClauses.selectors_iff,pointQuery_valid]
  exact (compiled_basis_strategy h size theory modes images).symm

end ModalityInference.ComparisonLayoutWorlds
