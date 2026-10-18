import ModalityInference.ComparisonGuardedWorldModes
import ModalityInference.ComparisonSignedEndpointQueries

/-! Symbolic shape alternatives activate endpoint queries through shared
constant guards. Their active type and mode obligations are synthesized jointly. -/
namespace ModalityInference.ComparisonGuardedEndpointQueries
open ComparisonSignedSynthesis ComparisonSignedQueries ComparisonSignedEndpoints

structure Source where
  guard : Clause
  source : ComparisonSignedEndpointQueries.Source

def Source.entries (source : Source) (size : Nat → Nat) : List ComparisonGuardedWorldModes.Entry :=
  (source.source.worlds size).map fun clause=>⟨source.guard,clause⟩

def entries (size : Nat → Nat) (sources : List Source) : List ComparisonGuardedWorldModes.Entry :=
  sources.flatMap fun source=>source.entries size

def guardPrefix (total : Nat) (guard : Clause) : Clause :=
  guard.map fun literal=>(2*ComparisonGuardedWorldModes.externalAtom total literal.1+1,literal.2)

def gate (total : Nat) (guard : Clause) (query : Query) : Query :=
  { query with clauses:=query.clauses.map fun clause=>{clause with guard:=guardPrefix total guard++clause.guard} }

def Source.nominal (source : Source) (total offset : Nat) (size : Nat → Nat) : Option Query := do
  let query ← source.source.nominal offset size
  return gate total source.guard query

def prepare (total : Nat) (size : Nat → Nat) : Nat → List Source → Option (List Query)
  | _,[] => some []
  | offset,source::sources => do
      let head ← source.nominal total offset size
      let tail ← prepare total size (offset+(source.source.worlds size).length) sources
      return head::tail

def shapeValue (size : Nat → Nat) (sources : List Source) (selectors : Nat → Bool) : Nat → Bool :=
  ComparisonGuardedWorldModes.externalValue (entries size sources).length selectors

def scalarQuery (side : Nat → Bool) (flex : List Nat) (size : Nat → Nat) (sources : List Source)
    (shapeCondition : CNF) : CNF :=
  ComparisonPropagation.rename (ComparisonGuardedWorldModes.externalAtom (entries size sources).length)
    shapeCondition ++ ComparisonGuardedWorldModes.query side flex (entries size sources)

def modes (side : Nat → Bool) (flex : List Nat) (input : Input) (sources : List Source)
    (selectors : Nat → Bool) :=
  ComparisonGuardedWorldModes.witness side flex (entries (fun n=>(input.bases n).length) sources) selectors

def run (fuel : Nat) (input : Input) (side : Nat → Bool) (flex : List Nat)
    (sources : List Source) (shapeCondition : CNF) : RunResult ComparisonSignedQuerySolver.Solution :=
  match prepare (entries (fun n=>(input.bases n).length) sources).length
      (fun n=>(input.bases n).length) 0 sources with
  | none => .rejected "guarded endpoint nominal parsing failed"
  | some queries => ComparisonSignedQuerySolver.run fuel input queries
      (scalarQuery side flex (fun n=>(input.bases n).length) sources shapeCondition)

/-- The separated clauses of one source are shared by nominal parsing,
selector indexing, and the scalar query. -/
structure CachedSource where
  guard : Clause
  names : List Call
  parsedNames : List Call
  worlds : List ComparisonWorldClauses.WorldClause

def Source.cache (source : Source) (size : Nat → Nat) : CachedSource where
  guard := source.guard
  names := ComparisonSignedWorlds.calls source.source.clauses
  parsedNames := ComparisonSignedWorlds.calls
    (source.source.clauses.map ComparisonSignedPoints.clause)
  worlds := source.source.worlds size

def CachedSource.entries (source : CachedSource) : List ComparisonGuardedWorldModes.Entry :=
  source.worlds.map fun clause=>⟨source.guard,clause⟩

def cachedEntries (sources : List CachedSource) : List ComparisonGuardedWorldModes.Entry :=
  sources.flatMap CachedSource.entries

def CachedSource.nominal (source : CachedSource) (total offset : Nat) : Option Query := do
  let clauses ← ComparisonSignedNominal.parse source.parsedNames
    (ComparisonWorldOffsets.nominal offset source.worlds)
  return gate total source.guard {
    payload := ComparisonSignedNominal.payload source.names
    decode := ComparisonSignedNominal.guardDecode
    theory := []
    clauses := clauses }

def prepareCached (total : Nat) : Nat → List CachedSource → Option (List Query)
  | _,[] => some []
  | offset,source::sources => do
      let head ← source.nominal total offset
      let tail ← prepareCached total (offset+source.worlds.length) sources
      return head::tail

theorem cachedEntries_map (size : Nat → Nat) (sources : List Source) :
    cachedEntries (sources.map fun (source : Source)=>source.cache size)=entries size sources := by
  simp only [cachedEntries,List.flatMap_map,entries,Source.entries,CachedSource.entries,Source.cache]

theorem Source.cache_nominal (source : Source) (size : Nat → Nat) (total offset : Nat) :
    (source.cache size).nominal total offset=source.nominal total offset size := by
  simp only [Source.cache,CachedSource.nominal,Source.nominal,
    ComparisonSignedEndpointQueries.Source.nominal,ComparisonSignedNominalEdges.prepare,
    ComparisonSignedEndpointQueries.Source.worlds]
  cases ComparisonSignedNominal.parse
    (ComparisonSignedWorlds.calls (source.source.clauses.map ComparisonSignedPoints.clause))
    (ComparisonWorldOffsets.nominal offset
      (ComparisonSignedStrategySynthesis.worlds size source.source.decode source.source.theory source.source.clauses)) <;> rfl

theorem prepareCached_map (total : Nat) (size : Nat → Nat) (offset : Nat) (sources : List Source) :
    prepareCached total offset (sources.map fun (source : Source)=>source.cache size)=prepare total size offset sources := by
  induction sources generalizing offset with
  | nil => rfl
  | cons source sources ih =>
    simp only [List.map_cons,prepareCached,prepare,Source.cache_nominal]
    change (do
      let head ← source.nominal total offset size
      let tail ← prepareCached total (offset+(source.source.worlds size).length)
        (sources.map fun (source : Source)=>source.cache size)
      return head::tail)=_
    simp only [ih]

/-- Cache each source before the common nominal and scalar solve. -/
def runCached (fuel : Nat) (input : Input) (side : Nat → Bool) (flex : List Nat)
    (sources : List Source) (shapeCondition : CNF) : RunResult ComparisonSignedQuerySolver.Solution :=
  let size := fun n=>(input.bases n).length
  let cached := sources.map fun source=>source.cache size
  let allEntries := cachedEntries cached
  match prepareCached allEntries.length 0 cached with
  | none => .rejected "guarded endpoint nominal parsing failed"
  | some queries => ComparisonSignedQuerySolver.run fuel input queries
      (ComparisonPropagation.rename (ComparisonGuardedWorldModes.externalAtom allEntries.length)
        shapeCondition ++ ComparisonGuardedWorldModes.query side flex allEntries)

@[csimp] theorem run_eq_runCached : @run = @runCached := by
  funext fuel input side flex sources shapeCondition
  simp only [run,runCached,cachedEntries_map,prepareCached_map,scalarQuery]

end ModalityInference.ComparisonGuardedEndpointQueries
