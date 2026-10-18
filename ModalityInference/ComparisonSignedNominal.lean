import ModalityInference.ComparisonSignedStrategySynthesis

/-! After world separation, image literals remain signed calls. The other
literals are fixed global selectors or nominal observer inputs. This decoder
retains their distinct namespaces for the signed relational solver. -/
namespace ModalityInference.ComparisonSignedNominal

open ComparisonSignedEndpoints

def isImage (v : Nat) : Bool := v%4==2

def guardAtom (v : Nat) : Nat :=
  if v%2=1 then 2*ComparisonWorldModes.worldConstant (v/2)+1 else 2*(v/4)

def guardDecode (v : Nat) : Sum Nat Nat :=
  if v%2=1 then .inl (v/2) else .inr (v/2)

def payload (names : List Call) (call : Call) (i : Nat) : Nat :=
  2*ComparisonSignedPoints.pointAtom names call i

def parseClause (names : List Call) : ModalityInference.Clause → Option CompiledClause
  | [] => some ⟨[],[]⟩
  | (v,p)::rest => do
      let parsed ← parseClause names rest
      if isImage v then
        let call ← names[v/4]?
        return ⟨parsed.guard,(call,p)::parsed.literals⟩
      else return ⟨(guardAtom v,p)::parsed.guard,parsed.literals⟩

def parse (names : List Call) : CNF → Option (List CompiledClause)
  | [] => some []
  | c::cs => do
      let head ← parseClause names c
      let tail ← parse names cs
      return head::tail

def prepare (size : Nat → Nat) (decode : Nat → Nat × Nat)
    (theory : CNF) (clauses : List CompiledClause) : Option (List CompiledClause) :=
  parse (ComparisonSignedWorlds.calls (clauses.map ComparisonSignedPoints.clause))
    (ComparisonSignedStrategySynthesis.nominalQuery size decode theory clauses)

end ModalityInference.ComparisonSignedNominal
