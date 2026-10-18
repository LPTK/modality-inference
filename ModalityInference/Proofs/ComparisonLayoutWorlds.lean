import ModalityInference.ComparisonLayoutWorlds
import ModalityInference.Proofs.ComparisonSignedWorlds
import ModalityInference.Proofs.SchemeModeWitness

/-! The actual route encoding gives disjoint scalar worlds. Route-wise evaluation
uses one common strategy and retains all nominal observations literally. -/
namespace ModalityInference.ComparisonLayoutWorlds
open ComparisonSignedEndpoints ComparisonSignedObservation ComparisonStructuralLayout

@[simp] theorem location_local (i : Nat) : location (localAtom i)=([],i) := by
  rw [location]
  simp [localAtom]

@[simp] theorem location_left (i : Nat) :
    location (leftAtom i)=(false::(location i).1,(location i).2) := by
  have h : (3*i+1)/3=i := by omega
  rw [location]
  simp [leftAtom,h]

@[simp] theorem location_right (i : Nat) :
    location (rightAtom i)=(true::(location i).1,(location i).2) := by
  have h : (3*i+2)/3=i := by omega
  rw [location]
  simp [rightAtom,h]

@[simp] theorem location_route (route : Route) (i : Nat) :
    location (routeAtom route (localAtom i))=(route,i) := by
  induction route with
  | nil => exact location_local i
  | cons direction rest ih =>
    cases direction <;> simp [routeAtom,ih]

@[simp] theorem decode_mode (route : Route) (i : Nat) :
    decode (routeAtom route (modeAtom i))=(routeCode route+1,i) := by
  have h : (4*i+2)/4=i := by omega
  simp [decode,modeAtom,h]

@[simp] theorem decode_basis (route : Route) (i : Nat) :
    decode (routeAtom route (basisAtom i))=(0,routeAtom route (basisAtom i)) := by
  simp [decode,basisAtom]

@[simp] theorem decode_head (route : Route) (i : Nat) :
    decode (routeAtom route (headAtom i))=(0,routeAtom route (headAtom i)) := by
  simp [decode,headAtom]

@[simp] theorem decode_choice (route : Route) (i : Nat) :
    decode (routeAtom route (choiceAtom i))=(0,routeAtom route (choiceAtom i)) := by
  simp [decode,choiceAtom]

theorem routeCode_injective : Function.Injective routeCode := by
  intro left
  induction left with
  | nil =>
    intro right h
    cases right with
    | nil => rfl
    | cons direction rest => cases direction <;> simp [routeCode] at h
  | cons direction rest ih =>
    intro right h
    cases right with
    | nil => cases direction <;> simp [routeCode] at h
    | cons direction' rest' =>
      cases direction <;> cases direction' <;> simp only [routeCode] at h
      · exact congrArg (false::·) (ih (by omega))
      · omega
      · omega
      · exact congrArg (true::·) (ih (by omega))

theorem location_inverse (v : Nat) :
    routeAtom (location v).1 (localAtom (location v).2)=v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    rw [location]
    split
    next hv =>
      simp only [routeAtom,id_eq,localAtom]
      omega
    next hv =>
      have hlt : v/3<v := by omega
      have ht := ih (v/3) hlt
      simp only [routeAtom,Function.comp_def]
      by_cases h : v%3=2
      · simp only [h,beq_self_eq_true,ite_true,rightAtom]
        rw [ht]
        omega
      · simp only [show (v%3==2)=false from beq_eq_false_iff_ne.mpr h,
          Bool.false_eq_true,ite_false,leftAtom]
        rw [ht]
        omega

@[simp] theorem rawValue_mode (nominal scalar : (Nat → Bool) → Nat → Bool)
    (world : Nat → Nat → Bool) (route : Route) (i : Nat) :
    ComparisonSignedWorlds.rawValue decode nominal scalar world
      (routeAtom route (modeAtom i))=scalar (world (routeCode route+1)) i := by
  simp [ComparisonSignedWorlds.rawValue,ComparisonWorldClauses.shared]

@[simp] theorem rawValue_basis (nominal scalar : (Nat → Bool) → Nat → Bool)
    (world : Nat → Nat → Bool) (route : Route) (i : Nat) :
    ComparisonSignedWorlds.rawValue decode nominal scalar world
      (routeAtom route (basisAtom i))=nominal (world 0) (routeAtom route (basisAtom i)) := by
  simp [ComparisonSignedWorlds.rawValue,ComparisonWorldClauses.shared]

@[simp] theorem rawValue_head (nominal scalar : (Nat → Bool) → Nat → Bool)
    (world : Nat → Nat → Bool) (route : Route) (i : Nat) :
    ComparisonSignedWorlds.rawValue decode nominal scalar world
      (routeAtom route (headAtom i))=nominal (world 0) (routeAtom route (headAtom i)) := by
  simp [ComparisonSignedWorlds.rawValue,ComparisonWorldClauses.shared]

@[simp] theorem rawValue_choice (nominal scalar : (Nat → Bool) → Nat → Bool)
    (world : Nat → Nat → Bool) (route : Route) (i : Nat) :
    ComparisonSignedWorlds.rawValue decode nominal scalar world
      (routeAtom route (choiceAtom i))=nominal (world 0) (routeAtom route (choiceAtom i)) := by
  simp [ComparisonSignedWorlds.rawValue,ComparisonWorldClauses.shared]

/-- Every route uses the same strategy; only its raw scalar input varies. -/
theorem rawValue_apply (scalar : (Nat → Bool) → Nat → Bool)
    (world : Nat → Nat → Bool) :
    ComparisonSignedWorlds.rawValue decode id scalar world =
      apply scalar (ComparisonSignedWorlds.rawValue decode id id world) := by
  funext v
  unfold apply
  by_cases h : (location v).2%4=2
  · have hm : (fun i=>ComparisonSignedWorlds.rawValue decode id id world
        (routeAtom (location v).1 (modeAtom i)))=world (routeCode (location v).1+1) := by
      funext i
      exact rawValue_mode id id world _ i
    simp only [h,ite_true,hm]
    simp [ComparisonSignedWorlds.rawValue,decode,h,ComparisonWorldClauses.shared]
  · simp [ComparisonSignedWorlds.rawValue,decode,h,ComparisonWorldClauses.shared]

theorem scalarWorld_injective : Function.Injective (fun route=>routeCode route+1) := by
  intro left right h
  exact routeCode_injective (Nat.add_right_cancel h)

/-- Every symbolic formula reads the same scalar strategy at a route's input. -/
theorem scalarFormula (nominal scalar : (Nat → Bool) → Nat → Bool)
    (world : Nat → Nat → Bool) (route : Route) (e : BoolExpr) :
    (ComparisonStructuralLayout.rename (fun i=>routeAtom route (modeAtom i)) e).eval
        (ComparisonSignedWorlds.rawValue decode nominal scalar world)=
      e.eval (scalar (world (routeCode route+1))) := by
  rw [ComparisonStructuralLayout.rename,SymbolicCNF.substitute_eval]
  congr 1
  funext i
  exact rawValue_mode nominal scalar world route i

end ModalityInference.ComparisonLayoutWorlds
