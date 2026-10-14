import ModalityInference.Constraints

namespace ModalityInference

structure InferenceState where
  nextType : Nat := 0
  nextMode : Nat := 0
  constraints : Bounds := []
  deriving Repr

namespace InferenceState
def freshType (s : InferenceState) : Ty × InferenceState :=
  (.var (.flex s.nextType), {s with nextType := s.nextType + 1})
def freshMode (s : InferenceState) : ModExpr × InferenceState :=
  (.var (.flex s.nextMode), {s with nextMode := s.nextMode + 1})
def emit (s : InferenceState) (cs : Bounds) : InferenceState :=
  {s with constraints := s.constraints ++ cs}
def instantiate (s : InferenceState) (scheme : Scheme) : Ty × InferenceState :=
  let (cs, t) := scheme.instantiate s.nextType s.nextMode
  (t, {nextType := s.nextType + scheme.typeParams.length
       nextMode := s.nextMode + scheme.modParams.length
       constraints := s.constraints ++ cs ++ t.wellFormedBounds})
end InferenceState

/-- Quantified modal weakening. The caller chooses `p` fresh for the scheme;
each use can select a different modality satisfying the added subtype bound. -/
def Scheme.refineMode (s : Scheme) (p : Nat) : Scheme :=
  {s with modParams := s.modParams ++ [p]
          bounds := s.bounds ++ [.sub s.body (.modal s.body (.var (.flex p)))]
          body := .modal s.body (.var (.flex p))}

/-- Restrictions on a polymorphic binding remain under its quantifiers. Each use
freshens them together with the body, so two uses do not share inference variables. -/
def Scheme.share (s : Scheme) : Scheme :=
  {s with body := .modal s.body (.const Mode.aliased)
          bounds := s.bounds ++ [.sub s.body (.modal s.body (.const Mode.many))]}
def Scheme.lock (s : Scheme) (m : ModExpr) : Scheme :=
  {s with body := .modal s.body (.capture m)
          bounds := s.bounds ++ [.sub s.body (.modal s.body (.future m))]}

/-- Resolve a list of symbolic locks, with the outermost lock first. -/
def Scheme.lockAll (s : Scheme) : List ModExpr → Scheme
  | [] => s
  | m :: ms => (s.lockAll ms).lock m

/-- Indices count bindings, never locks. Locks nearest the binding act first. -/
def lookupScheme : AlgorithmicContext → Nat → RunResult Scheme
  | [], _ => .rejected "unbound term index"
  | .binding s :: Γ, i => match i with
    | 0 => match s with
      | none => .rejected "binding unavailable in this usage context"
      | some s => .success s
    | i + 1 => lookupScheme Γ i
  | .lock m :: Γ, i => do return (← lookupScheme Γ i).lock m

/-- Free-variable routing preserves de Bruijn positions and symbolic locks. -/
def splitContext (X Y : Finset Nat) : AlgorithmicContext → AlgorithmicContext × AlgorithmicContext
  | [] => ([], [])
  | .lock m :: Γ => let (a,b) := splitContext X Y Γ; (.lock m :: a, .lock m :: b)
  | .binding s :: Γ =>
    let (a,b) := splitContext (X.filter (0 < ·) |>.image (· - 1))
      (Y.filter (0 < ·) |>.image (· - 1)) Γ
    let shared := if 0 ∈ X ∧ 0 ∈ Y then s.map Scheme.share else s
    (.binding (if 0 ∈ X then shared else none) :: a,
     .binding (if 0 ∈ Y then shared else none) :: b)

structure Generated where
  type : Ty
  /-- Source syntax contains no capture schemes. -/
  term : RawTerm
  state : InferenceState
  deriving Repr

/-- Fuel bounds recursion depth and each closed-definition solve. Exhaustion is
propagated unchanged, including when it occurs in an unused definition. -/
def generate : Nat → AlgorithmicContext → RawTerm → InferenceState → RunResult Generated
  | 0, _, _, _ => .exhausted
  | fuel + 1, Γ, term, s => match term with
    | .var i => do
      let scheme ← lookupScheme Γ i
      let (t,s) := s.instantiate scheme
      return ⟨t, .var i, s⟩
    | .unit => .success ⟨.modal .unit .bottom, .unit, s⟩
    | .lam _ body => do
      let (a,s) := s.freshType
      let (m,s) := s.freshMode
      let r ← generate fuel (.binding (some (.mono a)) :: .lock m :: Γ) body s
      return ⟨.modal (.fn a r.type) m,
        .lam () r.term, r.state⟩
    | .app f x => do
      let (Γ₁,Γ₂) := splitContext f.freeVars x.freeVars Γ
      let f ← generate fuel Γ₁ f s
      let x ← generate fuel Γ₂ x f.state
      let (a,s) := x.state.freshType
      let (m,s) := s.freshMode
      return ⟨a, .app f.term x.term, s.emit [.sub f.type (.modal (.fn x.type a) m)]⟩
    | .pair x y | .stackPair x y => do
      let stack := match term with | .stackPair _ _ => true | _ => false
      let (Γ₁,Γ₂) := splitContext x.freeVars y.freeVars Γ
      let x ← generate fuel Γ₁ x s
      let y ← generate fuel Γ₂ y x.state
      let (a,s) := y.state.freshType
      let (b,s) := s.freshType
      let (m,s) := s.freshMode
      let s := s.emit [.sub x.type (.modal a m), .sub y.type (.modal b m)]
      let s := if stack then s.emit [.mode (.const Mode.localLower) m] else s
      return ⟨.modal (.prod a b) m,
        if stack then .stackPair x.term y.term else .pair x.term y.term, s⟩
    | .inl x | .inr x => do
      let left := match term with | .inl _ => true | _ => false
      let x ← generate fuel Γ x s
      let (a,s) := x.state.freshType
      let (b,s) := s.freshType
      let (m,s) := s.freshMode
      return ⟨.modal (.sum a b) m, if left then .inl x.term else .inr x.term,
        s.emit [.sub x.type (.modal (if left then a else b) m)]⟩
    | .split x body => do
      let (Γ₁,Γ₂) := splitContext x.freeVars (body.freeVars 3) Γ
      let x ← generate fuel Γ₁ x s
      let (a,s) := x.state.freshType
      let (b,s) := s.freshType
      let (m,s) := s.freshMode
      let r ← generate fuel
        (.binding (some (.mono (.modal .credit m))) ::
         .binding (some (.mono (.modal a m))) ::
         .binding (some (.mono (.modal b m))) :: Γ₂) body
        (s.emit [.sub x.type (.modal (.prod a b) m)])
      return ⟨r.type, .split x.term r.term, r.state⟩
    | .case x l r => do
      let (Γ₁,Γ₂) := splitContext x.freeVars (l.freeVars 1 ∪ r.freeVars 1) Γ
      let x ← generate fuel Γ₁ x s
      let (a,s) := x.state.freshType
      let (b,s) := s.freshType
      let (c,s) := s.freshType
      let (m,s) := s.freshMode
      let l ← generate fuel (.binding (some (.mono (.modal a m))) :: Γ₂) l
        (s.emit [.sub x.type (.modal (.sum a b) m)])
      let r ← generate fuel (.binding (some (.mono (.modal b m))) :: Γ₂) r l.state
      return ⟨c, .case x.term l.term r.term, r.state.emit [.sub l.type c, .sub r.type c]⟩
    | .reuse k x y => do
      let (Γ₁,Γ₂₃) := splitContext k.freeVars (x.freeVars ∪ y.freeVars) Γ
      let (Γ₂,Γ₃) := splitContext x.freeVars y.freeVars Γ₂₃
      let k ← generate fuel Γ₁ k s
      let x ← generate fuel Γ₂ x k.state
      let y ← generate fuel Γ₃ y x.state
      let (a,s) := y.state.freshType
      let (b,s) := s.freshType
      let (m,s) := s.freshMode
      let (n,s) := s.freshMode
      return ⟨.modal (.prod a b) m, .reuse k.term x.term y.term,
        s.emit [.sub k.type (.modal .credit n), .mode n (.const Mode.uniqueOnly),
          .sub x.type (.modal a m), .sub y.type (.modal b m),
          .mode (.compose n (.const Mode.many)) m]⟩
    | .region t => do
      let t ← generate fuel Γ t s
      let (a,s) := t.state.freshType
      return ⟨a, .region t.term, s.emit [.sub t.type (.modal a (.const Mode.global))]⟩
    | .defn rhs body => do
      if rhs.freeVars != ∅ then return ← .rejected "def RHS must be closed in term variables"
      let r ← generate fuel [] rhs {nextType := s.nextType, nextMode := s.nextMode}
      let solved ← solveFrom fuel r.state.nextType r.state.nextMode r.state.constraints
      let scheme := Scheme.generalize solved.bounds (solved.substitution.ty r.type)
      let body ← generate fuel (.binding (some scheme) :: Γ) body
        {s with nextType := solved.nextType, nextMode := solved.nextMode}
      return ⟨body.type, .defn r.term body.term, body.state⟩

structure Inferred where
  scheme : Scheme
  /-- The original source term; solving changes types and bounds only. -/
  elaborated : RawTerm
  substitution : Substitution
  residual : Bounds
  trace : List RewriteRule
  deriving Repr

def initialInferenceState (Γ : Context) : InferenceState :=
  {nextType := Γ.foldl (fun n s => max n (s.map Scheme.freshTypeIndex |>.getD 0)) 0
   nextMode := Γ.foldl (fun n s => max n (s.map Scheme.freshModeIndex |>.getD 0)) 0}

def generalizeOver (Γ : Context) (cs : Bounds) (t : Ty) : Scheme :=
  let s := Scheme.generalize cs t
  let ft := Γ.foldl (fun xs s => xs ∪ (s.map Scheme.freeTypes |>.getD ∅)) ∅
  let fm := Γ.foldl (fun xs s => xs ∪ (s.map Scheme.freeModes |>.getD ∅)) ∅
  {s with typeParams := s.typeParams.filter (fun n => .flex n ∉ ft)
          modParams := s.modParams.filter (fun n => .flex n ∉ fm)}

/-- Full inference, retaining principal residual bounds rather than committing the
finite consistency witness to the inferred scheme. -/
def infer (fuel : Nat) (Γ : Context) (term : RawTerm) : RunResult Inferred := do
  let r ← generate fuel (Γ.map ContextEntry.binding) term (initialInferenceState Γ)
  let s ← solveFrom fuel r.state.nextType r.state.nextMode r.state.constraints
  let context := Γ.map (Option.map (fun t => t.subst s.substitution))
  let scheme := generalizeOver context s.bounds (s.substitution.ty r.type)
  return ⟨scheme, r.term, s.substitution, s.bounds, s.trace⟩

end ModalityInference
