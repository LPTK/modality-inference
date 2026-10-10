import ModalityInference.Core.Syntax

namespace ModalityInference

inductive Location where
  | heap (cell : Nat)
  | stack (frame cell : Nat)
  deriving Repr, DecidableEq, BEq

/-- An infinite arithmetic progression. Positive stride is a semantic precondition. -/
structure Supply where
  start : Nat := 0
  stride : Nat := 1
  deriving Repr, DecidableEq
def Supply.at (s : Supply) (n : Nat) : Nat := s.start + s.stride * n
def Supply.tail (s : Supply) : Supply := { s with start := s.at 1 }
def Supply.slice (s : Supply) (k i : Nat) : Supply := ⟨s.at i, s.stride * k⟩

structure Supplies where
  heap : Supply := {}
  stack : Supply := {}
  currentFrame : Nat := 0
  frames : Supply := ⟨1, 1⟩
  deriving Repr, DecidableEq

namespace Supplies
def branch (s : Supplies) (k i : Nat) : Supplies :=
  { heap := s.heap.slice k i
    stack := s.stack.slice k i
    currentFrame := s.currentFrame
    frames := s.frames.slice k i }
def afterHeap (s : Supplies) : Supplies := { s with heap := s.heap.tail }
def afterStack (s : Supplies) : Supplies := { s with stack := s.stack.tail }
def enter (s : Supplies) : Supplies :=
  { s with currentFrame := s.frames.start, stack := {}, frames := s.frames.tail }
def Valid (s : Supplies) : Prop :=
  0 < s.heap.stride ∧ 0 < s.stack.stride ∧ 0 < s.frames.stride ∧
    ∀ n, s.frames.at n ≠ s.currentFrame
def FreshLocation (s : Supplies) : Location → Prop
  | .heap c => ∃ n, c = s.heap.at n
  | .stack f c => (f = s.currentFrame ∧ ∃ n, c = s.stack.at n) ∨
      ∃ n, f = s.frames.at n
end Supplies

inductive Value where
  | unit
  | credit (location : Location)
  | pair (location : Location) (first second : Value)
  | inl (value : Value)
  | inr (value : Value)
  | closure (environment : List Value) (capture : Capture) (body : AnnotatedTerm)
  deriving Repr

abbrev Environment := List Value

/-- Erase unused environment entries, independently of typing metadata. Indices stay stable. -/
def trimEnvironment (γ : Environment) (used : Finset Nat) : Environment :=
  γ.mapIdx fun i v => if i ∈ used then v else .unit

def evalFuel : Nat → Supplies → Environment → AnnotatedTerm → RunResult Value
  | 0, _, _, _ => .exhausted
  | fuel + 1, s, γ, term => match term with
    | .var i => match γ[i]? with
      | some v => .success v
      | none => .rejected "unbound term variable"
    | .unit => .success .unit
    | .lam captured body =>
      .success (.closure (trimEnvironment γ (body.freeVars 1)) captured body)
    | .app f a => do
      let vf ← evalFuel fuel (s.branch 3 0) γ f
      let va ← evalFuel fuel (s.branch 3 1) γ a
      match vf with
      | .closure γ' _ body => evalFuel fuel (s.branch 3 2) (va :: γ') body
      | _ => .rejected "application of a non-function"
    | .pair a b => do
      let va ← evalFuel fuel (s.afterHeap.branch 2 0) γ a
      let vb ← evalFuel fuel (s.afterHeap.branch 2 1) γ b
      return .pair (.heap s.heap.start) va vb
    | .stackPair a b => do
      let va ← evalFuel fuel (s.afterStack.branch 2 0) γ a
      let vb ← evalFuel fuel (s.afterStack.branch 2 1) γ b
      return .pair (.stack s.currentFrame s.stack.start) va vb
    | .inl a => return .inl (← evalFuel fuel s γ a)
    | .inr a => return .inr (← evalFuel fuel s γ a)
    | .defn rhs body => do
      let v ← evalFuel fuel (s.branch 2 0) [] rhs
      evalFuel fuel (s.branch 2 1) (v :: γ) body
    | .split a body => do
      let v ← evalFuel fuel (s.branch 2 0) γ a
      match v with
      | .pair l x y => evalFuel fuel (s.branch 2 1) (.credit l :: x :: y :: γ) body
      | _ => .rejected "destructuring a non-pair"
    | .case a left right => do
      let v ← evalFuel fuel (s.branch 3 0) γ a
      match v with
      | .inl x => evalFuel fuel (s.branch 3 1) (x :: γ) left
      | .inr x => evalFuel fuel (s.branch 3 2) (x :: γ) right
      | _ => .rejected "case analysis of a non-sum"
    | .reuse a b c => do
      let credit ← evalFuel fuel (s.branch 3 0) γ a
      let first ← evalFuel fuel (s.branch 3 1) γ b
      let second ← evalFuel fuel (s.branch 3 2) γ c
      match credit with
      | .credit l => return .pair l first second
      | _ => .rejected "reuse requires a space credit"
    | .region a => evalFuel fuel s.enter γ a

/-- Big-step semantics, independent of the evaluator and its fuel. -/
inductive Eval : Supplies → Environment → AnnotatedTerm → Value → Prop where
  | var {s γ i v} : γ[i]? = some v → Eval s γ (.var i) v
  | unit {s γ} : Eval s γ .unit .unit
  | lam {s γ captured body} : Eval s γ (.lam captured body)
      (.closure (trimEnvironment γ (body.freeVars 1)) captured body)
  | app {s γ f a γ' captured body va v} :
      Eval (s.branch 3 0) γ f (.closure γ' captured body) →
      Eval (s.branch 3 1) γ a va → Eval (s.branch 3 2) (va :: γ') body v →
      Eval s γ (.app f a) v
  | pair {s γ a b va vb} : Eval (s.afterHeap.branch 2 0) γ a va →
      Eval (s.afterHeap.branch 2 1) γ b vb →
      Eval s γ (.pair a b) (.pair (.heap s.heap.start) va vb)
  | stackPair {s γ a b va vb} : Eval (s.afterStack.branch 2 0) γ a va →
      Eval (s.afterStack.branch 2 1) γ b vb →
      Eval s γ (.stackPair a b) (.pair (.stack s.currentFrame s.stack.start) va vb)
  | inl {s γ a v} : Eval s γ a v → Eval s γ (.inl a) (.inl v)
  | inr {s γ a v} : Eval s γ a v → Eval s γ (.inr a) (.inr v)
  | defn {s γ rhs body a b} : Eval (s.branch 2 0) [] rhs a →
      Eval (s.branch 2 1) (a :: γ) body b → Eval s γ (.defn rhs body) b
  | split {s γ a body l x y v} : Eval (s.branch 2 0) γ a (.pair l x y) →
      Eval (s.branch 2 1) (.credit l :: x :: y :: γ) body v →
      Eval s γ (.split a body) v
  | caseLeft {s γ a b c x v} : Eval (s.branch 3 0) γ a (.inl x) →
      Eval (s.branch 3 1) (x :: γ) b v → Eval s γ (.case a b c) v
  | caseRight {s γ a b c x v} : Eval (s.branch 3 0) γ a (.inr x) →
      Eval (s.branch 3 2) (x :: γ) c v → Eval s γ (.case a b c) v
  | reuse {s γ a b c l x y} : Eval (s.branch 3 0) γ a (.credit l) →
      Eval (s.branch 3 1) γ b x → Eval (s.branch 3 2) γ c y →
      Eval s γ (.reuse a b c) (.pair l x y)
  | region {s γ a v} : Eval s.enter γ a v → Eval s γ (.region a) v

/-- All references, including aliased cells. Used for freshness and liveness, not ownership. -/
inductive References : Value → Location → Prop where
  | credit {l} : References (.credit l) l
  | pairCell {l a b} : References (.pair l a b) l
  | pairLeft {l a b k} : References a k → References (.pair l a b) k
  | pairRight {l a b k} : References b k → References (.pair l a b) k
  | inl {v l} : References v l → References (.inl v) l
  | inr {v l} : References v l → References (.inr v) l
  | closure {γ captured body v l} : v ∈ γ → References v l →
      References (.closure γ captured body) l

def EnvironmentReferences (γ : Environment) (l : Location) : Prop :=
  ∃ v ∈ γ, References v l

structure World where
  liveFrames : Finset Nat
  deriving DecidableEq
def World.Live (w : World) : Location → Prop
  | .heap _ => True
  | .stack f _ => f ∈ w.liveFrames
def World.ValidValue (w : World) (v : Value) : Prop :=
  ∀ l, References v l → w.Live l
def World.Compatible (w : World) (s : Supplies) (γ : Environment) : Prop :=
  s.Valid ∧ s.currentFrame ∈ w.liveFrames ∧
  (∀ n, s.frames.at n ∉ w.liveFrames) ∧
  ∀ l, EnvironmentReferences γ l → ¬s.FreshLocation l

end ModalityInference

namespace ModalityInference
/-- Runtime equivalence that forgets only proof annotations. -/
inductive ValueErasure : Value → Value → Prop where
  | unit : ValueErasure .unit .unit
  | credit {l} : ValueErasure (.credit l) (.credit l)
  | pair {l a b c d} : ValueErasure a c → ValueErasure b d →
      ValueErasure (.pair l a b) (.pair l c d)
  | inl {a b} : ValueErasure a b → ValueErasure (.inl a) (.inl b)
  | inr {a b} : ValueErasure a b → ValueErasure (.inr a) (.inr b)
  | closure {γ δ Γ Δ t u} : List.Forall₂ ValueErasure γ δ → t.erase = u.erase →
      ValueErasure (.closure γ Γ t) (.closure δ Δ u)
end ModalityInference
