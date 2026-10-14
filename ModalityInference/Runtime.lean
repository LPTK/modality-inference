import ModalityInference.Evaluation

/-! The source evaluator contains no capture schemes. Runtime closures retain
only their trimmed environment and unannotated body. The annotated semantics
is connected to this evaluator by erasure in `Proofs.Runtime`. -/
namespace ModalityInference.Runtime

inductive Value where
  | unit
  | credit (location : Location)
  | pair (location : Location) (first second : Value)
  | inl (value : Value)
  | inr (value : Value)
  | closure (environment : List Value) (body : RawTerm)
  deriving Repr

abbrev Environment := List Value

/-- Erase unused environment entries, independently of typing metadata. Indices stay stable. -/
def trimEnvironment (γ : Environment) (used : Finset Nat) : Environment :=
  γ.mapIdx fun i v => if i ∈ used then v else .unit

def evalFuel : Nat → Supplies → Environment → RawTerm → RunResult Value
  | 0, _, _, _ => .exhausted
  | fuel + 1, s, γ, term => match term with
    | .var i => match γ[i]? with
      | some v => .success v
      | none => .rejected "unbound term variable"
    | .unit => .success .unit
    | .lam _ body =>
      .success (.closure (trimEnvironment γ (body.freeVars 1)) body)
    | .app f a => do
      let vf ← evalFuel fuel (s.branch 3 0) γ f
      let va ← evalFuel fuel (s.branch 3 1) γ a
      match vf with
      | .closure γ' body => evalFuel fuel (s.branch 3 2) (va :: γ') body
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
inductive Eval : Supplies → Environment → RawTerm → Value → Prop where
  | var {s γ i v} : γ[i]? = some v → Eval s γ (.var i) v
  | unit {s γ} : Eval s γ .unit .unit
  | lam {s γ body} : Eval s γ (.lam () body)
      (.closure (trimEnvironment γ (body.freeVars 1)) body)
  | app {s γ f a γ' body va v} :
      Eval (s.branch 3 0) γ f (.closure γ' body) →
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
  | closure {γ body v l} : v ∈ γ → References v l →
      References (.closure γ body) l

def EnvironmentReferences (γ : Environment) (l : Location) : Prop :=
  ∃ v ∈ γ, References v l

/-- Liveness uses every referenced location, including aliases. -/
def ValidValue (w : World) (v : Value) : Prop :=
  ∀ l, References v l → w.Live l

def Compatible (w : World) (s : Supplies) (γ : Environment) : Prop :=
  s.Valid ∧ s.currentFrame ∈ w.liveFrames ∧
  (∀ n, s.frames.at n ∉ w.liveFrames) ∧
  ∀ l, EnvironmentReferences γ l → ¬s.FreshLocation l

/-- Remove all proof annotations recursively, including inside environments. -/
def eraseValue : ModalityInference.Value → Value
  | .unit => .unit
  | .credit l => .credit l
  | .pair l a b => .pair l (eraseValue a) (eraseValue b)
  | .inl a => .inl (eraseValue a)
  | .inr a => .inr (eraseValue a)
  | .closure γ _ body => .closure (γ.map eraseValue) body.erase

def eraseResult : RunResult ModalityInference.Value → RunResult Value
  | .success v => .success (eraseValue v)
  | .rejected diagnostic => .rejected diagnostic
  | .exhausted => .exhausted

/-- Canonical proof representation; these empty annotations are never executed. -/
def annotateTerm (t : RawTerm) : AnnotatedTerm := t.mapAnnotation fun _ => []

def Value.annotate : Value → ModalityInference.Value
  | .unit => .unit
  | .credit l => .credit l
  | .pair l a b => .pair l a.annotate b.annotate
  | .inl a => .inl a.annotate
  | .inr a => .inr a.annotate
  | .closure γ body => .closure (γ.map Value.annotate) [] (annotateTerm body)

end ModalityInference.Runtime
