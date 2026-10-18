import ModalityInference.Proofs.ComparisonSignedCallCoverage
import ModalityInference.Proofs.ComparisonLayoutWorldDecoder
import ModalityInference.Proofs.ModeFormulaSupport

namespace ModalityInference.ComparisonLayoutScalarSupport
open ComparisonStructuralLayout ComparisonControls ComparisonSignedObservation
  ComparisonSignedEndpoints ComparisonLayoutWorlds

def Atoms (P : Nat→Prop) (e : BoolExpr) : Prop := ∀i∈e.atoms,P i

@[simp] theorem atoms_const {P : Nat→Prop} {b : Bool} : Atoms P (.const b) := by simp [Atoms,BoolExpr.atoms]
@[simp] theorem atoms_atom {P : Nat→Prop} {i : Nat} : Atoms P (.atom i) ↔ P i := by simp [Atoms,BoolExpr.atoms]
@[simp] theorem atoms_and {P : Nat→Prop} {a b : BoolExpr} : Atoms P (.and a b) ↔ Atoms P a ∧ Atoms P b := by
  simp [Atoms,BoolExpr.atoms,or_imp,forall_and]
@[simp] theorem atoms_or {P : Nat→Prop} {a b : BoolExpr} : Atoms P (.or a b) ↔ Atoms P a ∧ Atoms P b := by
  simp [Atoms,BoolExpr.atoms,or_imp,forall_and]
@[simp] theorem atoms_imp {P : Nat→Prop} {a b : BoolExpr} : Atoms P (.imp a b) ↔ Atoms P a ∧ Atoms P b := by
  simp [Atoms,BoolExpr.atoms,or_imp,forall_and]
@[simp] theorem atoms_equal {P : Nat→Prop} {a b : BoolExpr} : Atoms P (.equal a b) ↔ Atoms P a ∧ Atoms P b := by
  simp only [BoolExpr.equal,atoms_and,atoms_imp]
  tauto
@[simp] theorem atoms_all {P : Nat→Prop} {es : List BoolExpr} : Atoms P (.all es) ↔ ∀e∈es,Atoms P e := by
  induction es <;> simp_all [BoolExpr.all]
@[simp] theorem atoms_any {P : Nat→Prop} {es : List BoolExpr} : Atoms P (.any es) ↔ ∀e∈es,Atoms P e := by
  induction es <;> simp_all [BoolExpr.any]

theorem atoms_rename {P Q : Nat→Prop} {f : Nat→Nat} {e : BoolExpr}
    (h : Atoms P e) (hf : ∀i,P i→Q (f i)) : Atoms Q (rename f e) := by
  intro i hi
  obtain ⟨j,hj,he⟩:=SymbolicCNF.substitute_atoms hi
  have heq : i=f j := by simpa [BoolExpr.atoms] using he
  exact heq ▸ hf j (h j hj)

def Allowed (names : List ModVar) (i : Nat) : Prop :=
  (location i).2%4=2 → SymbolicModes.atomVariable ((location i).2/4)∈names

theorem allowed_decode {names : List ModVar} {i : Nat} : Allowed names i ↔
    (decode i).1≠0 → SymbolicModes.atomVariable (decode i).2∈names := by
  by_cases h : (location i).2%4=2 <;> simp [Allowed,decode,h]

@[simp] theorem allowed_basis (names : List ModVar) (i : Nat) : Allowed names (basisAtom i) := by
  simp [Allowed,basisAtom]
@[simp] theorem allowed_head (names : List ModVar) (i : Nat) : Allowed names (headAtom i) := by
  simp [Allowed,headAtom]
@[simp] theorem allowed_choice (names : List ModVar) (i : Nat) : Allowed names (choiceAtom i) := by
  simp [Allowed,choiceAtom]
@[simp] theorem allowed_mode (names : List ModVar) (i : Nat) :
    Allowed names (modeAtom i) ↔ SymbolicModes.atomVariable i∈names := by
  have he : (4*i+2)/4=i := by omega
  simp [Allowed,modeAtom,he]
@[simp] theorem allowed_left {names : List ModVar} {i : Nat} :
    Allowed names (leftAtom i) ↔ Allowed names i := by simp [Allowed]
@[simp] theorem allowed_right {names : List ModVar} {i : Nat} :
    Allowed names (rightAtom i) ↔ Allowed names i := by simp [Allowed]

theorem allowed_route {names : List ModVar} {i : Nat} (route : Route)
    (h : Allowed names i) : Allowed names (routeAtom route i) := by
  induction route with
  | nil => exact h
  | cons side route ih => cases side <;> simpa [routeAtom] using ih

abbrev Scoped (names : List ModVar) := Atoms (Allowed names)

theorem scoped_coordinate (names : List ModVar) (c : Coordinate) : Scoped names (coordinateTest c) := by
  simp [coordinateTest]

theorem scoped_modal {names : List ModVar} {e : BoolExpr} (c : Coordinate) (he : Scoped names e)
    {m : ModExpr} (hm : ∀v∈m.freeVariables,v∈names) : Scoped names (c.modalWith modeAtom e m) := by
  have hs:=project_support m
  have hl : Scoped names (rename modeAtom m.project.locality) :=
    atoms_rename (fun i hi=>hm _ (hs.1 i hi).2) (fun i hi=>(allowed_mode names i).mpr hi)
  have hf : Scoped names (rename modeAtom m.project.affinity) :=
    atoms_rename (fun i hi=>hm _ (hs.2.1 i hi).2) (fun i hi=>(allowed_mode names i).mpr hi)
  have hu : Scoped names (rename modeAtom m.project.uniqueness) :=
    atoms_rename (fun i hi=>hm _ (hs.2.2 i hi).2) (fun i hi=>(allowed_mode names i).mpr hi)
  cases c <;> simp_all [Coordinate.modalWith,rename]



theorem atoms_mapIdx {α : Type} {P : Nat→Prop} {xs : List α} {f : Nat→α→BoolExpr}
    (h : ∀i (hi : i<xs.length),Atoms P (f i xs[i])) : ∀e∈xs.mapIdx f,Atoms P e := by
  intro e he
  obtain ⟨i,hi,rfl⟩:=List.mem_mapIdx.mp he
  exact h i hi

theorem scoped_formula (basis : Basis) (c : Coordinate) {k : Key} (hk : k∈basis.keys) :
    Scoped basis.modes (basis.formula headAtom modeAtom c k) := by
  have hh : ∀e∈basis.heads.mapIdx (fun i _=>BoolExpr.atom (headAtom i)),Scoped basis.modes e :=
    atoms_mapIdx (fun i _=>by simp)
  have hl : Scoped basis.modes
      (c.modalWith modeAtom (.all (basis.heads.mapIdx (fun i _=>.atom (headAtom i)))) (.const Mode.bottom)) :=
    scoped_modal c (atoms_all.mpr hh) (by simp [ModExpr.freeVariables])
  have ht : Scoped basis.modes
      (c.modalWith modeAtom (.any (basis.heads.mapIdx (fun i _=>.atom (headAtom i)))) (.const Mode.top)) :=
    scoped_modal c (atoms_any.mpr hh) (by simp [ModExpr.freeVariables])
  cases k with
  | head a => simp [Basis.formula]
  | bottom => exact hl
  | top => exact ht
  | raised => exact scoped_modal c hl (by simp [ModExpr.freeVariables])
  | localFloor | affineFloor => exact scoped_modal c ht (by simp [ModExpr.freeVariables])
  | control q =>
    have hq : q∈basis.modes.flatMap controls := by simpa [Basis.keys] using hk
    obtain ⟨v,hv,hq⟩:=List.mem_flatMap.mp hq
    apply scoped_modal c
    · split <;> assumption
    · intro w hw
      have he : w=q.name := by
        simpa only [ModExpr.mem_freeVariables,control_vars,Finset.mem_singleton] using hw
      simpa only [he,controls_name_mem hq] using hv

theorem scoped_theoryAt (basis : Basis) (c : Coordinate) :
    Scoped basis.modes (basis.theoryAt basisAtom headAtom modeAtom c) := by
  rw [Scoped,Basis.theoryAt,atoms_all]
  apply atoms_mapIdx
  intro i hi
  exact atoms_equal.mpr ⟨by simp,scoped_formula basis c (List.getElem_mem hi)⟩

theorem cnfFormula_atoms {P : Nat→Prop} {cs : CNF} (dual : Bool) {f : Nat→BoolExpr}
    (h : ∀v∈CNFPropagation.atoms cs,Atoms P (f v)) :
    Atoms P (ComparisonStructuralFamily.cnfFormula dual f cs) := by
  have hc : ∀c∈cs,Atoms P (ComparisonStructuralFamily.clauseFormula dual f c) := by
    intro c hc
    have hl : ∀e∈c.map (ComparisonStructuralFamily.literalFormula f),Atoms P e := by
      intro e he
      obtain ⟨⟨v,b⟩,hl,rfl⟩:=List.mem_map.mp he
      have hh:=h v (CNFPropagation.mem_atoms.mpr ⟨c,hc,b,hl⟩)
      cases b <;> simpa [ComparisonStructuralFamily.literalFormula] using hh
    cases dual <;> simpa [ComparisonStructuralFamily.clauseFormula] using hl
  cases dual <;> simpa [ComparisonStructuralFamily.cnfFormula] using hc

theorem clauses_atoms {basisAtom : Nat→Nat} {bounds : List ComparisonStructuralNode.Bound} {v : Nat}
    (h : v∈CNFPropagation.atoms (ComparisonStructuralNode.clauses basisAtom bounds)) :
    ∃i,v=basisAtom i := by
  obtain ⟨c,hc,p,hp⟩:=CNFPropagation.mem_atoms.mp h
  obtain ⟨bound,hb,hc⟩:=List.mem_flatMap.mp hc
  obtain ⟨original,ho,rfl⟩:=List.mem_map.mp hc
  obtain ⟨literal,hl,he⟩:=List.mem_map.mp hp
  exact ⟨literal.1,(congrArg Prod.fst he).symm⟩

theorem scoped_rangeTheory (names : List ModVar) (basis : Basis) : Scoped names (rangeTheory basis) := by
  simp [rangeTheory]

theorem scoped_childCoordinate (names : List ModVar) (child : Nat→Nat)
    (hc : ∀i,Allowed names i→Allowed names (child i)) : Scoped names (childCoordinate child) := by
  simp only [childCoordinate,atoms_or,atoms_any,List.forall_mem_map,atoms_and]
  exact ⟨atoms_rename (scoped_coordinate names _) hc,fun c _=>
    ⟨scoped_coordinate names c,atoms_rename (scoped_coordinate names c) hc⟩⟩

theorem scoped_sharedModes (names : List ModVar) (child : Nat→Nat)
    (hc : ∀i,Allowed names i→Allowed names (child i)) : Scoped names (sharedModes names child) := by
  rw [Scoped,sharedModes,atoms_all]
  intro e he
  obtain ⟨v,hv,he⟩:=List.mem_flatMap.mp he
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp he
  have hl : Allowed names (modeAtom (v.atomIndex i)) :=
    (allowed_mode names _).mpr (by simpa only [atomVariable_atomIndex v i (List.mem_range.mp hi)] using hv)
  exact atoms_equal.mpr ⟨atoms_atom.mpr hl,atoms_atom.mpr (hc _ hl)⟩

theorem scoped_childTheory (k : Constructor) (names : List ModVar) (child : Nat→Nat)
    (hc : ∀i,Allowed names i→Allowed names (child i)) : Scoped names (childTheory k names child) := by
  unfold childTheory
  split
  · exact atoms_const
  · exact atoms_and.mpr ⟨scoped_childCoordinate names child hc,scoped_sharedModes names child hc⟩

theorem scoped_links (names : List ModVar) (kind : Constructor) (parent left right : Basis) (takeLeft : Bool) :
    Scoped names (links kind parent left right takeLeft) := by
  rw [Scoped,links,atoms_all]
  intro e he
  obtain ⟨a,ha,he⟩:=List.mem_flatMap.mp he
  obtain ⟨b,hb,rfl⟩:=List.mem_map.mp he
  cases takeLeft <;> cases kind <;> simp [Constructor.dual]


theorem scoped_nodeTheory (assumptions : Bounds) (basis : Basis) (bounds : List ComparisonStructuralNode.Bound)
    (ha : Scoped basis.modes (rename modeAtom (boundsModeFormula assumptions))) :
    Scoped basis.modes (nodeTheory assumptions basis bounds) := by
  have hc : Scoped basis.modes (ComparisonStructuralFamily.cnfFormula false BoolExpr.atom
      (ComparisonStructuralNode.clauses basisAtom bounds)) := by
    apply cnfFormula_atoms
    intro i hi
    obtain ⟨j,rfl⟩:=clauses_atoms hi
    simp
  simp only [nodeTheory,atoms_and,atoms_any,List.forall_mem_map]
  refine ⟨scoped_rangeTheory _ _,⟨fun c _=>⟨scoped_coordinate _ c,scoped_theoryAt basis c,?_⟩,hc⟩⟩
  split
  · exact atoms_const
  · exact ha

theorem scoped_query {names : List TypeVar} {modes : List ModVar} {fixed : TypeVar→ComparisonShape}
    {layout : Layout} (hb : Based names modes fixed layout)
    {assumptions : Bounds} (ha : Scoped modes (rename modeAtom (boundsModeFormula assumptions)))
    {endpoints : ComparisonShape→List (CompareTy×CompareTy)} {q : BoolExpr}
    (hq : query assumptions endpoints layout=some q) : Scoped modes q := by
  induction hb generalizing q with
  | @leaf s basis hb =>
    have hm:=(ComparisonStructuralBasis.basis_spec hb).2.1
    cases hc : ComparisonStructuralNode.prepare basis (endpoints s) <;> simp [query,hc] at hq
    subst q
    simpa only [hm] using scoped_nodeTheory assumptions basis _ (hm ▸ ha)
  | @fork k basis left right hb hl hr ihl ihr =>
    have hm:=(ComparisonStructuralBasis.basis_spec hb).2.1
    cases hc : ComparisonStructuralNode.prepare basis (endpoints (k.shape left.shape right.shape)) <;>
      simp [query,Layout.shape,hc] at hq
    cases hql : query assumptions endpoints left <;> simp [hql] at hq
    cases hqr : query assumptions endpoints right <;> simp [hqr] at hq
    subst q
    rename_i bounds leftQuery rightQuery
    have hh : Scoped modes (nodeTheory assumptions basis bounds) := by
      simpa only [hm] using scoped_nodeTheory assumptions basis _ (hm ▸ ha)
    have hleft:=atoms_rename (ihl hql) (fun i hi=>allowed_left.mpr hi)
    have hright:=atoms_rename (ihr hqr) (fun i hi=>allowed_right.mpr hi)
    have hcl:=scoped_childTheory k modes leftAtom (fun i hi=>allowed_left.mpr hi)
    have hcr:=scoped_childTheory k modes rightAtom (fun i hi=>allowed_right.mpr hi)
    simpa only [atoms_and,atoms_or,atoms_imp,atoms_atom,hm] using
      And.intro hh (And.intro
        (And.intro (allowed_choice modes 0) (And.intro (scoped_links modes k basis left.basis right.basis true)
          (And.intro hcl hleft)))
        (And.intro (And.intro (allowed_choice modes 0) (atoms_const (P:=Allowed modes) (b:=false)))
          (And.intro (scoped_links modes k basis left.basis right.basis false) (And.intro hcr hright))))

theorem scoped_coherence (names : List ModVar) (layout : Layout) :
    Scoped names (ComparisonStructuralCoherence.theory layout) := by
  have hhead (basis : Basis) : Scoped names (ComparisonStructuralCoherence.headCoherence basis) := by
    rw [Scoped,ComparisonStructuralCoherence.headCoherence,atoms_all]
    exact atoms_mapIdx (fun i hi=>by simp)
  have hclosure : Scoped names ComparisonStructuralCoherence.rangeClosure := by
    simp [ComparisonStructuralCoherence.rangeClosure,ComparisonStructuralCoherence.rangeAtom,scoped_coordinate]
  have hchild (k : Constructor) (left : Bool) :
      Scoped names (ComparisonStructuralCoherence.childClause k left (if left then leftAtom else rightAtom)) := by
    cases k <;> cases left <;>
      simp [ComparisonStructuralCoherence.childClause,ComparisonStructuralCoherence.rangeClause,
        Constructor.dual,scoped_coordinate]
  have hinclude (k : Constructor) (left : Bool) :
      Scoped names (ComparisonStructuralCoherence.rangeInclusion k left (if left then leftAtom else rightAtom)) := by
    cases left <;> simp [ComparisonStructuralCoherence.rangeInclusion,ComparisonStructuralCoherence.rangeAtom]
  induction layout with
  | leaf s b => exact atoms_and.mpr ⟨hhead b,hclosure⟩
  | fork k b left right ihl ihr =>
    have hl:=atoms_rename ihl (fun i hi=>allowed_left.mpr hi)
    have hr:=atoms_rename ihr (fun i hi=>allowed_right.mpr hi)
    simpa only [ComparisonStructuralCoherence.theory,atoms_and,atoms_or,atoms_imp,atoms_atom] using
      And.intro (hhead b) (And.intro hclosure (And.intro
        (And.intro (allowed_choice names 0) (And.intro (hchild k true) (And.intro (hinclude k true) hl)))
        (And.intro (And.intro (allowed_choice names 0) (atoms_const (P:=Allowed names) (b:=false)))
          (And.intro (hchild k false) (And.intro (hinclude k false) hr)))))

theorem coherence_run_support {names : List TypeVar} {modes : List ModVar} {fixed : TypeVar→ComparisonShape}
    {layout : Layout} (hb : Based names modes fixed layout)
    {assumptions : Bounds} (ha : Scoped modes (rename modeAtom (boundsModeFormula assumptions)))
    {endpoints : ComparisonShape→List (CompareTy×CompareTy)} {fuel : Nat} {output : CNF}
    (h : ComparisonStructuralCoherence.run fuel assumptions endpoints layout=.success output) :
    ∀i∈CNFPropagation.atoms output,Allowed modes i := by
  cases hq : query assumptions endpoints layout with
  | none => simp [ComparisonStructuralCoherence.run,hq] at h
  | some q =>
    have hc : CompactCNF.toCNF fuel true (.and q (ComparisonStructuralCoherence.theory layout))=.success output := by
      simpa only [ComparisonStructuralCoherence.run,hq] using h
    intro i hi
    exact (atoms_and.mpr ⟨scoped_query hb ha hq,scoped_coherence modes layout⟩) i
      (CompactCNF.toCNF_atoms hc hi)


theorem scoped_bounds {names : List ModVar} {bounds : Bounds}
    (h : ∀v∈bounds.modVars,v∈names) : Scoped names (rename modeAtom (boundsModeFormula bounds)) :=
  atoms_rename (fun _ hi=>h _ (boundsModeFormula_variables hi))
    (fun i hi=>(allowed_mode names i).mpr hi)

theorem scoped_action {names : List ModVar} {m : ModExpr}
    (hm : ∀v∈m.freeVariables,v∈names) (value : Bool) : Scoped names (action m value) := by
  simp only [action,atoms_any,List.forall_mem_map,atoms_and]
  exact fun c _=>⟨scoped_coordinate names c,scoped_modal c atoms_const hm⟩

def DataScoped (names : List ModVar) : Data→Prop
  | .fixed e => Scoped names e
  | .image _ _ => True

def ViewScoped (names : List ModVar) (v : View) : Prop :=
  DataScoped names v.data ∧ Scoped names v.lower ∧ Scoped names v.upper

def BranchScoped (names : List ModVar) (b : Branch) : Prop :=
  Scoped names b.guard ∧ ViewScoped names b.view

theorem data_flip {names : List ModVar} {d : Data} (h : DataScoped names d) :
    DataScoped names d.flip := by cases d <;> simp_all [DataScoped,Data.flip,neg]

theorem view_base {names : List ModVar} {d : Data} (h : DataScoped names d) :
    ViewScoped names (.base d) := ⟨h,atoms_const,atoms_const⟩

theorem view_dual {names : List ModVar} {v : View} (h : ViewScoped names v) :
    ViewScoped names v.dual :=
  ⟨data_flip h.1,atoms_imp.mpr ⟨h.2.2,atoms_const⟩,atoms_imp.mpr ⟨h.2.1,atoms_const⟩⟩

theorem view_act {names : List ModVar} {v : View} (h : ViewScoped names v)
    {l u : BoolExpr} (hl : Scoped names l) (hu : Scoped names u) :
    ViewScoped names (v.act l u) :=
  ⟨h.1,atoms_and.mpr ⟨atoms_or.mpr ⟨h.2.1,hl⟩,hu⟩,
    atoms_and.mpr ⟨atoms_or.mpr ⟨h.2.2,hl⟩,hu⟩⟩

theorem branch_guarded {names : List ModVar} {b : Branch} (h : BranchScoped names b)
    {e : BoolExpr} (he : Scoped names e) : BranchScoped names (b.guarded e) :=
  ⟨atoms_and.mpr ⟨he,h.1⟩,h.2⟩


structure ContextScoped (names : List ModVar) (ctx : ComparisonSignedEndpoints.Context) : Prop where
  fixed : ∀route a,Scoped names (ctx.fixed route a)
  choose : ∀route,Scoped names (ctx.choose route)
  action : ∀route (m : ModExpr),(∀v∈m.vars,v∈names) →
    Scoped names (ctx.action route m).1 ∧ Scoped names (ctx.action route m).2

theorem context_scoped (names : List ModVar) (layout : Layout) :
    ContextScoped names (context layout ModExpr.var) := by
  constructor
  · intro route a
    dsimp only [context]
    split
    · exact atoms_const
    · exact atoms_atom.mpr (allowed_route route (allowed_head _ _))
  · intro route
    exact atoms_atom.mpr (allowed_route route (allowed_choice _ _))
  · intro route m hm
    have h (b : Bool) : Scoped names (rename (routeAtom route) (action (m.subst ModExpr.var) b)) := by
      rw [ModExpr.subst_id]
      exact atoms_rename (scoped_action (fun v hv=>hm v (by simpa only [ModExpr.mem_freeVariables] using hv)) b)
        (fun _ hi=>allowed_route route hi)
    exact ⟨h false,h true⟩

theorem observe_scoped {names : List ModVar} {ctx : ComparisonSignedEndpoints.Context} (hc : ContextScoped names ctx)
    (keys : List Nat) (a : Ty) {route : Route} (ha : ∀v∈a.modVars,v∈names) :
    ∀b∈observe keys ctx route a,BranchScoped names b := by
  induction a generalizing route with
  | modal a m ih =>
      intro b hb
      obtain ⟨source,hs,rfl⟩:=List.mem_map.mp hb
      have hbase:=ih (fun v hv=>ha v (Finset.mem_union_left _ hv)) source hs
      have hmode:=hc.action route m (fun v hv=>ha v (Finset.mem_union_right _ hv))
      exact ⟨hbase.1,view_act hbase.2 hmode.1 hmode.2⟩
  | var v =>
      intro b hb
      have he : b=⟨.const true,.base (reference keys ctx route v)⟩ := by simpa [observe] using hb
      subst b
      refine ⟨atoms_const,view_base ?_⟩
      cases v with
      | rigid n => exact hc.fixed route _
      | flex n => simp only [reference]; split; trivial; exact hc.fixed route _
  | unit | credit =>
      intro b hb
      simp only [observe,List.mem_singleton] at hb
      subst b
      exact ⟨atoms_const,view_base (hc.fixed route _)⟩
  | prod a b iha ihb | sum a b iha ihb =>
      intro branch hbranch
      rcases List.mem_append.mp hbranch with hbranch|hbranch
      · obtain ⟨source,hs,rfl⟩:=List.mem_map.mp hbranch
        exact branch_guarded (iha (fun v hv=>ha v (Finset.mem_union_left _ hv)) _ hs) (hc.choose route)
      · obtain ⟨source,hs,rfl⟩:=List.mem_map.mp hbranch
        exact branch_guarded (ihb (fun v hv=>ha v (Finset.mem_union_right _ hv)) _ hs)
          (atoms_imp.mpr ⟨hc.choose route,atoms_const⟩)
  | fn a b iha ihb =>
      intro branch hbranch
      rcases List.mem_append.mp hbranch with hbranch|hbranch
      · obtain ⟨source,hs,rfl⟩:=List.mem_map.mp hbranch
        have hh:=iha (fun v hv=>ha v (Finset.mem_union_left _ hv)) _ hs
        exact branch_guarded (b:=⟨source.guard,source.view.dual⟩) ⟨hh.1,view_dual hh.2⟩ (hc.choose route)
      · obtain ⟨source,hs,rfl⟩:=List.mem_map.mp hbranch
        exact branch_guarded (ihb (fun v hv=>ha v (Finset.mem_union_right _ hv)) _ hs)
          (atoms_imp.mpr ⟨hc.choose route,atoms_const⟩)


theorem makeClause_scoped {names : List ModVar} {guard : BoolExpr} {data : List Data}
    (hg : Scoped names guard) (hd : ∀d∈data,DataScoped names d) :
    Scoped names (makeClause guard data).guard := by
  dsimp only [makeClause]
  rw [Scoped,atoms_or,atoms_any]
  refine ⟨hg,?_⟩
  intro e he
  obtain ⟨d,hdmem,he⟩:=List.mem_filterMap.mp he
  cases d with
  | fixed value =>
      have hv : value=e := by simpa using he
      exact hv ▸ hd _ hdmem
  | image call positive => simp at he

theorem compare_scoped {names : List ModVar} {active : BoolExpr} {left right : View}
    (ha : Scoped names active) (hl : ViewScoped names left) (hr : ViewScoped names right) :
    ∀c∈ComparisonSignedEndpoints.compare active left right,Scoped names c.guard := by
  intro c hc
  simp only [ComparisonSignedEndpoints.compare,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl <;> apply makeClause_scoped
  · simp [neg,ha,hl.2.1,hr.2.1]
  · simp [hl.1,hr.1]
  · simp [neg,ha,hl.2.1,hr.2.2]
  · simp [hl.1,data_flip hr.1]
  · simp [neg,ha,hl.2.2,hr.2.1]
  · simp [data_flip hl.1,hr.1]
  · simp [neg,ha,hl.2.2,hr.2.2]
  · simp [data_flip hl.1,data_flip hr.1]

theorem compile_scoped {names : List ModVar} {ctx : ComparisonSignedEndpoints.Context}
    (hc : ContextScoped names ctx) (keys : List Nat) {left right : Ty}
    (hl : ∀v∈left.modVars,v∈names) (hr : ∀v∈right.modVars,v∈names) :
    ∀c∈ComparisonSignedEndpoints.compile keys ctx left right,Scoped names c.guard := by
  intro c hmem
  obtain ⟨l,hlmem,hmem⟩:=List.mem_flatMap.mp hmem
  obtain ⟨r,hrmem,hmem⟩:=List.mem_flatMap.mp hmem
  have hleft:=observe_scoped hc keys left hl l hlmem
  have hright:=observe_scoped hc keys right hr r hrmem
  exact compare_scoped (atoms_and.mpr ⟨hleft.1,hright.1⟩) hleft.2 hright.2 c hmem

theorem compileGuards_support {names : List ModVar} {fuel : Nat}
    {clauses : List ComparisonSignedEndpoints.Clause} {output : List CompiledClause}
    (h : compileGuards fuel clauses=.success output)
    (hs : ∀c∈clauses,Scoped names c.guard) :
    ∀c∈output,∀i∈CNFPropagation.atoms [c.guard],Allowed names i := by
  induction clauses generalizing output with
  | nil =>
      have he : output=[] := by simpa [compileGuards] using h.symm
      subst output
      simp
  | cons clause clauses ih =>
      cases hg : CompactCNF.toCNF fuel true clause.guard with
      | exhausted => simp [compileGuards,hg,bind,RunResult.bind] at h
      | rejected reason => simp [compileGuards,hg,bind,RunResult.bind] at h
      | success guards =>
        cases ht : compileGuards fuel clauses with
        | exhausted => simp [compileGuards,hg,ht,bind,RunResult.bind] at h
        | rejected reason => simp [compileGuards,hg,ht,bind,RunResult.bind] at h
        | success tail =>
          have he : output=guards.map (fun guard=>⟨guard,clause.literals⟩)++tail := by
            simpa [compileGuards,hg,ht,bind,pure,RunResult.bind] using h.symm
          subst output
          intro c hc i hi
          rcases List.mem_append.mp hc with hc|hc
          · obtain ⟨guard,hguard,rfl⟩:=List.mem_map.mp hc
            apply hs clause List.mem_cons_self
            apply CompactCNF.toCNF_atoms hg
            obtain ⟨d,hd,pol,hpol⟩:=CNFPropagation.mem_atoms.mp hi
            have hd' : d=guard := by simpa using hd
            exact CNFPropagation.mem_atoms.mpr ⟨guard,hguard,pol,hd' ▸ hpol⟩
          · exact ih ht (fun c hc=>hs c (List.mem_cons_of_mem _ hc)) c hc i hi

end ModalityInference.ComparisonLayoutScalarSupport
