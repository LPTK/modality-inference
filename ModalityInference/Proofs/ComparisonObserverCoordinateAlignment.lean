import ModalityInference.Proofs.ComparisonObserverMachineCheck

/-! The finite product/sum alignment check follows from all-label absorption.
The signed finite tests recover exactly the relevant scalar inputs. -/
namespace ModalityInference.ComparisonObserverCoordinateAlignment

open ComparisonControls ComparisonAlgebra ComparisonStructuralAlignment
  ComparisonObserverMachineCheck

private theorem neutralFormula_complete {names m} (hm : m ∈ tests names)
    (c : Coordinate) (η : ModVar → Mode) :
    (neutralFormula c id m).eval (encodeModes η) = neutral c (m.complete η) := by
  obtain ⟨n,hn⟩ := Option.isSome_iff_exists.mp (tests_total hm η)
  rw [ModExpr.complete_of_eval hn]
  exact neutralFormula_of_eval hn

theorem absorption_aligned {Δ : Bounds} (names : List ModVar)
    (parent child : Coordinate) (η θ : ModVar → Mode)
    (h : ∀m, Entails Δ (.defined m) → ∀x,
      coordinateValue parent (coordinateValue child x (m.complete θ)) (m.complete η) =
        coordinateValue parent x (m.complete η)) :
    Aligned names parent child (encodeModes η) (encodeModes θ) := by
  apply tests_complete
  intro m hm hp
  have hpn := (neutral_iff parent (m.complete η)).mp ((neutralFormula_complete hm parent η) ▸ hp)
  rw [neutralFormula_complete hm child θ]
  apply (neutral_iff child (m.complete θ)).mpr
  intro x
  exact (hpn _).symm.trans ((h m (fun τ _ => tests_total hm τ) x).trans (hpn x))

private theorem encode_local (η : ModVar → Mode) (v : ModVar) :
    encodeModes η (v.atomIndex 0) = (η v).isLocal :=
  congrArg Mode.isLocal (congrFun (projectedModes_encodeModes η) v)

private theorem encode_affine (η : ModVar → Mode) (v : ModVar) :
    encodeModes η (v.atomIndex 1) = (η v).once :=
  congrArg Mode.once (congrFun (projectedModes_encodeModes η) v)

private theorem encode_unique (η : ModVar → Mode) (v : ModVar) :
    encodeModes η (v.atomIndex 2) = (η v).unique :=
  congrArg Mode.unique (congrFun (projectedModes_encodeModes η) v)

theorem sameInputs_correct {State : Type} (names : List ModVar) (parent child : Description State) :
    sameInputs names parent child = true ↔
      SameInputs names child.coordinate
        (encodeModes (modeValue names parent)) (encodeModes (modeValue names child)) := by
  cases hc : child.coordinate <;>
    simp [sameInputs, SameInputs, hc, List.all_eq_true, encode_local, encode_affine, encode_unique]

theorem pairOK_correct {State : Type} (names : List ModVar) (parent child : Description State) :
    pairOK names parent child = true ↔
      Aligned names parent.coordinate child.coordinate
        (encodeModes (modeValue names parent)) (encodeModes (modeValue names child)) := by
  simp only [pairOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, sameInputs_correct, Aligned]

theorem pairOK_of_absorption {State : Type} {Δ names} {parent child : Description State}
    (hp : scalarOK Δ names parent = true) (hc : scalarOK Δ names child = true)
    (h : ∀m, Entails Δ (.defined m) → ∀x,
      action names parent m (action names child m x) = action names parent m x) :
    pairOK names parent child = true := by
  apply (pairOK_correct names parent child).mpr
  apply absorption_aligned (Δ := Δ)
  intro m hm x
  have he := h m hm x
  simpa only [action_complete hp hm, action_complete hc hm] using he

theorem pairOK_iff_absorption {State : Type} {Δ names} {parent child : Description State}
    (hp : scalarOK Δ names parent = true) (hc : scalarOK Δ names child = true) :
    pairOK names parent child = true ↔
      ∀m, Entails Δ (.defined m) → ∀x,
        action names parent m (action names child m x) = action names parent m x := by
  exact ⟨fun h m hm x => pairOK_transfer hp hc h hm x, pairOK_of_absorption hp hc⟩

theorem pairOK_of_range_absorption {State : Type} {Δ names} {parent child : Description State}
    (hp : scalarOK Δ names parent = true) (hc : scalarOK Δ names child = true)
    (hr : child.coordinate = .unaffected ∨ ∀x, child.range x = true)
    (h : ∀m, Entails Δ (.defined m) → ∀x, child.range x = true →
      action names parent m (action names child m x) = action names parent m x) :
    pairOK names parent child = true := by
  rcases hr with hr | hr
  · simp [pairOK, hr]
  · exact pairOK_of_absorption hp hc (fun m hm x => h m hm x (hr x))

theorem closedRange_of_action {State : Type} {Δ names} {d : Description State}
    (h : ∀m, Entails Δ (.defined m) → ∀x, d.range x = true → d.range (action names d m x) = true) :
    closedRange d = true := by
  apply (closedRange_correct d).mpr
  apply (ComparisonStructuralCoherence.closedRange_iff _ _).mpr
  intro x hx m
  simpa only [action, ModExpr.eval, Option.getD_some, act_eq] using h (.const m) (fun _ _ => rfl) x hx

theorem functionRange_of_transfer {State : Type} {Δ names} {data : State → Description State} {i}
    (h : ∀m n, Submode Δ m (.compose n .top) → ∀x, (data ((data i).branch .fn).next).range x = true →
      action names (data i) m (ComparisonObserverMachine.sign .fn ((data i).branch .fn).left x) ≤
        action names (data i) n (ComparisonObserverMachine.sign .fn ((data i).branch .fn).left x)) :
    functionRange data i = true := by
  apply functionRange_correct.mpr
  intro hc x hx
  have ht : Submode Δ .top (.compose .epsilon .top) :=
    .valid (fun _ _ => ⟨Mode.top,Mode.top,rfl,rfl,rfl⟩)
  have hh := h .top .epsilon ht x hx
  simpa [action, ModExpr.eval, ModExpr.top, ModExpr.epsilon, hc, act,
    Mode.top, Mode.identity, Bool.le_iff_imp] using hh

/-- Coordinate-normalized semantic machines pass exactly the finite checks.
Every active node has both inhabited fibers; constant nodes use unaffected. -/
theorem check_complete {count : Nat} {Δ types names} {data : Fin count → Description (Fin count)}
    (hs : ∀i, scalarOK Δ names (data i) = true)
    (hr : ComparisonObserverMachine.RangeClosed Δ (nodes types names data))
    (hc : ComparisonObserverMachine.Coherent Δ (nodes types names data))
    (hb : ComparisonObserverMachine.BoundsHold Δ (nodes types names data))
    (hn : ∀i, (data i).coordinate = .unaffected ∨ ∀x, (data i).range x = true) :
    check Δ types names data = true := by
  apply check_correct.mpr
  intro i
  refine ⟨hs i, hr.unit i, hr.credit i, fun v _ => hr.atom i v, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact closedRange_of_action (fun m hm x hx => hr.modal i m hm x hx)
  · exact fun k => branchRange_correct.mpr (fun x hx => hr.branch i k x hx)
  · exact pairOK_of_range_absorption (hs i) (hs _) (hn _)
      (fun m hm x hx => hc.pair i .prod (.inl rfl) m hm x hx)
  · exact pairOK_of_range_absorption (hs i) (hs _) (hn _)
      (fun m hm x hx => hc.pair i .sum (.inr rfl) m hm x hx)
  · exact functionRange_of_transfer (fun m n hmn x hx => hc.fn i m n hmn x hx)
  · exact declared_correct.mpr (hb i)

end ModalityInference.ComparisonObserverCoordinateAlignment
