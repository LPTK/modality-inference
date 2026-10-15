import ModalityInference.Proofs.ComparisonAlgebra
import ModalityInference.Proofs.Normalization
import ModalityInference.ComparisonChecker
/-! Ordinary and compatible internal subsumption witnesses for simultaneous
partial annotation contexts, paired with executable acceptance checks. -/
namespace ModalityInference.ComparisonContextWitnesses

def bad : ModExpr := .leftResidual .epsilon (.const Mode.bottom)
def h : Ty := .var (.rigid 0)
def source : Scheme :=
  { modParams := [0, 1]
    body := .prod (.prod (.modal h (.var (.flex 0))) (.modal h (.var (.flex 0))))
      (.prod (.modal h (.close (.var (.flex 1)))) .unit) }
def target : Scheme := .mono
  (.prod (.prod (.modal h (.compose bad .epsilon)) (.modal h (.compose bad (.const Mode.global))))
      (.prod (.modal h (.close bad)) (.modal .unit .top)))
def witness : Substitution := { modes := [(0, .compose bad .bottom), (1, bad)] }
theorem partial_suffix {Δ : Bounds} (a : Ty) (m : ModExpr) (x y : Mode)
    (hxy : x.le y = true) :
    Subtype Δ (.modal a (.compose m (.const x))) (.modal a (.compose m (.const y))) := by
  exact Subtype.composeRev.trans ((Subtype.congr .refl
    (.valid fun _ _ => ⟨x, y, rfl, rfl, hxy⟩)).trans .compose)
theorem ordinary_witness : Subsumes [] source target := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · simp [Instantiates, source, witness]
  · simp [source, witness, EntailsAll, Substitution.bounds]
  · change Subtype [] (witness.ty source.body) target.body
    change Subtype []
      (.prod (.prod (.modal h (.compose bad .bottom)) (.modal h (.compose bad .bottom)))
        (.prod (.modal h (.close bad)) .unit)) target.body
    exact Subtype.prod_congr
      (Subtype.prod_congr (partial_suffix h bad Mode.bottom Mode.identity (by decide))
        (partial_suffix h bad Mode.bottom Mode.global (by decide)))
      (Subtype.prod_congr .refl (Subtype.identityRev.trans (.congr .refl
        (.valid fun _ _ => ⟨Mode.identity, Mode.top, rfl, rfl, by decide⟩))))

def sharedSource : Scheme :=
  { modParams := [0]
    body := .prod (.modal h (.close (.var (.flex 0))))
      (.prod (.modal h (.var (.flex 0))) .unit) }

def sharedTarget : Scheme := .mono
  (.prod (.modal h (.close bad))
    (.prod (.modal h (.compose bad .top)) (.modal .unit .top)))

def sharedWitness : Substitution := { modes := [(0, bad)] }

theorem shared_ordinary_witness : Subsumes [] sharedSource sharedTarget := by
  refine ⟨sharedWitness, ?_, ?_, ?_⟩
  · simp [Instantiates, sharedSource, sharedWitness]
  · simp [sharedSource, sharedWitness, EntailsAll, Substitution.bounds]
  · change Subtype []
      (.prod (.modal h (.close bad)) (.prod (.modal h bad) .unit)) sharedTarget.body
    exact Subtype.prod_congr .refl (Subtype.prod_congr
      (Subtype.identityRev.trans ((Subtype.congr .refl (.valid fun _ _ =>
        ⟨Mode.identity, Mode.top, rfl, rfl, by decide⟩)).trans .compose))
      (Subtype.identityRev.trans (.congr .refl
        (.valid fun _ _ => ⟨Mode.identity, Mode.top, rfl, rfl, by decide⟩))))

def mixedSource : Scheme :=
  { typeParams := [0], modParams := [0]
    body := .prod (.var (.flex 0))
      (.prod (.modal (.var (.flex 0)) (.var (.flex 0))) .unit) }

def mixedTarget : Scheme := .mono
  (.prod (.modal h bad) (.prod (.modal h bad) (.modal .unit .top)))

def mixedWitness : Substitution :=
  { types := [(0, .modal h bad)], modes := [(0, .epsilon)] }

theorem mixed_ordinary_witness : Subsumes [] mixedSource mixedTarget := by
  refine ⟨mixedWitness, ?_, ?_, ?_⟩
  · simp [Instantiates, mixedSource, mixedWitness]
  · simp [mixedSource, mixedWitness, EntailsAll, Substitution.bounds]
  · change Subtype []
      (.prod (.modal h bad) (.prod (.modal (.modal h bad) .epsilon) .unit)) mixedTarget.body
    exact Subtype.prod_congr .refl (Subtype.prod_congr .identity
      (Subtype.identityRev.trans (.congr .refl
        (.valid fun _ _ => ⟨Mode.identity, Mode.top, rfl, rfl, by decide⟩))))

theorem algebra_witnesses : AlgebraSubsumes [] source target ∧
    AlgebraSubsumes [] sharedSource sharedTarget ∧ AlgebraSubsumes [] mixedSource mixedTarget :=
  ⟨ordinary_witness.to_algebra, shared_ordinary_witness.to_algebra,
    mixed_ordinary_witness.to_algebra⟩

def meetBounds : Bounds := [.sub h (.var (.rigid 1))]

def mixedMeetTarget : Scheme :=
  { bounds := meetBounds
    body := .prod (.modal h bad)
      (.prod (.modal (.var (.rigid 1)) bad) (.modal .unit .top)) }

def meetImage : CompareTy :=
  .meet (.modal (.var (.rigid 0)) bad) (.modal (.var (.rigid 1)) bad)

def meetWitness : CompareSubstitution :=
  { types := [(0, meetImage)], modes := [(0, .epsilon)] }

theorem meetImage_wellShaped : meetImage.WellShaped meetBounds := by
  exact ⟨trivial, trivial, ComparisonShape.Equivalent.of_sub (a := h)
    (b := .var (.rigid 1)) (by simp [meetBounds])⟩

theorem mixed_meet_witness_bounds (bounds : Bounds)
    (hb : ShapedEntailsAll meetBounds (meetWitness.bounds bounds)) :
    ShapedSubsumes [] { mixedSource with bounds := bounds } mixedMeetTarget := by
  refine ⟨meetWitness, ?_, ?_, ?_, ?_⟩
  · simp [CompareInstantiates, mixedSource, meetWitness]
  · change meetWitness.WellShaped meetBounds
    simpa [CompareSubstitution.WellShaped, meetWitness] using meetImage_wellShaped
  · exact hb
  · change ShapedSubtype meetBounds
      (.prod meetImage (.prod (.modal meetImage .epsilon) .unit))
      (.prod (.modal (.var (.rigid 0)) bad)
        (.prod (.modal (.var (.rigid 1)) bad) (.modal .unit .top)))
    exact ShapedSubtype.prod_congr (.meetLeft meetImage_wellShaped)
      (.prod_congr ((ShapedSubtype.identity meetImage_wellShaped).trans
        (.meetRight meetImage_wellShaped))
        ((ShapedSubtype.identityRev (a := .unit) trivial).trans (.congr (.refl trivial)
          (.valid fun _ _ => ⟨Mode.identity, Mode.top, rfl, rfl, by decide⟩))))

theorem mixed_meet_shaped_witness : ShapedSubsumes [] mixedSource mixedMeetTarget :=
  mixed_meet_witness_bounds [] (by simp [ShapedEntailsAll, CompareSubstitution.bounds])

theorem mixed_meet_algebra_witness : AlgebraSubsumes [] mixedSource mixedMeetTarget :=
  mixed_meet_shaped_witness.to_algebra

def definedMixedSource : Scheme :=
  { mixedSource with bounds := [.defined (.var (.flex 0))] }

theorem defined_mixed_meet_witness : AlgebraSubsumes [] definedMixedSource mixedMeetTarget := by
  apply ShapedSubsumes.to_algebra
  apply mixed_meet_witness_bounds
  simp [ShapedEntailsAll, ShapedEntails, CompareSubstitution.bounds,
    CompareSubstitution.constraint, meetWitness, CompareSubstitution.mode,
    ModExpr.subst, ModExpr.epsilon, ModExpr.WellFormed, ModExpr.eval]

def combinedSource : Scheme :=
  { typeParams := [0], modParams := [0, 1]
    body := .prod (.prod (.var (.flex 0)) (.modal (.var (.flex 0)) (.var (.flex 0))))
      (.prod (.modal (.var (.rigid 2)) (.close (.var (.flex 1)))) .unit) }

def combinedTarget : Scheme :=
  { bounds := meetBounds
    body := .prod (.prod (.modal h bad) (.modal (.var (.rigid 1)) bad))
      (.prod (.modal (.var (.rigid 2)) (.close bad)) (.modal .unit .top)) }

def combinedWitness : CompareSubstitution :=
  { types := [(0, meetImage)], modes := [(0, .epsilon), (1, bad)] }

theorem combined_shaped_witness : ShapedSubsumes [] combinedSource combinedTarget := by
  refine ⟨combinedWitness, ?_, ?_, ?_, ?_⟩
  · simp [CompareInstantiates, combinedSource, combinedWitness]
  · change combinedWitness.WellShaped meetBounds
    simpa [CompareSubstitution.WellShaped, combinedWitness] using meetImage_wellShaped
  · simp [combinedSource, combinedWitness, ShapedEntailsAll, CompareSubstitution.bounds]
  · change ShapedSubtype meetBounds
      (.prod (.prod meetImage (.modal meetImage .epsilon))
        (.prod (.modal (.var (.rigid 2)) (.close bad)) .unit))
      (.prod (.prod (.modal (.var (.rigid 0)) bad) (.modal (.var (.rigid 1)) bad))
        (.prod (.modal (.var (.rigid 2)) (.close bad)) (.modal .unit .top)))
    exact ShapedSubtype.prod_congr
      (.prod_congr (.meetLeft meetImage_wellShaped)
        ((ShapedSubtype.identity meetImage_wellShaped).trans (.meetRight meetImage_wellShaped)))
      (.prod_congr (.refl trivial)
        ((ShapedSubtype.identityRev (a := .unit) trivial).trans (.congr (.refl trivial)
          (.valid fun _ _ => ⟨Mode.identity, Mode.top, rfl, rfl, by decide⟩))))

theorem combined_algebra_witness : AlgebraSubsumes [] combinedSource combinedTarget :=
  combined_shaped_witness.to_algebra

def forcedSource : Scheme :=
  { mixedSource with bounds := [.mode (.var (.flex 0)) (.const Mode.global),
      .mode (.const Mode.global) (.var (.flex 0))] }

def forcedTarget : Scheme :=
  { mixedMeetTarget with body := (.prod (.modal h bad)
      (.prod (.modal (.modal (.var (.rigid 1)) bad) (.const Mode.global))
        (.modal .unit .top))) }

def forcedWitness : CompareSubstitution :=
  { types := [(0, meetImage)], modes := [(0, .const Mode.global)] }

theorem forced_shaped_witness : ShapedSubsumes [] forcedSource forcedTarget := by
  refine ⟨forcedWitness, ?_, ?_, ?_, ?_⟩
  · simp [CompareInstantiates, forcedSource, mixedSource, forcedWitness]
  · change forcedWitness.WellShaped meetBounds
    simpa [CompareSubstitution.WellShaped, forcedWitness] using meetImage_wellShaped
  · change ShapedEntailsAll meetBounds [.mode (.const Mode.global) (.const Mode.global),
      .mode (.const Mode.global) (.const Mode.global)]
    simp only [ShapedEntailsAll, List.mem_cons, List.not_mem_nil, or_false, or_self,
      forall_eq, ShapedEntails]
    exact .valid fun _ _ => ⟨Mode.global, Mode.global, rfl, rfl, by decide⟩
  · change ShapedSubtype meetBounds
      (.prod meetImage (.prod (.modal meetImage (.const Mode.global)) .unit))
      (.prod (.modal (.var (.rigid 0)) bad)
        (.prod (.modal (.modal (.var (.rigid 1)) bad) (.const Mode.global))
          (.modal .unit .top)))
    exact ShapedSubtype.prod_congr (.meetLeft meetImage_wellShaped)
      (.prod_congr (.congr (.meetRight meetImage_wellShaped)
        (.valid fun _ _ => ⟨Mode.global, Mode.global, rfl, rfl, by decide⟩))
        ((ShapedSubtype.identityRev (a := .unit) trivial).trans (.congr (.refl trivial)
          (.valid fun _ _ => ⟨Mode.identity, Mode.top, rfl, rfl, by decide⟩))))

theorem forced_algebra_witness : AlgebraSubsumes [] forcedSource forcedTarget :=
  forced_shaped_witness.to_algebra

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
#guard [ (source, target), (sharedSource, sharedTarget), (mixedSource, mixedTarget),
    (mixedSource, mixedMeetTarget), (definedMixedSource, mixedMeetTarget),
    (combinedSource, combinedTarget), (forcedSource, forcedTarget) ].all
  fun (a, b) => (ComparisonChecker.run 20000 a b).isSuccess

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
#guard match ComparisonChecker.run 20000
    { mixedSource with bounds := [.sub (.var (.flex 0)) (.var (.flex 0))] }
    mixedMeetTarget with
  | .rejected _ => true
  | _ => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
#guard match ComparisonChecker.run 20000
    { mixedSource with bounds := [.mode .top (.var (.flex 0)),
      .mode (.var (.flex 0)) .bottom] }
    mixedMeetTarget with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonContextWitnesses
