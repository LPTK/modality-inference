import ModalityInference.Proofs.ComparisonPartialCarrierInterpretation
import ModalityInference.Proofs.ComparisonDefinedCovers

namespace ModalityInference.ComparisonPartialCarrier

 theorem compatible_prod {Δ : Bounds} {a b c d : CompareTy}
    (h : ComparisonAlgebra.Compatible Δ (.prod a b) (.prod c d)) :
    ComparisonAlgebra.Compatible Δ a c ∧ ComparisonAlgebra.Compatible Δ b d := by
  have hab := CompareTy.definedUnder_prod_iff.mp h.2.1
  have hcd := CompareTy.definedUnder_prod_iff.mp h.2.2
  have hs : ComparisonShape.Equivalent Δ a.shape c.shape ∧
      ComparisonShape.Equivalent Δ b.shape d.shape := by
    constructor
    all_goals intro ρ hρ; have hh := h.1.2.2 ρ hρ
    · exact (ComparisonShape.prod.inj hh).1
    · exact (ComparisonShape.prod.inj hh).2
  exact ⟨⟨⟨h.1.1.1, h.1.2.1.1, hs.1⟩, hab.1, hcd.1⟩,
    ⟨⟨h.1.1.2, h.1.2.1.2, hs.2⟩, hab.2, hcd.2⟩⟩

 theorem LowerIdeal.prod_factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (S T : LowerIdeal Δ) {a : CompareTy}
    (h : LowerClosure Δ (BinaryImage .prod S.mem T.mem) a) :
    ∃ b c, S.mem b ∧ T.mem c ∧ AlgebraSubtype Δ a (.prod b c) := by
  obtain ⟨d, hd, had⟩ := h.factor hΔ (fun a ha => by
    obtain ⟨b, c, hb, hc, rfl⟩ := ha
    exact ⟨S.carrier _ hb, T.carrier _ hc⟩) (fun a b ha hb hc => by
      obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := ha
      obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := hb
      obtain ⟨hc₁, hc₂⟩ := compatible_prod hc
      refine ⟨.prod (.join a₁ b₁) (.join a₂ b₂),
        ⟨_, _, S.join _ _ hc₁ ha₁ hb₁, T.join _ _ hc₂ ha₂ hb₂, rfl⟩, ?_, ?_⟩
      · exact ComparisonDefinedCovers.prod_congr (.shaped (.joinLeft hc₁.1))
          (.shaped (.joinLeft hc₂.1))
      · exact ComparisonDefinedCovers.prod_congr (.shaped (.joinRight hc₁.1))
          (.shaped (.joinRight hc₂.1)))
  obtain ⟨b, c, hb, hc, rfl⟩ := hd
  exact ⟨b, c, hb, hc, had⟩

 theorem compatible_sum {Δ : Bounds} {a b c d : CompareTy}
    (h : ComparisonAlgebra.Compatible Δ (.sum a b) (.sum c d)) :
    ComparisonAlgebra.Compatible Δ a c ∧ ComparisonAlgebra.Compatible Δ b d := by
  have hab := CompareTy.definedUnder_sum_iff.mp h.2.1
  have hcd := CompareTy.definedUnder_sum_iff.mp h.2.2
  have hs : ComparisonShape.Equivalent Δ a.shape c.shape ∧
      ComparisonShape.Equivalent Δ b.shape d.shape := by
    constructor
    all_goals intro ρ hρ; have hh := h.1.2.2 ρ hρ
    · exact (ComparisonShape.sum.inj hh).1
    · exact (ComparisonShape.sum.inj hh).2
  exact ⟨⟨⟨h.1.1.1, h.1.2.1.1, hs.1⟩, hab.1, hcd.1⟩,
    ⟨⟨h.1.1.2, h.1.2.1.2, hs.2⟩, hab.2, hcd.2⟩⟩

 theorem LowerIdeal.sum_factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (S T : LowerIdeal Δ) {a : CompareTy}
    (h : LowerClosure Δ (BinaryImage .sum S.mem T.mem) a) :
    ∃ b c, S.mem b ∧ T.mem c ∧ AlgebraSubtype Δ a (.sum b c) := by
  obtain ⟨d, hd, had⟩ := h.factor hΔ (fun a ha => by
    obtain ⟨b, c, hb, hc, rfl⟩ := ha
    exact ⟨S.carrier _ hb, T.carrier _ hc⟩) (fun a b ha hb hc => by
      obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := ha
      obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := hb
      obtain ⟨hc₁, hc₂⟩ := compatible_sum hc
      refine ⟨.sum (.join a₁ b₁) (.join a₂ b₂),
        ⟨_, _, S.join _ _ hc₁ ha₁ hb₁, T.join _ _ hc₂ ha₂ hb₂, rfl⟩, ?_, ?_⟩
      · exact ComparisonDefinedCovers.sum_congr (.shaped (.joinLeft hc₁.1))
          (.shaped (.joinLeft hc₂.1))
      · exact ComparisonDefinedCovers.sum_congr (.shaped (.joinRight hc₁.1))
          (.shaped (.joinRight hc₂.1)))
  obtain ⟨b, c, hb, hc, rfl⟩ := hd
  exact ⟨b, c, hb, hc, had⟩
 theorem UpperIdeal.prod_factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (S T : UpperIdeal Δ) {a : CompareTy}
    (h : UpperClosure Δ (BinaryImage .prod S.mem T.mem) a) :
    ∃ b c, S.mem b ∧ T.mem c ∧ AlgebraSubtype Δ (.prod b c) a := by
  obtain ⟨d, hd, had⟩ := h.factor hΔ (fun a ha => by
    obtain ⟨b, c, hb, hc, rfl⟩ := ha
    exact ⟨S.carrier _ hb, T.carrier _ hc⟩) (fun a b ha hb hc => by
      obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := ha
      obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := hb
      obtain ⟨hc₁, hc₂⟩ := compatible_prod hc
      refine ⟨.prod (.meet a₁ b₁) (.meet a₂ b₂),
        ⟨_, _, S.meet _ _ hc₁ ha₁ hb₁, T.meet _ _ hc₂ ha₂ hb₂, rfl⟩, ?_, ?_⟩
      · exact ComparisonDefinedCovers.prod_congr (.shaped (.meetLeft hc₁.1))
          (.shaped (.meetLeft hc₂.1))
      · exact ComparisonDefinedCovers.prod_congr (.shaped (.meetRight hc₁.1))
          (.shaped (.meetRight hc₂.1)))
  obtain ⟨b, c, hb, hc, rfl⟩ := hd
  exact ⟨b, c, hb, hc, had⟩
 theorem UpperIdeal.sum_factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (S T : UpperIdeal Δ) {a : CompareTy}
    (h : UpperClosure Δ (BinaryImage .sum S.mem T.mem) a) :
    ∃ b c, S.mem b ∧ T.mem c ∧ AlgebraSubtype Δ (.sum b c) a := by
  obtain ⟨d, hd, had⟩ := h.factor hΔ (fun a ha => by
    obtain ⟨b, c, hb, hc, rfl⟩ := ha
    exact ⟨S.carrier _ hb, T.carrier _ hc⟩) (fun a b ha hb hc => by
      obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := ha
      obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := hb
      obtain ⟨hc₁, hc₂⟩ := compatible_sum hc
      refine ⟨.sum (.meet a₁ b₁) (.meet a₂ b₂),
        ⟨_, _, S.meet _ _ hc₁ ha₁ hb₁, T.meet _ _ hc₂ ha₂ hb₂, rfl⟩, ?_, ?_⟩
      · exact ComparisonDefinedCovers.sum_congr (.shaped (.meetLeft hc₁.1))
          (.shaped (.meetLeft hc₂.1))
      · exact ComparisonDefinedCovers.sum_congr (.shaped (.meetRight hc₁.1))
          (.shaped (.meetRight hc₂.1)))
  obtain ⟨b, c, hb, hc, rfl⟩ := hd
  exact ⟨b, c, hb, hc, had⟩
 theorem compatible_fn {Δ : Bounds} {a b c d : CompareTy}
    (h : ComparisonAlgebra.Compatible Δ (.fn a b) (.fn c d)) :
    ComparisonAlgebra.Compatible Δ a c ∧ ComparisonAlgebra.Compatible Δ b d := by
  have hab := CompareTy.definedUnder_fn_iff.mp h.2.1
  have hcd := CompareTy.definedUnder_fn_iff.mp h.2.2
  have hs : ComparisonShape.Equivalent Δ a.shape c.shape ∧
      ComparisonShape.Equivalent Δ b.shape d.shape := by
    constructor
    all_goals intro ρ hρ; have hh := h.1.2.2 ρ hρ
    · exact (ComparisonShape.fn.inj hh).1
    · exact (ComparisonShape.fn.inj hh).2
  exact ⟨⟨⟨h.1.1.1, h.1.2.1.1, hs.1⟩, hab.1, hcd.1⟩,
    ⟨⟨h.1.1.2, h.1.2.1.2, hs.2⟩, hab.2, hcd.2⟩⟩
 theorem LowerIdeal.fn_factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (S : UpperIdeal Δ) (T : LowerIdeal Δ) {a : CompareTy}
    (h : LowerClosure Δ (BinaryImage .fn S.mem T.mem) a) :
    ∃ b c, S.mem b ∧ T.mem c ∧ AlgebraSubtype Δ a (.fn b c) := by
  obtain ⟨d, hd, had⟩ := h.factor hΔ (fun a ha => by
    obtain ⟨b, c, hb, hc, rfl⟩ := ha
    exact ⟨S.carrier _ hb, T.carrier _ hc⟩) (fun a b ha hb hc => by
      obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := ha
      obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := hb
      obtain ⟨hc₁, hc₂⟩ := compatible_fn hc
      refine ⟨.fn (.meet a₁ b₁) (.join a₂ b₂),
        ⟨_, _, S.meet _ _ hc₁ ha₁ hb₁, T.join _ _ hc₂ ha₂ hb₂, rfl⟩, ?_, ?_⟩
      · exact ComparisonDefinedCovers.fn_congr (.shaped (.meetLeft hc₁.1))
          (.shaped (.joinLeft hc₂.1))
      · exact ComparisonDefinedCovers.fn_congr (.shaped (.meetRight hc₁.1))
          (.shaped (.joinRight hc₂.1)))
  obtain ⟨b, c, hb, hc, rfl⟩ := hd
  exact ⟨b, c, hb, hc, had⟩
 theorem UpperIdeal.fn_factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (S : LowerIdeal Δ) (T : UpperIdeal Δ) {a : CompareTy}
    (h : UpperClosure Δ (BinaryImage .fn S.mem T.mem) a) :
    ∃ b c, S.mem b ∧ T.mem c ∧ AlgebraSubtype Δ (.fn b c) a := by
  obtain ⟨d, hd, had⟩ := h.factor hΔ (fun a ha => by
    obtain ⟨b, c, hb, hc, rfl⟩ := ha
    exact ⟨S.carrier _ hb, T.carrier _ hc⟩) (fun a b ha hb hc => by
      obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := ha
      obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := hb
      obtain ⟨hc₁, hc₂⟩ := compatible_fn hc
      refine ⟨.fn (.join a₁ b₁) (.meet a₂ b₂),
        ⟨_, _, S.join _ _ hc₁ ha₁ hb₁, T.meet _ _ hc₂ ha₂ hb₂, rfl⟩, ?_, ?_⟩
      · exact ComparisonDefinedCovers.fn_congr (.shaped (.joinLeft hc₁.1))
          (.shaped (.meetLeft hc₂.1))
      · exact ComparisonDefinedCovers.fn_congr (.shaped (.joinRight hc₁.1))
          (.shaped (.meetRight hc₂.1)))
  obtain ⟨b, c, hb, hc, rfl⟩ := hd
  exact ⟨b, c, hb, hc, had⟩

end ModalityInference.ComparisonPartialCarrier
