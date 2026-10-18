import ModalityInference.Proofs.ComparisonObserverRepresentativeData
import ModalityInference.Proofs.ComparisonObserverRestriction

/-! Every genuine parent has successors in one finite representative family,
preserving a subterm-closed boundary and the original declared edges. -/
namespace ModalityInference.ComparisonObserverRepresentatives

open ComparisonAlgebra ComparisonObserverGluing ComparisonObserverProfiles
  ComparisonObserverProfileExtension ComparisonStructuralLattice

def PortsClosed (boundary : List CompareTy) : Prop :=
  ∀ a ∈ boundary, ∀ p ∈ ports a, p.2 ∈ boundary

theorem finite_successors {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (g : Child Δ) (boundary : List CompareTy) (hd : DeclaredIn Δ boundary)
    (hp : PortsClosed boundary)
    (hsb : ∀ a ∈ boundary, ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a) :
    ∃ children : Kind → Child Δ,
      (∀ k, children k ∈ representatives hs boundary) ∧
      Replacement (restrictedData hs (data hn g)) children ∧
      PortsAgree (restrictedData hs (data hn g)) children boundary ∧
      Coherent ((restrictedData hs (data hn g)).replace children) ∧
      BoundsHold ((restrictedData hs (data hn g)).replace children) ∧
      ∀ a ∈ boundary, a.DefinedUnder Δ →
        ((restrictedData hs (data hn g)).replace children).value a =
          booleanValue g.observer a := by
  have hc (k : Kind) := representatives_cover hs boundary ((data hn g).branch k).child
  choose children hmem haction hrange hvalue using hc
  have hr : Replacement (restrictedData hs (data hn g)) children :=
    ⟨fun k x hx => (hrange k x).mpr hx,
      fun k m hm x _ => (haction k m hm x).symm⟩
  have hports : PortsAgree (restrictedData hs (data hn g)) children boundary := by
    intro a ha p hpa
    exact (hvalue p.1 p.2 (hp a ha p hpa)).symm
  refine ⟨children, hmem, hr, hports,
    (restrictedData_coherent hs (data_coherent hn g)).replace hr,
    (restrictedData_bounds hs (data hn g) hn hΔ (data_bounds hn hΔ g)).replace hd hports, ?_⟩
  intro a ha had
  rw [Data.replace_value _ children _ (hports a ha),
    restrictedData_value hs (data hn g) hn had, restrictedType_fixed (hsb a ha)]
  exact data_represents hn g a had

end ModalityInference.ComparisonObserverRepresentatives
