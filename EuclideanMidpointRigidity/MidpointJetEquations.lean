module

public import EuclideanMidpointRigidity.GeometricObstruction
public import EuclideanMidpointRigidity.GeometricSixth

/-! # The differential equations used in the maximum argument -/

@[expose] public section
open Set
open scoped ContDiff
namespace EuclideanMidpointRigidity
open Jet

variable {d : ℕ}

/-- Both identities are imposed on the same field with its actual spatial derivatives. -/
structure MidpointJetEquations (Ω : Set (Space d)) (C : Space d → Cubic d) : Prop where
  quartic : QuarticOn Ω C
  sixth : ∀ ⦃p⦄, p ∈ Ω → ∀ z : Space d,
    let f := Tree.realize (fieldDerivatives C p) z
    value affineSixth f 0 + value higherSixth f 0 = 0

theorem MidpointJetEquations.of_midpoint {Ω : Set (Space d)} {C : Space d → Cubic d}
    (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (hm : LocalMidpointInvariance Ω C) :
    MidpointJetEquations Ω C :=
  ⟨QuarticOn.of_midpoint hΩ (hC.of_le (by simp)) hm,
    fun _ hp z ↦ sixth_obstruction_of_localMidpointInvariance hΩ hC hm hp z⟩

theorem MidpointJetEquations.mono {Ω V : Set (Space d)} {C : Space d → Cubic d}
    (h : MidpointJetEquations Ω C) (hV : V ⊆ Ω) : MidpointJetEquations V C :=
  ⟨fun _ hp ↦ h.quartic (hV hp),fun _ hp ↦ h.sixth (hV hp)⟩

end EuclideanMidpointRigidity

