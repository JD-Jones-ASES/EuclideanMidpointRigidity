module

public import EuclideanMidpointRigidity.AnalyticObstruction
public import EuclideanMidpointRigidity.CanonicalMidpoints
public import EuclideanMidpointRigidity.CriticalAxis

/-! # The quartic identity for the canonical geometric midpoint -/

@[expose] public section
namespace EuclideanMidpointRigidity
open Set

variable {d : ℕ} {Ω : Set (Space d)} {C : Space d → Cubic d}

/-- The quartic differential equation throughout a spatial domain. -/
def QuarticOn (Ω : Set (Space d)) (C : Space d → Cubic d) : Prop :=
  ∀ ⦃p⦄, p ∈ Ω → ∀ h, obstruction (C p) (fderiv ℝ C p) h = 0

/-- Complementary short-geodesic midpoints imply the Nielsen–Okamura
quartic equation in every direction, at every point of the domain. -/
theorem obstruction_of_localMidpointInvariance (hΩ : IsOpen Ω) (hc : ContDiffOn ℝ 2 C Ω)
    (hm : LocalMidpointInvariance Ω C) {p : Space d} (hp : p ∈ Ω) (h : Space d) :
    obstruction (C p) (fderiv ℝ C p) h = 0 :=
  obstruction_of_short_complementary_pairs hΩ hp hc
    (localMidpointInvariance_arbitrarilyShort hΩ hp hc hm) h

theorem QuarticOn.of_midpoint (hΩ : IsOpen Ω) (hc : ContDiffOn ℝ 2 C Ω)
    (hm : LocalMidpointInvariance Ω C) : QuarticOn Ω C :=
  fun _ hp h ↦ obstruction_of_localMidpointInvariance hΩ hc hm hp h

end EuclideanMidpointRigidity
