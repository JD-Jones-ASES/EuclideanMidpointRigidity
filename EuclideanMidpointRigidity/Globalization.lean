module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Passing from open patches to the connected domain -/

public section

open Set Metric
open scoped ContDiff

namespace EuclideanMidpointRigidity

/-- The last local-to-global step of the dimension induction. Every ball
centered in the domain contains a point where the derivative vanishes. -/
theorem constant_of_dense_zero_derivative {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Ω : Set V} {F : V → W} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ContDiffOn ℝ 1 F Ω)
    (hdense : ∀ x ∈ Ω, ∀ r > (0 : ℝ), ∃ y ∈ Ω, y ∈ ball x r ∧ fderiv ℝ F y = 0) :
    ∃ c, ∀ x ∈ Ω, F x = c := by
  apply hΩ.exists_is_const_of_fderiv_eq_zero hconn (hF.differentiableOn (by norm_num))
  intro x hx
  change fderiv ℝ F x = 0
  by_contra hne
  have hc := hF.continuousOn_fderiv_of_isOpen hΩ (le_refl 1) x hx
  obtain ⟨r, hr, hclose⟩ := Metric.continuousWithinAt_iff.mp hc _ (norm_pos_iff.mpr hne)
  obtain ⟨y, hy, hball, hzero⟩ := hdense x hx r hr
  have h := hclose hy (mem_ball.mp hball)
  simp [hzero] at h

end EuclideanMidpointRigidity
