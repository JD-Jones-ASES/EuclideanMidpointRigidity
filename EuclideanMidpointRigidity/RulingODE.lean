module

public import EuclideanMidpointRigidity.RulingDifference
public import EuclideanMidpointRigidity.DifferenceLimit

/-! # A uniform sixth-order ODE for the mixed derivative on a maximizing line -/

public section
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
open Endpoint

theorem Endpoint.iteratedDeriv_iterated (n m : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv n (iteratedDeriv m f)=iteratedDeriv (n+m) f := by
  simp only [iteratedDeriv_eq_iterate,Function.iterate_add_apply]

theorem RulingResponseLaws.tilt_equation {W : Set ℝ} {η κ : ℝ} {Q P : ℝ → ℝ}
    (H : RulingResponseLaws W η κ Q P) (hW : IsOpen W) {p : ℝ} (hp : p ∈ W) :
    iteratedDeriv 6 P p=(tiltRate κ+1)*iteratedDeriv 4 P p-tiltRate κ*iteratedDeriv 2 P p := by
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hp)
  let U := ball p δ
  have hpU : p ∈ U := mem_ball_self hδ
  let F := iteratedDeriv 3 P
  let G := iteratedDeriv 1 P
  let r := tiltRate κ
  let V := F-(fun y ↦ r*G y)
  have hF := smooth_line_derivative hW H.smoothP 3
  have hG := smooth_line_derivative hW H.smoothP 1
  have smooth : ContDiffOn ℝ ∞ V W := hF.sub (contDiffOn_const.mul hG)
  have near (a : ℝ) : ∀ᶠ t in 𝓝 (0:ℝ), p+a*t ∈ U :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousAt (isOpen_ball.mem_nhds (by simpa using hpU : p+a*0 ∈ U))
  have he : ∀ᶠ t in 𝓝 (0:ℝ), lineDifference t V p=0 := by
    filter_upwards [near 1,near 2,near 3] with t h₁ h₂ h₃
    exact (H.mono hsub).difference_equation isOpen_ball (convex_ball p δ).isPreconnected
      (show p ∈ differenceDomain U t from ⟨⟨⟨hpU,by simpa using h₁⟩,h₂⟩,h₃⟩)
  have heq := differential_equation_of_difference hW smooth hp he
  have dV (n : ℕ) : iteratedDeriv n V p=iteratedDeriv (n+3) P p-r*iteratedDeriv (n+1) P p := by
    have h₁ : ContDiffAt ℝ n F p := (hF.contDiffAt (hW.mem_nhds hp)).of_le (by simp)
    have h₂ : ContDiffAt ℝ n (fun y ↦ r*G y) p := contDiffAt_const.mul ((hG.contDiffAt (hW.mem_nhds hp)).of_le (by simp))
    rw [show V=F-(fun y ↦ r*G y) from rfl,iteratedDeriv_sub h₁ h₂,iteratedDeriv_const_mul_field]
    simp only [F,G,iteratedDeriv_iterated]
  rw [dV,dV] at heq
  change iteratedDeriv 6 P p-r*iteratedDeriv 4 P p=iteratedDeriv 4 P p-r*iteratedDeriv 2 P p at heq
  change _=(r+1)*_-r*_
  linarith only [heq]

end EuclideanMidpointRigidity

