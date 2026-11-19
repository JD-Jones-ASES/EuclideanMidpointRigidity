module

public import EuclideanMidpointRigidity.MaximizerJet

/-! # A maximizing graph parametrized by local spatial coordinates -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d

theorem critical_of_fixed_maximum {C : Cubic d} {z : E} {a : ℝ} (ha : 0<a) (hC : amplitude C=a)
    (hu : ‖z‖=1) (hm : directionProfile z C=a) : K C z z=a • z := by
  apply maximizing_axis_product ha.le _ hu ((directionProfile_apply z C).symm.trans hm)
  intro v hv
  rw [← directionProfile_apply,← hC]
  exact directionProfile_le_amplitude (by simp [Metric.mem_closedBall,dist_zero_right,hv]) _

theorem maximizing_slice_jet {Ω U : Set E} {C : E → Cubic d} {X n : E → E} {a : ℝ}
    (hΩ : IsOpen Ω) (hC : ContDiffOn ℝ ∞ C Ω) (hQ : MidpointJetEquations Ω C) (hc : ∀ q ∈ Ω, Nonempty (OrientedEndpointChart C q))
    (ha : 0<a) (hamp : ∀ q ∈ Ω, amplitude (C q)=a) (hU : IsOpen U)
    (hX : ContDiffOn ℝ ∞ X U) (hn : ContDiffOn ℝ ∞ n U)
    (hm : ∀ q ∈ U, X q ∈ Ω ∧ ‖n q‖=1 ∧ directionProfile (n q) (C (X q))=a)
    {p : E} (hp : p ∈ U) (hi : (fderiv ℝ X p).IsInvertible) :
    fderiv ℝ C (X p) (n p)=0 ∧ ∀ l, K (fderiv ℝ C (X p) l) (n p) (n p)=0 := by
  obtain ⟨V,r,hV,hpV,hrp,hr,hsol⟩ := smooth_spatial_inverse hU hX hp hi
  let e := n ∘ r
  have he : ContDiffOn ℝ ∞ e V := hn.comp hr (fun q h ↦ (hsol q h).1)
  have h (q : E) (hq : q ∈ V) : q ∈ Ω ∧ ‖e q‖=1 ∧ directionProfile (e q) (C q)=a := by
    obtain ⟨hu,hx,_⟩ := hsol q hq
    have H := hm (r q) hu
    rwa [hx] at H
  have hVΩ : V ⊆ Ω := fun q hq ↦ (h q hq).1
  have hk (q : E) (hq : q ∈ V) := critical_of_fixed_maximum ha (hamp q (hVΩ hq)) (h q hq).2.1 (h q hq).2.2
  have H := maximizing_graph_jet hV (hC.mono hVΩ) (hQ.mono hVΩ) he ha (fun q h ↦ hamp q (hVΩ h))
    (fun q hq ↦ (h q hq).2.1) hk (fun q hq ↦ hc q (hVΩ hq)) hpV
  simpa only [e,Function.comp_apply,hrp] using H

end EuclideanMidpointRigidity

