module

public import EuclideanMidpointRigidity.SectionAmplitude

/-! # Straight maximizing directions and the derivative of their direction field -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d

def displacementLine (p l : E) (t : ℝ) := p+t • l

@[simp] theorem displacementLine_zero (p l : E) : displacementLine p l 0=p := by simp [displacementLine]

theorem hasDerivAt_displacementLine (p l : E) : HasDerivAt (displacementLine p l) l 0 := by
  change HasDerivAt (fun t : ℝ ↦ p+t • l) l 0
  simpa using ((hasDerivAt_id (0:ℝ)).smul_const l).const_add p

theorem differentiableAlongLine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {p : E} (hf : DifferentiableAt ℝ f p) (l : E) :
    HasDerivAt (f ∘ displacementLine p l) (fderiv ℝ f p l) 0 :=
  hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_displacementLine p l) (displacementLine_zero p l).symm

namespace LiftedSection
variable (S : LiftedSection d)

theorem stationary_value {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    fderiv ℝ S.a p=0 := by
  rw [← toDual_gradient (f := S.a), S.gradient_zero hp ((show ∀ᶠ q in 𝓝 p, q ∈ S.domain from S.isOpen.mem_nhds hp).mono hm), map_zero]

theorem stationary_axial_component {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) (l : E) :
    ⟪K (fderiv ℝ S.field p l) (S.axis p) (S.axis p),S.axis p⟫_ℝ=0 := by
  rw [← sectionValue_gradient S.isOpen S.smooth S.smoothAxis S.unit hp (S.critical _ hp),inner_gradient_left]
  exact congrArg (fun f : E →L[ℝ] ℝ ↦ f l) (S.stationary_value hp hm)

theorem stationary_axial_source {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    K (fderiv ℝ S.field p (S.axis p)) (S.axis p) (S.axis p)=0 := by
  let U := K (fderiv ℝ S.field p (S.axis p)) (S.axis p) (S.axis p)
  have h := critical_axis_source (S.positive p hp).ne' (S.critical _ hp) (S.equations.quartic hp)
  change 7*⟪K (fderiv ℝ S.field p U) (S.axis p) (S.axis p),S.axis p⟫_ℝ=13*⟪U,U⟫_ℝ at h
  rw [S.stationary_axial_component hp hm U] at h
  exact inner_self_eq_zero.mp (show ⟪U,U⟫_ℝ=0 by linarith)

theorem straight_axis {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) :
    fderiv ℝ S.axis p (S.axis p)=0 := by
  rw [S.lift p hp,liftStep,S.stationary_axial_source hp hm,smul_zero]

theorem axis_derivative_transverse {p : E} (hp : p ∈ S.domain) (l : E) :
    ⟪fderiv ℝ S.axis p l,S.axis p⟫_ℝ=0 := by
  let line := displacementLine p l
  have h₀ : line 0=p := displacementLine_zero p l
  have hn₀ : S.domain ∈ 𝓝 (line 0) := by rw [h₀]; exact S.isOpen.mem_nhds hp
  have hn : ∀ᶠ t in 𝓝 (0:ℝ), line t ∈ S.domain := (hasDerivAt_displacementLine p l).continuousAt hn₀
  have he := differentiableAlongLine ((S.smoothAxis.contDiffAt (S.isOpen.mem_nhds hp)).differentiableAt (by simp)) l
  have hz : HasDerivAt (fun t ↦ ⟪S.axis (line t),S.axis (line t)⟫_ℝ) 0 0 :=
    (hasDerivAt_const 0 (1:ℝ)).congr_of_eventuallyEq <| hn.mono fun t ht ↦ by
      change ⟪S.axis (line t),S.axis (line t)⟫_ℝ=1
      rw [real_inner_self_eq_norm_sq,S.unit (line t) ht,one_pow]
  have h := (he.inner ℝ he).unique hz
  simp only [Function.comp_apply,displacementLine_zero,real_inner_comm (S.axis p)] at h
  rw [real_inner_comm]
  linarith only [h]

/-- Differentiating the straight-line equation gives the Riccati equation for the spatial derivative. -/
theorem axis_riccati {p : E} (hp : p ∈ S.domain) (hm : ∀ q ∈ S.domain, S.Maximizes q) (l : E) :
    fderiv ℝ (fderiv ℝ S.axis) p (S.axis p) l = -fderiv ℝ S.axis p (fderiv ℝ S.axis p l) := by
  let line := displacementLine p l
  have h₀ : line 0=p := displacementLine_zero p l
  have hn₀ : S.domain ∈ 𝓝 (line 0) := by rw [h₀]; exact S.isOpen.mem_nhds hp
  have hn : ∀ᶠ t in 𝓝 (0:ℝ), line t ∈ S.domain := (hasDerivAt_displacementLine p l).continuousAt hn₀
  have he := S.smoothAxis.contDiffAt (S.isOpen.mem_nhds hp)
  have hA : ContDiffAt ℝ 1 (fderiv ℝ S.axis) p := he.fderiv_right (by simp)
  have dA := differentiableAlongLine (hA.differentiableAt (by norm_num)) l
  have de := differentiableAlongLine (he.differentiableAt (by simp)) l
  have hz : HasDerivAt (fun t ↦ fderiv ℝ S.axis (line t) (S.axis (line t))) 0 0 :=
    (hasDerivAt_const 0 (0:E)).congr_of_eventuallyEq <| hn.mono fun _ ht ↦ S.straight_axis ht hm
  have h := (dA.clm_apply de).unique hz
  simp only [Function.comp_apply,displacementLine_zero] at h
  rw [(he.isSymmSndFDerivAt (by simp)) (S.axis p) l]
  linear_combination (norm := module) h

end LiftedSection
end EuclideanMidpointRigidity

