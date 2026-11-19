module

public import EuclideanMidpointRigidity.EigenvalueTangency

/-! # First derivatives in a moving axial eigenframe -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

theorem axis_section_coordinate {Ω : Set E} {C : E → Coeff} {e : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω)
    (hc : ∀ q ∈ Ω, K (C q) (e q) (e q)=sectionValue C e q • e q)
    {p : E} (hp : p ∈ Ω) {w : E} {b : ℝ} (hor : ⟪e p,w⟫_ℝ=0)
    (hw : K (C p) (e p) w=(b*sectionValue C e p) • w) (l : E) :
    sectionValue C e p*(1-2*b)*⟪fderiv ℝ e p l,w⟫_ℝ=⟪K (fderiv ℝ C p l) (e p) (e p),w⟫_ℝ := by
  have h := congrArg (fun v : E ↦ ⟪v,w⟫_ℝ) (critical_section_differential hΩ hC he hc hp l)
  simp only [inner_sub_left,real_inner_smul_left,K_selfAdjoint (C p) (e p) _ w,hw,
    real_inner_smul_right,hor,mul_zero,sub_zero] at h
  linarith only [h]

/-- The off-diagonal derivative of the eigenvector identity is valid even if
the two eigenvalues agree. It keeps the angular velocity as a variable. -/
theorem eigen_rotation_coordinate {Ω : Set E} {C : E → Coeff} {e f : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω) {p : E} (hp : p ∈ Ω)
    (hf : DifferentiableAt ℝ f p) {b s : ℝ}
    (heig : ∀ᶠ q in 𝓝 p, K (C q) (e q) (f q)=(b*sectionValue C e q) • f q)
    {w : E} (hw : K (C p) (e p) w=(s*sectionValue C e p) • w)
    (hor : ⟪f p,w⟫_ℝ=0) (l : E) :
    (b-s)*sectionValue C e p*⟪fderiv ℝ f p l,w⟫_ℝ=
      ⟪K (fderiv ℝ C p l) (e p) (f p),w⟫_ℝ+⟪K (C p) (fderiv ℝ e p l) (f p),w⟫_ℝ := by
  have h := congrArg (fun v : E ↦ ⟪v,w⟫_ℝ) (eigen_section_derivative hΩ hC he hp hf heig l)
  simp only [inner_add_left,real_inner_smul_left,K_selfAdjoint (C p) (e p) _ w,hw,
    real_inner_smul_right,hor,mul_zero,add_zero] at h
  linarith only [h]

/-- Differentiating the two components against a fixed vector gives a Hessian row. -/
theorem gradient_frame_derivative {A u v : E → ℝ} {x y : E → E} {p : E}
    (hA : ContDiffAt ℝ ∞ A p) (hx : DifferentiableAt ℝ x p) (hy : DifferentiableAt ℝ y p)
    (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p)
    (hg : ∀ᶠ q in 𝓝 p, gradient A q=u q • x q+v q • y q) (l w : E) :
    fderiv ℝ (fderiv ℝ A) p l w=
      u p*⟪fderiv ℝ x p l,w⟫_ℝ+fderiv ℝ u p l*⟪x p,w⟫_ℝ+
      (v p*⟪fderiv ℝ y p l,w⟫_ℝ+fderiv ℝ v p l*⟪y p,w⟫_ℝ) := by
  let line := fun t : ℝ ↦ p+t • l
  have h₀ : line 0=p := by simp [line]
  have hd : HasDerivAt line l 0 := by simpa [line] using ((hasDerivAt_id (0:ℝ)).smul_const l).const_add p
  have hJ : ContDiffAt ℝ ∞ (fderiv ℝ A) p := hA.fderiv_right (by simp)
  have dJ := (hJ.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  have dx := hx.hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  have dy := hy.hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  have du := hu.hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  have dv := hv.hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  have dw := hasDerivAt_const (0:ℝ) w
  have d₁ := dJ.clm_apply dw
  have d₂ := ((du.smul dx).fun_add (dv.smul dy)).inner ℝ dw
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), gradient A (line t)=u (line t) • x (line t)+v (line t) • y (line t) :=
    hd.continuousAt (h₀ ▸ hg)
  have h := d₁.unique (d₂.congr_of_eventuallyEq (hnear.mono fun t ht ↦ by
    change fderiv ℝ A (line t) w=⟪u (line t) • x (line t)+v (line t) • y (line t),w⟫_ℝ
    rw [← ht,inner_gradient_left]))
  simpa only [Function.comp_apply,h₀,map_zero,zero_add,add_zero,inner_zero_right,
    inner_add_left,real_inner_smul_left] using h

/-- The transverse component of the gradient derivative couples the two angular
velocities to the transpose of the derivative of the critical section. -/
theorem gradient_frame_transport {Ω : Set E} {C : E → Coeff} {e x y : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω) (hm : QuarticOn Ω C)
    (hunit : ∀ q ∈ Ω, ‖e q‖=1) (hc : ∀ q ∈ Ω, K (C q) (e q) (e q)=sectionValue C e q • e q)
    (ha : ∀ q ∈ Ω, sectionValue C e q≠0) {p : E} (hp : p ∈ Ω) {u v : E → ℝ}
    (hx : DifferentiableAt ℝ x p) (hy : DifferentiableAt ℝ y p)
    (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p)
    (hg : ∀ᶠ q in 𝓝 p, gradient (sectionValue C e) q=u q • x q+v q • y q) (w : E) :
    u p*⟪fderiv ℝ x p (e p),w⟫_ℝ+fderiv ℝ u p (e p)*⟪x p,w⟫_ℝ+
      (v p*⟪fderiv ℝ y p (e p),w⟫_ℝ+fderiv ℝ v p (e p)*⟪y p,w⟫_ℝ) =
      -(u p*⟪fderiv ℝ e p w,x p⟫_ℝ+v p*⟪fderiv ℝ e p w,y p⟫_ℝ) := by
  have h := gradient_transport_along_section hΩ hC he hm hunit hc ha hp w
  dsimp only at h
  rw [gradient_frame_derivative ((contDiffOn_sectionValue hC he).contDiffAt (hΩ.mem_nhds hp)) hx hy hu hv hg,
    ← inner_gradient_left (f := sectionValue C e),hg.self_of_nhds,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    show ⟪x p,fderiv ℝ e p w⟫_ℝ=⟪fderiv ℝ e p w,x p⟫_ℝ from real_inner_comm _ _,
    show ⟪y p,fderiv ℝ e p w⟫_ℝ=⟪fderiv ℝ e p w,y p⟫_ℝ from real_inner_comm _ _] at h
  exact h

end EuclideanMidpointRigidity
