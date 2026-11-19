module

public import EuclideanMidpointRigidity.CriticalBranch
public import EuclideanMidpointRigidity.SpatialProlongation
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Spatial derivatives of a smooth section of critical directions -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

def sectionValue (C : E → Coeff) (e : E → E) (p : E) : ℝ :=
  ⟪K (C p) (e p) (e p),e p⟫_ℝ

set_option backward.isDefEq.respectTransparency false in
theorem contDiffOn_sectionValue {Ω : Set E} {C : E → Coeff} {e : E → E}
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω) : ContDiffOn ℝ ∞ (sectionValue C e) Ω := by
  let inc : Coeff →L[ℝ] (E →L[ℝ] E →L[ℝ] E) := (cubicSubspace d).subtypeL
  have hinc := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) («E» := Coeff)
    (F := E →L[ℝ] E →L[ℝ] E) inc
  have hi : ContDiffOn ℝ ∞ (inc ∘ C) Ω := ContDiff.comp_contDiffOn
    («E» := E) (F := Coeff) (G := E →L[ℝ] E →L[ℝ] E) hinc hC
  exact ((hi.clm_apply he).clm_apply he).inner ℝ he

private theorem line_derivative (p l : E) : HasDerivAt (fun t : ℝ ↦ p+t • l) l 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).smul_const l).const_add p

theorem sectionValue_gradient {Ω : Set E} {C : E → Coeff} {e : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω)
    (hunit : ∀ x ∈ Ω, ‖e x‖=1) {p : E} (hp : p ∈ Ω) {a : ℝ}
    (hc : K (C p) (e p) (e p)=a • e p) (l : E) :
    ⟪gradient (sectionValue C e) p,l⟫_ℝ = ⟪K (fderiv ℝ C p l) (e p) (e p),e p⟫_ℝ := by
  let line := fun t : ℝ ↦ p+t • l
  have h₀ : line 0=p := by simp [line]
  have hd : HasDerivAt line l 0 := line_derivative p l
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), line t ∈ Ω := hd.continuousAt (h₀ ▸ hΩ.mem_nhds hp)
  have dC := ((hC.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hd h₀.symm
  have de := ((he.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hd h₀.symm
  have hA := hasDerivAt_critical_value dC de (hnear.mono fun t ht ↦ hunit _ ht)
    (by simpa only [Function.comp_apply,h₀] using hc)
  have hF := (((contDiffOn_sectionValue hC he).contDiffAt (hΩ.mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  rw [inner_gradient_left]
  simpa only [Function.comp_apply,h₀] using hF.unique hA

theorem critical_section_differential {Ω : Set E} {C : E → Coeff} {e : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω)
    (hc : ∀ x ∈ Ω, K (C x) (e x) (e x)=sectionValue C e x • e x)
    {p : E} (hp : p ∈ Ω) (l : E) :
    sectionValue C e p • fderiv ℝ e p l - (2:ℝ) • K (C p) (e p) (fderiv ℝ e p l) =
      K (fderiv ℝ C p l) (e p) (e p) - (fderiv ℝ (sectionValue C e) p l) • e p := by
  let line := fun t : ℝ ↦ p+t • l
  have h₀ : line 0=p := by simp [line]
  have hd : HasDerivAt line l 0 := line_derivative p l
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), line t ∈ Ω := hd.continuousAt (h₀ ▸ hΩ.mem_nhds hp)
  have dC := ((hC.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hd h₀.symm
  have de := ((he.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hd h₀.symm
  have dA := (((contDiffOn_sectionValue hC he).contDiffAt (hΩ.mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  have lhs := hasDerivAt_K dC de de
  have rhs := dA.smul de
  have h := lhs.unique (rhs.congr_of_eventuallyEq (hnear.mono fun t ht ↦ hc _ ht))
  simp only [Function.comp_apply,h₀,K_symm (C p) (fderiv ℝ e p l) (e p)] at h
  linear_combination (norm := module) -h

theorem critical_section_value_along_axis {Ω : Set E} {C : E → Coeff} {e : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω) (hm : QuarticOn Ω C)
    (hunit : ∀ x ∈ Ω, ‖e x‖=1) {p : E} (hp : p ∈ Ω) {a : ℝ} (ha : a≠0)
    (hc : K (C p) (e p) (e p)=a • e p) : fderiv ℝ (sectionValue C e) p (e p)=0 := by
  rw [← inner_gradient_left,sectionValue_gradient hΩ hC he hunit hp hc]
  exact critical_axial_orthogonal ha hc (hm hp _)

/-- The differentiated identity `Dₑ a = 0` determines the Hessian with
one axial argument, including when the spherical Hessian is singular. -/
theorem gradient_transport_along_section {Ω : Set E} {C : E → Coeff} {e : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω) (hm : QuarticOn Ω C)
    (hunit : ∀ x ∈ Ω, ‖e x‖=1) (hc : ∀ x ∈ Ω, K (C x) (e x) (e x)=sectionValue C e x • e x)
    (ha : ∀ x ∈ Ω, sectionValue C e x≠0) {p : E} (hp : p ∈ Ω) (l : E) :
    let A := sectionValue C e
    fderiv ℝ (fderiv ℝ A) p (e p) l = -fderiv ℝ A p (fderiv ℝ e p l) := by
  let A := sectionValue C e
  let line := fun t : ℝ ↦ p+t • l
  have h₀ : line 0=p := by simp [line]
  have hd : HasDerivAt line l 0 := line_derivative p l
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), line t ∈ Ω := hd.continuousAt (h₀ ▸ hΩ.mem_nhds hp)
  have hA : ContDiffAt ℝ ∞ A p := (contDiffOn_sectionValue hC he).contDiffAt (hΩ.mem_nhds hp)
  have hJ : ContDiffAt ℝ 1 (fderiv ℝ A) p := hA.fderiv_right (by simp)
  have dJ := (hJ.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd h₀.symm
  have de := ((he.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hd h₀.symm
  have hz : HasDerivAt (fun t ↦ fderiv ℝ A (line t) (e (line t))) 0 0 :=
    (hasDerivAt_const 0 (0:ℝ)).congr_of_eventuallyEq (hnear.mono fun t ht ↦
      critical_section_value_along_axis hΩ hC he hm hunit ht (ha _ ht) (hc _ ht))
  have h := (dJ.clm_apply de).unique hz
  simp only [Function.comp_apply,h₀] at h
  change fderiv ℝ (fderiv ℝ A) p (e p) l = _
  rw [(hA.isSymmSndFDerivAt (by simp)) (e p) l]
  linarith only [h]

end EuclideanMidpointRigidity
