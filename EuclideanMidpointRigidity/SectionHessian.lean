module

public import EuclideanMidpointRigidity.CriticalSection
public import EuclideanMidpointRigidity.Resonances

/-! # The spatial Hessian of a critical value in the axial jet direction -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff InnerProductSpace
namespace EuclideanMidpointRigidity

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

theorem critical_gradient_product {c : Coeff} {J : E →L[ℝ] Coeff} {z g : E} {a : ℝ}
    (hc : K c z z=a • z) (h₄ : ∀ v, obstruction c J v=0)
    (hg : ∀ l, ⟪K (J l) z z,z⟫_ℝ=⟪g,l⟫_ℝ) :
    K c z g=(a/5) • g-(13*a/10) • K (J z) z z := by
  obtain ⟨hU,hV⟩ := critical_axis_resonances hc h₄ hg
  simp only [sub_eq_add_neg,K_add_right,K_neg_right,K_smul_right,smul_add,smul_neg,smul_smul,hU] at hV
  linear_combination (norm := module) hV

theorem section_axial_hessian {Ω : Set E} {C : E → Coeff} {e : E → E} (hΩ : IsOpen Ω)
    (hC : ContDiffOn ℝ ∞ C Ω) (he : ContDiffOn ℝ ∞ e Ω) (hm : QuarticOn Ω C)
    (hunit : ∀ x ∈ Ω, ‖e x‖=1) (hc : ∀ x ∈ Ω, K (C x) (e x) (e x)=sectionValue C e x • e x)
    (ha : ∀ x ∈ Ω, sectionValue C e x≠0) {p : E} (hp : p ∈ Ω) :
    let A := sectionValue C e
    let a := A p
    let z := e p
    let g := gradient A p
    let J := fderiv ℝ C p
    let U := K (J z) z z
    let r := K (J U) z z
    6*a*fderiv ℝ (fderiv ℝ A) p z U = 13*⟪U,r⟫_ℝ-10*⟪g,r⟫_ℝ := by
  let A := sectionValue C e
  let a := A p
  let z := e p
  let g := gradient A p
  let J := fderiv ℝ C p
  let U := K (J z) z z
  let r := K (J U) z z
  let q := fderiv ℝ e p U
  have hg (l : E) : ⟪K (J l) z z,z⟫_ℝ=⟪g,l⟫_ℝ :=
    (sectionValue_gradient hΩ hC he hunit hp (hc p hp) l).symm
  have h₄ := hm hp
  have hU : K (C p) z U = (-a/2) • U := (critical_axis_resonances (hc p hp) h₄ hg).1
  have hG : K (C p) z g = (a/5) • g-(13*a/10) • U := critical_gradient_product (hc p hp) h₄ hg
  have huz : ⟪U,z⟫_ℝ=0 := critical_axial_orthogonal (ha p hp) (hc p hp) (h₄ z)
  have hgz : ⟪g,z⟫_ℝ=0 := (hg z).symm.trans huz
  have hdiff : a • q-(2:ℝ) • K (C p) z q=r-(fderiv ℝ A p U) • z :=
    critical_section_differential hΩ hC he hc hp U
  have hqg := congrArg (fun w : E ↦ ⟪g,w⟫_ℝ) hdiff
  have hqu := congrArg (fun w : E ↦ ⟪U,w⟫_ℝ) hdiff
  simp only [inner_sub_right,real_inner_smul_right,huz,hgz,mul_zero,sub_zero,
    ← K_selfAdjoint (C p) z g q,← K_selfAdjoint (C p) z U q,hG,hU,inner_sub_left,
    real_inner_smul_left] at hqg hqu
  have hh := gradient_transport_along_section hΩ hC he hm hunit hc ha hp U
  change fderiv ℝ (fderiv ℝ A) p z U = -fderiv ℝ A p q at hh
  rw [← inner_gradient_left] at hh
  change 6*a*fderiv ℝ (fderiv ℝ A) p z U = 13*⟪U,r⟫_ℝ-10*⟪g,r⟫_ℝ
  rw [hh]
  change 6*a*(-⟪g,q⟫_ℝ) = _
  linarith only [hqg,hqu]

end EuclideanMidpointRigidity
